/* lazy-bench.c -- bench-only instrument: what does stage 2's escape-list-driven
   decode cost, and what would a lazy stage 2 leave behind?

   This is a cost probe, not a kernel unit and not a candidate for the tree's
   contract.  It links the route's own kernel objects at the route's compiler
   line, stages the caller's buffers the way `workspace.cc` shapes them, and
   times six acts in one binary and one session, rotating the acts within each
   round so every reading is a same-session pair:

     stage2        `leanllvm_json_stage2` over the pipeline's entry and escape
                   streams (the committed walk, S2_VAL | S2_STR | S2_EV);
     stage2_plain  the same walk with an empty escape list: every body takes the
                   input-span form, so no body is decoded and none is validated
                   against the list.  This is the committed ABI, and it is the
                   *lower* bound of a lazy stage 2;
     expand_arena  `leanllvm_json_escape_expand` over the escaped bodies, in
                   order, into the arena -- the deferred decode a consumer would
                   pay if it materialised the strings itself;
     expand_l1     the same calls, each body decoded into one reused 4 KiB
                   scratch instead of the 55,931-byte arena: the decode and its
                   validation without the materialisation.  Its per-body bytes
                   are gated against the arena slice, so the work is the same
                   and only the destination differs;
     copy_arena    `memcpy` of `ndst` bytes from the document into the arena:
                   the floor of writing the decoded extent at all;
     pipeline      `leanllvm_json_pipeline` (the anchor the route's native
                   interval is measured at).

   The gates are the cost profile's where they apply: the reference pipeline
   must accept with the recorded words, stage 2 over the same streams must
   reproduce the arena and events, the direct expander must reproduce the arena
   and the cursor, and each `expand_l1` body must equal its arena slice.  A gate
   failure exits 3 and prints nothing as a measurement.

   Usage: lazy-bench --doc <path> [--rounds N] [--reps N] [--core N]
   Exit status: 0 on a complete run with every gate held, 2 on a bad argument,
   3 on a gate failure. */
#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "entry.h"
#include "escape.h"
#include "pipeline.h"
#include "stage2.h"

#define ARM 2ULL
#define EXPECT_SIZE 65536ULL
#define EXPECT_NXP 1772ULL
#define EXPECT_NDST 55931ULL
#define EXPECT_NEV 8907ULL
#define EXPECT_ESCAPED_BODIES 620ULL
#define SCRATCH_BYTES 4096
#define CHAIN_IT 2000000ULL

static volatile uint64_t sink;

/* ---------------------------------------------------------------- time -- */
static uint64_t now_ns(void) {
  struct timespec t;
  if (clock_gettime(CLOCK_MONOTONIC_RAW, &t) != 0) {
    perror("clock_gettime");
    exit(2);
  }
  return (uint64_t)t.tv_sec * 1000000000ull + (uint64_t)t.tv_nsec;
}

/* The calibrated clock, the cost profile's own: `add $1; dec; jne` is one
   iteration per cycle on this part. */
static uint64_t clock_chain(uint64_t it) {
  uint64_t x = 0;
  __asm__ volatile("1: add $1, %0\n\tdec %1\n\tjne 1b"
                   : "+r"(x), "+r"(it)
                   :
                   : "cc");
  return x + it;
}

/* --------------------------------------------------------------- stats -- */
static int cmp_u64(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return x < y ? -1 : x > y ? 1 : 0;
}

static uint64_t median_of(const uint64_t *v, size_t n) {
  uint64_t *t = malloc(n * sizeof *t);
  if (t == NULL) { fprintf(stderr, "lazy-bench: out of memory\n"); exit(2); }
  memcpy(t, v, n * sizeof *t);
  qsort(t, n, sizeof *t, cmp_u64);
  uint64_t m = t[(n - 1) / 2];
  free(t);
  return m;
}

typedef struct { uint64_t median, min, max; } summary;

static summary summarise(const uint64_t *v, size_t n) {
  summary s;
  s.median = median_of(v, n);
  s.min = s.max = v[0];
  for (size_t i = 1; i < n; i++) {
    if (v[i] < s.min) s.min = v[i];
    if (v[i] > s.max) s.max = v[i];
  }
  return s;
}

/* ----------------------------------------------------------- allocation -- */
static void *xalloc(size_t n) {
  void *p = malloc(n ? n : 1);
  if (p == NULL) { fprintf(stderr, "lazy-bench: out of memory\n"); exit(2); }
  return p;
}

/* ------------------------------------------------------------- staging -- */
typedef struct {
  const uint8_t *doc;
  const uint8_t *src;
  uint64_t n, nb, doc_off;
  uint8_t *win;
  uint64_t epcap, xpcap, dstcap, evcap;
  uint32_t *ep, *xp;
  uint8_t *dst, *ev;
  uint64_t *sc, *mk, *entw, *xcarry;   /* s1_carry, s1_masks, the entry
                                           word, the escape list's carry */
  uint64_t nk, nxp, ndst, nev, err;
} state;

static void state_init(state *s, const uint8_t *src, uint64_t n) {
  memset(s, 0, sizeof *s);
  s->src = src;
  s->n = n;
  s->nb = (n + 63) >> 6;
  s->doc_off = 3;
  s->win = (uint8_t *)xalloc((size_t)n + (size_t)s->doc_off + 64);
  s->doc = s->win + s->doc_off;
  s->epcap = 64 * s->nb + 9;
  s->xpcap = 64 * s->nb + 8;
  s->dstcap = n + 64;
  s->evcap = 13 * n + 128;
  s->ep = (uint32_t *)xalloc((size_t)s->epcap * 4);
  s->xp = (uint32_t *)xalloc((size_t)s->xpcap * 4);
  s->dst = (uint8_t *)xalloc((size_t)s->dstcap);
  s->ev = (uint8_t *)xalloc((size_t)s->evcap);
  s->sc = (uint64_t *)xalloc(3 * sizeof(uint64_t));
  s->mk = (uint64_t *)xalloc(6 * sizeof(uint64_t));
  s->entw = (uint64_t *)xalloc(sizeof(uint64_t));
  s->xcarry = (uint64_t *)xalloc(2 * sizeof(uint64_t));
}

static void reset_pipeline(state *s) {
  memset(s->sc, 0, 24);
  memset(s->mk, 0, 48);
  memset(s->entw, 0, 8);
  memset(s->xcarry, 0, 16);
  s->nk = s->nxp = s->ndst = s->nev = s->err = 0;
}

static uint64_t run_pipeline(state *s) {
  memset(s->win, 0, (size_t)s->doc_off);
  memcpy(s->win + s->doc_off, s->src, (size_t)s->n);
  memset(s->win + s->doc_off + s->n, 0, 64);
  return leanllvm_json_pipeline(s->doc, s->n, s->sc, s->mk, s->entw, s->ep,
                                s->epcap, &s->nk, s->xp, s->xpcap, &s->nxp,
                                s->xcarry, s->dst, s->dstcap, &s->ndst, s->ev,
                                s->evcap, &s->nev, &s->err, ARM);
}

static uint64_t run_stage2(state *s, const state *src, uint64_t list_count) {
  return leanllvm_json_stage2(src->doc, src->n, src->ep, src->nk, src->xp,
                              list_count, s->dst, s->dstcap, &s->ndst, s->ev,
                              s->evcap, &s->nev, &s->err);
}

/* ------------------------------------------------------ body extraction -- */
typedef struct { uint32_t open, close; } body_t;

/* The escape rule of `probes/json/escape_driver.c`, and the quote pairs. */
static uint64_t scan_document(const uint8_t *d, uint64_t n, uint32_t *pos,
                              body_t *bodies, uint64_t *nbodies,
                              int *unterminated) {
  uint64_t k = 0, nb = 0, i = 0, run = 0;
  uint32_t open = 0;
  int in_string = 0;
  while (i < n) {
    uint8_t c = d[i];
    if (!in_string) {
      if (c == '"') {
        in_string = 1;
        run = 0;
        open = (uint32_t)i;
      }
      i++;
      continue;
    }
    if (c == '\\') {
      if ((run & 1) == 0) pos[k++] = (uint32_t)i;
      run++;
      i++;
      continue;
    }
    {
      int escaped = (int)(run & 1);
      run = 0;
      if (c < 0x20) {
        pos[k++] = (uint32_t)i;
      } else if (c == '"' && !escaped) {
        in_string = 0;
        bodies[nb].open = open;
        bodies[nb].close = (uint32_t)i;
        nb++;
      }
    }
    i++;
  }
  *nbodies = nb;
  *unterminated = in_string;
  return k;
}

static uint64_t fnv1a(uint64_t h, const uint8_t *p, uint64_t n) {
  for (uint64_t i = 0; i < n; i++) { h ^= p[i]; h *= 0x100000001b3ull; }
  return h;
}

/* --------------------------------------------------------------- acts -- */
enum {
  A_STAGE2, A_PLAIN, A_EXPAND_ARENA, A_EXPAND_L1, A_COPY, A_PIPELINE, A_CHAIN,
  A_COUNT
};

static const char *act_name[A_COUNT] = {
  "stage2", "stage2_plain", "expand_arena", "expand_l1", "copy_arena",
  "pipeline", "chain"
};

typedef struct {
  state *s;
  state *ref;
  body_t *esc;
  uint64_t *esc_len;      /* decoded length of each escaped body, from the arena */
  uint64_t *esc_off;      /* its arena offset */
  uint64_t nesc;
  uint32_t *xp;
  uint64_t nxp;
  uint8_t *scratch;
  uint64_t max_body;
} bench;

static void act_stage2(void *vp) {
  bench *b = vp;
  state *s = b->s;
  b->s->ndst = 0;
  b->s->nev = 0;
  b->s->err = 0;
  uint64_t v = run_stage2(s, b->ref, b->ref->nxp);
  sink ^= v ^ s->ndst ^ s->nev ^ s->err;
}

static void act_plain(void *vp) {
  bench *b = vp;
  state *s = b->s;
  b->s->ndst = 0;
  b->s->nev = 0;
  b->s->err = 0;
  uint64_t v = run_stage2(s, b->ref, 0);
  sink ^= v ^ s->ndst ^ s->nev;
}

/* The deferred decode, materialising: one cursor, the arena as the destination,
   exactly the calls stage 2 makes. */
static void act_expand_arena(void *vp) {
  bench *b = vp;
  state *s = b->s;
  uint64_t xj = 0, len = 0;
  for (uint64_t e = 0; e < b->nesc; e++) {
    const body_t *bd = &b->esc[e];
    uint64_t pos0 = (uint64_t)bd->open + 1;
    uint64_t blen = (uint64_t)bd->close - pos0;
    uint64_t err = 0;
    uint64_t on = leanllvm_json_escape_expand(b->ref->doc + pos0, blen,
                                              s->dst + len, &err, b->xp, &xj,
                                              b->nxp, pos0);
    if (on == (uint64_t)-1) { sink ^= err; return; }
    len += on;
  }
  sink ^= xj ^ len;
}

/* The deferred decode with validation kept and the destination L1-resident:
   each body decoded into one reused scratch. */
static void act_expand_l1(void *vp) {
  bench *b = vp;
  uint64_t xj = 0, acc = 0;
  for (uint64_t e = 0; e < b->nesc; e++) {
    const body_t *bd = &b->esc[e];
    uint64_t pos0 = (uint64_t)bd->open + 1;
    uint64_t blen = (uint64_t)bd->close - pos0;
    uint64_t err = 0;
    uint64_t on = leanllvm_json_escape_expand(b->ref->doc + pos0, blen,
                                              b->scratch, &err, b->xp, &xj,
                                              b->nxp, pos0);
    if (on == (uint64_t)-1) { sink ^= err; return; }
    acc += on ^ b->scratch[on ? on - 1 : 0];
  }
  sink ^= xj ^ acc;
}

/* The floor: the same number of bytes copied from the document to the arena. */
static void act_copy(void *vp) {
  bench *b = vp;
  state *s = b->s;
  memcpy(s->dst, b->ref->doc, (size_t)b->ref->ndst);
  sink ^= s->dst[b->ref->ndst ? b->ref->ndst - 1 : 0];
}

static void act_pipeline(void *vp) {
  bench *b = vp;
  state *s = b->s;
  reset_pipeline(s);
  uint64_t v = run_pipeline(s);
  sink ^= v ^ s->ndst ^ s->nev ^ s->err;
}

static void act_chain(void *vp) {
  (void)vp;
  sink ^= clock_chain(CHAIN_IT);
}

static void (*act_fn[A_COUNT])(void *) = {
  act_stage2, act_plain, act_expand_arena, act_expand_l1, act_copy,
  act_pipeline, act_chain
};

/* ------------------------------------------------------------------ main -- */
static uint8_t *read_file(const char *path, uint64_t *n) {
  FILE *f = fopen(path, "rb");
  if (f == NULL) { perror(path); exit(2); }
  if (fseek(f, 0, SEEK_END) != 0) { perror(path); exit(2); }
  long sz = ftell(f);
  if (sz < 0) { perror(path); exit(2); }
  rewind(f);
  uint8_t *p = (uint8_t *)xalloc((size_t)sz);
  if (fread(p, 1, (size_t)sz, f) != (size_t)sz) {
    fprintf(stderr, "lazy-bench: short read of %s\n", path);
    exit(2);
  }
  fclose(f);
  *n = (uint64_t)sz;
  return p;
}

static int failures;

static void gate_fail(const char *msg) {
  fprintf(stderr, "GATE: %s\n", msg);
  failures++;
}

int main(int argc, char **argv) {
  const char *doc_path = NULL;
  int rounds = 15, reps = 21;
  uint64_t core = 0;

  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--doc") == 0 && i + 1 < argc) doc_path = argv[++i];
    else if (strcmp(argv[i], "--rounds") == 0 && i + 1 < argc) rounds = atoi(argv[++i]);
    else if (strcmp(argv[i], "--reps") == 0 && i + 1 < argc) reps = atoi(argv[++i]);
    else if (strcmp(argv[i], "--core") == 0 && i + 1 < argc) core = (uint64_t)atoi(argv[++i]);
    else { fprintf(stderr, "lazy-bench: bad argument %s\n", argv[i]); return 2; }
  }
  if (doc_path == NULL || rounds < 1 || reps < 1) {
    fprintf(stderr, "usage: lazy-bench --doc <path> [--rounds N] [--reps N] [--core N]\n");
    return 2;
  }

  /* The pos8 emitter reads the unit's internal table, and the unit fills it
     only through `leanllvm_json_entry_table`; the route's adapter calls it once
     before the first pipeline call, and so does this instrument. */
  {
    static uint32_t entry_table[256 * 8];
    leanllvm_json_entry_table(entry_table);
  }

  uint64_t n = 0;
  uint8_t *src = read_file(doc_path, &n);
  if (n != EXPECT_SIZE) {
    fprintf(stderr, "lazy-bench: %s is %" PRIu64 " bytes, not %" PRIu64 "\n",
            doc_path, n, EXPECT_SIZE);
    return 2;
  }

  state ref, bstate;
  state_init(&ref, src, n);
  state_init(&bstate, src, n);

  uint32_t *pos = (uint32_t *)xalloc((size_t)(n + 1) * 4);
  body_t *bodies = (body_t *)xalloc((size_t)(n / 2 + 2) * sizeof *bodies);
  uint64_t nbodies = 0;
  int unterminated = 0;
  uint64_t npos = scan_document(src, n, pos, bodies, &nbodies, &unterminated);

  reset_pipeline(&ref);
  uint64_t verdict = run_pipeline(&ref);
  printf("reference verdict=%" PRIu64 " nk=%" PRIu64 " nxp=%" PRIu64
         " ndst=%" PRIu64 " nev=%" PRIu64 " err=%" PRIu64
         " arena_fnv=%016" PRIx64 "\n",
         verdict, ref.nk, ref.nxp, ref.ndst, ref.nev, ref.err,
         fnv1a(0xcbf29ce484222325ull, ref.dst, ref.ndst));
  if (verdict != 1) gate_fail("the reference pipeline refused the document");
  if (unterminated) gate_fail("the scan ended inside a string");
  if (ref.nxp != EXPECT_NXP) gate_fail("nxp is not the recorded 1772");
  if (ref.ndst != EXPECT_NDST) gate_fail("ndst is not the recorded 55931");
  if (ref.nev != EXPECT_NEV) gate_fail("nev is not the recorded 8907");
  if (npos != ref.nxp) gate_fail("the scan's position count differs from nxp");
  else if (memcmp(pos, ref.xp, (size_t)npos * 4) != 0)
    gate_fail("the scan's positions differ from the escape list");

  /* Gate: stage 2 over the pipeline's streams reproduces the pipeline. */
  uint8_t *ref_dst = (uint8_t *)xalloc((size_t)ref.dstcap);
  uint8_t *ref_ev = (uint8_t *)xalloc((size_t)ref.evcap);
  memcpy(ref_dst, ref.dst, (size_t)ref.ndst);
  memcpy(ref_ev, ref.ev, (size_t)ref.nev);
  bstate.ndst = bstate.nev = bstate.err = 0;
  uint64_t s2v = run_stage2(&bstate, &ref, ref.nxp);
  if (s2v != verdict) gate_fail("stage 2 returned a different verdict");
  if (bstate.ndst != ref.ndst || bstate.nev != ref.nev ||
      bstate.err != ref.err) gate_fail("stage 2 wrote different header words");
  else if (memcmp(bstate.dst, ref_dst, (size_t)ref.ndst) != 0)
    gate_fail("stage 2 wrote different arena bytes");
  else if (memcmp(bstate.ev, ref_ev, (size_t)ref.nev) != 0)
    gate_fail("stage 2 wrote different event bytes");

  /* Gate: the two event streams are the same records in the same order.  The
     plain walk's `str` records name the raw body where the committed walk's
     name the arena slice, so those records' length and field may differ; the
     tag sequence, the record count and every other record's bytes must not.
     This is what makes `stage2_plain` a cost proxy for a lazy stage 2 rather
     than a different stream. */
  {
    uint64_t nd3 = 0, ne3 = 0, er3 = 0;
    uint64_t v3 = leanllvm_json_stage2(ref.doc, n, ref.ep, ref.nk, ref.xp, 0,
                                       bstate.dst, bstate.dstcap, &nd3,
                                       bstate.ev, bstate.evcap, &ne3, &er3);
    uint64_t ka = 0, kb = 0, recs_a = 0, recs_b = 0, str_diff = 0;
    int shape_ok = (v3 == 1 && nd3 == 0);
    if (!shape_ok) gate_fail("the plain walk did not accept with an empty arena");
    while (shape_ok && ka < ref.nev && kb < ne3) {
      uint8_t ta = ref_ev[ka], tb = bstate.ev[kb];
      uint64_t wa = (ta == 5 || ta == 6) ? 13 : ta == 7 ? 9 : 1;
      uint64_t wb = (tb == 5 || tb == 6) ? 13 : tb == 7 ? 9 : 1;
      if (ta != tb || wa != wb) { shape_ok = 0; break; }
      if (wa == 13) { str_diff++; }
      else if (memcmp(ref_ev + ka, bstate.ev + kb, (size_t)wa) != 0) {
        shape_ok = 0; break;
      }
      ka += wa; kb += wb; recs_a++; recs_b++;
    }
    if (shape_ok && (ka != ref.nev || kb != ne3 || recs_a != recs_b))
      shape_ok = 0;
    if (!shape_ok) gate_fail("the plain event stream is not the same record shape");
    else
      printf("shape records=%" PRIu64 " str_records=%" PRIu64
             " (tag sequence identical; only their length and field differ)\n",
             recs_a, str_diff);
  }

  /* Gate: every position lies in exactly one body; count the escaped. */
  body_t *esc = (body_t *)xalloc((size_t)(nbodies ? nbodies : 1) * sizeof *esc);
  uint64_t nesc = 0, pi = 0;
  for (uint64_t i = 0; i < nbodies; i++) {
    uint64_t lo = bodies[i].open, hi = bodies[i].close;
    while (pi < npos && pos[pi] <= lo) {
      gate_fail("an escape position is outside a string body");
      break;
    }
    uint64_t cnt = 0;
    while (pi < npos && pos[pi] < hi) { pi++; cnt++; }
    if (cnt > 0) esc[nesc++] = bodies[i];
  }
  if (pi != npos) gate_fail("an escape position lies past the last body");
  if (nesc != EXPECT_ESCAPED_BODIES)
    gate_fail("the escaped-body count is not the recorded 620");

  /* Gate: the direct expander reproduces the arena and the cursor. */
  uint8_t *xbuf = (uint8_t *)xalloc((size_t)n + 64);
  uint64_t xj = 0, xlen = 0;
  for (uint64_t e = 0; e < nesc; e++) {
    uint64_t pos0 = (uint64_t)esc[e].open + 1;
    uint64_t blen = (uint64_t)esc[e].close - pos0;
    uint64_t err = 0;
    uint64_t on = leanllvm_json_escape_expand(src + pos0, blen, xbuf + xlen,
                                              &err, ref.xp, &xj, ref.nxp, pos0);
    if (on == (uint64_t)-1) { gate_fail("the direct expander refused a body"); break; }
    xlen += on;
  }
  if (xj != ref.nxp) gate_fail("the direct expander left xj != nxp");
  if (xlen != ref.ndst) gate_fail("the direct expander wrote a different byte count");
  else if (memcmp(xbuf, ref_dst, (size_t)ref.ndst) != 0)
    gate_fail("the direct expander's bytes differ from the pipeline arena");

  /* The escaped bodies' arena offsets and decoded lengths, and the maximum
     decoded length (the L1 scratch must hold it). */
  uint64_t *esc_off = (uint64_t *)xalloc((size_t)(nesc ? nesc : 1) * sizeof *esc_off);
  uint64_t *esc_len = (uint64_t *)xalloc((size_t)(nesc ? nesc : 1) * sizeof *esc_len);
  uint64_t max_body = 0, xj2 = 0, off = 0;
  for (uint64_t e = 0; e < nesc; e++) {
    uint64_t pos0 = (uint64_t)esc[e].open + 1;
    uint64_t blen = (uint64_t)esc[e].close - pos0;
    uint64_t err = 0;
    uint64_t on = leanllvm_json_escape_expand(src + pos0, blen, xbuf, &err,
                                              ref.xp, &xj2, ref.nxp, pos0);
    if (on == (uint64_t)-1) { gate_fail("a body's decoded length is unknown"); break; }
    esc_off[e] = off;
    esc_len[e] = on;
    off += on;
    if (on > max_body) max_body = on;
  }
  if (off != ref.ndst) gate_fail("the per-body lengths do not sum to ndst");
  if (max_body + 64 > SCRATCH_BYTES)
    gate_fail("the largest decoded body exceeds the L1 scratch");

  /* Gate: each body decoded into the L1 scratch equals its arena slice. */
  {
    uint8_t *scratch = (uint8_t *)xalloc(SCRATCH_BYTES);
    uint64_t j = 0;
    for (uint64_t e = 0; e < nesc; e++) {
      uint64_t pos0 = (uint64_t)esc[e].open + 1;
      uint64_t blen = (uint64_t)esc[e].close - pos0;
      uint64_t err = 0;
      uint64_t on = leanllvm_json_escape_expand(src + pos0, blen, scratch, &err,
                                                ref.xp, &j, ref.nxp, pos0);
      if (on == (uint64_t)-1 || on != esc_len[e] ||
          memcmp(scratch, ref_dst + esc_off[e], (size_t)on) != 0) {
        gate_fail("the L1-scratch decode differs from the arena slice");
        break;
      }
    }
    free(scratch);
  }

  printf("bodies total=%" PRIu64 " escaped=%" PRIu64 " positions=%" PRIu64
         " expanded_bytes=%" PRIu64 " max_body=%" PRIu64 "\n",
         nbodies, nesc, ref.nxp, ref.ndst, max_body);

  /* The consumer's fold at both artifacts: stage 2's and stage2_plain's. */
  if (failures != 0) {
    fprintf(stderr, "lazy-bench: %d gate(s) failed before the clock\n", failures);
    return 3;
  }

  /* ---------------------------------------------------------- timing -- */
  bench b;
  memset(&b, 0, sizeof b);
  b.s = &bstate;
  b.ref = &ref;
  b.esc = esc;
  b.esc_off = esc_off;
  b.esc_len = esc_len;
  b.nesc = nesc;
  b.xp = ref.xp;
  b.nxp = ref.nxp;
  b.scratch = (uint8_t *)xalloc(SCRATCH_BYTES);
  b.max_body = max_body;

  uint64_t *round_ns[A_COUNT];
  uint64_t *samples = (uint64_t *)xalloc((size_t)reps * sizeof *samples);
  for (int a = 0; a < A_COUNT; a++)
    round_ns[a] = (uint64_t *)xalloc((size_t)rounds * sizeof(uint64_t));

  for (int round = 0; round < rounds; round++) {
    for (int k = 0; k < A_COUNT; k++) {
      int a = (k + round) % A_COUNT;
      for (int rep = 0; rep < reps; rep++) {
        uint64_t t0 = now_ns();
        act_fn[a](&b);
        uint64_t t1 = now_ns();
        samples[rep] = t1 - t0;
      }
      round_ns[a][round] = median_of(samples, (size_t)reps);
    }
  }

  /* After the clock: the gates still hold. */
  bstate.ndst = bstate.nev = bstate.err = 0;
  if (run_stage2(&bstate, &ref, ref.nxp) != 1 ||
      bstate.ndst != ref.ndst || bstate.nev != ref.nev ||
      memcmp(bstate.dst, ref_dst, (size_t)ref.ndst) != 0 ||
      memcmp(bstate.ev, ref_ev, (size_t)ref.nev) != 0)
    gate_fail("stage 2 changed during the timed rounds");
  if (failures != 0) {
    fprintf(stderr, "lazy-bench: %d gate(s) failed after the clock\n", failures);
    return 3;
  }

  /* ---------------------------------------------------------- report -- */
  summary sm[A_COUNT];
  for (int a = 0; a < A_COUNT; a++)
    sm[a] = summarise(round_ns[a], (size_t)rounds);

  double ghz = (double)CHAIN_IT / (double)sm[A_CHAIN].median;
  printf("\ninstrument lazy-bench=1 arm=%" PRIu64
         " compiler=%s rounds=%d reps=%d core=%" PRIu64 "\n",
         ARM, __VERSION__, rounds, reps, core);
  printf("clock: chain=%" PRIu64 " ns / %" PRIu64 " iterations -> %.3f GHz\n",
         sm[A_CHAIN].median, CHAIN_IT, ghz);
  printf("statistic: median of the round medians, min-max of those medians\n\n");
  printf("%-15s %14s %12s %12s %10s\n", "act", "median_ns", "min_ns", "max_ns",
         "us");
  for (int a = 0; a < A_COUNT; a++)
    printf("%-15s %14" PRIu64 " %12" PRIu64 " %12" PRIu64 " %10.3f\n",
           act_name[a], sm[a].median, sm[a].min, sm[a].max,
           (double)sm[a].median / 1000.0);

  /* Per-round paired differences, then the median of the differences. */
  uint64_t *d = (uint64_t *)xalloc((size_t)rounds * sizeof(uint64_t));
  printf("\npaired differences (ns; each round's difference of that round's "
         "act medians, then median/min/max)\n");
  const struct { const char *name; int hi, lo; } pairs[] = {
    {"stage2-plain", A_STAGE2, A_PLAIN},
    {"expand_l1-plain", A_EXPAND_L1, A_PLAIN},
    {"expand_arena-plain", A_EXPAND_ARENA, A_PLAIN},
    {"expand_arena-l1", A_EXPAND_ARENA, A_EXPAND_L1},
    {"copy", A_COPY, A_PLAIN},
  };
  for (size_t p = 0; p < sizeof pairs / sizeof pairs[0]; p++) {
    for (int r = 0; r < rounds; r++) {
      int64_t t = (int64_t)round_ns[pairs[p].hi][r] -
                  (int64_t)round_ns[pairs[p].lo][r];
      d[r] = (uint64_t)(t > 0 ? t : 0);
    }
    summary s = summarise(d, (size_t)rounds);
    printf("%-20s %12" PRIu64 " %10" PRIu64 " %10" PRIu64 "\n", pairs[p].name,
           s.median, s.min, s.max);
  }

  /* The lazy pipeline, per round: the pipeline with stage 2's list-driven
     decode removed, once without validation and once with it kept (the L1
     decode added back). */
  const struct { const char *name; int sign_l1; } lazy[] = {
    {"lazy pipeline (no validation)", 0},
    {"lazy pipeline (validation kept)", 1},
  };
  printf("\nlazy pipeline, per round: pipeline - stage2 + plain (+ L1 decode)\n");
  for (size_t p = 0; p < sizeof lazy / sizeof lazy[0]; p++) {
    for (int r = 0; r < rounds; r++) {
      int64_t t = (int64_t)round_ns[A_PIPELINE][r] -
                  (int64_t)round_ns[A_STAGE2][r] +
                  (int64_t)round_ns[A_PLAIN][r];
      if (lazy[p].sign_l1) t += (int64_t)round_ns[A_EXPAND_L1][r];
      d[r] = (uint64_t)(t > 0 ? t : 0);
    }
    summary s = summarise(d, (size_t)rounds);
    printf("%-32s %12" PRIu64 " %10" PRIu64 " %10" PRIu64 "\n", lazy[p].name,
           s.median, s.min, s.max);
  }

  printf("\nsave fraction of the pipeline, from the same rounds: "
         "no-validation=%.1f%% validation-kept=%.1f%%\n",
         100.0 * (double)(sm[A_STAGE2].median - sm[A_PLAIN].median) /
           (double)sm[A_PIPELINE].median,
         100.0 * (double)(sm[A_STAGE2].median - sm[A_PLAIN].median -
                          sm[A_EXPAND_L1].median) /
           (double)sm[A_PIPELINE].median);

  free(d);
  free(samples);
  for (int a = 0; a < A_COUNT; a++) free(round_ns[a]);
  free(src);
  return 0;
}
