/* cost-profile.c -- a C-only decomposition of the native interval the reused
   workspace measures on `syn-strings-64k`, at the route's own compiler line and
   arm.

   The interval.  `probes/json/route/workspace.cc`'s `act_native_reused` is one
   `leanllvm_json_pipeline` call, the tagged header's ten stores, and two
   `memcpy`s into the result buffer: 80 header bytes and 64,838 payload bytes,
   64,918 bytes of result in all.  `run_reused` calls it after the two-phase
   admission and the reused staging, and the route's rotation runs a complete
   fresh call -- a 1.44 MiB allocation, zero-fill, one more pipeline call and a
   result buffer -- between two reused calls.  This harness reproduces that
   context and measures the interval beside the pieces it is made of.

   The acts.  Each is one call into the staged kernel objects at the route's
   line (`-O2 -march=x86-64-v3 -mpclmul -falign-loops=64
   -falign-functions=64`), arm 2, with the caller's buffers shaped as the
   workspace shapes them:

     masks            the mask unit plus the entry word's composition and the
                      tail clamp -- `pipeline.c`'s block prologue
     entry            the entry emitter over the precomputed words
     escape           the escape-list builder over the precomputed masks
     s1_no_escape     the block prologue plus the emitter, no escape list
     s1_fused         the whole of `pipeline.c`'s block loop, no UTF-8, no stage 2
     pipe_nostage2    the block loop plus the UTF-8 call, no stage 2
     utf8             `leanllvm_json_utf8` at the route's gate, eight runs per
                      sample divided by eight
     stage2           the walk over the pipeline's own entry and escape streams
     stage2_plain     the same walk with an empty escape list (a cost probe: its
                      arena differs by construction and it is never read through
                      an identity gate)
     expand           `leanllvm_json_escape_expand` once per escaped body
     pipeline         `leanllvm_json_pipeline` alone
     native           `pipeline` plus the tagged header and both `memcpy`s, which
                      is `act_native_reused`'s body
     copy_total       the header stores and both `memcpy`s, no pipeline
     copy_dst         the arena `memcpy` alone
     copy_ev          the event `memcpy` alone
     chain            the calibrated clock: a serial dependent-add chain of
                      2,000,000 iterations, one per cycle on this part, timed by
                      the same clock

   The nested acts telescope: `masks`, `s1_no_escape`, `s1_fused`,
   `pipe_nostage2` and `pipeline` differ by exactly one call each, so the
   per-round differences

     entry  = s1_no_escape - masks
     escape = s1_fused     - s1_no_escape
     utf8   = pipe_nostage2- s1_fused
     stage2 = pipeline     - pipe_nostage2
     copy   = native       - pipeline

   each isolate one term of the interval in a pair measured inside one round.
   The residual `pipeline - (masks + entry + escape + utf8 + stage2)` is reported
   as the de-fusion term, and the same residual against the *isolated* acts
   (`entry`, `escape`, `stage2` over precomputed streams) is reported beside it.
   Neither is a partition of a hypothetical fused body: both are arithmetic on
   paired measurements, printed with the identity so a reader can see what it is.

   The context.  With `--context route` (the default) every timed act is
   preceded by the fresh call and the reused admission and staging, outside the
   clock, in the route's rotation; with `--context none` the acts run back to
   back.  The difference between the two runs is measured, not assumed, and the
   report names which regime each row belongs to.

   The checks before the clock.  One untimed `leanllvm_json_pipeline` call is
   the reference observation; it must accept, and `nxp=1772`, `ndst=55931`,
   `nev=8907` are the recorded values for this document.  Then:

     1. a separately run stage-1 loop writes entry and escape streams that are
        byte-identical to the pipeline's, and stage 2 over them writes the same
        header words, arena and events;
     2. an independent byte scan -- the rule `probes/json/escape_driver.c`
        states -- derives the escape positions and the quote pairs; the
        positions must equal the pipeline's list, every position must lie inside
        exactly one body, and 620 bodies must carry one;
     3. `leanllvm_json_escape_expand` over those 620 bodies, in document order
        and with one threaded cursor, must write exactly the pipeline's arena
        and leave the cursor at `nxp`;
     4. the admission must select arm 2 (`escape_skip == 0`).

   A failed gate exits 3 and prints nothing as a measurement.  After the timed
   rounds the same gates run again, so a timed act that corrupted the streams
   fails the run rather than being reported.

   Statistics follow `workspace.cc`: each round times every act `reps` times in
   a rotated order, an act's sample is the round's median, and the row is the
   median of the round medians with the minimum and maximum beside it.  Cycles
   are each round's act median times the iteration count over that round's chain
   median, then reduced the same way; the chain makes the frequency of each
   round visible instead of assuming one.

   Usage: cost-profile --doc <path> [--arm 2] [--win-offset N]
                       [--context route|none] [--rounds N] [--reps N]

   Exit status: 0 on a complete run with every gate held; 2 on a bad argument or
   unreadable document; 3 on a gate disagreement.
*/
#define _GNU_SOURCE
#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "admission.h"
#include "entry.h"
#include "escape.h"
#include "pipeline.h"
#include "s1_block.h"
#include "stage2.h"
#include "utf8.h"

#define ARM 2ULL
#define EXPECT_SIZE 65536ULL
#define EXPECT_NXP 1772ULL
#define EXPECT_NDST 55931ULL
#define EXPECT_NEV 8907ULL
#define EXPECT_ESCAPED_BODIES 620ULL
#define HEADER_BYTES 80ULL
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

/* The calibrated clock.  `add $1; dec; jne` is one iteration per cycle on this
   part; the chain is timed by the same clock immediately before/after the acts
   of its round. */
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
  if (t == NULL) { fprintf(stderr, "cost-profile: out of memory\n"); exit(2); }
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
/* The reused workspace's buffers come from `malloc`, not an aligned allocator,
   and its document sits at offset 3 of a window that begins `[0,0,0]`.  The
   layout is part of the interval being decomposed, so this harness allocates
   the same way and stages its own window at the caller's offset. */
static void *xalloc(size_t n) {
  void *p = malloc(n ? n : 1);
  if (p == NULL) {
    fprintf(stderr, "cost-profile: cannot allocate %zu bytes\n", n);
    exit(2);
  }
  memset(p, 0, n ? n : 1);
  return p;
}

/* ------------------------------------------------------------ the state -- */
enum { W_SC, W_MK, W_ENTW, W_EP, W_NK, W_XP, W_NXP, W_XCARRY,
       W_DST, W_NDST, W_EV, W_NEV, W_ERR, W_COUNT };

typedef struct {
  uint8_t *win;            /* the route window: `[0,0,0] ++ document` */
  const uint8_t *src;      /* the document's own bytes */
  const uint8_t *doc;      /* `win + doc_off` */
  uint64_t doc_off;
  uint64_t n, nb;
  uint64_t epcap, xpcap, dstcap, evcap;

  uint64_t sc[3];
  uint64_t mk[6];
  uint64_t entw;
  uint64_t xcarry[2];

  uint32_t *ep;
  uint64_t nk;
  uint32_t *xp;
  uint64_t nxp;

  uint8_t *dst;
  uint64_t ndst;
  uint8_t *ev;
  uint64_t nev;
  uint64_t err;

  uint8_t *result;
  uint64_t resultcap;

  uint8_t *cls;            /* the reused admission's class array */
  uint64_t clscap;

  /* The profile's precomputed per-block words. */
  s1_masks *mks;
  uint64_t *entws;
} state;

static uint64_t g_win_offset = 3;   /* the route's `[0,0,0] ++ doc` window */
static int g_context = 1;           /* the route's fresh/reused rotation */

static uint64_t wlen(const state *s, int i) {
  switch (i) {
  case W_SC: return 24;
  case W_MK: return 48;
  case W_ENTW: return 8;
  case W_EP: return 4 * s->epcap;
  case W_NK: return 8;
  case W_XP: return 4 * s->xpcap;
  case W_NXP: return 8;
  case W_XCARRY: return 16;
  case W_DST: return s->dstcap;
  case W_NDST: return 8;
  case W_EV: return s->evcap;
  case W_NEV: return 8;
  case W_ERR: return 8;
  default: return 0;
  }
}

static void state_init(state *s, const uint8_t *src, uint64_t n) {
  memset(s, 0, sizeof *s);
  s->src = src;
  s->n = n;
  s->nb = (n + 63) >> 6;
  s->doc_off = g_win_offset;
  s->win = (uint8_t *)xalloc((size_t)n + (size_t)s->doc_off + 64);
  memcpy(s->win + s->doc_off, src, (size_t)n);
  s->doc = s->win + s->doc_off;
  s->epcap = 64 * s->nb + 9;
  s->xpcap = 64 * s->nb + 8;
  s->dstcap = n + 64;
  s->evcap = 13 * n + 128;
  s->ep = (uint32_t *)xalloc((size_t)s->epcap * 4);
  s->xp = (uint32_t *)xalloc((size_t)s->xpcap * 4);
  s->dst = (uint8_t *)xalloc((size_t)s->dstcap);
  s->ev = (uint8_t *)xalloc((size_t)s->evcap);
  s->mks = (s1_masks *)xalloc((size_t)s->nb * sizeof *s->mks);
  s->entws = (uint64_t *)xalloc((size_t)s->nb * sizeof *s->entws);
  s->clscap = n + 1;
  s->cls = (uint8_t *)xalloc((size_t)s->clscap);
  s->resultcap = HEADER_BYTES + s->dstcap + s->evcap;
  s->result = (uint8_t *)xalloc((size_t)s->resultcap);
}

static void state_free(state *s) {
  free(s->win);
  free(s->ep); free(s->xp); free(s->dst); free(s->ev);
  free(s->mks); free(s->entws); free(s->cls); free(s->result);
  memset(s, 0, sizeof *s);
}

/* ---------------------------------------------------------- word access -- */
static void store64(uint8_t *p, uint64_t v) {
  for (int i = 0; i < 8; i++) p[i] = (uint8_t)(v >> (8 * i));
}

static uint64_t load64(const uint8_t *p) {
  uint64_t v = 0;
  for (int i = 0; i < 8; i++) v |= (uint64_t)p[i] << (8 * i);
  return v;
}

static uint32_t load32(const uint8_t *p) {
  return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) |
         ((uint32_t)p[3] << 24);
}

static uint64_t fnv1a(uint64_t h, const uint8_t *p, uint64_t n) {
  for (uint64_t i = 0; i < n; i++) {
    h ^= p[i];
    h *= 0x100000001b3ull;
  }
  return h;
}

/* --------------------------------------------------------------- calls -- */
static uint64_t call_pipeline(const uint8_t *b, uint64_t n,
                              uint64_t *sc, uint64_t *mk, uint64_t *entw,
                              uint32_t *ep, uint64_t epcap, uint64_t *nk,
                              uint32_t *xp, uint64_t xpcap, uint64_t *nxp,
                              uint64_t *xcarry,
                              uint8_t *dst, uint64_t dstcap, uint64_t *ndst,
                              uint8_t *ev, uint64_t evcap, uint64_t *nev,
                              uint64_t *err) {
  return leanllvm_json_pipeline(b, n, sc, mk, entw, ep, epcap, nk, xp, xpcap,
                                nxp, xcarry, dst, dstcap, ndst, ev, evcap, nev,
                                err, ARM);
}

static uint64_t run_pipeline(state *s) {
  return call_pipeline(s->doc, s->n, s->sc, (uint64_t *)s->mk, &s->entw,
                       s->ep, s->epcap, &s->nk, s->xp, s->xpcap, &s->nxp,
                       s->xcarry, s->dst, s->dstcap, &s->ndst,
                       s->ev, s->evcap, &s->nev, &s->err);
}

static uint64_t run_stage2(state *s, const state *src, uint64_t list_count) {
  return leanllvm_json_stage2(src->doc, src->n, src->ep, src->nk,
                              src->xp, list_count,
                              s->dst, s->dstcap, &s->ndst,
                              s->ev, s->evcap, &s->nev, &s->err);
}

static void reset_pipeline(state *s) {
  memset(s->sc, 0, sizeof s->sc);
  memset(s->mk, 0, sizeof s->mk);
  memset(s->xcarry, 0, sizeof s->xcarry);
  s->nk = 0;
  s->nxp = 0;
  s->ndst = 0;
  s->nev = 0;
  s->err = 0;
}

/* The block loop `pipeline.c` runs before UTF-8, with its per-block words kept
   so the isolated acts read the same masks without recomputing them. */
static void precompute_stage1(state *s) {
  s1_carry sc = {0, 0, 0};
  s1_masks m;
  uint64_t prevS = 0, k = 0, nxp = 0;
  uint64_t carry[2] = {0, 0};
  for (uint64_t i = 0; i < s->nb; i++) {
    const uint8_t *p = s->doc + (i << 6);
    leanllvm_json_s1_masks(p, &sc, &m);
    s->mks[i] = m;
    uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);
    uint64_t ent = m.quote | (m.delim & ~m.in_string);
    ent |= S & ~((S << 1) | prevS);
    prevS = S >> 63;
    uint64_t lim = s->n - (i << 6);
    if (lim < 64) ent &= (1ULL << lim) - 1ULL;
    s->entws[i] = ent;
    k = leanllvm_json_entry_pos8(&s->entws[i], i, 1, s->ep, k);
    leanllvm_json_escape_list(m.backslash, m.ctl, m.in_string, i, s->xp,
                              &nxp, carry);
  }
  s->nk = k;
  s->nxp = nxp;
}

/* ------------------------------------------------------ body extraction -- */
typedef struct { uint32_t open, close; } body_t;

/* The escape rule of `probes/json/escape_driver.c`'s `ref_positions`, and the
   quote pairs the same scan sees. */
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

/* The consumer's fold, from `workspace.cc`'s `consume`. */
typedef struct {
  uint64_t tokens, events, arena, sum, values;
  int walked;
} folded;

static folded fold_result(const uint8_t *arena, uint64_t ndst,
                          const uint8_t *ev, uint64_t nev) {
  folded c;
  memset(&c, 0, sizeof c);
  uint64_t sum = 0;
  for (uint64_t k = 0; k < ndst; k++) sum += arena[k];
  c.arena = ndst;
  uint64_t k = 0, tokens = 0;
  while (k < nev) {
    uint8_t t = ev[k];
    uint64_t width = (t == 5 || t == 6) ? 13 : t == 7 ? 9 : 1;
    if (k + width > nev) break;
    const uint8_t *base = ev + k;
    uint64_t len = (width == 13) ? (uint64_t)load32(base + 1) : 0;
    uint64_t payload = 0;
    if (width == 13) payload = load64(base + 5);
    else if (width == 9) payload = load64(base + 1);
    sum += (uint64_t)t + len + payload;
    k += width;
    tokens++;
  }
  c.tokens = tokens;
  c.events = k;
  c.sum = sum;
  c.walked = (k == nev) ? 1 : 0;
  c.values = c.walked ? tokens : 0;
  return c;
}

/* --------------------------------------------------------- the context -- */
/* The route's fresh call, complete: the window and the thirteen buffers
   allocated and zeroed, the adapter's copies filled, one pipeline call, the
   result allocated and filled, then every allocation released.  This is the
   work the route's rotation runs between two reused calls. */
static void fresh_arm(state *s) {
  admit_facts af;
  admit_decide(s->src, s->n, 1ull << 20, 128, NULL, 0, &af);

  uint8_t *win = (uint8_t *)xalloc((size_t)s->n + 3 + 64);
  memcpy(win + 3, s->src, (size_t)s->n);

  uint8_t *buf[W_COUNT], *copies[W_COUNT];
  uint64_t len[W_COUNT];
  for (int i = 0; i < W_COUNT; i++) {
    len[i] = wlen(s, i);
    buf[i] = (uint8_t *)xalloc((size_t)len[i]);
  }
  for (int i = 0; i < W_COUNT; i++) {
    copies[i] = (uint8_t *)xalloc((size_t)len[i]);
    memcpy(copies[i], buf[i], (size_t)len[i]);
  }

  uint64_t sc[3] = {0, 0, 0}, mk[6] = {0, 0, 0, 0, 0, 0}, entw = 0;
  uint64_t xcarry[2] = {0, 0};
  uint64_t nk = 0, nxp = 0, ndst = 0, nev = 0, err = 0;
  uint64_t v = leanllvm_json_pipeline(
      win + 3, s->n, sc, mk, &entw,
      (uint32_t *)copies[W_EP], s->epcap, &nk,
      (uint32_t *)copies[W_XP], s->xpcap, &nxp, xcarry,
      copies[W_DST], s->dstcap, &ndst,
      copies[W_EV], s->evcap, &nev, &err, ARM);

  uint64_t total = HEADER_BYTES + ndst + nev;
  uint8_t *res = (uint8_t *)xalloc((size_t)total);
  store64(res + 0, v == 1 ? 0 : 1);
  store64(res + 8, 0);
  store64(res + 16, 0);
  store64(res + 24, 0);
  uint64_t obs[6] = {v, nk, nxp, ndst, nev, err};
  for (int i = 0; i < 6; i++) store64(res + 32 + 8 * (size_t)i, obs[i]);
  memcpy(res + 80, copies[W_DST], (size_t)ndst);
  memcpy(res + 80 + ndst, copies[W_EV], (size_t)nev);

  free(res);
  for (int i = 0; i < W_COUNT; i++) free(copies[i]);
  for (int i = 0; i < W_COUNT; i++) free(buf[i]);
  free(win);
  sink ^= v ^ ndst ^ nev;
}

/* Reused admission and staging, with the route's fresh call before it in the
   rounds where the fresh arm runs first. */
static void context_pre(state *s, int fresh_first) {
  if (!g_context) return;
  if (fresh_first) fresh_arm(s);
  admit_facts af;
  admit_decide(s->doc, s->n, 1ull << 20, 128, s->cls, s->clscap, &af);
  memcpy(s->win + s->doc_off, s->src, (size_t)s->n);
  memset(s->sc, 0, sizeof s->sc);
  memset(s->xcarry, 0, sizeof s->xcarry);
  s->nk = 0;
  s->nxp = 0;
  s->ndst = 0;
  s->nev = 0;
  s->err = 0;
}

static void context_post(state *s, int fresh_first) {
  if (g_context && !fresh_first) fresh_arm(s);
}

/* --------------------------------------------------------------- the acts -- */
typedef struct {
  state *s;        /* the benchmark state the acts write */
  state *ref;      /* the reference observation, read only */
  body_t *esc;     /* the escaped bodies, in document order */
  uint64_t nesc;
  uint32_t *xp;    /* the reference escape list */
  uint64_t nxp;
  uint8_t *x;      /* the direct expand's destination */
  uint64_t xj, xlen;
} bench;

/* masks: the mask unit plus the entry word's composition and the tail clamp. */
static void act_masks(void *vp) {
  bench *b = vp;
  state *s = b->s;
  s1_carry sc = {0, 0, 0};
  s1_masks m;
  uint64_t prevS = 0, acc = 0;
  for (uint64_t i = 0; i < s->nb; i++) {
    leanllvm_json_s1_masks(s->doc + (i << 6), &sc, &m);
    uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);
    uint64_t ent = m.quote | (m.delim & ~m.in_string);
    ent |= S & ~((S << 1) | prevS);
    prevS = S >> 63;
    uint64_t lim = s->n - (i << 6);
    if (lim < 64) ent &= (1ULL << lim) - 1ULL;
    acc ^= ent;
  }
  sink ^= acc;
}

/* entry: the emitter over the precomputed words. */
static void act_entry(void *vp) {
  bench *b = vp;
  state *s = b->s;
  uint64_t k = 0;
  for (uint64_t i = 0; i < s->nb; i++)
    k = leanllvm_json_entry_pos8(&s->entws[i], i, 1, s->ep, k);
  sink ^= k;
}

/* escape: the list builder over the precomputed masks. */
static void act_escape(void *vp) {
  bench *b = vp;
  state *s = b->s;
  uint64_t nxp = 0, carry[2] = {0, 0};
  for (uint64_t i = 0; i < s->nb; i++)
    leanllvm_json_escape_list(s->mks[i].backslash, s->mks[i].ctl,
                              s->mks[i].in_string, i, s->xp, &nxp, carry);
  sink ^= nxp;
}

/* s1_no_escape: the block prologue plus the emitter. */
static void act_s1_no_escape(void *vp) {
  bench *b = vp;
  state *s = b->s;
  s1_carry sc = {0, 0, 0};
  s1_masks m;
  uint64_t prevS = 0, k = 0;
  for (uint64_t i = 0; i < s->nb; i++) {
    leanllvm_json_s1_masks(s->doc + (i << 6), &sc, &m);
    uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);
    uint64_t ent = m.quote | (m.delim & ~m.in_string);
    ent |= S & ~((S << 1) | prevS);
    prevS = S >> 63;
    uint64_t lim = s->n - (i << 6);
    if (lim < 64) ent &= (1ULL << lim) - 1ULL;
    uint64_t entw = ent;
    k = leanllvm_json_entry_pos8(&entw, i, 1, s->ep, k);
  }
  s->nk = k;
  sink ^= k;
}

/* s1_fused: `pipeline.c`'s block loop, without UTF-8 and without stage 2. */
static void act_s1_fused(void *vp) {
  bench *b = vp;
  state *s = b->s;
  s1_carry sc = {0, 0, 0};
  s1_masks m;
  uint64_t prevS = 0, k = 0, nxp = 0;
  uint64_t carry[2] = {0, 0};
  for (uint64_t i = 0; i < s->nb; i++) {
    leanllvm_json_s1_masks(s->doc + (i << 6), &sc, &m);
    uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);
    uint64_t ent = m.quote | (m.delim & ~m.in_string);
    ent |= S & ~((S << 1) | prevS);
    prevS = S >> 63;
    uint64_t lim = s->n - (i << 6);
    if (lim < 64) ent &= (1ULL << lim) - 1ULL;
    uint64_t entw = ent;
    k = leanllvm_json_entry_pos8(&entw, i, 1, s->ep, k);
    leanllvm_json_escape_list(m.backslash, m.ctl, m.in_string, i, s->xp,
                              &nxp, carry);
  }
  s->nk = k;
  s->nxp = nxp;
  sink ^= k ^ nxp;
}

/* pipe_nostage2: the block loop plus the UTF-8 call, no stage 2. */
static void act_pipe_nostage2(void *vp) {
  bench *b = vp;
  state *s = b->s;
  act_s1_fused(vp);
  sink ^= leanllvm_json_utf8(s->doc, s->n, 0);
}

/* utf8: the validity stage at the route's gate, eight runs per sample. */
static void act_utf8(void *vp) {
  bench *b = vp;
  state *s = b->s;
  const unsigned reps = 8;
  uint64_t acc = 0;
  for (unsigned r = 0; r < reps; r++)
    acc ^= leanllvm_json_utf8(s->doc, s->n, 0);
  sink ^= acc;
}

/* stage2: the walk over the pipeline's own entry and escape streams. */
static void act_stage2(void *vp) {
  bench *b = vp;
  state *s = b->s;
  uint64_t v = run_stage2(s, b->ref, b->ref->nxp);
  sink ^= v ^ s->ndst ^ s->nev ^ s->err;
}

/* stage2_plain: the same walk with an empty escape list.  A cost probe only:
   every body takes the span form, so the arena and events differ. */
static void act_stage2_plain(void *vp) {
  bench *b = vp;
  state *s = b->s;
  uint64_t v = run_stage2(s, b->ref, 0);
  sink ^= v ^ s->ndst ^ s->nev ^ s->err;
}

/* expand: `leanllvm_json_escape_expand` once per escaped body, one cursor.
   It writes the same arena buffer stage 2 writes and reads the same document
   copy stage 2 reads, so the only difference from inside the walk is the walk
   itself. */
static void act_expand(void *vp) {
  bench *b = vp;
  state *s = b->s;
  uint64_t xj = b->xj, len = b->xlen;
  for (uint64_t e = 0; e < b->nesc; e++) {
    const body_t *bd = &b->esc[e];
    uint64_t pos0 = (uint64_t)bd->open + 1;
    uint64_t blen = (uint64_t)bd->close - pos0;
    uint64_t err = 0;
    uint64_t on = leanllvm_json_escape_expand(b->ref->doc + pos0, blen,
                                              s->dst + len, &err, b->xp, &xj,
                                              b->nxp, pos0);
    if (on == (uint64_t)-1) { b->xj = (uint64_t)-1; b->xlen = 0; return; }
    len += on;
  }
  b->xj = xj;
  b->xlen = len;
  sink ^= xj ^ len;
}

/* pipeline: the whole staged body, no result buffer. */
static void act_pipeline(void *vp) {
  bench *b = vp;
  state *s = b->s;
  uint64_t v = run_pipeline(s);
  sink ^= v ^ s->ndst ^ s->nev ^ s->err;
}

/* native: `act_native_reused`'s body. */
static void act_native(void *vp) {
  bench *b = vp;
  state *s = b->s;
  uint64_t v = run_pipeline(s);
  uint64_t nd = s->ndst, ne = s->nev;
  uint64_t total = HEADER_BYTES + nd + ne;
  if (total > s->resultcap) {
    fprintf(stderr, "cost-profile: result buffer too small\n");
    exit(3);
  }
  store64(s->result + 0, v == 1 ? 0 : 1);
  store64(s->result + 8, 0);
  store64(s->result + 16, 0);
  store64(s->result + 24, 0);
  uint64_t obs[6] = {v, s->nk, s->nxp, nd, ne, s->err};
  for (int i = 0; i < 6; i++) store64(s->result + 32 + 8 * (size_t)i, obs[i]);
  memcpy(s->result + 80, s->dst, (size_t)nd);
  memcpy(s->result + 80 + nd, s->ev, (size_t)ne);
  sink ^= load64(s->result + 56) ^ load64(s->result + 64);
}

/* copy_total: the header stores and both memcpys only.  The sizes are the
   reference observation's, because the route-shaped context has already reset
   the state's cursors and the bytes in `dst`/`ev` are the reference's. */
static void act_copy_total(void *vp) {
  bench *b = vp;
  state *s = b->s;
  uint64_t nd = b->ref->ndst, ne = b->ref->nev;
  uint64_t total = HEADER_BYTES + nd + ne;
  if (total > s->resultcap) {
    fprintf(stderr, "cost-profile: result buffer too small\n");
    exit(3);
  }
  store64(s->result + 0, 0);
  store64(s->result + 8, 0);
  store64(s->result + 16, 0);
  store64(s->result + 24, 0);
  uint64_t obs[6] = {1, b->ref->nk, b->ref->nxp, nd, ne, 0};
  for (int i = 0; i < 6; i++) store64(s->result + 32 + 8 * (size_t)i, obs[i]);
  memcpy(s->result + 80, s->dst, (size_t)nd);
  memcpy(s->result + 80 + nd, s->ev, (size_t)ne);
  sink ^= load64(s->result + 56) ^ load64(s->result + 64);
}

static void act_copy_dst(void *vp) {
  bench *b = vp;
  state *s = b->s;
  uint64_t nd = b->ref->ndst;
  memcpy(s->result + 80, s->dst, (size_t)nd);
  sink ^= s->result[80] ^ s->result[80 + nd - 1];
}

static void act_copy_ev(void *vp) {
  bench *b = vp;
  state *s = b->s;
  uint64_t nd = b->ref->ndst, ne = b->ref->nev;
  memcpy(s->result + 80 + nd, s->ev, (size_t)ne);
  sink ^= s->result[80 + nd] ^ s->result[80 + nd + ne - 1];
}

static void act_chain(void *vp) {
  (void)vp;
  sink ^= clock_chain(CHAIN_IT);
}

enum {
  A_MASKS, A_ENTRY, A_ESCAPE, A_S1_NO_ESCAPE, A_S1_FUSED, A_PIPE_NOSTAGE2,
  A_UTF8, A_STAGE2, A_STAGE2_PLAIN, A_EXPAND, A_PIPELINE, A_NATIVE,
  A_COPY_TOTAL, A_COPY_DST, A_COPY_EV, A_CHAIN, A_COUNT
};

static const char *act_name[A_COUNT] = {
  "masks", "entry", "escape", "s1_no_escape", "s1_fused", "pipe_nostage2",
  "utf8", "stage2", "stage2_plain", "expand", "pipeline", "native",
  "copy_total", "copy_dst", "copy_ev", "chain"
};

static void (*const act_fn[A_COUNT])(void *) = {
  act_masks, act_entry, act_escape, act_s1_no_escape, act_s1_fused,
  act_pipe_nostage2, act_utf8, act_stage2, act_stage2_plain, act_expand,
  act_pipeline, act_native, act_copy_total, act_copy_dst, act_copy_ev,
  act_chain
};

/* --------------------------------------------------------------- gates -- */
static int failures;

static void gate_fail(const char *what) {
  fprintf(stderr, "GATE: %s\n", what);
  failures++;
}

static uint64_t direct_expand(bench *b, int zero_first) {
  if (zero_first) memset(b->x, 0, (size_t)b->s->n + 64);
  uint64_t xj = 0, len = 0, ok = 0;
  for (uint64_t e = 0; e < b->nesc; e++) {
    const body_t *bd = &b->esc[e];
    uint64_t pos0 = (uint64_t)bd->open + 1;
    uint64_t blen = (uint64_t)bd->close - pos0;
    uint64_t err = 0;
    uint64_t on = leanllvm_json_escape_expand(b->s->doc + pos0, blen,
                                              b->x + len, &err, b->xp, &xj,
                                              b->nxp, pos0);
    if (on == (uint64_t)-1) {
      fprintf(stderr, "GATE: expand refused body %" PRIu64 " (open %u)\n", e,
              bd->open);
      return (uint64_t)-1;
    }
    len += on;
    ok++;
  }
  b->xj = xj;
  b->xlen = len;
  return ok;
}

static int verify_expand(bench *b, const state *ref) {
  uint64_t calls = direct_expand(b, 1);
  if (calls != b->nesc) return -1;
  if (calls != EXPECT_ESCAPED_BODIES)
    { gate_fail("the escaped-body count is not 620"); return -1; }
  if (b->xj != ref->nxp) { gate_fail("expand left xj != nxp"); return -1; }
  if (b->xlen != ref->ndst) { gate_fail("expand wrote a different byte count");
    return -1; }
  if (memcmp(b->x, ref->dst, (size_t)ref->ndst) != 0)
    { gate_fail("expand bytes differ from the pipeline arena"); return -1; }
  return 0;
}

/* ---------------------------------------------------------------- main -- */
static uint8_t *read_file(const char *path, uint64_t *n) {
  FILE *f = fopen(path, "rb");
  if (f == NULL) {
    fprintf(stderr, "cost-profile: %s: %s\n", path, strerror(errno));
    exit(2);
  }
  if (fseek(f, 0, SEEK_END) != 0) { fprintf(stderr, "cost-profile: seek\n"); exit(2); }
  long m = ftell(f);
  if (m < 0 || fseek(f, 0, SEEK_SET) != 0) {
    fprintf(stderr, "cost-profile: size\n");
    exit(2);
  }
  uint8_t *buf = (uint8_t *)xalloc((size_t)m + 64);
  if (m > 0 && fread(buf, 1, (size_t)m, f) != (size_t)m) {
    fprintf(stderr, "cost-profile: read\n");
    exit(2);
  }
  if (fclose(f) != 0) { fprintf(stderr, "cost-profile: close\n"); exit(2); }
  *n = (uint64_t)m;
  return buf;
}

static unsigned core_class(void) {
  unsigned eax, ebx, ecx, edx;
  __asm__ volatile("cpuid"
                   : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
                   : "a"(0x1AU), "c"(0U));
  return (eax >> 24) & 0xFF;
}

static const char *base_name(const char *path) {
  const char *s = strrchr(path, '/');
  return s ? s + 1 : path;
}

int main(int argc, char **argv) {
  const char *doc_path = NULL;
  int rounds = 15, reps = 21;
  uint64_t arm = ARM;

  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--doc") && i + 1 < argc) {
      doc_path = argv[++i];
    } else if (!strcmp(argv[i], "--arm") && i + 1 < argc) {
      arm = strtoull(argv[++i], NULL, 10);
    } else if (!strcmp(argv[i], "--win-offset") && i + 1 < argc) {
      g_win_offset = strtoull(argv[++i], NULL, 10);
      if (g_win_offset > 64) {
        fprintf(stderr, "cost-profile: win-offset out of range\n");
        return 2;
      }
    } else if (!strcmp(argv[i], "--context") && i + 1 < argc) {
      const char *c = argv[++i];
      if (!strcmp(c, "route")) g_context = 1;
      else if (!strcmp(c, "none")) g_context = 0;
      else { fprintf(stderr, "cost-profile: unknown context %s\n", c); return 2; }
    } else if (!strcmp(argv[i], "--rounds") && i + 1 < argc) {
      rounds = atoi(argv[++i]);
      if (rounds < 3 || rounds > 1001) {
        fprintf(stderr, "cost-profile: rounds out of range\n");
        return 2;
      }
    } else if (!strcmp(argv[i], "--reps") && i + 1 < argc) {
      reps = atoi(argv[++i]);
      if (reps < 3 || reps > 10001) {
        fprintf(stderr, "cost-profile: reps out of range\n");
        return 2;
      }
    } else {
      fprintf(stderr, "cost-profile: bad argument %s\n", argv[i]);
      return 2;
    }
  }
  if (doc_path == NULL) {
    fprintf(stderr, "usage: cost-profile --doc <path> [--arm 2] "
                    "[--win-offset N] [--context route|none] "
                    "[--rounds N] [--reps N]\n");
    return 2;
  }
  if (arm != ARM) {
    fprintf(stderr, "cost-profile: this instrument is the route's arm 2, "
                    "not %" PRIu64 "\n", arm);
    return 2;
  }

  uint64_t n = 0;
  uint8_t *doc = read_file(doc_path, &n);
  if (n != EXPECT_SIZE) {
    fprintf(stderr, "cost-profile: the measured document is 65,536 bytes, "
                    "not %" PRIu64 "\n", n);
    return 2;
  }
  if (n % 64 != 0) {
    fprintf(stderr, "cost-profile: the measured document is a whole number of "
                    "blocks\n");
    return 2;
  }

  /* The entry unit's static table, as the adapter's setup fills it. */
  static uint32_t entry_table[256 * 8];
  leanllvm_json_entry_table(entry_table);

  /* The admission must select the route's arm. */
  {
    admit_facts af;
    admit_decide(doc, n, 1ull << 20, 128, NULL, 0, &af);
    if (af.tag != ADMIT_MEASURED || af.verdict != 1 || af.candidate != 1 ||
        af.escape_skip != 0) {
      fprintf(stderr, "GATE: admission tag=%" PRIu64 " verdict=%" PRIu64
                      " candidate=%" PRIu64 " escape_skip=%" PRIu64
                      " does not select arm 2\n",
              af.tag, af.verdict, af.candidate, af.escape_skip);
      failures++;
    }
  }

  state ref, bstate;
  state_init(&ref, doc, n);
  state_init(&bstate, doc, n);

  /* The independent scan: positions and quote pairs. */
  uint32_t *pos = (uint32_t *)xalloc((size_t)(n + 1) * 4);
  body_t *bodies = (body_t *)xalloc((size_t)(n / 2 + 2) * sizeof *bodies);
  uint64_t nbodies = 0;
  int unterminated = 0;
  uint64_t npos = scan_document(doc, n, pos, bodies, &nbodies, &unterminated);
  if (unterminated) { gate_fail("the scan ended inside a string"); }

  /* The reference observation. */
  reset_pipeline(&ref);
  uint64_t verdict = run_pipeline(&ref);
  printf("reference doc=%s size=%" PRIu64 " verdict=%" PRIu64
         " nk=%" PRIu64 " nxp=%" PRIu64 " ndst=%" PRIu64 " nev=%" PRIu64
         " err=%" PRIu64 " arena_fnv=%016" PRIx64 " event_fnv=%016" PRIx64
         "\n",
         base_name(doc_path), n, verdict, ref.nk, ref.nxp, ref.ndst, ref.nev,
         ref.err, fnv1a(0xcbf29ce484222325ull, ref.dst, ref.ndst),
         fnv1a(0xcbf29ce484222325ull, ref.ev, ref.nev));
  if (verdict != 1) gate_fail("the reference pipeline refused the document");
  if (ref.err != 0) gate_fail("the reference pipeline wrote a refusal offset");
  if (ref.nxp != EXPECT_NXP) gate_fail("nxp is not the recorded 1772");
  if (ref.ndst != EXPECT_NDST) gate_fail("ndst is not the recorded 55931");
  if (ref.nev != EXPECT_NEV) gate_fail("nev is not the recorded 8907");

  /* Gate 1: the separate stage-1 loop and stage 2 reproduce the observation. */
  precompute_stage1(&bstate);
  if (bstate.nk != ref.nk)
    { gate_fail("the separate stage-1 loop wrote a different entry count"); }
  else if (memcmp(bstate.ep, ref.ep, (size_t)ref.nk * 4) != 0)
    { gate_fail("the separate stage-1 loop wrote a different entry stream"); }
  if (bstate.nxp != ref.nxp)
    { gate_fail("the separate stage-1 loop wrote a different escape count"); }
  else if (memcmp(bstate.xp, ref.xp, (size_t)ref.nxp * 4) != 0)
    { gate_fail("the separate stage-1 loop wrote a different escape list"); }
  bstate.ndst = 0;
  bstate.nev = 0;
  bstate.err = 0;
  uint64_t s2v = run_stage2(&bstate, &ref, ref.nxp);
  if (s2v != verdict) gate_fail("stage 2 returned a different verdict");
  if (bstate.ndst != ref.ndst || bstate.nev != ref.nev ||
      bstate.err != ref.err)
    { gate_fail("stage 2 wrote different header words"); }
  else if (memcmp(bstate.dst, ref.dst, (size_t)ref.ndst) != 0)
    { gate_fail("stage 2 wrote different arena bytes"); }
  else if (memcmp(bstate.ev, ref.ev, (size_t)ref.nev) != 0)
    { gate_fail("stage 2 wrote different event bytes"); }
  if (failures == 0)
    printf("identity stage2=ok entry_stream=identical escape_list=identical "
           "arena=identical events=identical\n");

  /* Gate 2: the independent scan agrees with the pipeline's list. */
  if (npos != ref.nxp)
    { gate_fail("the independent scan counted a different position count"); }
  else if (memcmp(pos, ref.xp, (size_t)npos * 4) != 0)
    { gate_fail("the independent scan's positions differ from the list"); }
  for (uint64_t i = 0; i < npos; i++)
    if (pos[i] >= n) { gate_fail("a position is past the document"); break; }

  /* Gate 3: every position lies in exactly one body; count the escaped. */
  body_t *esc = (body_t *)xalloc((size_t)(nbodies ? nbodies : 1) * sizeof *esc);
  uint64_t nesc = 0, pi = 0;
  if (failures == 0) {
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
  }
  printf("bodies total=%" PRIu64 " escaped=%" PRIu64 " positions=%" PRIu64
         " expanded_bytes=%" PRIu64 "\n",
         nbodies, nesc, npos, ref.ndst);

  /* Gate 4: direct expand over the 620 bodies reproduces the arena. */
  bench b;
  memset(&b, 0, sizeof b);
  b.s = &bstate;
  b.ref = &ref;
  b.esc = esc;
  b.nesc = nesc;
  b.xp = ref.xp;
  b.nxp = ref.nxp;
  b.x = (uint8_t *)xalloc((size_t)n + 64);

  int exp_ok = (failures == 0) ? verify_expand(&b, &ref) : -1;
  if (exp_ok == 0)
    printf("identity expand=calls=%" PRIu64 " xj=%" PRIu64 " bytes=%" PRIu64
           " arena=identical arena_fnv=%016" PRIx64 "\n",
           nesc, b.xj, b.xlen,
           fnv1a(0xcbf29ce484222325ull, b.x, b.xlen));

  folded fold = fold_result(ref.dst, ref.ndst, ref.ev, ref.nev);
  printf("consumer tokens=%" PRIu64 " values=%" PRIu64 " foldsum=%" PRIu64
         " walked=%d\n", fold.tokens, fold.values, fold.sum, fold.walked);
  if (!fold.walked) gate_fail("the consumer walk did not reach the stream end");

  /* The ablation acts that are meant to preserve stage 1's streams do so. */
  act_s1_no_escape(&b);
  if (bstate.nk != ref.nk ||
      memcmp(bstate.ep, ref.ep, (size_t)ref.nk * 4) != 0)
    gate_fail("the s1_no_escape act wrote a different entry stream");
  act_s1_fused(&b);
  if (bstate.nk != ref.nk || bstate.nxp != ref.nxp ||
      memcmp(bstate.ep, ref.ep, (size_t)ref.nk * 4) != 0 ||
      memcmp(bstate.xp, ref.xp, (size_t)ref.nxp * 4) != 0)
    gate_fail("the s1_fused act wrote a different stage-1 stream");
  act_pipe_nostage2(&b);
  if (bstate.nk != ref.nk || bstate.nxp != ref.nxp ||
      memcmp(bstate.ep, ref.ep, (size_t)ref.nk * 4) != 0 ||
      memcmp(bstate.xp, ref.xp, (size_t)ref.nxp * 4) != 0)
    gate_fail("the pipe_nostage2 act wrote a different stage-1 stream");
  if (failures == 0)
    printf("identity ablations=streams_identical (stage2_plain is a cost "
           "probe and is not read through a gate)\n");

  if (failures != 0) {
    fprintf(stderr, "cost-profile: %d gate(s) failed before the clock\n",
            failures);
    return 3;
  }

  /* The copy acts read the pipeline's output; the state holds it from gate 1. */
  bstate.ndst = ref.ndst;
  bstate.nev = ref.nev;

  /* ---------------------------------------------------------- timing -- */
  uint64_t *round_ns[A_COUNT];
  uint64_t *samples = (uint64_t *)xalloc((size_t)reps * sizeof *samples);
  for (int a = 0; a < A_COUNT; a++)
    round_ns[a] = (uint64_t *)xalloc((size_t)rounds * sizeof(uint64_t));

  for (int round = 0; round < rounds; round++) {
    int fresh_first = (round % 2) == 0;
    for (int k = 0; k < A_COUNT; k++) {
      int a = (k + round) % A_COUNT;
      for (int rep = 0; rep < reps; rep++) {
        if (a != A_CHAIN) context_pre(&bstate, fresh_first);
        switch (a) {
        case A_PIPELINE:
        case A_NATIVE:
          reset_pipeline(&bstate);
          break;
        case A_STAGE2:
        case A_STAGE2_PLAIN:
          bstate.ndst = 0;
          bstate.nev = 0;
          bstate.err = 0;
          break;
        case A_EXPAND:
          b.xj = 0;
          b.xlen = 0;
          break;
        default:
          break;
        }
        uint64_t t0 = now_ns();
        act_fn[a](&b);
        uint64_t t1 = now_ns();
        samples[rep] = (a == A_UTF8) ? (t1 - t0) / 8 : (t1 - t0);
        if (a != A_CHAIN) context_post(&bstate, fresh_first);
      }
      round_ns[a][round] = median_of(samples, (size_t)reps);
    }
  }

  /* After the clock: the acts must have left the observation intact. */
  if (verify_expand(&b, &ref) != 0) failures++;
  reset_pipeline(&bstate);
  if (run_pipeline(&bstate) != 1 ||
      bstate.ndst != ref.ndst || bstate.nev != ref.nev ||
      bstate.nxp != ref.nxp ||
      memcmp(bstate.dst, ref.dst, (size_t)ref.ndst) != 0 ||
      memcmp(bstate.ev, ref.ev, (size_t)ref.nev) != 0)
    gate_fail("the pipeline changed during the timed rounds");
  if (failures != 0) {
    fprintf(stderr, "cost-profile: %d gate(s) failed after the clock\n",
            failures);
    return 3;
  }

  /* ---------------------------------------------------------- report -- */
  summary sm[A_COUNT];
  for (int a = 0; a < A_COUNT; a++)
    sm[a] = summarise(round_ns[a], (size_t)rounds);

  /* Cycles per round, from that round's chain. */
  uint64_t *round_cyc[A_COUNT];
  for (int a = 0; a < A_COUNT; a++) {
    round_cyc[a] = (uint64_t *)xalloc((size_t)rounds * sizeof(uint64_t));
    for (int r = 0; r < rounds; r++) {
      uint64_t chain_ns = round_ns[A_CHAIN][r];
      round_cyc[a][r] = (a == A_CHAIN)
                            ? CHAIN_IT
                            : (uint64_t)((double)round_ns[a][r] *
                                         (double)CHAIN_IT /
                                         (double)chain_ns);
    }
  }
  summary cm[A_COUNT];
  for (int a = 0; a < A_COUNT; a++)
    cm[a] = summarise(round_cyc[a], (size_t)rounds);

  double ghz = (double)CHAIN_IT / (double)sm[A_CHAIN].median;
  printf("\ninstrument cost-profile=1 arm=%" PRIu64 " context=%s "
         "compiler=%s core_class=0x%02x window_offset=%" PRIu64
         " rounds=%d reps=%d\n",
         arm, g_context ? "route" : "none", __VERSION__, core_class(),
         g_win_offset, rounds, reps);
  printf("clock: chain=%" PRIu64 " ns / %" PRIu64
         " iterations -> %.3f GHz (per-round range %.3f-%.3f)\n",
         sm[A_CHAIN].median, CHAIN_IT, ghz,
         (double)CHAIN_IT / (double)sm[A_CHAIN].max,
         (double)CHAIN_IT / (double)sm[A_CHAIN].min);
  printf("statistic: median of the round medians, min-max of those medians; "
         "cycles use each round's chain\n\n");
  printf("%-15s %14s %12s %12s %12s %10s\n", "act", "median_ns", "min_ns",
         "max_ns", "median_cyc", "us");
  for (int a = 0; a < A_COUNT; a++)
    printf("%-15s %14" PRIu64 " %12" PRIu64 " %12" PRIu64 " %12" PRIu64
           " %10.3f\n",
           act_name[a], sm[a].median, sm[a].min, sm[a].max, cm[a].median,
           (double)sm[a].median / 1000.0);

  /* Per-round paired differences: the telescoping chain. */
  uint64_t *d = (uint64_t *)xalloc((size_t)rounds * sizeof(uint64_t));
  const struct { const char *name; int hi, lo; } pairs[] = {
    {"copy", A_NATIVE, A_PIPELINE},
    {"stage2", A_PIPELINE, A_PIPE_NOSTAGE2},
    {"utf8", A_PIPE_NOSTAGE2, A_S1_FUSED},
    {"escape", A_S1_FUSED, A_S1_NO_ESCAPE},
    {"entry", A_S1_NO_ESCAPE, A_MASKS},
  };
  printf("\npaired differences (ns; each round's difference of that round's "
         "act medians, then the median of the differences)\n");
  uint64_t masks_med = sm[A_MASKS].median;
  uint64_t paired_sum = masks_med;
  uint64_t pm[8] = {0};
  for (size_t p = 0; p < sizeof pairs / sizeof pairs[0]; p++) {
    for (int r = 0; r < rounds; r++) {
      int64_t t = (int64_t)round_ns[pairs[p].hi][r] -
                  (int64_t)round_ns[pairs[p].lo][r];
      d[r] = (uint64_t)(t > 0 ? t : 0);
    }
    summary s = summarise(d, (size_t)rounds);
    printf("%-15s %14" PRIu64 " %12" PRIu64 " %12" PRIu64 "\n", pairs[p].name,
           s.median, s.min, s.max);
    pm[p] = s.median;
    paired_sum += s.median;
  }
  printf("%-15s %14" PRIu64 "\n", "masks (base)", masks_med);
  printf("%-15s %14" PRIu64 "  (per round the chain telescopes exactly to the "
         "pipeline; this row is the sum of the terms' medians, so it need not "
         "equal the pipeline row)\n", "sum", paired_sum);

  /* The isolated acts against the chain: the de-fusion term. */
  uint64_t iso = sm[A_MASKS].median + sm[A_ENTRY].median +
                 sm[A_ESCAPE].median + sm[A_UTF8].median +
                 sm[A_STAGE2].median;
  printf("\nisolated acts: masks+entry+escape+utf8+stage2 = %" PRIu64
         " pipeline = %" PRIu64 "\n", iso, sm[A_PIPELINE].median);
  printf("de-fusion (pipeline - isolated) = %" PRId64 "\n",
         (int64_t)sm[A_PIPELINE].median - (int64_t)iso);
  printf("stage2 - stage2_plain (list-driven decode) = %" PRId64
         " expand (620 calls) = %" PRIu64 "\n",
         (int64_t)sm[A_STAGE2].median - (int64_t)sm[A_STAGE2_PLAIN].median,
         sm[A_EXPAND].median);

  uint64_t nd = ref.ndst, ne = ref.nev;
  printf("\ncopy bytes: arena=%" PRIu64 " events=%" PRIu64
         " memcpy_total=%" PRIu64 " header=%" PRIu64
         " result_total=%" PRIu64 "\n",
         nd, ne, nd + ne, HEADER_BYTES, HEADER_BYTES + nd + ne);
  printf("throughput: pipeline=%.3f GB/s native=%.3f GB/s\n",
         (double)n / (double)sm[A_PIPELINE].median,
         (double)n / (double)sm[A_NATIVE].median);
  printf("shares_of_native (paired chain): masks=%.1f%% entry=%.1f%% "
         "escape=%.1f%% utf8=%.1f%% stage2=%.1f%% copy=%.1f%%\n",
         100.0 * (double)masks_med / (double)sm[A_NATIVE].median,
         100.0 * (double)pm[4] / (double)sm[A_NATIVE].median,
         100.0 * (double)pm[3] / (double)sm[A_NATIVE].median,
         100.0 * (double)pm[2] / (double)sm[A_NATIVE].median,
         100.0 * (double)pm[1] / (double)sm[A_NATIVE].median,
         100.0 * (double)pm[0] / (double)sm[A_NATIVE].median);
  printf("shares_of_native (standalone acts): pipeline=%.1f%% copy_total=%.1f%% "
         "stage2=%.1f%% expand=%.1f%% utf8=%.1f%% masks+entry+escape=%.1f%%\n",
         100.0 * (double)sm[A_PIPELINE].median / (double)sm[A_NATIVE].median,
         100.0 * (double)sm[A_COPY_TOTAL].median / (double)sm[A_NATIVE].median,
         100.0 * (double)sm[A_STAGE2].median / (double)sm[A_NATIVE].median,
         100.0 * (double)sm[A_EXPAND].median / (double)sm[A_NATIVE].median,
         100.0 * (double)sm[A_UTF8].median / (double)sm[A_NATIVE].median,
         100.0 * (double)(sm[A_MASKS].median + sm[A_ENTRY].median +
                            sm[A_ESCAPE].median) /
             (double)sm[A_NATIVE].median);

  free(d);
  free(samples);
  for (int a = 0; a < A_COUNT; a++) { free(round_ns[a]); free(round_cyc[a]); }
  free(b.x);
  free(esc);
  free(bodies);
  free(pos);
  state_free(&ref);
  state_free(&bstate);
  free(doc);
  return 0;
}
