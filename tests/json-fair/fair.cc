// Ported from /tmp/c-fair/fair.cc (sha256 832c4dfcfc62b4c79d38c12e86e8c0331d1224db25645854e028cde5441cdaf3) with the deviations listed below and in README.md.

/* fair.cc -- equal-output comparison between simdjson 5.0.5's full traversal
   and this tree's JSON pipeline, both read by the same C consumer.

   The writer below reproduces the event stream and arena `stage2.c` emits, so
   the comparison is between equal outputs and not between two different
   readings.  Its encoding (the constants `kernel/json/stage2.c` defines):

     containers  one byte: T_OBJ=1, T_OBJ_END=2, T_ARR=3, T_ARR_END=4
     key/string  13 bytes: tag (T_KEY=5 or T_STR=6), a 4-byte LE length and an
                 8-byte LE payload.  A plain body's payload is the body's
                 document offset with the top bit set (`(uint64_t)(p + 1) |
                 1 << 63`, `p` the opening quote); an escaped body's payload is
                 its offset in the arena, and its decoded bytes are appended to
                 the arena in document order.
     number      9 bytes: T_NUM=7 and the value's eight IEEE-754 bytes
     literal     1 byte: T_TRUE=8, T_FALSE=9, T_NULL=10

   A string body is the plain form or the escaped form according to the same
   stage-1 escape list stage 2 reads: the list is built when the route selects
   arm bit 1, and a body with no list position inside it is a plain span.  That
   is the route's own arm choice (`leanllvm_route_escape_can_skip`, the
   admission's cheap presence scan, evaluated once per document outside every
   timed region), so `rp` is the call the shipped route makes and not a
   different arming of the same object.  The decoded bytes come from
   `leanllvm_json_escape_expand`, the entry point `stage2.c` itself calls, so
   the arena is a reproduction of the reader's arithmetic rather than a second
   unescaper.

   Gates, once per document before anything is timed:

     - the writer's event stream and arena equal `leanllvm_json_pipeline`'s
       byte for byte;
     - the same C consumer (`consume`) reads both streams and agrees on
       tokens, values, walked and sum;
     - the cell-by-cell direct sum (`ps`) equals that consumer's fold over the
       pipeline's stream.  This is the consumer boundary without an event
       buffer, and it is the denominator the no-event row is measured against.

   A gate failure is a setup failure: the document is reported and not timed,
   and the process exits non-zero.

   Terms: `parse` (simdjson traversal only), `pw` (traversal + the writer),
   `pwc` (`pw` + the consumer), `ps` (traversal + the direct consumer sum, no
   event buffer), `rp` (the pipeline call, which materialises its stream),
   `rpc` (`rp` + the consumer), and `rpn` (the no-event pipeline's returned
   reading, no event buffer and no consumer walk).

   `rpn` is compiled only when `FAIR_NOEVENT` is defined and the no-event
   objects are linked; without it the harness links the certified set alone and
   the arm is absent.  When present, the arm is gated like the others: its
   tokens, values and sum equal the certified stream's fold, and its stage-1
   cursors equal the certified call's.

   Differences from the ported file, which was written against a tree whose
   kernel interfaces differ from this one:

     - A plain body's payload is its document offset (`p + 1`, `p` the opening
       quote), not an address into the input window.
     - The arm word is the route admission's: bit 1 (the stage-1 escape list)
       is cleared exactly when the document has neither a backslash nor a
       control byte, and the choice is made once per document outside every
       timed region.
     - A body's form and decoded bytes come from the pipeline's own stage-1
       escape list and `leanllvm_json_escape_expand`, the entry `stage2.c`
       calls.  This tree has neither `leanllvm_json_escape_decode` nor the
       `pipeline_fast` headers the ported file included.
     - One `ROW` line is printed per (document, arm, trial), so a driver can
       take medians of within-trial quotients; the ported file printed one
       median per arm. */
#define _GNU_SOURCE 1
#ifndef FAIR_NOEVENT
#define FAIR_NOEVENT 0
#endif
#include "simdjson.h"

extern "C" {
#include "entry.h"
#include "escape.h"
#include "escape_guard.h"
#include "pipeline.h"
#if FAIR_NOEVENT
#include "stage2_noevent.h"
#endif
}

#include <algorithm>
#include <cerrno>
#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <string>
#include <vector>

static volatile uint64_t sink;

static uint64_t now_ns(void) {
  struct timespec t;
  if (clock_gettime(CLOCK_MONOTONIC_RAW, &t) != 0) { perror("clock"); exit(2); }
  return (uint64_t)t.tv_sec * 1000000000ull + (uint64_t)t.tv_nsec;
}
static uint64_t median_of(uint64_t *v, int n) {
  for (int i = 1; i < n; i++) {
    uint64_t t = v[i]; int j = i - 1;
    while (j >= 0 && v[j] > t) { v[j + 1] = v[j]; j--; }
    v[j + 1] = t;
  }
  return v[(n - 1) / 2];
}
static void die(int c, const char *m) { fprintf(stderr, "fair: %s\n", m); exit(c); }

static const uint8_t T_OBJ = 1, T_OBJ_END = 2, T_ARR = 3, T_ARR_END = 4,
                     T_KEY = 5, T_STR = 6, T_NUM = 7, T_TRUE = 8, T_FALSE = 9,
                     T_NULL = 10;

/* ---------------------------------------------------------------- writer -- */
struct W {
  uint8_t *ev; uint64_t evlen, evcap;
  uint8_t *ar; uint64_t arlen, arcap;
  const uint8_t *doc;      /* the pipeline's input window */
  const uint8_t *ps;       /* simdjson's padded base, for offset translation */
  const uint32_t *xp;      /* the stage-1 escape list the pipeline built */
  uint64_t nxp, xj;        /* ... and the body cursor stage 2 threads */
  int err, sum_only;
  /* consumer accumulator (sum_only) */
  uint64_t tokens, values, sum;
};

static inline void ev_put(W *w, uint8_t t) {
  if (w->sum_only) { w->sum += t; w->tokens++; w->values++; return; }
  if (w->evlen + 1 > w->evcap) { w->err = 1; return; }
  w->ev[w->evlen++] = t;
}
static inline void ev_rec(W *w, uint8_t tag, uint64_t len, uint64_t rec) {
  if (w->sum_only) { w->sum += tag + len + rec; w->tokens++; w->values++; return; }
  if (w->evlen + 13 > w->evcap) { w->err = 1; return; }
  uint8_t *p = w->ev + w->evlen;
  p[0] = tag;
  p[1] = (uint8_t)len; p[2] = (uint8_t)(len >> 8);
  p[3] = (uint8_t)(len >> 16); p[4] = (uint8_t)(len >> 24);
  for (int i = 0; i < 8; i++) p[5 + i] = (uint8_t)(rec >> (8 * i));
  w->evlen += 13;
}
static inline void ev_num(W *w, uint64_t bits) {
  if (w->sum_only) { w->sum += T_NUM + bits; w->tokens++; w->values++; return; }
  if (w->evlen + 9 > w->evcap) { w->err = 1; return; }
  uint8_t *p = w->ev + w->evlen;
  p[0] = T_NUM;
  for (int i = 0; i < 8; i++) p[1 + i] = (uint8_t)(bits >> (8 * i));
  w->evlen += 9;
}

/* Body scan: the closing quote and the first special byte, 32 bytes at a
   time, the same classification stage2's scan makes.  The padded_string's
   SIMDJSON_PADDING makes the tail load safe; a zero pad byte is a control byte
   and ends the scan with a refusal rather than running past the document. */
static int scan_body(const uint8_t *raw, uint64_t *len, uint64_t *off) {
  const __m256i quote = _mm256_set1_epi8('"');
  const __m256i bs = _mm256_set1_epi8('\\');
  const __m256i c19 = _mm256_set1_epi8(0x1F);
  const uint8_t *q = raw;
  uint64_t sp = UINT64_MAX;
  for (;;) {
    __m256i v = _mm256_loadu_si256((const __m256i *)(const void *)q);
    uint32_t mq = (uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v, quote));
    uint32_t mb = (uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v, bs));
    uint32_t mc = (uint32_t)_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(_mm256_min_epu8(v, c19), v));
    uint32_t m = mq | mb | mc;
    if (!m) { q += 32; continue; }
    unsigned b = (unsigned)__builtin_ctz(m);
    if (mq & (1u << b)) { *len = (uint64_t)(q + b - raw); *off = sp; return 1; }
    if (mc & (1u << b)) return 0;   /* raw control byte: stage2 refuses */
    if (sp == UINT64_MAX) sp = (uint64_t)(q + b - raw);
    q += b + 2;                      /* skip the backslash and its escaped byte */
  }
}

/* One string body (raw points just after the opening quote).  The form is the
   pipeline's own: a list position inside the body selects the decoded form. */
static void write_string(W *w, const uint8_t *raw, int is_key) {
  uint64_t len = 0, special = UINT64_MAX;
  if (!scan_body(raw, &len, &special)) { w->err = 1; return; }
  (void)special;
  uint8_t tag = is_key ? T_KEY : T_STR;
  uint64_t pos0 = (uint64_t)(raw - w->ps);
  while (w->xj < w->nxp && (uint64_t)w->xp[w->xj] < pos0) w->xj++;
  if (!(w->xj < w->nxp && (uint64_t)w->xp[w->xj] < pos0 + len)) {
    uint64_t rec = pos0 | (1ULL << 63);
    ev_rec(w, tag, len, rec);
    return;
  }
  uint64_t at = w->arlen;
  if (at + len + 64 > w->arcap) { w->err = 1; return; }
  uint64_t e = 0;
  uint64_t on = leanllvm_json_escape_expand(w->doc + pos0, len, w->ar + at, &e,
                                            w->xp, &w->xj, w->nxp, pos0);
  if (on == ~0ULL) { w->err = 1; return; }
  if (w->sum_only) {
    for (uint64_t i = 0; i < on; i++) w->sum += w->ar[at + i];
  }
  w->arlen += on;
  ev_rec(w, tag, on, at);
}

/* ------------------------------------------------------------ traversal -- */
static int write_value(W *w, simdjson::ondemand::value &v);

static int write_object(W *w, simdjson::ondemand::value &v) {
  ev_put(w, T_OBJ);
  if (w->err) return 0;
  simdjson::ondemand::object obj;
  if (auto e = v.get_object().get(obj)) { w->err = 1; return 0; }
  for (auto &&f : obj) {
    simdjson::ondemand::raw_json_string k = f.key();
    write_string(w, (const uint8_t *)k.raw(), 1);
    if (w->err) return 0;
    simdjson::ondemand::value fv;
    auto vr = f.value();
    if (auto e = std::move(vr).get(fv)) { w->err = 1; return 0; }
    if (!write_value(w, fv)) return 0;
  }
  ev_put(w, T_OBJ_END);
  return !w->err;
}
static int write_array(W *w, simdjson::ondemand::value &v) {
  ev_put(w, T_ARR);
  if (w->err) return 0;
  simdjson::ondemand::array arr;
  if (auto e = v.get_array().get(arr)) { w->err = 1; return 0; }
  for (auto x : arr) {
    simdjson::ondemand::value xv;
    if (auto e = x.get(xv)) { w->err = 1; return 0; }
    if (!write_value(w, xv)) return 0;
  }
  ev_put(w, T_ARR_END);
  return !w->err;
}
static int write_value(W *w, simdjson::ondemand::value &v) {
  simdjson::ondemand::json_type t;
  if (auto e = v.type().get(t)) { w->err = 1; return 0; }
  switch (t) {
  case simdjson::ondemand::json_type::object: return write_object(w, v);
  case simdjson::ondemand::json_type::array: return write_array(w, v);
  case simdjson::ondemand::json_type::string: {
    simdjson::ondemand::raw_json_string r;
    if (auto e = v.get_raw_json_string().get(r)) { w->err = 1; return 0; }
    write_string(w, (const uint8_t *)r.raw(), 0);
    return !w->err;
  }
  case simdjson::ondemand::json_type::number: {
    double d;
    if (auto e = v.get_double().get(d)) { w->err = 1; return 0; }
    uint64_t bits; memcpy(&bits, &d, 8);
    ev_num(w, bits);
    return !w->err;
  }
  case simdjson::ondemand::json_type::boolean: {
    bool b;
    if (auto e = v.get_bool().get(b)) { w->err = 1; return 0; }
    ev_put(w, b ? T_TRUE : T_FALSE);
    return !w->err;
  }
  case simdjson::ondemand::json_type::null:
    ev_put(w, T_NULL);
    return !w->err;
  case simdjson::ondemand::json_type::unknown:
    w->err = 1;
    return 0;
  }
  return 0;
}
static int write_doc(W *w, simdjson::ondemand::document &doc) {
  simdjson::ondemand::value v;
  if (auto e = doc.get_value().get(v)) { w->err = 1; return 0; }
  return write_value(w, v);
}

/* parse-only traversal (validation and counting, no events). */
static simdjson::error_code g_err;
static void set_err(simdjson::error_code e) { if (g_err == simdjson::SUCCESS) g_err = e; }
static uint64_t count_value(simdjson::ondemand::value &v) {
  using namespace simdjson;
  if (g_err != SUCCESS) return 0;
  ondemand::json_type t;
  if (auto e = v.type().get(t)) { set_err(e); return 0; }
  switch (t) {
  case ondemand::json_type::null: return 1;
  case ondemand::json_type::boolean: { bool b; if (auto e=v.get_bool().get(b)){set_err(e);return 0;} return 1+b; }
  case ondemand::json_type::number: { double d; if (auto e=v.get_double().get(d)){set_err(e);return 0;} if (!(d==d)||d>=9e18||d<=-9e18) return 1; return 1+(uint64_t)(int64_t)d; }
  case ondemand::json_type::string: { std::string_view s; if (auto e=v.get_string().get(s)){set_err(e);return 0;} return 1+s.size(); }
  case ondemand::json_type::array: {
    ondemand::array a; if (auto e=v.get_array().get(a)){set_err(e);return 0;}
    uint64_t n=0; for (auto x : a) { ondemand::value xv; if (auto e=x.get(xv)){set_err(e);break;} n+=count_value(xv); if (g_err!=SUCCESS) break; }
    return n+1; }
  case ondemand::json_type::object: {
    ondemand::object o; if (auto e=v.get_object().get(o)){set_err(e);return 0;}
    uint64_t n=0; for (auto &&f : o) { std::string_view k; auto kr=f.unescaped_key(); if (auto e=std::move(kr).get(k)){set_err(e);break;} n+=k.size();
      auto vr=f.value(); ondemand::value fv; if (auto e=std::move(vr).get(fv)){set_err(e);break;} n+=count_value(fv); if (g_err!=SUCCESS) break; }
    return n+1; }
  case ondemand::json_type::unknown: return 0;
  }
  return 0;
}
static uint64_t parse_only(simdjson::ondemand::parser &parser,
                           const simdjson::padded_string &ps, uint64_t *check) {
  g_err = simdjson::SUCCESS;
  simdjson::ondemand::document doc;
  uint64_t walked = 0;
  auto dr = parser.iterate(ps);
  if (auto e = std::move(dr).get(doc)) { set_err(e); }
  else {
    simdjson::ondemand::value v;
    if (auto e = doc.get_value().get(v)) set_err(e);
    else walked = count_value(v);
  }
  *check = ((uint64_t)g_err << 32) ^ walked;
  return walked;
}

/* --------------------------------------------------------------- consumer -- */
typedef struct { uint64_t tokens, values, sum, arena, events; int walked; } C;
static uint64_t ev_width(uint8_t t) { return (t == 5 || t == 6) ? 13 : (t == 7 ? 9 : 1); }
static C consume(const uint8_t *ar, uint64_t narena, const uint8_t *ev,
                 uint64_t nev) {
  C c = {0, 0, 0, 0, 0, 0};
  uint64_t sum = 0;
  for (uint64_t i = 0; i < narena; i++) sum += ar[i];
  uint64_t k = 0, tokens = 0, values = 0;
  while (k < nev) {
    uint8_t t = ev[k];
    uint64_t w = ev_width(t);
    if (k + w > nev) { c.tokens=tokens; c.events=k; c.sum=sum; c.walked=0; c.values=values; c.arena=narena; return c; }
    uint64_t len = 0, payload = 0;
    if (w == 13) {
      len = (uint64_t)ev[k+1] | ((uint64_t)ev[k+2]<<8) | ((uint64_t)ev[k+3]<<16) | ((uint64_t)ev[k+4]<<24);
      memcpy(&payload, ev + k + 5, 8);
    } else if (w == 9) memcpy(&payload, ev + k + 1, 8);
    sum += (uint64_t)t + len + payload;
    values++; tokens++;
    k += w;
  }
  c.tokens=tokens; c.values=values; c.sum=sum; c.arena=narena; c.events=k; c.walked=1;
  return c;
}

/* --------------------------------------------------------------- staging -- */
typedef struct {
  std::string name, path;
  std::string bytes;
  uint64_t n, nb, epcap, xpcap, dstcap, evcap;
  uint8_t *win, *sc, *mk, *entw, *ep, *nk, *xp, *nxp, *xcarry;
  uint8_t *dst, *ndst, *ev, *nev, *err, *ent;
  uint64_t arm;                 /* the route's admission arm word for this doc */
#if FAIR_NOEVENT
  uint8_t *scratch;
  uint64_t scratchcap, nt, nv, ns, nerr;
#endif
} doc_t;

static void read_file(const char *p, std::string *s) {
  FILE *f = fopen(p, "rb");
  if (!f) { fprintf(stderr, "fair: %s: %s\n", p, strerror(errno)); exit(2); }
  char b[65536]; size_t g;
  while ((g = fread(b, 1, sizeof b, f)) > 0) s->append(b, g);
  fclose(f);
}
static void *xa(size_t n) { void *p = malloc(n ? n : 1); if (!p) die(4, "alloc"); return p; }
static void stage(doc_t *d) {
  d->nb = (d->n + 63) >> 6;
  d->epcap = 64 * d->nb + 9; d->xpcap = 64 * d->nb + 8;
  d->dstcap = d->n + 64; d->evcap = 13 * d->n + 128;
  d->win = (uint8_t *)xa((size_t)(3 + 64 * d->nb + 32));
  memset(d->win, 0, (size_t)(3 + 64 * d->nb + 32));
  memcpy(d->win + 3, d->bytes.data(), (size_t)d->n);
  d->sc = (uint8_t *)xa(24); d->mk = (uint8_t *)xa(48); d->entw = (uint8_t *)xa(8);
  d->ep = (uint8_t *)xa((size_t)(4 * d->epcap)); d->nk = (uint8_t *)xa(8);
  d->xp = (uint8_t *)xa((size_t)(4 * d->xpcap)); d->nxp = (uint8_t *)xa(8);
  d->xcarry = (uint8_t *)xa(16); d->dst = (uint8_t *)xa((size_t)d->dstcap);
  d->ndst = (uint8_t *)xa(8); d->ev = (uint8_t *)xa((size_t)d->evcap);
  d->nev = (uint8_t *)xa(8); d->err = (uint8_t *)xa(8); d->ent = (uint8_t *)xa((size_t)(8 * d->nb));
  /* The arm word is the route admission's: bit 1 (the stage-1 escape list) is
     cleared exactly when the document has neither a backslash nor a control
     byte, so the list the pipeline would build is empty.  The scan is outside
     every timed region; it is not a stage of the pipeline. */
  d->arm = leanllvm_route_escape_can_skip(d->win + 3, d->n) ? 0 : 2;
#if FAIR_NOEVENT
  d->scratchcap = d->n + 64;
  d->scratch = (uint8_t *)xa((size_t)d->scratchcap);
  d->nt = d->nv = d->ns = d->nerr = 0;
#endif
}
static void reset(doc_t *d) {
  memset(d->nk, 0, 8); memset(d->nxp, 0, 8); memset(d->ndst, 0, 8);
  memset(d->nev, 0, 8); memset(d->err, 0, 8);
  memset(d->sc, 0, 24); memset(d->mk, 0, 48); memset(d->entw, 0, 8); memset(d->xcarry, 0, 16);
}
static uint64_t route_pipeline(doc_t *d) {
  return leanllvm_json_pipeline(d->win + 3, d->n, (uint64_t *)d->sc,
                                (uint64_t *)d->mk, (uint64_t *)d->entw,
                                (uint32_t *)d->ep, d->epcap, (uint64_t *)d->nk,
                                (uint32_t *)d->xp, d->xpcap, (uint64_t *)d->nxp,
                                (uint64_t *)d->xcarry, d->dst, d->dstcap,
                                (uint64_t *)d->ndst, d->ev, d->evcap,
                                (uint64_t *)d->nev, (uint64_t *)d->err, d->arm);
}
#if FAIR_NOEVENT
static uint64_t noevent_pipeline(doc_t *d) {
  d->nt = d->nv = d->ns = 0;
  return leanllvm_json_pipeline_noevent(
      d->win + 3, d->n, (uint64_t *)d->sc, (uint64_t *)d->mk,
      (uint64_t *)d->entw, (uint32_t *)d->ep, d->epcap, (uint64_t *)d->nk,
      (uint32_t *)d->xp, d->xpcap, (uint64_t *)d->nxp,
      (uint64_t *)d->xcarry, d->scratch, d->scratchcap, &d->nt, &d->nv, &d->ns,
      &d->nerr, d->arm);
}
#endif
static uint64_t ld(const uint8_t *p) { uint64_t x; memcpy(&x, p, 8); return x; }

/* ------------------------------------------------------------------ main -- */
int main(int argc, char **argv) {
  int reps = 51, trials = 3;
  std::vector<const char *> paths;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--doc") && i + 1 < argc) paths.push_back(argv[++i]);
    else if (!strcmp(argv[i], "--reps") && i + 1 < argc) reps = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--trials") && i + 1 < argc) trials = atoi(argv[++i]);
    else { fprintf(stderr, "fair: bad arg %s\n", argv[i]); return 2; }
  }
  if (paths.empty() || reps < 3 || trials < 1 || reps > 512) return 2;
  {
    static uint32_t tab[256 * 8];
    leanllvm_json_entry_table(tab);
  }
  std::printf("META\treps=%d\ttrials=%d\tdocs=%zu\tnoevent=%d\n", reps, trials,
              paths.size(), (int)(FAIR_NOEVENT ? 1 : 0));

  int gate_fail = 0;
  for (size_t di = 0; di < paths.size(); di++) {
    doc_t d;
    d.path = paths[di];
    const char *base = strrchr(paths[di], '/'); base = base ? base + 1 : paths[di];
    d.name = base; size_t dot = d.name.rfind('.'); if (dot != std::string::npos) d.name.resize(dot);
    read_file(paths[di], &d.bytes);
    d.n = d.bytes.size();
    stage(&d);

    /* route reference */
    reset(&d);
    uint64_t rv = route_pipeline(&d);
    uint64_t ndst = ld(d.ndst), nev = ld(d.nev);
    uint64_t ref_nk = ld(d.nk), ref_nxp = ld(d.nxp);
    std::vector<uint8_t> dst0(d.dst, d.dst + ndst), ev0(d.ev, d.ev + nev);
    C routeC = consume(d.dst, ndst, d.ev, nev);

    /* simdjson writer */
    simdjson::padded_string ps(reinterpret_cast<const char *>(d.bytes.data()),
                               d.bytes.size());
    simdjson::ondemand::parser parser;
    std::vector<uint8_t> wbuf(13 * d.n + 128), abuf(d.n + 128 + 64);
    W w; memset(&w, 0, sizeof w);
    w.ev = wbuf.data(); w.evcap = wbuf.size();
    w.ar = abuf.data(); w.arcap = abuf.size();
    w.doc = d.win + 3;
    w.ps = reinterpret_cast<const uint8_t *>(ps.data());
    w.xp = reinterpret_cast<const uint32_t *>(d.xp); w.nxp = ref_nxp; w.xj = 0;
    simdjson::ondemand::document wdoc;
    bool writer_ok = true;
    {
      auto dr = parser.iterate(ps);
      if (auto e = std::move(dr).get(wdoc)) writer_ok = false;
      else if (!write_doc(&w, wdoc)) writer_ok = false;
      if (w.err) writer_ok = false;
    }
    int ev_eq = writer_ok && ev0.size() == w.evlen &&
                memcmp(ev0.data(), w.ev, (size_t)w.evlen) == 0;
    int ar_eq = writer_ok && ndst == w.arlen &&
                memcmp(dst0.data(), w.ar, (size_t)ndst) == 0;
    C wc = writer_ok ? consume(w.ar, w.arlen, w.ev, w.evlen) : C{};
    int c_eq = routeC.tokens == wc.tokens && routeC.values == wc.values &&
               routeC.sum == wc.sum && wc.walked == routeC.walked;

    /* direct-sum traversal (consumer boundary, no event buffer) */
    W s; memset(&s, 0, sizeof s);
    s.ar = abuf.data(); s.arcap = abuf.size();
    s.doc = d.win + 3; s.ps = w.ps;
    s.xp = w.xp; s.nxp = ref_nxp; s.xj = 0; s.sum_only = 1;
    bool sum_ok = true;
    {
      simdjson::ondemand::document sdoc;
      auto dr = parser.iterate(ps);
      if (auto e = std::move(dr).get(sdoc)) sum_ok = false;
      else if (!write_doc(&s, sdoc)) sum_ok = false;
      if (s.err) sum_ok = false;
    }
    int sum_eq = sum_ok && s.tokens == routeC.tokens && s.values == routeC.values &&
                 s.sum == routeC.sum;

#if FAIR_NOEVENT
    /* the no-event arm's reading, against the same certified fold */
    reset(&d);
    uint64_t rn = noevent_pipeline(&d);
    int rpn_eq = rn == rv && ld(d.nk) == ref_nk && ld(d.nxp) == ref_nxp &&
                 d.nt == routeC.tokens && d.nv == routeC.values &&
                 d.ns == routeC.sum;
#endif

    int ok = writer_ok && ev_eq && ar_eq && c_eq;
    if (!ok) {
      size_t at = 0;
      if (writer_ok && !ev_eq) { while (at < std::min(ev0.size(), (size_t)w.evlen) && ev0[at] == w.ev[at]) at++; }
      else if (writer_ok && !ar_eq) { while (at < std::min(dst0.size(), (size_t)w.arlen) && dst0[at] == w.ar[at]) at++; }
      printf("GATE\t%s\tFAIL\twriter=%d ev=%d arena=%d consumer=%d\t"
             "evlen=%zu/%" PRIu64 "\tarenalen=%zu/%" PRIu64 "\tat=%zu\t"
             "counts=%" PRIu64 "/%" PRIu64 " sum=%" PRIu64 "/%" PRIu64 "\n",
             d.name.c_str(), writer_ok, ev_eq, ar_eq, c_eq, ev0.size(), w.evlen,
             dst0.size(), w.arlen, at, routeC.tokens, wc.tokens, routeC.sum, wc.sum);
      gate_fail++;
      continue;
    }
    if (!sum_eq) {
      printf("GATE\t%s\tFAIL\tdirect-sum tokens=%" PRIu64 "/%" PRIu64
             " values=%" PRIu64 "/%" PRIu64 " sum=%" PRIu64 "/%" PRIu64 "\n",
             d.name.c_str(), s.tokens, routeC.tokens, s.values, routeC.values,
             s.sum, routeC.sum);
      gate_fail++;
      continue;
    }
#if FAIR_NOEVENT
    if (!rpn_eq) {
      printf("GATE\t%s\tFAIL\tnoevent verdict=%" PRIu64 "/%" PRIu64
             " tokens=%" PRIu64 "/%" PRIu64 " values=%" PRIu64 "/%" PRIu64
             " sum=%" PRIu64 "/%" PRIu64 "\n",
             d.name.c_str(), rn, rv, d.nt, routeC.tokens, d.nv, routeC.values,
             d.ns, routeC.sum);
      gate_fail++;
      continue;
    }
#endif
    printf("GATE\t%s\tpass\tev=%" PRIu64 "\tarena=%" PRIu64 "\ttokens=%" PRIu64
           "\tvalues=%" PRIu64 "\tsum=%" PRIu64 "\tarm=%" PRIu64 "\n",
           d.name.c_str(), nev, ndst, routeC.tokens, routeC.values, routeC.sum,
           d.arm);

    /* timed acts: parse, pw, pwc, ps, rp, rpc[, rpn] */
    enum { A_PARSE, A_PW, A_PWC, A_PS, A_RP, A_RPC,
#if FAIR_NOEVENT
           A_RPN,
#endif
           A_COUNT };
    static const char *const aname[A_COUNT] = {"parse", "pw", "pwc", "ps", "rp",
                                               "rpc"
#if FAIR_NOEVENT
                                               , "rpn"
#endif
    };
    uint64_t med[A_COUNT][512];
    W *wr = &w;
    for (int a = 0; a < A_COUNT; a++) {
      /* one warm pass per arm, outside the clock */
      uint64_t v = 0;
      if (a == A_PARSE) { uint64_t chk; v = parse_only(parser, ps, &chk); }
      else if (a == A_PW || a == A_PWC) {
        wr->evlen = 0; wr->arlen = 0; wr->err = 0; wr->xj = 0;
        simdjson::ondemand::document doc;
        auto dr = parser.iterate(ps);
        if (auto e = std::move(dr).get(doc)) wr->err = 1;
        else write_doc(wr, doc);
        if (a == A_PWC) { C cc = consume(wr->ar, wr->arlen, wr->ev, wr->evlen); v = cc.sum ^ cc.tokens; }
        else v = wr->evlen;
      } else if (a == A_PS) {
        s.tokens = s.values = s.sum = 0; s.err = 0; s.evlen = 0; s.arlen = 0; s.xj = 0;
        simdjson::ondemand::document doc;
        auto dr = parser.iterate(ps);
        if (auto e = std::move(dr).get(doc)) s.err = 1;
        else write_doc(&s, doc);
        v = s.sum ^ s.tokens;
#if FAIR_NOEVENT
      } else if (a == A_RPN) {
        reset(&d);
        v = noevent_pipeline(&d);
        v ^= d.ns;
#endif
      } else {
        reset(&d);
        v = route_pipeline(&d);
        if (a == A_RPC) { C cc = consume(d.dst, ld(d.ndst), d.ev, ld(d.nev)); v ^= cc.sum; }
      }
      sink ^= v;
    }
    for (int t = 0; t < trials; t++) {
      int order[A_COUNT]; for (int i = 0; i < A_COUNT; i++) order[i] = i;
      int rot = t % A_COUNT;
      for (int i = 0; i < rot; i++) { int f = order[0]; for (int j = 0; j + 1 < A_COUNT; j++) order[j] = order[j+1]; order[A_COUNT-1] = f; }
      for (int oi = 0; oi < A_COUNT; oi++) {
        int a = order[oi];
        uint64_t samples[512];
        for (int r = 0; r < reps; r++) {
          uint64_t t0 = now_ns(), v = 0;
          if (a == A_PARSE) {
            uint64_t chk;
            v = parse_only(parser, ps, &chk);
          } else if (a == A_PW || a == A_PWC) {
            wr->evlen = 0; wr->arlen = 0; wr->err = 0; wr->xj = 0;
            simdjson::ondemand::document doc;
            auto dr = parser.iterate(ps);
            if (auto e = std::move(dr).get(doc)) wr->err = 1;
            else write_doc(wr, doc);
            if (a == A_PWC) {
              C cc = consume(wr->ar, wr->arlen, wr->ev, wr->evlen);
              v = cc.sum ^ cc.tokens;
            } else v = wr->evlen;
          } else if (a == A_PS) {
            s.tokens = s.values = s.sum = 0; s.err = 0; s.evlen = 0; s.arlen = 0; s.xj = 0;
            simdjson::ondemand::document doc;
            auto dr = parser.iterate(ps);
            if (auto e = std::move(dr).get(doc)) s.err = 1;
            else write_doc(&s, doc);
            v = s.sum ^ s.tokens;
#if FAIR_NOEVENT
          } else if (a == A_RPN) {
            reset(&d);
            v = noevent_pipeline(&d);
            v ^= d.ns;
#endif
          } else {
            reset(&d);
            v = route_pipeline(&d);
            if (a == A_RPC) { C cc = consume(d.dst, ld(d.ndst), d.ev, ld(d.nev)); v ^= cc.sum; }
          }
          uint64_t t1 = now_ns();
          sink ^= v;
          samples[r] = t1 - t0;
        }
        med[a][t] = median_of(samples, reps);
        printf("ROW\t%s\t%" PRIu64 "\t%s\t%d\t%" PRIu64 "\n", d.name.c_str(),
               d.n, aname[a], t, med[a][t]);
      }
    }
  }
  fprintf(stderr, "fair: %d gate failures over %zu documents\n", gate_fail,
          paths.size());
  return gate_fail ? 1 : 0;
}
