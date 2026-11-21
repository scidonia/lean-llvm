/* workspace.cc -- the composed route's four intervals with a fresh workspace
   and with a reused one, on the three accepted 64 KiB documents, beside
   simdjson 5.0.5's full parse in the same process.

   The route's staging is `RouteMain.lean`'s `stage`: the window
   `[0,0,0] ++ doc ++ padding ++ 32` and the thirteen buffers the adapter's
   copies fill, every one a fresh allocation zeroed before the call, about
   1.44 MiB per repetition.  This harness runs the same four stages

     admission  the two-phase decision: the depth walk over the structural
                delimiter sequence, then the character-policy scan where the
                walk saw a candidate byte (`admission.h`)
     staging    the caller's window and the thirteen buffers in the record's
                shape
     native     the adapter's copy-in, `leanllvm_json_pipeline`, and the tagged
                result's copy-out
     consumer   `--consume`'s reading that materialises one record per event,
                with the header decode in the interval

   twice: `fresh` rebuilds the workspace for every call, as the route does,
   and `reused` keeps one allocation of the same capacities, resets the five
   cursor words, copies the document into the window, and copies the caller's
   buffers into the adapter's persistent copies.  Both arms call the same
   pipeline with the same arm word and both are checked against one reference
   observation per document before and after every timed act.

   The two arms' results must be identical to the byte: the tagged header
   words, the arena and event bytes, and the consumer's token count, value
   count and both checksums.  The reused arm alternates the three documents in
   a rotated order so a call sees the previous document's buffers, which is
   where a cursor that is not reset and a stale byte a consumer reads would
   show.  A `stale` row is the affirmative control: it reports transitions
   where the previous document left event bytes past the current one's `nev`,
   and the output is still the reference's.

   simdjson's arm is `tests/json-units-bench/simdjson-baseline.cc`'s `parse`:
   `iterate` plus the full value traversal over a `padded_string` staged before
   the clock.  `native` is divided by it inside one round, which is what
   `docs/json-pipeline-performance.md` calls the like-for-like full-parse pair.

   Exit status: 0 on a complete run with every gate held, 2 on a bad argument
   or unreadable document, 3 on a pre-clock or timed-act disagreement.

   Usage: workspace --doc <name>=<path> [--doc ...] [--refused <name>=<path>]
                    [--rounds N] [--reps N]
*/

#include "simdjson.h"

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

extern "C" {
#include "admission.h"
#include "entry.h"
#include "pipeline.h"
}

#define MAX_DOCS 16

static volatile uint64_t sink;

/* ---------------------------------------------------------------- time -- */
static uint64_t now_ns(void) {
  struct timespec t;
  if (clock_gettime(CLOCK_MONOTONIC_RAW, &t) != 0) {
    std::perror("clock_gettime");
    std::exit(2);
  }
  return (uint64_t)t.tv_sec * 1000000000ull + (uint64_t)t.tv_nsec;
}

/* --------------------------------------------------------------- stats -- */
static int cmp_u64(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return x < y ? -1 : x > y ? 1 : 0;
}

static uint64_t median_of(std::vector<uint64_t> &v) {
  std::qsort(v.data(), v.size(), sizeof(uint64_t), cmp_u64);
  return v[(v.size() - 1) / 2];
}

typedef struct {
  uint64_t median, min, max;
} summary;

static summary summarise(std::vector<uint64_t> v) {
  summary s;
  std::qsort(v.data(), v.size(), sizeof(uint64_t), cmp_u64);
  s.min = v.front();
  s.max = v.back();
  s.median = v[(v.size() - 1) / 2];
  return s;
}

static void store64(uint8_t *p, uint64_t v) {
  for (int i = 0; i < 8; i++) p[i] = (uint8_t)(v >> (8 * i));
}

static uint64_t load64(const uint8_t *p) {
  uint64_t v = 0;
  for (int i = 0; i < 8; i++) v |= (uint64_t)p[i] << (8 * i);
  return v;
}

/* --------------------------------------------------------------- corpus -- */
typedef struct {
  char name[64];
  const char *path;
  std::string bytes;
  uint64_t n;
  uint64_t blocks;
  uint64_t epcap, xpcap, dstcap, evcap;
  uint64_t winlen;
  /* The reference observation every act is checked against. */
  uint8_t *arena;
  uint8_t *events;
  uint64_t verdict, nk, nxp, ndst, nev, err;
  uint64_t tokens, values, foldsum, valuessum;
  int walked;
} doc_t;

static doc_t docs[MAX_DOCS];
static int ndocs;
static doc_t refused_docs[MAX_DOCS];
static int nrefused;

static void die(int code, const char *what) {
  std::fprintf(stderr, "workspace: %s\n", what);
  std::exit(code);
}

static void read_file(const char *path, std::string *out) {
  FILE *f = std::fopen(path, "rb");
  if (f == NULL) {
    std::fprintf(stderr, "workspace: %s: %s\n", path, std::strerror(errno));
    std::exit(2);
  }
  char buf[65536];
  size_t got;
  while ((got = std::fread(buf, 1, sizeof buf, f)) > 0) out->append(buf, got);
  if (std::ferror(f)) die(2, "short read");
  if (std::fclose(f) != 0) die(2, "close failed");
}

static void add_doc(doc_t *table, int *count, const char *spec) {
  if (*count >= MAX_DOCS) die(2, "too many documents");
  const char *eq = std::strchr(spec, '=');
  if (eq == NULL || eq == spec || eq[1] == '\0')
    die(2, "a document wants <name>=<path>");
  doc_t *d = &table[(*count)++];
  size_t len = (size_t)(eq - spec);
  if (len >= sizeof d->name) die(2, "document name too long");
  std::memcpy(d->name, spec, len);
  d->path = eq + 1;
}

/* ----------------------------------------------------------- the record -- */
/* The thirteen buffers the adapter copies, in `shim.c`'s order. */
enum { W_SC, W_MK, W_ENTW, W_EP, W_NK, W_XP, W_NXP, W_XCARRY,
       W_DST, W_NDST, W_EV, W_NEV, W_ERR, W_COUNT };

static void capacities(doc_t *d) {
  d->n = d->bytes.size();
  d->blocks = d->n / 64 + (d->n % 64 != 0);
  d->epcap = 64 * d->blocks + 9;
  d->xpcap = 64 * d->blocks + 8;
  d->dstcap = d->n + 64;
  d->evcap = 13 * d->n + 128;
  d->winlen = 3 + d->n + (64 * d->blocks - d->n) + 32;
}

struct Event {
  uint8_t tag;
  uint64_t len;
  uint64_t payload;
};

/* One workspace: the caller's record shape, the adapter's persistent copies,
   the class array the policy scan can reuse, and the consumer's record buffer. */
struct Workspace {
  uint8_t *win = nullptr;
  uint8_t *buf[W_COUNT] = {nullptr};
  uint64_t buflen[W_COUNT] = {0};
  uint8_t *cls = nullptr;
  uint64_t clscap = 0;
  uint8_t *copies[W_COUNT] = {nullptr};
  uint8_t *result = nullptr;
  uint64_t resultcap = 0;
  std::vector<Event> recs;
  uint64_t prev_nev = 0;
};

static uint64_t buf_len(uint64_t epcap, uint64_t xpcap, uint64_t dstcap,
                        uint64_t evcap, int i) {
  switch (i) {
  case W_SC: return 24;
  case W_MK: return 48;
  case W_ENTW: return 8;
  case W_EP: return 4 * epcap;
  case W_NK: return 8;
  case W_XP: return 4 * xpcap;
  case W_NXP: return 8;
  case W_XCARRY: return 16;
  case W_DST: return dstcap;
  case W_NDST: return 8;
  case W_EV: return evcap;
  case W_NEV: return 8;
  case W_ERR: return 8;
  default: return 0;
  }
}

static void *xmalloc(size_t n) {
  void *p = std::malloc(n ? n : 1);
  if (p == nullptr) die(3, "allocation failed");
  return p;
}

static uint64_t *nk_of(Workspace *w) { return (uint64_t *)w->buf[W_NK]; }
static uint64_t *nxp_of(Workspace *w) { return (uint64_t *)w->buf[W_NXP]; }
static uint64_t *ndst_of(Workspace *w) { return (uint64_t *)w->buf[W_NDST]; }
static uint64_t *nev_of(Workspace *w) { return (uint64_t *)w->buf[W_NEV]; }
static uint64_t *err_of(Workspace *w) { return (uint64_t *)w->buf[W_ERR]; }

/* ------------------------------------------------------------- the acts -- */

/* admission: both phases, with the workspace's class array where there is one. */
static void act_admission(const doc_t *d, uint8_t *ws, uint64_t cap,
                          admit_facts *out) {
  admit_decide((const uint8_t *)d->bytes.data(), d->n, 1ull << 20, 128, ws,
               cap, out);
}

/* staging, fresh: the window and the thirteen buffers allocated and zeroed. */
static void act_stage_fresh(Workspace *w, const doc_t *d) {
  w->win = (uint8_t *)xmalloc(d->winlen);
  std::memset(w->win, 0, d->winlen);
  std::memcpy(w->win + 3, d->bytes.data(), d->n);
  for (int i = 0; i < W_COUNT; i++) {
    w->buflen[i] = buf_len(d->epcap, d->xpcap, d->dstcap, d->evcap, i);
    w->buf[i] = (uint8_t *)xmalloc(w->buflen[i]);
    std::memset(w->buf[i], 0, w->buflen[i]);
  }
}

/* staging, reused: the same bytes, with the five cursor words reset and the
   document copied into the window the previous call left.  Nothing else in the
   buffers is rewritten, so a stage that reads a stale byte is caught by the
   output check rather than hidden by a zero fill. */
static void act_stage_reused(Workspace *w, const doc_t *d) {
  std::memcpy(w->win + 3, d->bytes.data(), d->n);
  *nk_of(w) = 0;
  *nxp_of(w) = 0;
  *ndst_of(w) = 0;
  *nev_of(w) = 0;
  *err_of(w) = 0;
  /* The two carries the mask unit and the escape list read before they write:
     the pipeline has no initialising store of them, so the caller owns them. */
  std::memset(w->buf[W_SC], 0, 24);
  std::memset(w->buf[W_XCARRY], 0, 16);
}

/* native, fresh: the adapter's copies allocated and filled, the pipeline, and
   the tagged result allocated and filled. */
static void act_native_fresh(Workspace *w, const doc_t *d, uint64_t arm) {
  for (int i = 0; i < W_COUNT; i++) {
    w->copies[i] = (uint8_t *)xmalloc(w->buflen[i]);
    std::memcpy(w->copies[i], w->buf[i], w->buflen[i]);
  }
  uint64_t verdict = leanllvm_json_pipeline(
      (const uint8_t *)w->win + 3, d->n,
      (uint64_t *)w->copies[W_SC], (uint64_t *)w->copies[W_MK],
      (uint64_t *)w->copies[W_ENTW], (uint32_t *)w->copies[W_EP], d->epcap,
      (uint64_t *)w->copies[W_NK], (uint32_t *)w->copies[W_XP], d->xpcap,
      (uint64_t *)w->copies[W_NXP], (uint64_t *)w->copies[W_XCARRY],
      w->copies[W_DST], d->dstcap, (uint64_t *)w->copies[W_NDST],
      w->copies[W_EV], d->evcap, (uint64_t *)w->copies[W_NEV],
      (uint64_t *)w->copies[W_ERR], arm);
  uint64_t nd = *(uint64_t *)w->copies[W_NDST];
  uint64_t ne = *(uint64_t *)w->copies[W_NEV];
  uint64_t total = 80 + nd + ne;
  w->resultcap = total;
  w->result = (uint8_t *)xmalloc(total);
  store64(w->result + 0, verdict == 1 ? 0 : 1);
  store64(w->result + 8, 0);
  store64(w->result + 16, 0);
  store64(w->result + 24, 0);
  uint64_t obs[6] = {verdict, *(uint64_t *)w->copies[W_NK],
                     *(uint64_t *)w->copies[W_NXP], nd, ne,
                     *(uint64_t *)w->copies[W_ERR]};
  for (int i = 0; i < 6; i++) store64(w->result + 32 + 8 * (size_t)i, obs[i]);
  std::memcpy(w->result + 80, w->copies[W_DST], nd);
  std::memcpy(w->result + 80 + nd, w->copies[W_EV], ne);
  for (int i = 0; i < W_COUNT; i++) {
    std::free(w->copies[i]);
    w->copies[i] = nullptr;
  }
}

/* native, reused: the caller's own buffers are the ones the object writes, so
   the adapter's protective copy has no work to do and the workspace carries
   the previous document's bytes.  Only the tagged result is still built, in
   the persistent result buffer, because that is what the consumer reads. */
static void act_native_reused(Workspace *w, const doc_t *d, uint64_t arm) {
  uint64_t verdict = leanllvm_json_pipeline(
      (const uint8_t *)w->win + 3, d->n,
      (uint64_t *)w->buf[W_SC], (uint64_t *)w->buf[W_MK],
      (uint64_t *)w->buf[W_ENTW], (uint32_t *)w->buf[W_EP], d->epcap,
      (uint64_t *)w->buf[W_NK], (uint32_t *)w->buf[W_XP], d->xpcap,
      (uint64_t *)w->buf[W_NXP], (uint64_t *)w->buf[W_XCARRY],
      w->buf[W_DST], d->dstcap, (uint64_t *)w->buf[W_NDST],
      w->buf[W_EV], d->evcap, (uint64_t *)w->buf[W_NEV],
      (uint64_t *)w->buf[W_ERR], arm);
  uint64_t nd = *(uint64_t *)w->buf[W_NDST];
  uint64_t ne = *(uint64_t *)w->buf[W_NEV];
  uint64_t total = 80 + nd + ne;
  if (total > w->resultcap) {
    std::free(w->result);
    w->resultcap = total;
    w->result = (uint8_t *)xmalloc(total);
  }
  store64(w->result + 0, verdict == 1 ? 0 : 1);
  store64(w->result + 8, 0);
  store64(w->result + 16, 0);
  store64(w->result + 24, 0);
  uint64_t obs[6] = {verdict, *(uint64_t *)w->buf[W_NK],
                     *(uint64_t *)w->buf[W_NXP], nd, ne,
                     *(uint64_t *)w->buf[W_ERR]};
  for (int i = 0; i < 6; i++) store64(w->result + 32 + 8 * (size_t)i, obs[i]);
  std::memcpy(w->result + 80, w->buf[W_DST], nd);
  std::memcpy(w->result + 80 + nd, w->buf[W_EV], ne);
}

/* Release a fresh act's allocations; a reused workspace is built once and
   released by the caller. */
static void ws_free_buffers(Workspace *w) {
  std::free(w->win);
  w->win = nullptr;
  for (int i = 0; i < W_COUNT; i++) {
    std::free(w->buf[i]);
    w->buf[i] = nullptr;
    std::free(w->copies[i]);
    w->copies[i] = nullptr;
  }
  std::free(w->result);
  w->result = nullptr;
}

/* The consumer's reading, `RouteMain.lean`'s `consumeResult` with the header
   decode inside the interval: `build` materialises one record per event,
   without it the same fields are folded and no record object exists. */
struct Consumed {
  uint64_t tokens = 0, events = 0, arena = 0, sum = 0, values = 0;
  int walked = 0;
};

static uint64_t event_width(uint8_t tag) {
  if (tag == 5 || tag == 6) return 13;
  if (tag == 7) return 9;
  return 1;
}

static Consumed consume(const uint8_t *result, uint64_t result_size, int build,
                        int reuse, Workspace *w, int *ok) {
  Consumed c;
  *ok = 0;
  if (result_size < 80) return c;
  uint64_t tag = load64(result + 0);
  if (tag != 0 && tag != 1) return c;
  uint64_t ndst = load64(result + 56);
  uint64_t nev = load64(result + 64);
  if (result_size != 80 + ndst + nev) return c;
  /* A fresh reading constructs its record vector here, so the growth its
     pushes pay is inside the interval; a reused reading keeps the capacity. */
  std::vector<Event> local;
  std::vector<Event> *recs = &local;
  if (reuse) {
    w->recs.clear();
    recs = &w->recs;
  }
  uint64_t arena = 0;
  for (uint64_t k = 0; k < ndst; k++) arena += result[80 + k];
  c.arena = ndst;
  uint64_t sum = arena;
  uint64_t k = 0, tokens = 0;
  while (k < nev) {
    uint8_t t = result[80 + ndst + k];
    uint64_t width = event_width(t);
    if (k + width > nev) {
      c.tokens = tokens;
      c.events = k;
      c.sum = sum;
      c.walked = 0;
      c.values = (uint64_t)recs->size();
      *ok = 1;
      return c;
    }
    const uint8_t *base = result + 80 + ndst + k;
    uint64_t len = width == 13 ? (uint64_t)(base[1] | (base[2] << 8) |
                                            (base[3] << 16) | (base[4] << 24))
                               : 0;
    uint64_t payload = 0;
    if (width == 13) payload = load64(base + 5);
    else if (width == 9) payload = load64(base + 1);
    sum += (uint64_t)t + len + payload;
    if (build) recs->push_back(Event{t, len, payload});
    k += width;
    tokens++;
  }
  c.tokens = tokens;
  c.events = k;
  c.sum = sum;
  c.walked = 1;
  c.values = (uint64_t)recs->size();
  *ok = 1;
  return c;
}

static uint64_t result_size_of(const Workspace *w) {
  return 80 + load64(w->result + 56) + load64(w->result + 64);
}

/* --------------------------------------------------------------- checks -- */
static int failures;

/* Compare one act against the document's reference observation. */
static void check_act(const doc_t *d, Workspace *w, const char *arm) {
  const uint8_t *r = w->result;
  uint64_t verdict = load64(r + 32), nk = load64(r + 40), nxp = load64(r + 48);
  uint64_t ndst = load64(r + 56), nev = load64(r + 64), err = load64(r + 72);
  if (verdict != d->verdict || nk != d->nk || nxp != d->nxp ||
      ndst != d->ndst || nev != d->nev || err != d->err) {
    std::fprintf(stderr,
                 "FAIL: %s/%s header verdict=%" PRIu64 " nk=%" PRIu64
                 " nxp=%" PRIu64 " ndst=%" PRIu64 " nev=%" PRIu64
                 " err=%" PRIu64 " (expected %" PRIu64 " %" PRIu64 " %" PRIu64
                 " %" PRIu64 " %" PRIu64 " %" PRIu64 ")\n",
                 d->name, arm, verdict, nk, nxp, ndst, nev, err, d->verdict,
                 d->nk, d->nxp, d->ndst, d->nev, d->err);
    failures++;
    return;
  }
  if (std::memcmp(r + 80, d->arena, d->ndst) != 0) {
    std::fprintf(stderr, "FAIL: %s/%s arena bytes\n", d->name, arm);
    failures++;
    return;
  }
  if (std::memcmp(r + 80 + d->ndst, d->events, d->nev) != 0) {
    std::fprintf(stderr, "FAIL: %s/%s event bytes\n", d->name, arm);
    failures++;
    return;
  }
  int ok = 0;
  uint64_t size = result_size_of(w);
  Consumed fold = consume(r, size, 0, 1, w, &ok);
  if (!ok) { std::fprintf(stderr, "FAIL: %s/%s fold\n", d->name, arm);
             failures++; return; }
  Consumed built = consume(r, size, 1, 1, w, &ok);
  if (!ok) { std::fprintf(stderr, "FAIL: %s/%s values\n", d->name, arm);
             failures++; return; }
  if (fold.tokens != d->tokens || built.values != d->values ||
      fold.sum != d->foldsum || built.sum != d->valuessum ||
      fold.walked != d->walked || built.walked != d->walked) {
    std::fprintf(stderr,
                 "FAIL: %s/%s consumer tokens=%" PRIu64 "/%" PRIu64
                 " values=%" PRIu64 "/%" PRIu64 " sums=%016" PRIx64
                 "/%016" PRIx64 " walked=%d/%d\n",
                 d->name, arm, fold.tokens, d->tokens, built.values, d->values,
                 fold.sum, d->foldsum, fold.walked, built.walked);
    failures++;
  }
  sink ^= fold.sum ^ built.sum ^ fold.tokens;
}

/* The affirmative control: the bytes past the current `nev` the previous
   document left in the event buffer, and whether any of them is nonzero. */
static uint64_t stale_tail(const Workspace *w, uint64_t nev, int *nonzero) {
  uint64_t n = w->prev_nev > nev ? w->prev_nev - nev : 0;
  *nonzero = 0;
  for (uint64_t i = 0; i < n; i++)
    if (w->buf[W_EV][nev + i] != 0) *nonzero = 1;
  return n;
}

/* ------------------------------------------------------------- one arm -- */
typedef struct {
  uint64_t admission, staging, native, consumer;
} intervals;

/* One fresh act.  The workspace is built and torn down on every call, which is
   the fresh discipline; the admission uses the scan's own allocation. */
static intervals run_fresh(const doc_t *d, Workspace *w) {
  intervals t;
  *w = Workspace();
  w->recs.reserve(4096);
  admit_facts f;

  uint64_t a0 = now_ns();
  act_admission(d, nullptr, 0, &f);
  uint64_t a1 = now_ns();

  uint64_t s0 = now_ns();
  act_stage_fresh(w, d);
  uint64_t s1 = now_ns();

  uint64_t n0 = now_ns();
  act_native_fresh(w, d, 0);
  uint64_t n1 = now_ns();

  uint64_t size = result_size_of(w);
  uint64_t c0 = now_ns();
  int ok = 0;
  consume(w->result, size, 1, 0, w, &ok);
  uint64_t c1 = now_ns();
  if (!ok) { std::fprintf(stderr, "FAIL: %s/fresh consumer\n", d->name);
             failures++; }

  t.admission = a1 - a0;
  t.staging = s1 - s0;
  t.native = n1 - n0;
  t.consumer = c1 - c0;

  check_act(d, w, "fresh");
  if (f.policy_class == UINT64_MAX) {
    std::fprintf(stderr, "FAIL: %s/fresh policy allocation\n", d->name);
    failures++;
  }
  ws_free_buffers(w);
  return t;
}

/* One reused act against a workspace built once.  The document is copied into
   the window, the cursor words are reset, and the adapter's copies are
   refilled; nothing is allocated. */
static intervals run_reused(const doc_t *d, Workspace *w, uint64_t *stale_bytes,
                            int *stale_nonzero) {
  intervals t;
  admit_facts f;

  uint64_t a0 = now_ns();
  act_admission(d, w->cls, w->clscap, &f);
  uint64_t a1 = now_ns();

  uint64_t s0 = now_ns();
  act_stage_reused(w, d);
  uint64_t s1 = now_ns();

  uint64_t n0 = now_ns();
  act_native_reused(w, d, 0);
  uint64_t n1 = now_ns();

  uint64_t size = result_size_of(w);
  uint64_t c0 = now_ns();
  int ok = 0;
  consume(w->result, size, 1, 1, w, &ok);
  uint64_t c1 = now_ns();
  if (!ok) { std::fprintf(stderr, "FAIL: %s/reused consumer\n", d->name);
             failures++; }

  t.admission = a1 - a0;
  t.staging = s1 - s0;
  t.native = n1 - n0;
  t.consumer = c1 - c0;

  *stale_bytes = stale_tail(w, d->nev, stale_nonzero);
  check_act(d, w, "reused");
  if (f.policy_class == UINT64_MAX) {
    std::fprintf(stderr, "FAIL: %s/reused policy allocation\n", d->name);
    failures++;
  }
  w->prev_nev = d->nev;
  return t;
}

/* ------------------------------------------------------------ simdjson -- */
typedef struct {
  simdjson::error_code err;
  uint64_t walked;
  uint64_t checksum;
} parse_result;

static simdjson::error_code g_err = simdjson::SUCCESS;

static uint64_t mix(uint64_t h, uint64_t v) {
  return (h ^ v) * 0x100000001B3ull;
}

static void set_err(simdjson::error_code e) {
  if (g_err == simdjson::SUCCESS) g_err = e;
}

/* `tests/json-units-bench/simdjson-baseline.cc`'s traversal, unchanged in
   shape: every value visited, every string fetched, every number converted. */
static uint64_t od_count_value(simdjson::ondemand::value &v) {
  using namespace simdjson;
  if (g_err != SUCCESS) return 0;
  ondemand::json_type t;
  if (auto e = v.type().get(t)) { set_err(e); return 0; }
  switch (t) {
  case ondemand::json_type::null: return 1;
  case ondemand::json_type::boolean: {
    bool b;
    if (auto e = v.get_bool().get(b)) { set_err(e); return 0; }
    return 1 + (uint64_t)b;
  }
  case ondemand::json_type::number: {
    double d;
    if (auto e = v.get_double().get(d)) { set_err(e); return 0; }
    if (!(d == d) || d >= 9.0e18 || d <= -9.0e18) return 1;
    return 1 + (uint64_t)(int64_t)d;
  }
  case ondemand::json_type::string: {
    std::string_view s;
    if (auto e = v.get_string().get(s)) { set_err(e); return 0; }
    return 1 + s.size();
  }
  case ondemand::json_type::array: {
    ondemand::array arr;
    if (auto e = v.get_array().get(arr)) { set_err(e); return 0; }
    uint64_t n = 0;
    for (auto x : arr) {
      ondemand::value xv;
      if (auto e = x.get(xv)) { set_err(e); break; }
      n += od_count_value(xv);
      if (g_err != SUCCESS) break;
    }
    return n + 1;
  }
  case ondemand::json_type::object: {
    ondemand::object obj;
    if (auto e = v.get_object().get(obj)) { set_err(e); return 0; }
    uint64_t n = 0;
    for (auto &&f : obj) {
      std::string_view k;
      auto kr = f.unescaped_key();
      if (auto e = std::move(kr).get(k)) { set_err(e); break; }
      n += k.size();
      auto vr = f.value();
      ondemand::value fv;
      if (auto e = std::move(vr).get(fv)) { set_err(e); break; }
      n += od_count_value(fv);
      if (g_err != SUCCESS) break;
    }
    return n + 1;
  }
  case ondemand::json_type::unknown: return 0;
  }
  return 0;
}

static parse_result parse_act(simdjson::ondemand::parser &parser,
                              const simdjson::padded_string &ps) {
  parse_result r;
  r.err = simdjson::SUCCESS;
  r.walked = 0;
  simdjson::ondemand::document doc;
  auto dr = parser.iterate(ps);
  if (auto e = std::move(dr).get(doc)) {
    r.err = e;
  } else {
    simdjson::ondemand::value v;
    auto vr = doc.get_value();
    if (auto e = vr.get(v)) {
      r.err = e;
    } else {
      g_err = simdjson::SUCCESS;
      r.walked = od_count_value(v);
      r.err = g_err;
    }
  }
  r.checksum = mix(0x84222325CBF29CE4ull, (uint64_t)r.err);
  r.checksum = mix(r.checksum, r.walked);
  return r;
}

/* --------------------------------------------------------------- output -- */
static void print_abs(const char *name, const char *arm, const summary s[4]) {
  std::printf("%-20s %-8s %7" PRIu64 " (%6" PRIu64 "-%" PRIu64
              ") %7" PRIu64 " (%6" PRIu64 "-%" PRIu64
              ") %7" PRIu64 " (%6" PRIu64 "-%" PRIu64
              ") %7" PRIu64 " (%6" PRIu64 "-%" PRIu64 ")\n",
              name, arm, s[0].median, s[0].min, s[0].max, s[1].median,
              s[1].min, s[1].max, s[2].median, s[2].min, s[2].max, s[3].median,
              s[3].min, s[3].max);
}

int main(int argc, char **argv) {
  int rounds = 15, reps = 21;
  for (int i = 1; i < argc; i++) {
    if (!std::strcmp(argv[i], "--doc") && i + 1 < argc) {
      add_doc(docs, &ndocs, argv[++i]);
    } else if (!std::strcmp(argv[i], "--refused") && i + 1 < argc) {
      add_doc(refused_docs, &nrefused, argv[++i]);
    } else if (!std::strcmp(argv[i], "--rounds") && i + 1 < argc) {
      rounds = std::atoi(argv[++i]);
      if (rounds < 3 || rounds > 201) die(2, "rounds out of range");
    } else if (!std::strcmp(argv[i], "--reps") && i + 1 < argc) {
      reps = std::atoi(argv[++i]);
      if (reps < 3 || reps > 10001) die(2, "reps out of range");
    } else {
      std::fprintf(stderr, "workspace: bad argument %s\n", argv[i]);
      return 2;
    }
  }
  if (ndocs != 3)
    die(2, "the measured set is the three accepted 64 KiB documents");

  if (std::strcmp(SIMDJSON_VERSION, "5.0.5") != 0) {
    std::fprintf(stderr, "workspace: header is simdjson %s, not 5.0.5\n",
                 SIMDJSON_VERSION);
    return 2;
  }
  std::string impl(simdjson::get_active_implementation()->name());

  /* The entry unit's static table, as the adapter's `route_init` fills it. */
  static uint32_t entry_table_slot[256 * 8];
  leanllvm_json_entry_table(entry_table_slot);

  for (int i = 0; i < ndocs; i++) {
    doc_t *d = &docs[i];
    read_file(d->path, &d->bytes);
    if (d->bytes.empty()) die(2, "empty document");
    capacities(d);
    if (d->n != 65536) die(2, "the measured documents are 65,536 bytes");
  }
  for (int i = 0; i < nrefused; i++) {
    doc_t *d = &refused_docs[i];
    read_file(d->path, &d->bytes);
    capacities(d);
  }

  std::printf("instrument workspace=1 simdjson=%s implementation=%s"
              " rounds=%d reps=%d\n", SIMDJSON_VERSION, impl.c_str(), rounds,
              reps);
  std::printf("compiler: %s\n", __VERSION__);

  /* --- the reference observation ---------------------------------------- */
  for (int i = 0; i < ndocs; i++) {
    doc_t *d = &docs[i];
    Workspace w;
    // the local Workspace is default-initialised
    w.recs.reserve(4096);
    admit_facts f;
    act_admission(d, nullptr, 0, &f);
    act_stage_fresh(&w, d);
    act_native_fresh(&w, d, 0);
    d->verdict = load64(w.result + 32);
    d->nk = load64(w.result + 40);
    d->nxp = load64(w.result + 48);
    d->ndst = load64(w.result + 56);
    d->nev = load64(w.result + 64);
    d->err = load64(w.result + 72);
    d->arena = (uint8_t *)xmalloc(d->ndst ? d->ndst : 1);
    d->events = (uint8_t *)xmalloc(d->nev ? d->nev : 1);
    std::memcpy(d->arena, w.result + 80, d->ndst);
    std::memcpy(d->events, w.result + 80 + d->ndst, d->nev);
    int ok = 0;
    uint64_t size = result_size_of(&w);
    Consumed fold = consume(w.result, size, 0, 1, &w, &ok);
    Consumed built = consume(w.result, size, 1, 1, &w, &ok);
    d->tokens = fold.tokens;
    d->values = built.values;
    d->foldsum = fold.sum;
    d->valuessum = built.sum;
    d->walked = fold.walked && built.walked;
    ws_free_buffers(&w);
    std::printf("reference doc=%s size=%" PRIu64 " verdict=%" PRIu64
                " nk=%" PRIu64 " nxp=%" PRIu64 " ndst=%" PRIu64
                " nev=%" PRIu64 " err=%" PRIu64 " tokens=%" PRIu64
                " values=%" PRIu64 " foldsum=%" PRIu64 " valuessum=%" PRIu64
                " walked=%d\n",
                d->name, d->n, d->verdict, d->nk, d->nxp, d->ndst, d->nev,
                d->err, d->tokens, d->values, d->foldsum, d->valuessum,
                d->walked);
  }

  /* --- the refusal control --------------------------------------------- */
  for (int i = 0; i < nrefused; i++) {
    doc_t *d = &refused_docs[i];
    Workspace w;
    // the local Workspace is default-initialised
    w.recs.reserve(4096);
    admit_facts f;
    act_admission(d, nullptr, 0, &f);
    act_stage_fresh(&w, d);
    act_native_fresh(&w, d, 0);
    d->verdict = load64(w.result + 32);
    d->nk = load64(w.result + 40);
    d->nxp = load64(w.result + 48);
    d->ndst = load64(w.result + 56);
    d->nev = load64(w.result + 64);
    d->err = load64(w.result + 72);
    d->arena = (uint8_t *)xmalloc(d->ndst ? d->ndst : 1);
    d->events = (uint8_t *)xmalloc(d->nev ? d->nev : 1);
    std::memcpy(d->arena, w.result + 80, d->ndst);
    std::memcpy(d->events, w.result + 80 + d->ndst, d->nev);
    int ok = 0;
    uint64_t size = result_size_of(&w);
    Consumed fold = consume(w.result, size, 0, 1, &w, &ok);
    Consumed built = consume(w.result, size, 1, 1, &w, &ok);
    d->tokens = fold.tokens;
    d->values = built.values;
    d->foldsum = fold.sum;
    d->valuessum = built.sum;
    d->walked = fold.walked && built.walked;
    ws_free_buffers(&w);
    std::printf("refusal-reference doc=%s verdict=%" PRIu64 " nk=%" PRIu64
                " nxp=%" PRIu64 " ndst=%" PRIu64 " nev=%" PRIu64
                " err=%" PRIu64 "\n",
                d->name, d->verdict, d->nk, d->nxp, d->ndst, d->nev, d->err);
  }

  /* --- the reused workspace, built once --------------------------------- */
  Workspace reuse;
  // the reused Workspace is default-initialised
  {
    const doc_t *first = &docs[0];
    reuse.win = (uint8_t *)xmalloc(first->winlen);
    std::memset(reuse.win, 0, first->winlen);
    for (int i = 0; i < W_COUNT; i++) {
      reuse.buflen[i] =
          buf_len(first->epcap, first->xpcap, first->dstcap, first->evcap, i);
      reuse.buf[i] = (uint8_t *)xmalloc(reuse.buflen[i]);
      std::memset(reuse.buf[i], 0, reuse.buflen[i]);
      reuse.copies[i] = (uint8_t *)xmalloc(reuse.buflen[i]);
    }
    reuse.clscap = first->n + 1;
    reuse.cls = (uint8_t *)xmalloc(reuse.clscap);
    reuse.resultcap = 80 + first->dstcap + first->evcap;
    reuse.result = (uint8_t *)xmalloc(reuse.resultcap);
    reuse.recs.reserve(4096);
    reuse.prev_nev = 0;
  }

  uint64_t stale_total = 0, stale_nonzero_total = 0;
  /* The warm-up and the gate: every document through both arms, with the reused
     arm's documents rotated so each follows a different one. */
  for (int i = 0; i < ndocs; i++) {
    Workspace w;
    intervals t = run_fresh(&docs[i], &w);
    sink ^= t.admission ^ t.staging ^ t.native ^ t.consumer;
  }
  for (int i = 0; i < 2 * ndocs; i++) {
    uint64_t sb = 0;
    int snz = 0;
    run_reused(&docs[i % ndocs], &reuse, &sb, &snz);
    stale_total += sb;
    stale_nonzero_total += (uint64_t)snz;
  }
  if (failures != 0) die(3, "a pre-clock act disagreed with the reference");

  /* --- simdjson, staged before every clock ------------------------------ */
  std::vector<simdjson::padded_string> ps;
  ps.reserve(ndocs);
  std::vector<simdjson::ondemand::parser> parsers;
  parsers.reserve((size_t)ndocs);
  std::vector<parse_result> parse_ref;
  for (int i = 0; i < ndocs; i++) {
    ps.emplace_back(docs[i].bytes.data(), docs[i].bytes.size());
    parsers.emplace_back();
    if (auto e = parsers[i].allocate(ps[i].size())) {
      std::fprintf(stderr, "workspace: %s: parser allocate: %s\n",
                   docs[i].name, simdjson::error_message(e));
      return 3;
    }
    parse_result r = parse_act(parsers[i], ps[i]);
    if (r.err != simdjson::SUCCESS)
      die(3, "simdjson refuses a document the route accepts");
    parse_ref.push_back(r);
    sink ^= r.checksum;
  }

  /* --- the timed rounds -------------------------------------------------- */
  std::vector<std::vector<uint64_t>> f_ad(ndocs, std::vector<uint64_t>(rounds));
  std::vector<std::vector<uint64_t>> f_st(ndocs, std::vector<uint64_t>(rounds));
  std::vector<std::vector<uint64_t>> f_na(ndocs, std::vector<uint64_t>(rounds));
  std::vector<std::vector<uint64_t>> f_co(ndocs, std::vector<uint64_t>(rounds));
  std::vector<std::vector<uint64_t>> r_ad(ndocs, std::vector<uint64_t>(rounds));
  std::vector<std::vector<uint64_t>> r_st(ndocs, std::vector<uint64_t>(rounds));
  std::vector<std::vector<uint64_t>> r_na(ndocs, std::vector<uint64_t>(rounds));
  std::vector<std::vector<uint64_t>> r_co(ndocs, std::vector<uint64_t>(rounds));
  std::vector<std::vector<uint64_t>> s_ns(ndocs, std::vector<uint64_t>(rounds));

  for (int round = 0; round < rounds; round++) {
    bool fresh_first = (round % 2 == 0);
    std::vector<std::vector<uint64_t>> fa(ndocs), fs(ndocs), fna(ndocs),
        fco(ndocs), ra(ndocs), rs(ndocs), rna(ndocs), rco(ndocs);
    for (int i = 0; i < ndocs; i++) {
      fa[i].reserve(reps); fs[i].reserve(reps); fna[i].reserve(reps);
      fco[i].reserve(reps); ra[i].reserve(reps); rs[i].reserve(reps);
      rna[i].reserve(reps); rco[i].reserve(reps);
    }
    /* The reused arm's documents alternate inside the round, so each call
       inherits the previous document's buffers. */
    for (int rep = 0; rep < reps; rep++) {
      for (int k = 0; k < ndocs; k++) {
        int i = (k + round + rep) % ndocs;
        doc_t *d = &docs[i];
        Workspace w;
        intervals t;
        if (fresh_first) {
          t = run_fresh(d, &w);
          fa[i].push_back(t.admission); fs[i].push_back(t.staging);
          fna[i].push_back(t.native); fco[i].push_back(t.consumer);
          uint64_t sb = 0;
          int snz = 0;
          t = run_reused(d, &reuse, &sb, &snz);
          ra[i].push_back(t.admission); rs[i].push_back(t.staging);
          rna[i].push_back(t.native); rco[i].push_back(t.consumer);
          stale_total += sb;
          stale_nonzero_total += (uint64_t)snz;
        } else {
          uint64_t sb = 0;
          int snz = 0;
          t = run_reused(d, &reuse, &sb, &snz);
          ra[i].push_back(t.admission); rs[i].push_back(t.staging);
          rna[i].push_back(t.native); rco[i].push_back(t.consumer);
          stale_total += sb;
          stale_nonzero_total += (uint64_t)snz;
          t = run_fresh(d, &w);
          fa[i].push_back(t.admission); fs[i].push_back(t.staging);
          fna[i].push_back(t.native); fco[i].push_back(t.consumer);
        }
        if (failures != 0) die(3, "a timed act disagreed with the reference");
      }
    }
    for (int i = 0; i < ndocs; i++) {
      f_ad[i][round] = median_of(fa[i]);
      f_st[i][round] = median_of(fs[i]);
      f_na[i][round] = median_of(fna[i]);
      f_co[i][round] = median_of(fco[i]);
      r_ad[i][round] = median_of(ra[i]);
      r_st[i][round] = median_of(rs[i]);
      r_na[i][round] = median_of(rna[i]);
      r_co[i][round] = median_of(rco[i]);

      std::vector<uint64_t> p;
      p.reserve(reps);
      for (int rep = 0; rep < reps; rep++) {
        parse_result last;
        uint64_t t0 = now_ns();
        last = parse_act(parsers[i], ps[i]);
        uint64_t t1 = now_ns();
        p.push_back(t1 - t0);
        if (last.checksum != parse_ref[i].checksum) {
          std::fprintf(stderr, "FAIL: %s/simdjson parse checksum moved\n",
                       docs[i].name);
          failures++;
          break;
        }
      }
      s_ns[i][round] = median_of(p);
      std::printf("round=%d doc=%s fresh_first=%d admission=%" PRIu64
                  " staging=%" PRIu64 " native=%" PRIu64 " consumer=%" PRIu64
                  " reused_admission=%" PRIu64 " reused_staging=%" PRIu64
                  " reused_native=%" PRIu64 " reused_consumer=%" PRIu64
                  " simdjson_parse=%" PRIu64 "\n",
                  round, docs[i].name, (int)fresh_first, f_ad[i][round],
                  f_st[i][round], f_na[i][round], f_co[i][round],
                  r_ad[i][round], r_st[i][round], r_na[i][round],
                  r_co[i][round], s_ns[i][round]);
    }
  }
  if (failures != 0) die(3, "a gate failed during the timed rounds");

  /* --- reduction --------------------------------------------------------- */
  std::printf("\n## absolute, unit ns (median of the round medians; min-max of "
              "those)\n");
  std::printf("%-20s %-8s %18s %18s %18s %18s\n", "document", "arm",
              "admission", "staging", "native", "consumer");
  for (int i = 0; i < ndocs; i++) {
    summary s[4];
    const doc_t *d = &docs[i];
    s[0] = summarise(f_ad[i]);
    s[1] = summarise(f_st[i]);
    s[2] = summarise(f_na[i]);
    s[3] = summarise(f_co[i]);
    print_abs(d->name, "fresh", s);
    s[0] = summarise(r_ad[i]);
    s[1] = summarise(r_st[i]);
    s[2] = summarise(r_na[i]);
    s[3] = summarise(r_co[i]);
    print_abs("", "reused", s);
  }

  std::printf("\n## the paired ratios (unit: multiplier; per-round quotients, "
              "median with min-max)\n");
  std::printf("reused/fresh above 1 means the reused workspace costs more; "
              "native/parse divides the route's native interval by simdjson's "
              "full parse in the same round.\n");
  std::printf("%-20s %19s %19s %19s %19s %21s %21s\n", "document",
              "admission", "staging", "native", "consumer",
              "fresh native/parse", "reused native/parse");
  for (int i = 0; i < ndocs; i++) {
    std::vector<uint64_t> qa, qs, qn, qc, qfp, qrp;
    for (int r = 0; r < rounds; r++) {
      qa.push_back(f_ad[i][r] ? r_ad[i][r] * 10000 / f_ad[i][r] : 0);
      qs.push_back(f_st[i][r] ? r_st[i][r] * 10000 / f_st[i][r] : 0);
      qn.push_back(f_na[i][r] ? r_na[i][r] * 10000 / f_na[i][r] : 0);
      qc.push_back(f_co[i][r] ? r_co[i][r] * 10000 / f_co[i][r] : 0);
      qfp.push_back(s_ns[i][r] ? f_na[i][r] * 10000 / s_ns[i][r] : 0);
      qrp.push_back(s_ns[i][r] ? r_na[i][r] * 10000 / s_ns[i][r] : 0);
    }
    summary sa = summarise(qa), ss = summarise(qs), sn = summarise(qn);
    summary sc = summarise(qc), sfp = summarise(qfp), srp = summarise(qrp);
    std::printf("%-20s %6.3f (%6.3f-%6.3f) %6.3f (%6.3f-%6.3f)"
                " %6.3f (%6.3f-%6.3f) %6.3f (%6.3f-%6.3f)"
                " %7.3f (%7.3f-%7.3f) %7.3f (%7.3f-%7.3f)\n",
                docs[i].name, sa.median / 10000.0, sa.min / 10000.0,
                sa.max / 10000.0, ss.median / 10000.0, ss.min / 10000.0,
                ss.max / 10000.0, sn.median / 10000.0, sn.min / 10000.0,
                sn.max / 10000.0, sc.median / 10000.0, sc.min / 10000.0,
                sc.max / 10000.0, sfp.median / 10000.0, sfp.min / 10000.0,
                sfp.max / 10000.0, srp.median / 10000.0, srp.min / 10000.0,
                srp.max / 10000.0);
  }

  std::printf("\n## simdjson's full parse (unit ns; median of the round "
              "medians, min-max)\n");
  for (int i = 0; i < ndocs; i++) {
    summary s = summarise(s_ns[i]);
    std::printf("doc=%s parse=%" PRIu64 " (%" PRIu64 "-%" PRIu64 ")"
                " walked=%" PRIu64 "\n",
                docs[i].name, s.median, s.min, s.max, parse_ref[i].walked);
  }

  std::printf("\n## the stale-tail control\n");
  std::printf("stale_bytes=%" PRIu64 " transitions_with_nonzero_stale=%" PRIu64
              "\n", stale_total, stale_nonzero_total);
  if (stale_nonzero_total == 0) {
    std::fprintf(stderr,
                 "FAIL: the reused workspace never carried a nonzero stale "
                 "tail; the alternating check is vacuous\n");
    return 3;
  }

  std::printf("\n## the refusal control\n");
  for (int i = 0; i < nrefused; i++) {
    doc_t *d = &refused_docs[i];
    Workspace w;
    intervals t;
    *(&w) = Workspace();
    w.recs.reserve(4096);
    admit_facts f;
    act_admission(d, nullptr, 0, &f);
    act_stage_fresh(&w, d);
    act_native_fresh(&w, d, 0);
    uint64_t fverdict = load64(w.result + 32);
    uint64_t ferr = load64(w.result + 72);
    uint64_t size = result_size_of(&w);
    int ok = 0;
    consume(w.result, size, 1, 0, &w, &ok);
    check_act(d, &w, "fresh-refusal");
    ws_free_buffers(&w);
    (void)t;
    uint64_t sb = 0;
    int snz = 0;
    intervals u = run_reused(d, &reuse, &sb, &snz);
    (void)u;
    uint64_t rverdict = load64(reuse.result + 32);
    uint64_t rerr = load64(reuse.result + 72);
    if (fverdict != rverdict || ferr != rerr) {
      std::fprintf(stderr,
                   "FAIL: %s refusal moved under reuse: verdict %" PRIu64
                   "/%" PRIu64 " err %" PRIu64 "/%" PRIu64 "\n",
                   d->name, fverdict, rverdict, ferr, rerr);
      return 3;
    }
    std::printf("doc=%s verdict=%" PRIu64 " err=%" PRIu64
                " fresh_err=%" PRIu64 " reused_err=%" PRIu64 "\n",
                d->name, fverdict, ferr, ferr, rerr);
  }

  std::printf("\nok: %d documents x %d rounds x %d repetitions per arm; every "
              "act's header, bytes and consumer readings equal the reference\n",
              ndocs, rounds, reps);
  return 0;
}
