/* shape.cc -- where the native parse core's time goes, in the shape the route
   calls it and in the shape the stage profile measures it, beside simdjson
   On-Demand in the same process.

   `kernel/json/bench/profile-pipeline.cc` prices the six stages with a
   64-byte-aligned document window and buffers reused across rounds.  The route
   does neither: it stages the document as `[0,0,0] ++ doc ++ pad` and hands the
   object `window + 3`, and every repetition's thirteen buffers are fresh
   allocations.  The route's `--stages` native figure is therefore not the
   profile's `pipeline` figure, and this harness measures the difference
   instead of assuming it away.

   One act is one pipeline call over one document.  The variants:

     site      window at page+64, the route's buffer capacities, reused
               buffers -- the profile's shape with the route's capacities
     off3      window at page+3, reused buffers: the route's window offset
     off0      window at page+0, reused buffers
     fresh3    window at page+3, fresh malloc'd buffers per call, zeroed
               outside the clock (the route's staging and copy-in shape)
     fresh+64  the same, with the thirteen buffers 64-byte aligned
     fresh0    the same as fresh3, window at page+0
     reference simdjson 4.6.11 On-Demand: iterate plus the full traversal
     pad       one simdjson padded_string construction (its staging)

   The six stages are also timed separately in the `site` shape, and the walk
   is priced over the `site` call's own entry stream, so the stage numbers and
   the whole-call numbers come from one process.

   Every variant must produce the same nk, nxp, ndst, nev, err, event bytes and
   arena bytes as `site` before anything is timed; otherwise the harness exits
   with a setup fault rather than printing a duration for a different parse.

   Usage: shape --corpus <manifest> [--rounds N] [--core N]

   The manifest is the one `profile-pipeline.sh` reads (name, arm, record
   ratios, digest, path); a row whose digest differs is refused.  Exit 0 on a
   complete run, 3 on a setup fault. */

#include <simdjson.h>

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <string>
#include <vector>

extern "C" {
#include "pipeline.h"
#include "s1_block.h"
#include "entry.h"
#include "utf8.h"
#include "escape.h"
#include "stage2.h"
}

#define PINNED_MAJOR 4
#define PINNED_MINOR 6
#define PINNED_REVISION 11
#define ARM 2

static volatile uint64_t sink;

/* The entry emitter reads the unit's own 8 KiB static table; the caller's slot
   is the initialiser's handle, and a process that never calls it emits zero
   positions.  `profile-pipeline.cc` does the same before its first call. */
static uint32_t entry_table_slot[256 * 8];
__attribute__((constructor)) static void arm_init(void) {
  leanllvm_json_entry_table(entry_table_slot);
}

static uint64_t now_ns(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (uint64_t)t.tv_sec * 1000000000ull + (uint64_t)t.tv_nsec;
}

static double median_of(std::vector<double> v) {
  if (v.empty()) return 0.0;
  std::sort(v.begin(), v.end());
  return v[v.size() / 2];
}

static void *xmalloc(size_t n) {
  void *p = malloc(n ? n : 1);
  if (!p) { fprintf(stderr, "out of memory\n"); exit(2); }
  return p;
}

static void *aligned_bytes(size_t n, size_t align) {
  void *p = nullptr;
  if (posix_memalign(&p, align, n) != 0) {
    fprintf(stderr, "cannot allocate %zu bytes\n", n);
    exit(2);
  }
  memset(p, 0, n);
  return p;
}

/* ---- the route's thirteen buffers, in its capacities --------------------- */

struct buffers {
  uint64_t sc[3];
  uint64_t mk[6];
  uint64_t entw;
  uint32_t *ep;
  uint64_t epcap;
  uint64_t nk;
  uint32_t *xp;
  uint64_t xpcap;
  uint64_t nxp;
  uint64_t xcarry[2];
  uint8_t *dst;
  uint64_t dstcap;
  uint64_t ndst;
  uint8_t *ev;
  uint64_t evcap;
  uint64_t nev;
  uint64_t err;
};

static void caps_of(uint64_t n, uint64_t nb, uint64_t *epcap, uint64_t *xpcap,
                    uint64_t *dstcap, uint64_t *evcap) {
  *epcap = 64 * nb + 9;
  *xpcap = 64 * nb + 8;
  *dstcap = n + 64;
  *evcap = 13 * n + 128;
}

static void buffers_alloc(buffers *b, uint64_t n, uint64_t nb, int align64) {
  caps_of(n, nb, &b->epcap, &b->xpcap, &b->dstcap, &b->evcap);
  size_t a = align64 ? 64 : 16;
  b->ep = (uint32_t *)aligned_bytes(b->epcap * sizeof *b->ep, a);
  b->xp = (uint32_t *)aligned_bytes(b->xpcap * sizeof *b->xp, a);
  b->dst = (uint8_t *)aligned_bytes(b->dstcap, a);
  b->ev = (uint8_t *)aligned_bytes(b->evcap, a);
}

static void cursors_zero(buffers *b) {
  b->sc[0] = b->sc[1] = b->sc[2] = 0;
  b->mk[0] = b->mk[1] = b->mk[2] = b->mk[3] = b->mk[4] = b->mk[5] = 0;
  b->entw = 0;
  b->nk = 0;
  b->nxp = 0;
  b->xcarry[0] = b->xcarry[1] = 0;
  b->ndst = 0;
  b->nev = 0;
  b->err = 0;
}

/* the route's staging: every buffer at its capacity, zero-filled, outside the
   clock for the fresh variants (the route times that as `staging`) */
static void buffers_zero(buffers *b) {
  cursors_zero(b);
  memset(b->ep, 0, b->epcap * sizeof *b->ep);
  memset(b->xp, 0, b->xpcap * sizeof *b->xp);
  memset(b->dst, 0, b->dstcap);
  memset(b->ev, 0, b->evcap);
}

static void buffers_free(buffers *b) {
  free(b->ep);
  free(b->xp);
  free(b->dst);
  free(b->ev);
}

/* one pipeline call; the cursor slots are zeroed first because the object
   reads them */
static uint64_t pipeline_call(const uint8_t *doc, uint64_t n, buffers &b,
                              uint64_t arm = ARM) {
  cursors_zero(&b);
  return leanllvm_json_pipeline(doc, n, b.sc, b.mk, &b.entw, b.ep, b.epcap,
                                &b.nk, b.xp, b.xpcap, &b.nxp, b.xcarry, b.dst,
                                b.dstcap, &b.ndst, b.ev, b.evcap, &b.nev,
                                &b.err, arm);
}

struct doc {
  char name[64];
  char sha[65];
  char path[1024];
  uint64_t n, nb, entries, events, ndst;
  uint8_t *win_site;   /* doc at +64 */
  uint8_t *win_off3;   /* doc at +3 */
  uint8_t *win_off0;   /* doc at +0 */
  buffers b;           /* the reused buffers */
  uint64_t *entw;      /* the entry word per block */
  s1_masks *mks;       /* the masks per block */
  simdjson::ondemand::parser *sp;
  simdjson::padded_string *ps;
};

/* ---- simdjson's act, transcribed from the reference arm ------------------ */

template <class T>
static T od_get(simdjson::simdjson_result<T> r, const char *what) {
  T out{};
  auto e = std::move(r).get(out);
  if (e) {
    fprintf(stderr, "reference: %s: %s\n", what, simdjson::error_message(e));
    exit(3);
  }
  return out;
}

static uint64_t od_count_value(simdjson::ondemand::value &v) {
  using namespace simdjson;
  switch (v.type()) {
  case ondemand::json_type::null:
    return 1;
  case ondemand::json_type::boolean:
    return 1 + (uint64_t)od_get(v.get_bool(), "bool");
  case ondemand::json_type::number:
    return 1 + (uint64_t)(int64_t)od_get(v.get_double(), "number");
  case ondemand::json_type::string:
    return 1 + od_get(v.get_string(), "string").size();
  case ondemand::json_type::array: {
    ondemand::array arr = od_get(v.get_array(), "array");
    uint64_t n = 0;
    for (auto x : arr) {
      ondemand::value xv = od_get(x, "array element");
      n += od_count_value(xv);
    }
    return n + 1;
  }
  case ondemand::json_type::object: {
    ondemand::object obj = od_get(v.get_object(), "object");
    uint64_t n = 0;
    for (auto &&f : obj) {
      n += od_get(f.unescaped_key(), "key").size();
      ondemand::value xv = f.value();
      n += od_count_value(xv);
    }
    return n + 1;
  }
  }
  return 0;
}

/* the same traversal with the number conversion removed: the differential
   against `reference_walk` is the reference's own number-conversion cost */
static uint64_t od_count_value_nonum(simdjson::ondemand::value &v) {
  using namespace simdjson;
  switch (v.type()) {
  case ondemand::json_type::null:
    return 1;
  case ondemand::json_type::boolean:
    return 1 + (uint64_t)od_get(v.get_bool(), "bool");
  case ondemand::json_type::number:
    return 1;
  case ondemand::json_type::string:
    return 1 + od_get(v.get_string(), "string").size();
  case ondemand::json_type::array: {
    ondemand::array arr = od_get(v.get_array(), "array");
    uint64_t n = 0;
    for (auto x : arr) {
      ondemand::value xv = od_get(x, "array element");
      n += od_count_value_nonum(xv);
    }
    return n + 1;
  }
  case ondemand::json_type::object: {
    ondemand::object obj = od_get(v.get_object(), "object");
    uint64_t n = 0;
    for (auto &&f : obj) {
      n += od_get(f.unescaped_key(), "key").size();
      ondemand::value xv = f.value();
      n += od_count_value_nonum(xv);
    }
    return n + 1;
  }
  }
  return 0;
}

static uint64_t reference_walk_nonum(doc &d) {
  simdjson::ondemand::document docv = od_get(d.sp->iterate(*d.ps), "iterate");
  simdjson::ondemand::value v = od_get(docv.get_value(), "document value");
  return od_count_value_nonum(v);
}

static uint64_t reference_walk(doc &d) {
  simdjson::ondemand::document docv = od_get(d.sp->iterate(*d.ps), "iterate");
  simdjson::ondemand::value v = od_get(docv.get_value(), "document value");
  return od_count_value(v);
}

/* ---- loading ------------------------------------------------------------- */

static int stage_doc(const char *path, doc &d) {
  FILE *f = fopen(path, "rb");
  long m;
  if (!f) { fprintf(stderr, "SETUP: absent %s\n", path); return 3; }
  if (fseek(f, 0, SEEK_END) != 0 || (m = ftell(f)) < 0 || fseek(f, 0, SEEK_SET) != 0) {
    fprintf(stderr, "SETUP: cannot size %s\n", path); fclose(f); return 3;
  }
  d.n = (uint64_t)m;
  std::string bytes((size_t)m, '\0');
  if (d.n && fread(&bytes[0], 1, (size_t)d.n, f) != d.n) {
    fprintf(stderr, "SETUP: cannot read %s\n", path); fclose(f); return 3;
  }
  fclose(f);
  d.nb = (d.n + 63) / 64;
  size_t win = (size_t)((d.nb ? d.nb : 1) * 64) + 256;
  d.win_site = (uint8_t *)aligned_bytes(win, 4096);
  d.win_off3 = (uint8_t *)aligned_bytes(win, 4096);
  d.win_off0 = (uint8_t *)aligned_bytes(win, 4096);
  if (d.n) {
    memcpy(d.win_site + 64, bytes.data(), (size_t)d.n);
    memcpy(d.win_off3 + 3, bytes.data(), (size_t)d.n);
    memcpy(d.win_off0 + 0, bytes.data(), (size_t)d.n);
  }
  buffers_alloc(&d.b, d.n, d.nb, 0);
  cursors_zero(&d.b);
  size_t nblk = (size_t)(d.nb ? d.nb : 1);
  d.entw = (uint64_t *)xmalloc(nblk * sizeof *d.entw);
  d.mks = (s1_masks *)xmalloc(nblk * sizeof *d.mks);
  d.sp = new simdjson::ondemand::parser();
  d.ps = new simdjson::padded_string(bytes.data(), bytes.size());
  return 0;
}

static int parse_manifest(const char *path, std::vector<doc> &docs) {
  FILE *f = fopen(path, "rb");
  if (!f) { fprintf(stderr, "SETUP: absent manifest %s\n", path); return 3; }
  char line[4096];
  while (fgets(line, (int)sizeof line, f)) {
    if (line[0] == '#' || line[0] == '\n') continue;
    if (strncmp(line, "name\t", 5) == 0) continue;
    char name[64], sha[65], file[1024];
    unsigned ae, ap;
    double re, rp;
    if (sscanf(line, "%63s\t%u\t%u\t%lf\t%lf\t%64s\t%1023[^\n]", name, &ae,
               &ap, &re, &rp, sha, file) != 7) {
      fprintf(stderr, "SETUP: bad manifest row\n");
      fclose(f);
      return 3;
    }
    doc d;
    memset(&d, 0, sizeof d);
    snprintf(d.name, sizeof d.name, "%s", name);
    snprintf(d.sha, sizeof d.sha, "%s", sha);
    snprintf(d.path, sizeof d.path, "%s", file);
    if (stage_doc(file, d) != 0) { fclose(f); return 3; }
    docs.push_back(d);
  }
  fclose(f);
  return 0;
}

static int digest_of(const char *path, char out[65]) {
  std::string cmd = "sha256sum '";
  cmd += path;
  cmd += "'";
  FILE *p = popen(cmd.c_str(), "r");
  if (!p) return 3;
  int got = fscanf(p, "%64s", out);
  pclose(p);
  return got == 1 ? 0 : 3;
}

/* ---- the acts ------------------------------------------------------------ */

enum { A_SITE, A_ARM0, A_OFF3, A_OFF0, A_FRESH3, A_FRESHA64, A_FRESH0,
       A_REF, A_REFNONUM, A_PAD, NA };

static double act_site(doc &d) {
  double t0 = now_ns();
  uint64_t v = pipeline_call(d.win_site + 64, d.n, d.b);
  double t1 = now_ns();
  sink ^= v;
  return t1 - t0;
}

/* arm 0 on a document with no backslash: the escape list is empty under both
   arms, so the two calls differ only in the list's own per-block call. */
static double act_arm0(doc &d) {
  double t0 = now_ns();
  uint64_t v = pipeline_call(d.win_site + 64, d.n, d.b, 0);
  double t1 = now_ns();
  sink ^= v;
  return t1 - t0;
}

static double act_off3(doc &d) {
  double t0 = now_ns();
  uint64_t v = pipeline_call(d.win_off3 + 3, d.n, d.b);
  double t1 = now_ns();
  sink ^= v;
  return t1 - t0;
}

static double act_off0(doc &d) {
  double t0 = now_ns();
  uint64_t v = pipeline_call(d.win_off0, d.n, d.b);
  double t1 = now_ns();
  sink ^= v;
  return t1 - t0;
}

static double act_fresh(doc &d, int align64, const uint8_t *win) {
  buffers b;
  memset(&b, 0, sizeof b);
  buffers_alloc(&b, d.n, d.nb, align64);
  buffers_zero(&b);
  double t0 = now_ns();
  uint64_t v = pipeline_call(win, d.n, b);
  double t1 = now_ns();
  sink ^= v;
  buffers_free(&b);
  return t1 - t0;
}

static double act_ref(doc &d) {
  double t0 = now_ns();
  uint64_t v = reference_walk(d);
  double t1 = now_ns();
  sink ^= v;
  return t1 - t0;
}

static double act_ref_nonum(doc &d) {
  double t0 = now_ns();
  uint64_t v = reference_walk_nonum(d);
  double t1 = now_ns();
  sink ^= v;
  return t1 - t0;
}

static double act_pad(doc &d) {
  double t0 = now_ns();
  simdjson::padded_string s((const char *)(d.win_site + 64), (size_t)d.n);
  double t1 = now_ns();
  sink ^= (uint64_t)s.size();
  return t1 - t0;
}

/* ---- the stage acts, in the `site` shape --------------------------------- */

static double act_masks(doc &d) {
  s1_carry sc = {0, 0, 0};
  s1_masks m;
  uint64_t prevS = 0, acc = 0;
  double t0 = now_ns();
  for (uint64_t i = 0; i < d.nb; i++) {
    leanllvm_json_s1_masks(d.win_site + 64 + (i << 6), &sc, &m);
    uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);
    uint64_t ent = m.quote | (m.delim & ~m.in_string);
    ent |= S & ~((S << 1) | prevS);
    prevS = S >> 63;
    uint64_t lim = d.n - (i << 6);
    if (lim < 64) ent &= (1ULL << lim) - 1ULL;
    d.entw[i] = ent;
    d.mks[i] = m;
    acc ^= ent;
  }
  double t1 = now_ns();
  sink ^= acc;
  return t1 - t0;
}

static uint32_t *entry_scratch;
static uint64_t entry_scratch_cap;

static double act_entry(doc &d) {
  uint64_t k = 0, acc = 0;
  double t0 = now_ns();
  for (uint64_t i = 0; i < d.nb; i++)
    k = leanllvm_json_entry_pos8(&d.entw[i], i, 1, entry_scratch, k);
  double t1 = now_ns();
  acc = k;
  sink ^= acc;
  return t1 - t0;
}

static double act_escape(doc &d) {
  uint64_t nxp = 0, carry[2] = {0, 0}, acc = 0;
  double t0 = now_ns();
  for (uint64_t i = 0; i < d.nb; i++)
    leanllvm_json_escape_list(d.mks[i].backslash, d.mks[i].ctl,
                              d.mks[i].in_string, i, d.b.xp, &nxp, carry);
  double t1 = now_ns();
  acc = nxp;
  sink ^= acc;
  return t1 - t0;
}

static double act_utf8(doc &d) {
  const unsigned reps = 8;
  uint64_t acc = 0;
  double t0 = now_ns();
  for (unsigned r = 0; r < reps; r++)
    acc ^= leanllvm_json_utf8(d.win_site + 64, d.n, 0);
  double t1 = now_ns();
  sink ^= acc;
  return (t1 - t0) / (double)reps;
}

static double act_stage2(doc &d) {
  uint64_t ndst = 0, nev = 0, err = 0;
  double t0 = now_ns();
  uint64_t v = leanllvm_json_stage2(d.win_site + 64, d.n, d.b.ep, d.b.nk,
                                    d.b.xp, d.b.nxp, d.b.dst, d.b.dstcap, &ndst,
                                    d.b.ev, d.b.evcap, &nev, &err);
  double t1 = now_ns();
  sink ^= v ^ ndst ^ nev ^ err;
  return t1 - t0;
}

/* ---- verification -------------------------------------------------------- */

static int verify(doc &d) {
  uint64_t v = pipeline_call(d.win_site + 64, d.n, d.b);
  if (v != 1) { fprintf(stderr, "SETUP: %s refused: err=%llu nk=%llu nxp=%llu nev=%llu\n", d.name, (unsigned long long)d.b.err, (unsigned long long)d.b.nk, (unsigned long long)d.b.nxp, (unsigned long long)d.b.nev); return 3; }
  d.entries = d.b.nk;
  d.events = d.b.nev;
  d.ndst = d.b.ndst;
  if (!entry_scratch || entry_scratch_cap < d.b.epcap) {
    free(entry_scratch);
    entry_scratch = (uint32_t *)xmalloc((size_t)d.b.epcap * sizeof(uint32_t));
    entry_scratch_cap = d.b.epcap;
  }
  std::vector<uint8_t> ev0(d.b.ev, d.b.ev + d.b.nev);
  std::vector<uint8_t> dst0(d.b.dst, d.b.dst + d.b.ndst);
  const uint8_t *wins[3] = {d.win_off3 + 3, d.win_off0, d.win_site + 64};
  for (int k = 0; k < 3; k++) {
    for (int a = 0; a < 2; a++) {
      buffers b;
      memset(&b, 0, sizeof b);
      buffers_alloc(&b, d.n, d.nb, a);
      buffers_zero(&b);
      uint64_t vv = pipeline_call(wins[k], d.n, b);
      int bad = vv != 1 || b.nk != d.b.nk || b.nxp != d.b.nxp ||
                b.ndst != d.b.ndst || b.nev != d.b.nev || b.err != d.b.err ||
                memcmp(b.ev, ev0.data(), ev0.size()) != 0 ||
                memcmp(b.dst, dst0.data(), dst0.size()) != 0;
      buffers_free(&b);
      if (bad) {
        fprintf(stderr, "SETUP: %s: variant window %d align %d differs\n",
                d.name, k, a);
        return 3;
      }
    }
  }
  /* arm 0 is the same call on a document with no backslash: the escape list
     is empty under both arms, so every output must agree */
  if (d.b.nxp == 0) {
    buffers b;
    memset(&b, 0, sizeof b);
    buffers_alloc(&b, d.n, d.nb, 0);
    buffers_zero(&b);
    uint64_t vv = pipeline_call(d.win_site + 64, d.n, b, 0);
    int bad = vv != 1 || b.nk != d.b.nk || b.nxp != 0 ||
              b.ndst != d.b.ndst || b.nev != d.b.nev || b.err != d.b.err ||
              memcmp(b.ev, ev0.data(), ev0.size()) != 0 ||
              memcmp(b.dst, dst0.data(), dst0.size()) != 0;
    buffers_free(&b);
    if (bad) {
      fprintf(stderr, "SETUP: %s: arm 0 differs with an empty escape list\n", d.name);
      return 3;
    }
  }

  /* the stage acts read the entry words and masks of this call; fill them */
  (void)act_masks(d);
  if (reference_walk(d) == 0) {
    fprintf(stderr, "SETUP: %s: reference walk counted nothing\n", d.name);
    return 3;
  }
  return 0;
}

int main(int argc, char **argv) {
  const char *corpus_path = nullptr;
  int rounds = 21;
  std::vector<int> cores;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--corpus") && i + 1 < argc) corpus_path = argv[++i];
    else if (!strcmp(argv[i], "--rounds") && i + 1 < argc) rounds = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--core") && i + 1 < argc) cores.push_back(atoi(argv[++i]));
    else { fprintf(stderr, "usage: shape --corpus <manifest> [--rounds N] [--core N]\n"); return 3; }
  }
  if (!corpus_path || rounds < 1) {
    fprintf(stderr, "usage: shape --corpus <manifest> [--rounds N] [--core N]\n");
    return 3;
  }
  if (simdjson::SIMDJSON_VERSION_MAJOR != PINNED_MAJOR || simdjson::SIMDJSON_VERSION_MINOR != PINNED_MINOR ||
      simdjson::SIMDJSON_VERSION_REVISION != PINNED_REVISION) {
    fprintf(stderr, "SETUP: header is not simdjson %d.%d.%d\n", PINNED_MAJOR,
            PINNED_MINOR, PINNED_REVISION);
    return 3;
  }
  printf("reference simdjson %s, implementation %s\n", SIMDJSON_VERSION,
         simdjson::get_active_implementation()->name().c_str());
  if (!cores.empty()) printf("pinned cpu %d\n", cores[0]);

  std::vector<doc> docs;
  if (parse_manifest(corpus_path, docs) != 0) return 3;
  for (auto &d : docs) {
    char got[65] = {0};
    if (digest_of(d.path, got) != 0) return 3;
    if (strcmp(got, d.sha) != 0) {
      fprintf(stderr, "SETUP: %s: digest %s, the manifest names %s\n", d.name,
              got, d.sha);
      return 3;
    }
  }
  for (auto &d : docs) if (verify(d) != 0) return 3;

  printf("\ndoc            bytes  blocks  entries  ev/blk  events  ndst  win+3 mod 64\n");
  for (auto &d : docs)
    printf("%-14s %5llu %7llu %8llu %7.2f %7llu %5llu %9llu\n", d.name,
           (unsigned long long)d.n, (unsigned long long)d.nb,
           (unsigned long long)d.entries,
           (double)d.entries / (double)(d.nb ? d.nb : 1),
           (unsigned long long)d.events, (unsigned long long)d.ndst,
           (unsigned long long)((uintptr_t)(d.win_off3 + 3) & 63));

  /* warm-up: one untimed act per variant per document */
  for (auto &d : docs) {
    act_site(d); act_off3(d); act_off0(d);
    act_fresh(d, 0, d.win_off3 + 3);
    act_fresh(d, 1, d.win_off3 + 3);
    act_fresh(d, 0, d.win_off0);
    act_ref(d); act_pad(d);
  }

  size_t nd = docs.size();
  std::vector<std::vector<double>> t(NA * nd);
  for (int r = 0; r < rounds; r++) {
    for (size_t i = 0; i < nd; i++) {
      doc &d = docs[i];
      double nb = (double)(d.nb ? d.nb : 1);
      for (int a = 0; a < NA; a++) {
        int s = (a + r) % NA;
        double ns = 0.0;
        switch (s) {
        case A_SITE: ns = act_site(d); break;
        case A_ARM0: ns = act_arm0(d); break;
        case A_OFF3: ns = act_off3(d); break;
        case A_OFF0: ns = act_off0(d); break;
        case A_FRESH3: ns = act_fresh(d, 0, d.win_off3 + 3); break;
        case A_FRESHA64: ns = act_fresh(d, 1, d.win_off3 + 3); break;
        case A_FRESH0: ns = act_fresh(d, 0, d.win_off0); break;
        case A_REF: ns = act_ref(d); break;
        case A_REFNONUM: ns = act_ref_nonum(d); break;
        case A_PAD: ns = act_pad(d); break;
        }
        t[s * nd + i].push_back(ns / nb);
      }
    }
  }

  printf("\nrounds %d, one act per variant per document per round, order rotated\n", rounds);
  printf("ns/block: one block is 64 document bytes\n\n");
  printf("%-14s %9s %9s %9s %9s %9s %9s %9s %10s %7s %7s %7s\n", "document",
         "site", "arm0", "off3", "off0", "fresh3", "fresh+64", "fresh0",
         "reference", "ref-num", "pad", "fresh/ref");
  for (size_t i = 0; i < nd; i++) {
    double v[NA];
    for (int s = 0; s < NA; s++) v[s] = median_of(t[s * nd + i]);
    printf("%-14s %9.3f %9.3f %9.3f %9.3f %9.3f %9.3f %9.3f %10.3f %7.3f %7.3f %7.3f\n",
           docs[i].name, v[A_SITE], v[A_ARM0], v[A_OFF3], v[A_OFF0], v[A_FRESH3],
           v[A_FRESHA64], v[A_FRESH0], v[A_REF], v[A_REF] - v[A_REFNONUM],
           v[A_PAD], v[A_FRESH3] / v[A_REF]);
  }

  /* the six stages, in the site shape */
  std::vector<std::vector<double>> st(5 * nd);
  enum { S_MASKS, S_ENTRY, S_ESCAPE, S_UTF8, S_STAGE2 };
  for (int r = 0; r < rounds; r++) {
    for (size_t i = 0; i < nd; i++) {
      doc &d = docs[i];
      double nb = (double)(d.nb ? d.nb : 1);
      for (int a = 0; a < 5; a++) {
        int s = (a + r) % 5;
        double ns = s == S_MASKS ? act_masks(d)
                   : s == S_ENTRY ? act_entry(d)
                   : s == S_ESCAPE ? act_escape(d)
                   : s == S_UTF8 ? act_utf8(d)
                                  : act_stage2(d);
        st[s * nd + i].push_back(ns / nb);
      }
    }
  }
  printf("\nstages in the site shape (ns/block): masks is the mask unit plus the\n");
  printf("entry word; stage1 = masks + entry + escape + utf8; stage2 is the walk\n");
  printf("over the site call's entry and escape streams\n");
  printf("%-14s %8s %8s %8s %8s %8s %9s %9s %9s %9s\n", "document", "masks",
         "entry", "escape", "utf8", "stage2", "stage1", "sum", "site", "sum/site");
  for (size_t i = 0; i < nd; i++) {
    double m = median_of(st[S_MASKS * nd + i]);
    double e = median_of(st[S_ENTRY * nd + i]);
    double x = median_of(st[S_ESCAPE * nd + i]);
    double u = median_of(st[S_UTF8 * nd + i]);
    double w = median_of(st[S_STAGE2 * nd + i]);
    double site = median_of(t[A_SITE * nd + i]);
    printf("%-14s %8.3f %8.3f %8.3f %8.3f %8.3f %9.3f %9.3f %9.3f %9.3f\n",
           docs[i].name, m, e, x, u, w, m + e + x + u, m + e + x + u + w, site,
           (m + e + x + u + w) / site);
  }

  printf("\nbuild core-shape\n");
  printf("sink %llu\n", (unsigned long long)sink);
  return 0;
}
