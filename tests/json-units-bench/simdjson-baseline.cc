/* simdjson-baseline.cc -- simdjson 5.0.5's stage 1 and its full on-demand
   parse, over the corpus the three proved stage-1 units are measured on.

   `bench-simdjson.sh` compiles this against the realised simdjson 5.0.5 dev
   output and links the realised library.  It is not the route's 4.6.11 arm in
   `probes/json/route/bench/simdjson-baseline.cc`: that arm needs a 4.6.11
   `singleheader/` source tree, and this one needs only the 5.0.5 dev output's
   `simdjson.h` and the shared library.  The three arms are:

   * `pad`    -- one `padded_string` construction inside a timed region:
                 simdjson's staging (allocate, copy, pad to its boundary).  It
                 is reported so that the stage-1 row's exclusion of staging is
                 visible.  It is not stage-1 work, and it is not comparable
                 with a unit row, whose staging is done once outside the clock.
   * `stage1` -- one `dom_parser_implementation::stage1` call in
                 `stage1_mode::regular` over a buffer staged before the clock.
                 This is simdjson's stage 1: structural-character
                 classification, the string/escape state machine, UTF-8
                 validation, and the structural-index array stage 2 reads.  It
                 is the closest stage-for-stage counterpart to the three units,
                 which split the same work into `s1_masks` (masks only, no
                 UTF-8, no index array), `entry_pos8`/`entry_b8` (positions
                 from a precomputed mask stream) and `utf8_gated` (validity).
   * `parse`  -- one `ondemand::parser::iterate` plus the full value traversal
                 inside a timed region, over a `padded_string` staged before the
                 clock: every string fetched (which validates it), every member
                 key unescaped, every number converted, and a count accumulated
                 so the compiler cannot elide the walk.  This is stage 1 plus
                 the lazy stage 2.  It is a parser, not a unit, and it is
                 reported separately.

   The document is read once, before the clock; the two parsers and their
   buffers are constructed before the clock.  `pad` constructs a
   `padded_string` per repetition because allocating and copying is what that
   row prices.  The stage-1 and parse arms reuse one `padded_string` staged
   before every clock in the run.

   Gates: the `stage1` arm's error code, structural-index count and index
   checksum, and the `parse` arm's error code and walk count, must equal their
   warm-up values in every timed repetition; a disagreement exits 3 rather
   than printing a number.  A document the parser refuses still gets a row --
   `stage1` with `status=rejected` when stage 1 returns an error, `parse` with
   `status=refused` -- but only a `parse` row with `status=ok` is a full-parse
   figure.  The script repeats the binary as trials and asserts the row
   checksums are identical across trials and core classes.

   Flags: the harness is compiled at `-O3 -march=x86-64-v3 -mpclmul
   -std=c++17 -falign-loops=64 -falign-functions=64`, the units' measured
   compiler line with the C++ standard.  The library is the realised nix build
   and is not recompiled at those flags: `stage1` and the library's stage-2
   helpers run the library's code, while the on-demand traversal in `parse` is
   compiled here.  The script records both, and so does
   `docs/json-pipeline-performance.md`.

     simdjson-baseline --doc <name>=<path> [--doc ...] [--reps <n>] [--samples]

   Exit status: 0 on success, 2 on a bad argument or unreadable document, 3
   when a gate above fails. */
#define _GNU_SOURCE 1

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
#include <string_view>
#include <vector>

#if defined(__x86_64__)
#include <cpuid.h>
#include <x86intrin.h>
#endif
#if defined(__linux__)
#include <sched.h>
#endif

/* The release the script checks before compiling: a row against an unnamed
   release is not a comparison. */
#define PINNED_VERSION "5.0.5"

#define MAX_DOCS 64

static volatile uint64_t sink;

/* ------------------------------------------------------------------ time -- */
static uint64_t now_ns(void) {
  struct timespec t;
  if (clock_gettime(CLOCK_MONOTONIC_RAW, &t) != 0) {
    std::perror("clock_gettime");
    std::exit(2);
  }
  return (uint64_t)t.tv_sec * 1000000000ull + (uint64_t)t.tv_nsec;
}

static uint64_t rdtsc_now(void) {
#if defined(__x86_64__)
  return __rdtsc();
#else
  return now_ns();
#endif
}

/* The core clock, in cycles per nanosecond, by a serial dependent-add chain.
   One `add` per iteration is the loop-carried dependency and its latency is
   one cycle on this part, so `iterations / nanoseconds` is the core's GHz. */
static volatile uint64_t cal_sink;

static void serial_chain(uint64_t n) {
  uint64_t x = cal_sink;
#if defined(__x86_64__)
  __asm__ __volatile__("1:\n\t"
                       "addq $1, %0\n\t"
                       "decq %1\n\t"
                       "jne 1b\n\t"
                       : "+r"(x), "+r"(n)
                       :
                       : "cc");
#else
  while (n--) x += 1;
#endif
  cal_sink = x;
}

static double calibrate_ghz(void) {
  const uint64_t iterations = 1ull << 25;
  serial_chain(1ull << 20); /* warm the loop and the clock */
  uint64_t t0 = now_ns();
  serial_chain(iterations);
  uint64_t t1 = now_ns();
  uint64_t ns = t1 - t0;
  return ns ? (double)iterations / (double)ns : 0.0;
}

static double tsc_ghz(void) {
  uint64_t t0 = now_ns();
  uint64_t c0 = rdtsc_now();
  while (now_ns() - t0 < 15000000ull) {}
  uint64_t t1 = now_ns();
  uint64_t c1 = rdtsc_now();
  uint64_t ns = t1 - t0;
  return ns ? (double)(c1 - c0) / (double)ns : 0.0;
}

static unsigned cpuid_core_class(void) {
#if defined(__x86_64__)
  unsigned a = 0, b = 0, c = 0, d = 0;
  if (__get_cpuid(0x1A, &a, &b, &c, &d)) return (a >> 24) & 0xFFu;
#endif
  return 0;
}

/* ---------------------------------------------------------------- stats -- */
typedef struct {
  uint64_t min, p10, median, p90, max;
} summary;

static int cmp_u64(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return x < y ? -1 : x > y ? 1 : 0;
}

static summary summarise(std::vector<uint64_t> &s) {
  summary out;
  std::qsort(s.data(), s.size(), sizeof(uint64_t), cmp_u64);
  int n = (int)s.size();
  out.min = s[0];
  out.max = s[n - 1];
  out.p10 = s[(int)((double)(n - 1) * 0.10)];
  out.median = s[(n - 1) / 2];
  out.p90 = s[(int)((double)(n - 1) * 0.90)];
  return out;
}

static uint64_t mix(uint64_t h, uint64_t v) {
  return (h ^ v) * 0x100000001B3ull;
}

static const char *error_slug(simdjson::error_code e) {
  switch (e) {
  case simdjson::SUCCESS: return "SUCCESS";
  case simdjson::CAPACITY: return "CAPACITY";
  case simdjson::MEMALLOC: return "MEMALLOC";
  case simdjson::TAPE_ERROR: return "TAPE_ERROR";
  case simdjson::DEPTH_ERROR: return "DEPTH_ERROR";
  case simdjson::STRING_ERROR: return "STRING_ERROR";
  case simdjson::T_ATOM_ERROR: return "T_ATOM_ERROR";
  case simdjson::F_ATOM_ERROR: return "F_ATOM_ERROR";
  case simdjson::N_ATOM_ERROR: return "N_ATOM_ERROR";
  case simdjson::NUMBER_ERROR: return "NUMBER_ERROR";
  case simdjson::BIGINT_ERROR: return "BIGINT_ERROR";
  case simdjson::UTF8_ERROR: return "UTF8_ERROR";
  case simdjson::UNINITIALIZED: return "UNINITIALIZED";
  case simdjson::EMPTY: return "EMPTY";
  case simdjson::UNESCAPED_CHARS: return "UNESCAPED_CHARS";
  case simdjson::UNCLOSED_STRING: return "UNCLOSED_STRING";
  case simdjson::UNSUPPORTED_ARCHITECTURE: return "UNSUPPORTED_ARCHITECTURE";
  case simdjson::INCORRECT_TYPE: return "INCORRECT_TYPE";
  case simdjson::NUMBER_OUT_OF_RANGE: return "NUMBER_OUT_OF_RANGE";
  case simdjson::INDEX_OUT_OF_BOUNDS: return "INDEX_OUT_OF_BOUNDS";
  case simdjson::NO_SUCH_FIELD: return "NO_SUCH_FIELD";
  case simdjson::IO_ERROR: return "IO_ERROR";
  case simdjson::INVALID_JSON_POINTER: return "INVALID_JSON_POINTER";
  case simdjson::INVALID_URI_FRAGMENT: return "INVALID_URI_FRAGMENT";
  case simdjson::UNEXPECTED_ERROR: return "UNEXPECTED_ERROR";
  case simdjson::PARSER_IN_USE: return "PARSER_IN_USE";
  case simdjson::OUT_OF_ORDER_ITERATION: return "OUT_OF_ORDER_ITERATION";
  case simdjson::INSUFFICIENT_PADDING: return "INSUFFICIENT_PADDING";
  case simdjson::INCOMPLETE_ARRAY_OR_OBJECT: return "INCOMPLETE_ARRAY_OR_OBJECT";
  case simdjson::SCALAR_DOCUMENT_AS_VALUE: return "SCALAR_DOCUMENT_AS_VALUE";
  case simdjson::OUT_OF_BOUNDS: return "OUT_OF_BOUNDS";
  case simdjson::TRAILING_CONTENT: return "TRAILING_CONTENT";
  case simdjson::OUT_OF_CAPACITY: return "OUT_OF_CAPACITY";
  case simdjson::UNKNOWN_FIELD: return "UNKNOWN_FIELD";
  default: return "OTHER";
  }
}

/* ------------------------------------------------------------- documents -- */
typedef struct {
  char name[64];
  const char *path;
  std::string bytes;
} doc;

static doc docs[MAX_DOCS];
static int ndocs;

static void die(int code, const char *what) {
  std::fprintf(stderr, "baseline: %s\n", what);
  std::exit(code);
}

static void read_file(const char *path, std::string *out) {
  FILE *f = std::fopen(path, "rb");
  if (f == NULL) {
    std::fprintf(stderr, "baseline: %s: %s\n", path, std::strerror(errno));
    std::exit(2);
  }
  char buf[65536];
  size_t got;
  while ((got = std::fread(buf, 1, sizeof buf, f)) > 0) out->append(buf, got);
  if (std::ferror(f)) die(2, "short read");
  if (std::fclose(f) != 0) die(2, "close failed");
}

static void add_doc(const char *spec) {
  if (ndocs >= MAX_DOCS) die(2, "too many documents");
  const char *eq = std::strchr(spec, '=');
  if (eq == NULL || eq == spec || eq[1] == '\0')
    die(2, "--doc wants <name>=<path>");
  doc *d = &docs[ndocs];
  *d = doc{};
  size_t name_len = (size_t)(eq - spec);
  if (name_len >= sizeof d->name) die(2, "document name too long");
  std::memcpy(d->name, spec, name_len);
  d->name[name_len] = '\0';
  d->path = eq + 1;
  ndocs++;
}

/* --------------------------------------------------------------- arm pad -- */
static uint64_t pad_check(const simdjson::padded_string &ps) {
  uint64_t h = mix(0x84222325CBF29CE4ull, (uint64_t)ps.size());
  if (ps.size()) {
    h = mix(h, (uint8_t)ps.data()[0]);
    h = mix(h, (uint8_t)ps.data()[ps.size() - 1]);
  }
  return h;
}

/* ------------------------------------------------------------ arm stage1 -- */
typedef struct {
  simdjson::error_code err;
  uint32_t n;
} s1_result;

static s1_result stage1_act(simdjson::dom::parser &parser,
                            const simdjson::padded_string &ps) {
  s1_result r;
  r.err = parser.implementation->stage1(
      reinterpret_cast<const uint8_t *>(ps.data()), ps.size(),
      simdjson::stage1_mode::regular);
  r.n = parser.implementation->n_structural_indexes;
  return r;
}

/* Read after the clock: it checks the whole index array the timed call wrote,
   and it is not part of the row's measured interval. */
static uint64_t stage1_check(const simdjson::dom::parser &parser,
                             const s1_result &r) {
  uint64_t h = mix(0x84222325CBF29CE4ull, (uint64_t)r.err);
  h = mix(h, r.n);
  const uint32_t *idx = parser.implementation->structural_indexes.get();
  for (uint32_t i = 0; i < r.n; i++) h = mix(h, idx[i]);
  return h;
}

/* ------------------------------------------------------------- arm parse -- */
static simdjson::error_code g_err = simdjson::SUCCESS;

static void set_err(simdjson::error_code e) {
  if (g_err == simdjson::SUCCESS) g_err = e;
}

/* The reference act: the full traversal, with a count so the walk survives
   optimization.  Same shape as `probes/json/route/bench/simdjson-baseline.cc`'s
   `od_count_value`, except that an error is recorded and the traversal stops
   instead of exiting: a refused document is a row with `status=refused`, not a
   reason to lose the run. */
static uint64_t od_count_value(simdjson::ondemand::value &v) {
  using namespace simdjson;
  if (g_err != SUCCESS) return 0;

  ondemand::json_type t;
  if (auto e = v.type().get(t)) {
    set_err(e);
    return 0;
  }

  switch (t) {
  case ondemand::json_type::null:
    return 1;
  case ondemand::json_type::boolean: {
    bool b;
    if (auto e = v.get_bool().get(b)) {
      set_err(e);
      return 0;
    }
    return 1 + (uint64_t)b;
  }
  case ondemand::json_type::number: {
    double d;
    if (auto e = v.get_double().get(d)) {
      set_err(e);
      return 0;
    }
    /* The corpus's numbers are integers; the range guard keeps a decimal or a
       non-finite value out of the integer cast's undefined range. */
    if (!(d == d) || d >= 9.0e18 || d <= -9.0e18) return 1;
    return 1 + (uint64_t)(int64_t)d;
  }
  case ondemand::json_type::string: {
    std::string_view s;
    if (auto e = v.get_string().get(s)) {
      set_err(e);
      return 0;
    }
    return 1 + s.size();
  }
  case ondemand::json_type::array: {
    ondemand::array arr;
    if (auto e = v.get_array().get(arr)) {
      set_err(e);
      return 0;
    }
    uint64_t n = 0;
    for (auto x : arr) {
      ondemand::value xv;
      if (auto e = x.get(xv)) {
        set_err(e);
        break;
      }
      n += od_count_value(xv);
      if (g_err != SUCCESS) break;
    }
    return n + 1;
  }
  case ondemand::json_type::object: {
    ondemand::object obj;
    if (auto e = v.get_object().get(obj)) {
      set_err(e);
      return 0;
    }
    uint64_t n = 0;
    for (auto &&f : obj) {
      std::string_view k;
      auto kr = f.unescaped_key();
      if (auto e = std::move(kr).get(k)) {
        set_err(e);
        break;
      }
      n += k.size();
      auto vr = f.value();
      simdjson::ondemand::value fv;
      if (auto e = std::move(vr).get(fv)) {
        set_err(e);
        break;
      }
      n += od_count_value(fv);
      if (g_err != SUCCESS) break;
    }
    return n + 1;
  }
  case ondemand::json_type::unknown:
    return 0;
  }
  return 0;
}

typedef struct {
  simdjson::error_code err;
  uint64_t walked;
  uint64_t checksum;
} parse_result;

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

/* ------------------------------------------------------------------ rows -- */
template <class Call, class Check>
static void run_arm(const char *doc_name, const char *arm, uint64_t bytes,
                    uint64_t blocks, int reps, int samples, int cpu,
                    const char *status, const char *error, int error_num,
                    uint32_t structurals, uint64_t walked, uint64_t reference,
                    Call call, Check check) {
  double g1 = calibrate_ghz();
  double g2 = calibrate_ghz();
  double ghz = 0.5 * (g1 + g2);

  std::vector<uint64_t> times;
  times.reserve((size_t)reps);
  for (int i = 0; i < reps; i++) {
    uint64_t t0 = now_ns();
    call();
    uint64_t t1 = now_ns();
    uint64_t h = check();
    if (h != reference) {
      std::fprintf(stderr,
                   "baseline: %s/%s: a timed pass produced checksum %016" PRIx64
                   ", the warm-up pass %016" PRIx64 "\n",
                   doc_name, arm, h, reference);
      std::exit(3);
    }
    times.push_back(t1 - t0);
  }
  summary m = summarise(times);

  double median_ns_per_byte = (double)m.median / (double)bytes;
  double gbps = (double)bytes / (double)m.median;
  double cycles_per_byte = median_ns_per_byte * ghz;

  std::printf("row cpu=%d doc=%s arm=%s bytes=%" PRIu64 " blocks=%" PRIu64
              " reps=%d status=%s error=%s error_num=%d"
              " min_ns=%" PRIu64 " p10_ns=%" PRIu64 " median_ns=%" PRIu64
              " p90_ns=%" PRIu64 " max_ns=%" PRIu64
              " ns_per_byte=%.5f gbps=%.3f cycles_per_byte=%.4f"
              " core_ghz=%.3f calib_spread_pct=%.2f"
              " structurals=%u walked=%" PRIu64 " checksum=0x%016" PRIx64 "\n",
              cpu, doc_name, arm, bytes, blocks, reps, status, error, error_num,
              m.min, m.p10, m.median, m.p90, m.max,
              median_ns_per_byte, gbps, cycles_per_byte, ghz,
              g1 > g2 ? 100.0 * (g1 - g2) / ghz : 100.0 * (g2 - g1) / ghz,
              structurals, walked, reference);

  if (samples) {
    for (int i = 0; i < reps; i++)
      std::printf("sample cpu=%d doc=%s arm=%s rep=%d ns=%" PRIu64
                  " gbps=%.3f\n",
                  cpu, doc_name, arm, i, times[i],
                  (double)bytes / (double)times[i]);
  }
}

/* ------------------------------------------------------------------ main -- */
int main(int argc, char **argv) {
  int reps = 51;
  int samples = 0;
  for (int i = 1; i < argc; i++) {
    if (!std::strcmp(argv[i], "--doc") && i + 1 < argc) {
      add_doc(argv[++i]);
    } else if (!std::strcmp(argv[i], "--reps") && i + 1 < argc) {
      reps = std::atoi(argv[++i]);
      if (reps < 5 || reps > 100000) die(2, "reps out of range");
    } else if (!std::strcmp(argv[i], "--samples")) {
      samples = 1;
    } else {
      std::fprintf(stderr, "baseline: bad argument %s\n", argv[i]);
      return 2;
    }
  }
  if (ndocs == 0) die(2, "no --doc given");

  /* Named, not assumed: the header and the active implementation must both be
     the pinned release, or no row is reported. */
  if (std::strcmp(SIMDJSON_VERSION, PINNED_VERSION) != 0) {
    std::fprintf(stderr, "baseline: header is simdjson %s, not %s\n",
                 SIMDJSON_VERSION, PINNED_VERSION);
    return 2;
  }
  std::string impl(simdjson::get_active_implementation()->name());

  int cpu = -1;
#if defined(__linux__)
  cpu = sched_getcpu();
#endif

  std::printf("instrument bench=simdjson reps=%d tsc_ghz=%.3f cpuid_1a=%02x"
              " cpu=%d simdjson=%s implementation=%s\n",
              reps, tsc_ghz(), cpuid_core_class(), cpu, SIMDJSON_VERSION,
              impl.c_str());

  for (int i = 0; i < ndocs; i++) {
    doc *d = &docs[i];
    read_file(d->path, &d->bytes);
    if (d->bytes.empty()) die(2, "empty document");
    uint64_t bytes = d->bytes.size();
    uint64_t blocks = bytes / 64;

    /* Staged before every clock in the run: simdjson's required padding is
       the construction's work and belongs to `pad`, not to `stage1`/`parse`. */
    simdjson::padded_string ps(d->bytes.data(), d->bytes.size());

    simdjson::dom::parser dp;
    if (auto e = dp.allocate(ps.size(), dp.max_depth())) {
      std::fprintf(stderr, "baseline: %s: dom allocate: %s\n", d->name,
                   simdjson::error_message(e));
      std::exit(3);
    }
    simdjson::ondemand::parser op;
    if (auto e = op.allocate(ps.size())) {
      std::fprintf(stderr, "baseline: %s: ondemand allocate: %s\n", d->name,
                   simdjson::error_message(e));
      std::exit(3);
    }

    /* Warm-ups, and the values every timed pass is gated against. */
    simdjson::padded_string pad_ps(d->bytes.data(), d->bytes.size());
    uint64_t pad_ref = pad_check(pad_ps);
    s1_result s1_ref = stage1_act(dp, ps);
    uint64_t s1_ref_checksum = stage1_check(dp, s1_ref);
    parse_result parse_ref = parse_act(op, ps);
    sink ^= pad_ref ^ s1_ref_checksum ^ parse_ref.checksum ^ parse_ref.walked;

    const char *s1_status = s1_ref.err == simdjson::SUCCESS ? "ok" : "rejected";
    const char *parse_status =
        parse_ref.err == simdjson::SUCCESS ? "ok" : "refused";

    std::printf("doc name=%s bytes=%" PRIu64 " blocks=%" PRIu64
                " stage1_error=%s stage1_error_num=%d stage1_structurals=%u"
                " stage1_checksum=0x%016" PRIx64
                " parse_status=%s parse_error=%s parse_error_num=%d"
                " parse_walked=%" PRIu64
                " parse_checksum=0x%016" PRIx64 "\n",
                d->name, bytes, blocks, error_slug(s1_ref.err), (int)s1_ref.err,
                s1_ref.n, s1_ref_checksum, parse_status,
                error_slug(parse_ref.err), (int)parse_ref.err, parse_ref.walked,
                parse_ref.checksum);

    /* `pad`: the construction is inside the clock; the two-byte check is read
       after it. */
    run_arm(d->name, "pad", bytes, blocks, reps, samples, cpu, "ok", "SUCCESS",
            0, 0, 0, pad_ref,
            [&] { pad_ps = simdjson::padded_string(d->bytes.data(), d->bytes.size()); },
            [&] { return pad_check(pad_ps); });

    /* `stage1`: the call is inside the clock; the index-array check is read
       after it. */
    s1_result s1_timed{simdjson::SUCCESS, 0};
    run_arm(d->name, "stage1", bytes, blocks, reps, samples, cpu, s1_status,
            error_slug(s1_ref.err), (int)s1_ref.err, s1_ref.n, 0,
            s1_ref_checksum,
            [&] { s1_timed = stage1_act(dp, ps); },
            [&] { return stage1_check(dp, s1_timed); });

    /* `parse`: the iterate and the traversal are inside the clock; the
       checksum is the two small mixes `parse_act` performs. */
    parse_result parse_timed{simdjson::SUCCESS, 0, 0};
    run_arm(d->name, "parse", bytes, blocks, reps, samples, cpu, parse_status,
            error_slug(parse_ref.err), (int)parse_ref.err, 0, parse_ref.walked,
            parse_ref.checksum,
            [&] { parse_timed = parse_act(op, ps); },
            [&] { return parse_timed.checksum; });
  }

  return 0;
}
