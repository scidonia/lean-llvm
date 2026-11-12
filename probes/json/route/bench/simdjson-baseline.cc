/* simdjson-baseline.cc -- the route's reference arm: simdjson 4.6.11's
   on-demand parser over the same document, with two stages that correspond to
   the route's own.

   `probes/json/route/bench.sh` compiles this against the local simdjson
   source's amalgamated singleheader and runs it on the same corpus as the
   route.  The two rows it prints are:

   * `pad` -- one `padded_string` construction from the document's bytes inside
     a timed region: simdjson's own staging (allocate, copy, pad to a 64-byte
     boundary with the required padding bytes).  This is the arm comparable to
     the route's `staging + copyin` stages.
   * `parse` -- one `iterate` plus the full value traversal inside a timed
     region, over a `padded_string` staged before the clock: every string
     fetched (which validates it), every member key unescaped, every number
     converted, and a count accumulated so the compiler cannot elide the walk.
     This is the arm comparable to the route's `native` stage.

   The parser and its internal buffers are constructed before the clock, as
   `kernel/json/bench/paired-reference.cc` stages its reference arm: an act that
   allocates its parser per call would be measuring the constructor.  The
   document is read once, before the clock; the route's row reports its own
   read separately, so neither arm's figure includes the file read.

   The traversal is the reference's, transcribed: the reference arm this page
   is compared with walks every value rather than trusting `iterate` alone, and
   `iterate` by itself is a setup call, not a parse. */

#include "simdjson.h"

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <string>
#include <vector>

/* The release `bench.sh` selects and checks before compiling: a row against an
   unnamed release is not a comparison. */
#define PINNED_VERSION "4.6.11"

static volatile uint64_t sink;

static uint64_t now_ns(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (uint64_t)t.tv_sec * 1000000000ull + (uint64_t)t.tv_nsec;
}

static uint64_t median_of(std::vector<uint64_t> v) {
  if (v.empty()) return 0;
  std::sort(v.begin(), v.end());
  return v[v.size() / 2];
}

template <class T>
static T od_get(simdjson::simdjson_result<T> r, const char *what) {
  T out{};
  auto e = std::move(r).get(out);
  if (e) {
    std::fprintf(stderr, "baseline: reference: %s: %s\n", what,
                 simdjson::error_message(e));
    std::exit(3);
  }
  return out;
}

/* The reference act: the full traversal, with a count so the walk survives
   optimization.  Same shape as `paired-reference.cc`'s `od_count_value`. */
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
  case ondemand::json_type::unknown:
    return 0;
  }
  return 0;
}

static uint64_t reference_act(simdjson::ondemand::parser &parser,
                              const simdjson::padded_string &ps) {
  uint64_t n = 0;
  for (auto doc : parser.iterate(ps)) {
    simdjson::ondemand::value v = od_get(doc, "document");
    n += od_count_value(v);
  }
  return n;
}

int main(int argc, char **argv) {
  if (argc != 3) {
    std::fprintf(stderr, "usage: simdjson-baseline <file> <reps>\n");
    return 1;
  }
  const char *path = argv[1];
  long reps = std::strtol(argv[2], NULL, 10);
  if (reps < 1) {
    std::fprintf(stderr, "baseline: reps must be positive\n");
    return 1;
  }

  std::string bytes;
  {
    FILE *f = std::fopen(path, "rb");
    if (!f) {
      std::fprintf(stderr, "baseline: cannot read %s\n", path);
      return 2;
    }
    char buf[65536];
    size_t got;
    while ((got = std::fread(buf, 1, sizeof buf, f)) > 0) bytes.append(buf, got);
    std::fclose(f);
  }
  if (bytes.empty()) {
    std::fprintf(stderr, "baseline: %s is empty\n", path);
    return 2;
  }

  /* Named, not assumed: the header and the active implementation must both be
     the pinned release, or no row is reported. */
  if (std::strcmp(SIMDJSON_VERSION, PINNED_VERSION) != 0) {
    std::fprintf(stderr, "baseline: header is simdjson %s, not %s\n",
                 SIMDJSON_VERSION, PINNED_VERSION);
    return 2;
  }
  const std::string implName =
      std::string(simdjson::get_active_implementation()->name());
  const char *impl = implName.c_str();

  /* Before the clock: the parser and its buffers, and one accepted act per arm
     so a refused document cannot be timed as a pass. */
  simdjson::ondemand::parser parser;
  {
    simdjson::padded_string ps(bytes.data(), bytes.size());
    uint64_t acc = reference_act(parser, ps);
    if (acc == 0) {
      std::fprintf(stderr, "baseline: the reference walk counted nothing\n");
      return 3;
    }
    sink ^= acc;
  }

  std::vector<uint64_t> pad, parse, both;
  pad.reserve((size_t)reps);
  parse.reserve((size_t)reps);
  both.reserve((size_t)reps);
  uint64_t walked = 0;
  for (long i = 0; i < reps; i++) {
    uint64_t t0 = now_ns();
    simdjson::padded_string ps(bytes.data(), bytes.size());
    uint64_t t1 = now_ns();
    uint64_t acc = reference_act(parser, ps);
    uint64_t t2 = now_ns();
    pad.push_back(t1 - t0);
    parse.push_back(t2 - t1);
    both.push_back(t2 - t0);
    walked += acc;
  }
  sink ^= walked;

  const char *base = std::strrchr(path, '/');
  base = base ? base + 1 : path;
  std::printf("row doc=%s size=%zu path=simdjson version=%s implementation=%s "
              "reps=%ld pad_ns=%llu parse_ns=%llu pad_plus_parse_ns=%llu "
              "walked=%llu\n",
              base, bytes.size(), SIMDJSON_VERSION, impl, reps,
              (unsigned long long)median_of(pad),
              (unsigned long long)median_of(parse),
              (unsigned long long)median_of(both),
              (unsigned long long)walked);
  return 0;
}
