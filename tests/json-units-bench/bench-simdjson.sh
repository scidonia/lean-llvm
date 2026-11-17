#!/usr/bin/env bash
# simdjson 5.0.5's stage 1 and full parse, over the corpus the three proved
# stage-1 units are measured on.
#
#   nix develop -c bash tests/json-units-bench/bench-simdjson.sh
#
# What is measured.  `simdjson-baseline.cc` is compiled at the units' measured
# compiler line with the C++ standard and linked against the realised nix
# simdjson 5.0.5 dev output and shared library.  The rows are:
#
#   pad     one `padded_string` construction: simdjson's staging, not stage 1
#   stage1  one `dom_parser_implementation::stage1` call: classification, the
#           string/escape state, UTF-8 validation and the structural-index
#           array
#   parse   one on-demand `iterate` plus the full value traversal: stage 1 plus
#           the lazy stage 2
#
# `stage1` is the stage-for-stage counterpart of the units.  `parse` is a
# parser and is reported separately; it is not a like-for-like figure for three
# units.  `pad` is reported so the stage-1 row's exclusion of staging is
# visible.
#
# Corpus.  The eight documents of `tests/json-units-bench/transcript.txt` are
# used, byte for byte: the six route documents tiled to 65,536 bytes and the
# three synthetic shapes at 65,536 and 4,194,304 bytes from `gen.c` at seed
# 0x243F6A8885A308D3.  Every file is checked against the size and sha256 the
# units' transcript records, and a mismatch is a setup failure, not a row.  If
# the units' build directory holds the corpus it is reused; otherwise this
# script regenerates it with the same procedure and checks the same hashes.
#
# Discipline.  The binary is pinned with `taskset`, the corpus is staged once
# and warmed before the clock, each arm is 51 repetitions, and the whole binary
# runs three times per CPU.  Medians, with the minimum and maximum of the three
# trial medians, are reported per row; the row itself carries the p10-p90
# spread.  The harness exits 3 rather than printing a number when a timed pass
# disagrees with its warm-up, and the aggregation exits 1 when a (document,
# arm) checksum, status or error differs across trials or core classes.
#
# Provenance.  The two store outputs were realised with:
#
#   nix build --no-link --print-out-paths 'nixpkgs#simdjson.dev'
#   nix build --no-link --print-out-paths 'nixpkgs#simdjson'
#
# On a host that does not already hold them, those fetches need network access.
# This script does not fetch: it verifies the recorded paths and refuses to run
# if either is absent.
#
# Environment: BENCH_CPUS (default "0 4"), BENCH_TRIALS (3), BENCH_REPS (51),
# BENCH_DIR, BENCH_CORPUS, BENCH_CC (clang), BENCH_CXX (clang++),
# SIMDJSON_DEV and SIMDJSON_LIB (the store paths above).
#
# Exit status: 0 when every row was measured and the gates held, 1 when a gate
# failed, 3 when the route is not usable (absent compiler, store output,
# corpus document or `taskset`, or an unbuildable translation unit).
set -uo pipefail
export LC_ALL=C

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
work=${BENCH_DIR:-$repo/tests/json-units-bench/build-simdjson}
bin=$work/bin
cpus=${BENCH_CPUS:-"0 4"}
trials=${BENCH_TRIALS:-3}
reps=${BENCH_REPS:-51}
seed=${BENCH_SEED:-0x243F6A8885A308D3}
cc=${BENCH_CC:-clang}
cxx=${BENCH_CXX:-clang++}
dev=${SIMDJSON_DEV:-/nix/store/m2i8165bayxxgzj3fbvdg6gihz6na93d-simdjson-5.0.5-dev}
lib=${SIMDJSON_LIB:-/nix/store/jglxdk9y0yfk3mc9dbr675pfmv42a89y-simdjson-5.0.5}

die() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

# The compiler line the units are measured at (`bench.sh`'s `kflags`), with the
# C++ standard this harness needs.  The library is not rebuilt at these flags;
# see the header the script prints and the note it carries.
cxxflags=(-O3 -march=x86-64-v3 -mpclmul -std=c++17 -falign-loops=64 -falign-functions=64)

[ -n "$work" ] && [ "$work" != "/" ] || die "refusing work directory '$work'"
[ -f "$here/simdjson-baseline.cc" ] || die "absent: tests/json-units-bench/simdjson-baseline.cc"
[ -f "$here/gen.c" ] || die "absent: tests/json-units-bench/gen.c"
command -v "$cc" >/dev/null 2>&1 || die "no $cc on PATH; run this under nix develop"
command -v "$cxx" >/dev/null 2>&1 || die "no $cxx on PATH; run this under nix develop"
command -v taskset >/dev/null 2>&1 || die "no taskset on PATH"

header=$dev/include/simdjson.h
solib=$lib/lib/libsimdjson.so.34.0.0
[ -f "$header" ] || die "absent: $header
  realise it with: nix build --no-link --print-out-paths 'nixpkgs#simdjson.dev'"
[ -f "$solib" ] || die "absent: $solib
  realise it with: nix build --no-link --print-out-paths 'nixpkgs#simdjson'"

ver=$(sed -n 's/^#define SIMDJSON_VERSION "\(.*\)"/\1/p' "$header" | head -1)
[ "$ver" = "5.0.5" ] || die "header is simdjson '$ver', not 5.0.5"
nixver=$(nix eval --raw 'nixpkgs#simdjson.version' 2>/dev/null || echo unknown)

rm -rf "$work"
mkdir -p "$bin" || die "cannot create $work"

# --- Corpus -----------------------------------------------------------------
# Size and sha256 as `tests/json-units-bench/transcript.txt` records them.  A
# document that differs is not the units' document and is not timed.
expected="route-s1-64k.json 65536 41f918853d55dad0e05d3ec03682e037925759031632f045a755db5a5173535c
route-u8-64k.json 65536 d14a6a6842610aaaf2bdd13a292730f156cf5c6c5724eddae93effa9b697f18c
syn-dense-4m.json 4194304 243e8f36f14e1acb5694d8c873c18f46a86a073c768944abaa94cfb57883accd
syn-dense-64k.json 65536 3d9e0237ec66adb2d77848a24f1998fa4b56b4dbe77a11431b02176fcd162995
syn-strings-4m.json 4194304 3ce71d559eef1d11e83272b999fe944f49cb5bef656b5ec863044ed8f1b5cd27
syn-strings-64k.json 65536 bd007090d7a5ab09a1fc69c0b96879f101dbf8b3f13a300d7d3e46127d26fb12
syn-utf8-4m.json 4194304 2091fc28bf071e8a7311f43754d8bb82cb2ddef54360be8570c46b7a94d298f2
syn-utf8-64k.json 65536 f95f4aeaac083d5d97ff98f9ad6aa09e4ed8c905d89e1bf3a3177179533400a4"

corpus_ok() { # <dir>
  local dir=$1 name size sha
  while read -r name size sha; do
    [ -n "$name" ] || continue
    [ -f "$dir/$name" ] || return 1
    [ "$(stat -c %s "$dir/$name")" = "$size" ] || return 1
    [ "$(sha256sum "$dir/$name" | cut -d' ' -f1)" = "$sha" ] || return 1
  done <<<"$expected"
  return 0
}

tile() { # <out> <size> <src>...
  local out=$1 size=$2
  shift 2
  : >"$out"
  while [ "$(stat -c %s "$out")" -lt "$size" ]; do
    cat "$@" >>"$out" || die "cat into $out failed"
  done
  head -c "$size" "$out" >"$out.tmp" || die "head into $out failed"
  mv "$out.tmp" "$out"
}

generate_corpus() { # <dir>
  local dir=$1
  mkdir -p "$dir" || die "cannot create $dir"
  "$cc" -O2 -std=gnu11 -o "$bin/gen" "$here/gen.c" 2>"$work/gen.cc.err" ||
    { cat "$work/gen.cc.err" >&2; die "gen did not build"; }

  local s1_docs=() u8_docs=()
  while IFS= read -r f; do s1_docs+=("$f"); done < <(
    find "$repo/tests/json-s1-masks/corpus" -mindepth 1 -maxdepth 1 -type f | sort)
  while IFS= read -r f; do u8_docs+=("$f"); done < <(
    find "$repo/tests/json/corpus" -mindepth 1 -maxdepth 1 -name 'utf8-*.json' -type f | sort)
  [ "${#s1_docs[@]}" -gt 0 ] || die "no stage-1 route documents"
  [ "${#u8_docs[@]}" -gt 0 ] || die "no UTF-8 route documents"

  tile "$dir/route-s1-64k.json" 65536 "${s1_docs[@]}"
  tile "$dir/route-u8-64k.json" 65536 "${u8_docs[@]}"

  local shape size tag
  for shape in dense strings utf8; do
    for size in 65536 4194304; do
      case $size in
        65536) tag=64k ;;
        4194304) tag=4m ;;
      esac
      "$bin/gen" --shape "$shape" --size "$size" --seed "$seed" \
        --out "$dir/syn-$shape-$tag.json" 2>"$work/gen.err" ||
        { cat "$work/gen.err" >&2; die "gen $shape/$size failed"; }
    done
  done
}

if [ -n "${BENCH_CORPUS:-}" ]; then
  corpus=$BENCH_CORPUS
  corpus_source="BENCH_CORPUS=$corpus"
  corpus_ok "$corpus" || die "BENCH_CORPUS does not hold the units' eight documents"
elif [ -d "$repo/tests/json-units-bench/build/corpus" ] &&
     corpus_ok "$repo/tests/json-units-bench/build/corpus"; then
  corpus=$repo/tests/json-units-bench/build/corpus
  corpus_source="reused tests/json-units-bench/build/corpus (the units' corpus)"
else
  corpus=$work/corpus
  corpus_source="generated under $corpus"
  generate_corpus "$corpus"
  corpus_ok "$corpus" || die "the regenerated corpus does not match the units' hashes"
fi

# --- Build ------------------------------------------------------------------
"$cxx" "${cxxflags[@]}" -I "$dev/include" "$here/simdjson-baseline.cc" \
  -L "$lib/lib" -Wl,-rpath,"$lib/lib" -lsimdjson -o "$bin/simdjson-baseline" \
  2>"$work/simdjson.cc.err" ||
  { cat "$work/simdjson.cc.err" >&2; die "simdjson-baseline did not build"; }

header_sha=$(sha256sum "$header" | cut -d' ' -f1)
lib_sha=$(sha256sum "$solib" | cut -d' ' -f1)

# --- Host and build record ---------------------------------------------------
printf 'command: nix develop -c bash tests/json-units-bench/bench-simdjson.sh\n'
printf 'simdjson: %s (header); nixpkgs simdjson.version=%s\n' "$ver" "$nixver"
printf 'simdjson dev: %s\n' "$dev"
printf 'simdjson lib: %s\n' "$lib"
printf 'library: %s sha256=%s\n' "$(basename "$solib")" "$lib_sha"
printf 'header: simdjson.h sha256=%s\n' "$header_sha"
printf 'provenance: nix build --no-link --print-out-paths '\''nixpkgs#simdjson.dev'\''\n'
printf 'provenance: nix build --no-link --print-out-paths '\''nixpkgs#simdjson'\''\n'
printf 'compiler: %s (%s)\n' "$cxx" "$("$cxx" --version | head -1)"
printf 'harness flags: %s\n' "${cxxflags[*]}"
printf 'library note: the shared library is the realised nix build, not recompiled at\n'
printf '              these flags; stage1 is the library'"'"'s code, while the on-demand\n'
printf '              traversal in parse is compiled here at the flags above.\n'
printf 'host: %s\n' "$(uname -srm)"
printf 'cpu: %s\n' "$(awk -F: '/^model name/ { sub(/^ /, "", $2); print $2; exit }' /proc/cpuinfo)"
printf 'cpus online: %s; pinned to: %s\n' "$(nproc)" "$cpus"
printf 'scaling governor: %s\n' "$(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null || echo unknown)"
printf 'perf_event_paranoid: %s (no PMU; cycles are calibrated, see simdjson-baseline.cc)\n' \
  "$(cat /proc/sys/kernel/perf_event_paranoid 2>/dev/null || echo unknown)"
for c in $cpus; do
  printf 'cpu%s cache: L1d=%s L2=%s L3=%s\n' "$c" \
    "$(cat "/sys/devices/system/cpu/cpu$c/cache/index0/size" 2>/dev/null || echo '?')" \
    "$(cat "/sys/devices/system/cpu/cpu$c/cache/index2/size" 2>/dev/null || echo '?')" \
    "$(cat "/sys/devices/system/cpu/cpu$c/cache/index3/size" 2>/dev/null || echo '?')"
done
printf '\ncorpus: %s\n' "$corpus_source"
printf 'corpus seed: %s (synthetic documents; route documents tiled)\n' "$seed"
printf '%-18s %10s %s\n' file bytes sha256
for f in "$corpus"/*.json; do
  printf '%-18s %10s %s\n' "$(basename "$f")" "$(wc -c <"$f")" \
    "$(sha256sum "$f" | cut -d' ' -f1)"
done
printf '\n'

# --- Measure ----------------------------------------------------------------
# The order is the units' corpus order, so a later reader can line the rows up
# with `transcript.txt` without re-sorting.
docargs=()
for name in route-s1-64k route-u8-64k syn-dense-4m syn-dense-64k \
            syn-strings-4m syn-strings-64k syn-utf8-4m syn-utf8-64k; do
  docargs+=(--doc "$name=$corpus/$name.json")
done

for cpu in $cpus; do
  for trial in $(seq 1 "$trials"); do
    printf 'trial cpu=%s trial=%s/%s\n' "$cpu" "$trial" "$trials"
    out=$work/bench.$cpu.$trial.out
    err=$work/bench.$cpu.$trial.err
    status=0
    taskset -c "$cpu" "$bin/simdjson-baseline" --reps "$reps" "${docargs[@]}" \
      >"$out" 2>"$err" || status=$?
    cat "$out"
    if [ -s "$err" ]; then cat "$err" >&2; fi
    if [ "$status" -ne 0 ]; then
      printf 'FAIL: simdjson-baseline exited %s on cpu %s trial %s\n' \
        "$status" "$cpu" "$trial" >&2
      exit 1
    fi
    observed=$(awk '$1 == "instrument" {
        for (i = 2; i <= NF; i++) { split($i, a, "="); if (a[1] == "cpu") print a[2] }
      }' "$out")
    if [ "$observed" != "$cpu" ]; then
      printf 'FAIL: pin asked for cpu%s, the harness observed cpu%s\n' \
        "$cpu" "$observed" >&2
      exit 1
    fi
  done
done
printf '\n'

# --- Aggregate --------------------------------------------------------------
# One summary row per (cpu, document, arm): the median and the minimum/maximum
# of the trial medians, the median within-row p10-p90 spread, and the median
# calibrated core clock.  Checksums, statuses and errors are asserted two ways:
# per row across trials, and per (document, arm) across every trial and both
# core classes.  A refused parse keeps its row; its `status=refused` is part of
# the key's stable identity, and only `status=ok` parse rows are full-parse
# figures.
awk '
  function parse(   i, a) {
    delete kv
    for (i = 2; i <= NF; i++) { split($i, a, "="); kv[a[1]] = a[2] }
  }
  function sortn(arr, n,   i, j, t) {
    for (i = 2; i <= n; i++) {
      t = arr[i]
      for (j = i - 1; j >= 1 && arr[j] > t; j--) arr[j + 1] = arr[j]
      arr[j + 1] = t
    }
  }
  function med(arr, n) {
    if (n % 2) return arr[(n + 1) / 2]
    return 0.5 * (arr[n / 2] + arr[n / 2 + 1])
  }
  function key_of(kv) { return kv["cpu"] SUBSEP kv["doc"] SUBSEP kv["arm"] }
  $1 == "instrument" {
    parse()
    impl[kv["implementation"]] = 1
    next
  }
  $1 == "doc" {
    parse()
    if (!(kv["name"] in docseen)) {
      docseen[kv["name"]] = 1
      ndocs++
    }
    next
  }
  $1 == "row" {
    parse()
    key = key_of(kv)
    if (!(key in n)) { order[++nkeys] = key }
    cpuset[kv["cpu"]] = 1
    n[key]++
    t = n[key]
    gbps[key, t] = kv["gbps"] + 0
    npb[key, t] = kv["ns_per_byte"] + 0
    cyc[key, t] = kv["cycles_per_byte"] + 0
    ghz[key, t] = kv["core_ghz"] + 0
    if (kv["median_ns"] + 0 > 0)
      spread[key, t] = 100.0 * ((kv["p90_ns"] + 0) - (kv["p10_ns"] + 0)) / (kv["median_ns"] + 0)
    else
      spread[key, t] = 0
    bytes[key] = kv["bytes"] + 0
    localcs[key, kv["checksum"]] = 1
    localst[key, kv["status"]] = 1
    localer[key, kv["error"]] = 1
    rowcs[kv["doc"], kv["arm"], kv["checksum"]] = 1
    rowst[kv["doc"], kv["arm"], kv["status"]] = 1
    rower[kv["doc"], kv["arm"], kv["error"]] = 1
    pairs[kv["doc"] SUBSEP kv["arm"]] = 1
    next
  }
  END {
    bad = 0
    impln = 0
    for (i in impl) impln++
    if (impln != 1) {
      printf "FAIL: %d active implementations were recorded, not 1\n", impln > "/dev/stderr"
      bad = 1
    }
    ncpu = 0
    for (c in cpuset) ncpu++
    if (ndocs != 8) {
      printf "FAIL: %d document(s), not the units corpus of 8\n", ndocs > "/dev/stderr"
      bad = 1
    }
    if (nkeys != ndocs * 3 * ncpu) {
      printf "FAIL: %d row(s) for %d document(s) x 3 arms x %d CPU(s)\n",
        nkeys, ndocs, ncpu > "/dev/stderr"
      bad = 1
    }
    for (key in n) {
      delete cs
      for (c in localcs) {
        split(c, p, SUBSEP)
        if ((p[1] SUBSEP p[2] SUBSEP p[3]) == key) cs[p[4]] = 1
      }
      cnt = 0; for (v in cs) cnt++
      if (cnt != 1) {
        printf "FAIL: %s printed %d distinct checksums across its trials\n", key, cnt > "/dev/stderr"
        bad = 1
      }
      delete cs
      for (c in localst) {
        split(c, p, SUBSEP)
        if ((p[1] SUBSEP p[2] SUBSEP p[3]) == key) cs[p[4]] = 1
      }
      cnt = 0; for (v in cs) cnt++
      if (cnt != 1) {
        printf "FAIL: %s printed %d distinct statuses across its trials\n", key, cnt > "/dev/stderr"
        bad = 1
      }
      delete cs
      for (c in localer) {
        split(c, p, SUBSEP)
        if ((p[1] SUBSEP p[2] SUBSEP p[3]) == key) cs[p[4]] = 1
      }
      cnt = 0; for (v in cs) cnt++
      if (cnt != 1) {
        printf "FAIL: %s printed %d distinct errors across its trials\n", key, cnt > "/dev/stderr"
        bad = 1
      }
    }
    for (r in pairs) {
      delete cs
      for (c in rowcs) {
        split(c, p, SUBSEP)
        if ((p[1] SUBSEP p[2]) == r) cs[p[3]] = 1
      }
      cnt = 0; for (v in cs) cnt++
      if (cnt != 1) {
        printf "FAIL: %s produced %d distinct checksums across trials and CPUs\n", r, cnt > "/dev/stderr"
        bad = 1
      }
      delete cs
      for (c in rowst) {
        split(c, p, SUBSEP)
        if ((p[1] SUBSEP p[2]) == r) cs[p[3]] = 1
      }
      cnt = 0; for (v in cs) cnt++
      if (cnt != 1) {
        printf "FAIL: %s produced %d distinct statuses across trials and CPUs\n", r, cnt > "/dev/stderr"
        bad = 1
      }
      delete cs
      for (c in rower) {
        split(c, p, SUBSEP)
        if ((p[1] SUBSEP p[2]) == r) cs[p[3]] = 1
      }
      cnt = 0; for (v in cs) cnt++
      if (cnt != 1) {
        printf "FAIL: %s produced %d distinct errors across trials and CPUs\n", r, cnt > "/dev/stderr"
        bad = 1
      }
    }
    printf "SUMMARY cpu doc arm bytes trials status error gbps gbps_min gbps_max ns_per_byte cycles_per_byte rep_spread_pct core_ghz\n"
    for (k = 1; k <= nkeys; k++) {
      key = order[k]
      m = n[key]
      for (i = 1; i <= m; i++) {
        gv[i] = gbps[key, i]
        bv[i] = npb[key, i]
        cv[i] = cyc[key, i]
        sv[i] = spread[key, i]
        zv[i] = ghz[key, i]
      }
      sortn(gv, m); sortn(bv, m); sortn(cv, m); sortn(sv, m); sortn(zv, m)
      split(key, p, SUBSEP)
      st = ""; er = ""
      for (v in localst) {
        split(v, q, SUBSEP)
        if ((q[1] SUBSEP q[2] SUBSEP q[3]) == key) st = q[4]
      }
      for (v in localer) {
        split(v, q, SUBSEP)
        if ((q[1] SUBSEP q[2] SUBSEP q[3]) == key) er = q[4]
      }
      printf "%s %s %s %d %d %s %s %.3f %.3f %.3f %.5f %.4f %.2f %.3f\n",
        p[1], p[2], p[3], bytes[key], m, st, er,
        med(gv, m), gv[1], gv[m], med(bv, m), med(cv, m), med(sv, m), med(zv, m)
    }
    exit bad
  }
' "$work"/bench.*.out
status=$?
if [ "$status" -ne 0 ]; then
  printf 'FAIL: the aggregation gates did not hold\n' >&2
  exit 1
fi

# --- Report -----------------------------------------------------------------
printf 'ok: %s row(s) measured over %s CPU(s), %s trial(s), %s repetition(s) per row\n' \
  "$(grep -h '^row ' "$work"/bench.*.out | wc -l)" \
  "$(printf '%s' "$cpus" | wc -w)" "$trials" "$reps"
printf 'ok: every (document, arm) checksum, status and error is stable across its trials and both core classes\n'
printf 'ok: one active implementation was recorded on every trial\n'
printf 'note: cycles/byte = median ns/byte x the core clock calibrated immediately before the row; no PMU on this host\n'
printf 'note: `parse` rows with status=refused time a refusal, not a full parse; the route corpus is tiled and\n'
printf '      route-u8 is invalid UTF-8, so only the six synthetic documents have a full-parse row\n'
