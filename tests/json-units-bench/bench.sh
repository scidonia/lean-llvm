#!/usr/bin/env bash
# Measurement of the three proved stage-1 units, from a warm buffer.
#
#   nix develop -c bash tests/json-units-bench/bench.sh
#
# What is measured.  `kernel/json/s1_block.c`, `kernel/json/entry.c` and
# `kernel/json/utf8.c` are compiled at the measured compiler line the unit routes
# compile them with, and called through `tests/json-units-bench/bench.c` with
# their own ABIs.  No kernel source is edited.  The rows are `s1_masks`,
# `entry_pos8`, `entry_b8`, `utf8_gated` and `utf8_ungated`; `bench.c`'s header
# states what each pass does, how the core clock is measured, and which gates
# the rows hold fixed.
#
# Corpus.  Two classes, both written under the build directory so nothing in the
# tree is modified:
#
#   route-*   the checked-in documents the unit routes use -- the stage-1 route's
#             six documents in `tests/json-s1-masks/corpus/`, and the UTF-8
#             route's raw UTF-8 documents in `tests/json/corpus/utf8-*.json` --
#             each class concatenated in byte order and tiled for measurement to
#             exactly 65,536 bytes.
#   syn-*     three synthetic documents from `gen.c` at a fixed seed,
#             `dense`, `strings` and `utf8`, at 65,536 and 4,194,304 bytes.
#
# The seed is 0x243F6A8885A308D3 (the seed the unit drivers' random arms use),
# so the synthetic bytes are reproducible; every corpus file's size and sha256
# are printed.  Tiling changes where block boundaries and the escape/in-string
# carry fall, which is what the measurement is not about; it is the same byte
# class from the same documents, and the document records it.
#
# Trials.  `bench` runs `BENCH_REPS` repetitions per row and prints the median,
# p10, p90 and extremes of the per-repetition ns/byte; the whole binary is run
# `BENCH_TRIALS` times, so process-to-process variance is visible beside the
# within-row spread.  Each trial is pinned with `taskset` to a CPU; the harness
# reports the CPU it observes and a mismatch is a failure.
#
# Exit status: 0 when every row was measured and the gates held, 1 when a gate
# failed, 3 when the route is not usable (absent compiler, kernel, corpus
# document or `taskset`, or an unbuildable translation unit).
set -uo pipefail
export LC_ALL=C

repo=$(cd "$(dirname "$0")/../.." && pwd)
work=${BENCH_DIR:-$repo/tests/json-units-bench/build}
corpus=$work/corpus
bin=$work/bin
cpus=${BENCH_CPUS:-"0 4"}
trials=${BENCH_TRIALS:-3}
reps=${BENCH_REPS:-51}
seed=${BENCH_SEED:-0x243F6A8885A308D3}
cc=${BENCH_CC:-clang}

# The measured compiler line (`build49.sh:17`), as every unit route uses it.
kflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)

die() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

[ -n "$work" ] && [ "$work" != "/" ] || die "refusing work directory '$work'"
for src in kernel/json/s1_block.c kernel/json/entry.c kernel/json/utf8.c \
           tests/json-units-bench/bench.c tests/json-units-bench/gen.c; do
  [ -f "$repo/$src" ] || die "absent: $src"
done
command -v "$cc" >/dev/null 2>&1 || die "no $cc on PATH; run this under nix develop"
command -v taskset >/dev/null 2>&1 || die "no taskset on PATH"

rm -rf "$work"
mkdir -p "$bin" "$corpus" || die "cannot create $work"

# --- Build ------------------------------------------------------------------
"$cc" -O2 -std=gnu11 -o "$bin/gen" "$repo/tests/json-units-bench/gen.c" \
  2>"$work/gen.cc.err" || { cat "$work/gen.cc.err" >&2; die "gen did not build"; }

for unit in s1_block entry utf8; do
  "$cc" "${kflags[@]}" -I "$repo/kernel/json" -c "$repo/kernel/json/$unit.c" \
    -o "$bin/$unit.o" 2>"$work/$unit.cc.err" ||
    { cat "$work/$unit.cc.err" >&2; die "$unit did not compile at the measured flags"; }
done

"$cc" -O2 -std=gnu11 -o "$bin/bench" "$repo/tests/json-units-bench/bench.c" \
  "$bin/s1_block.o" "$bin/entry.o" "$bin/utf8.o" 2>"$work/bench.cc.err" ||
  { cat "$work/bench.cc.err" >&2; die "bench did not build"; }

kernel_sha=$(sha256sum "$bin/s1_block.o" "$bin/entry.o" "$bin/utf8.o" |
  awk '{ n = split($2, a, "/"); printf "%s=%s ", a[n], substr($1, 1, 16) }')

# --- Corpus -----------------------------------------------------------------
tile() { # <out> <size> <src>...
  local out=$1 size=$2
  shift 2
  : > "$out"
  while [ "$(stat -c %s "$out")" -lt "$size" ]; do
    cat "$@" >> "$out" || die "cat into $out failed"
  done
  head -c "$size" "$out" > "$out.tmp" || die "head into $out failed"
  mv "$out.tmp" "$out"
}

s1_docs=()
while IFS= read -r f; do s1_docs+=("$f"); done < <(
  find "$repo/tests/json-s1-masks/corpus" -mindepth 1 -maxdepth 1 -type f | sort)
u8_docs=()
while IFS= read -r f; do u8_docs+=("$f"); done < <(
  find "$repo/tests/json/corpus" -mindepth 1 -maxdepth 1 -name 'utf8-*.json' -type f | sort)

[ "${#s1_docs[@]}" -gt 0 ] || die "no stage-1 route documents under tests/json-s1-masks/corpus"
[ "${#u8_docs[@]}" -gt 0 ] || die "no UTF-8 route documents under tests/json/corpus"

tile "$corpus/route-s1-64k.json" 65536 "${s1_docs[@]}"
tile "$corpus/route-u8-64k.json" 65536 "${u8_docs[@]}"

for shape in dense strings utf8; do
  for size in 65536 4194304; do
    case $size in
      65536) tag=64k ;;
      4194304) tag=4m ;;
    esac
    "$bin/gen" --shape "$shape" --size "$size" --seed "$seed" \
      --out "$corpus/syn-$shape-$tag.json" 2>"$work/gen.err" ||
      { cat "$work/gen.err" >&2; die "gen $shape/$size failed"; }
  done
done

docargs=()
for f in "$corpus"/*.json; do
  docargs+=(--doc "$(basename "$f" .json)=$f")
done

# --- Host and build record ---------------------------------------------------
printf 'command: nix develop -c bash tests/json-units-bench/bench.sh\n'
printf 'objects: %s\n' "$kernel_sha"
printf 'compiler: %s (%s)\n' "$cc" "$("$cc" --version | head -1)"
printf 'unit flags: %s\n' "${kflags[*]}"
printf 'harness flags: -O2 -std=gnu11\n'
printf 'host: %s\n' "$(uname -srm)"
printf 'cpu: %s\n' "$(awk -F: '/^model name/ { sub(/^ /, "", $2); print $2; exit }' /proc/cpuinfo)"
printf 'cpus online: %s; pinned to: %s\n' "$(nproc)" "$cpus"
printf 'scaling governor: %s\n' "$(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null || echo unknown)"
printf 'perf_event_paranoid: %s (no PMU; cycles are calibrated, see bench.c)\n' \
  "$(cat /proc/sys/kernel/perf_event_paranoid 2>/dev/null || echo unknown)"
for c in $cpus; do
  printf 'cpu%s cache: L1d=%s L2=%s L3=%s\n' "$c" \
    "$(cat "/sys/devices/system/cpu/cpu$c/cache/index0/size" 2>/dev/null || echo '?')" \
    "$(cat "/sys/devices/system/cpu/cpu$c/cache/index2/size" 2>/dev/null || echo '?')" \
    "$(cat "/sys/devices/system/cpu/cpu$c/cache/index3/size" 2>/dev/null || echo '?')"
done
printf '\ncorpus seed: %s\n' "$seed"
printf '%-18s %10s %s\n' file bytes sha256
for f in "$corpus"/*.json; do
  printf '%-18s %10s %s\n' "$(basename "$f")" "$(wc -c < "$f")" \
    "$(sha256sum "$f" | cut -d' ' -f1)"
done
printf '\n'

# --- Measure ----------------------------------------------------------------
for cpu in $cpus; do
  for trial in $(seq 1 "$trials"); do
    printf 'trial cpu=%s trial=%s/%s\n' "$cpu" "$trial" "$trials"
    out=$work/bench.$cpu.$trial.out
    err=$work/bench.$cpu.$trial.err
    status=0
    taskset -c "$cpu" "$bin/bench" --reps "$reps" "${docargs[@]}" \
      >"$out" 2>"$err" || status=$?
    cat "$out"
    if [ -s "$err" ]; then cat "$err" >&2; fi
    if [ "$status" -ne 0 ]; then
      printf 'FAIL: bench exited %s on cpu %s trial %s\n' "$status" "$cpu" "$trial" >&2
      exit 1
    fi
    observed=$(awk '$1 == "instrument" {
        for (i = 2; i <= NF; i++) { split($i, a, "="); if (a[1] == "cpu") print a[2] }
      }' "$out")
    if [ "$observed" != "$cpu" ]; then
      printf 'FAIL: pin asked for cpu%s, the harness observed cpu%s\n' "$cpu" "$observed" >&2
      exit 1
    fi
  done
done
printf '\n'

# --- Aggregate --------------------------------------------------------------
# One summary row per (cpu, document, unit): the median and the minimum/maximum
# of the trial medians, the median of the rows' own p10-p90 spread, and the
# median calibrated core clock.  Checksums are asserted two ways: one per row
# across trials, and one per document and unit across every trial and both core
# classes, so a row that reached different code on another core fails rather
# than printing a number.  The pin is asserted against the CPU the harness
# reports.
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
  $1 == "doc" {
    parse()
    if (!(kv["name"] in docseen)) {
      docseen[kv["name"]] = 1
      printf "CORPUS name=%s bytes=%s blocks=%s structural_per_block=%s ascii_vectors=%s vectors=%s utf8_word=%s\n",
        kv["name"], kv["bytes"], kv["blocks"], kv["structural_per_block"],
        kv["ascii_vectors"], kv["vectors"], kv["utf8_word"]
    }
    next
  }
  $1 == "row" {
    parse()
    key = kv["cpu"] SUBSEP kv["doc"] SUBSEP kv["unit"]
    if (!(key in n)) { order[++nkeys] = key }
    cpuset[kv["cpu"]] = 1
    n[key]++
    t = n[key]
    gbps[key, t] = kv["gbps"] + 0
    cyc[key, t] = kv["cycles_per_byte"] + 0
    ghz[key, t] = kv["core_ghz"] + 0
    if (kv["median_ns"] + 0 > 0)
      spread[key, t] = 100.0 * ((kv["p90_ns"] + 0) - (kv["p10_ns"] + 0)) / (kv["median_ns"] + 0)
    else
      spread[key, t] = 0
    bytes[key] = kv["bytes"] + 0
    blocks[key] = kv["blocks"] + 0
    localcs[key, kv["checksum"]] = 1
    rowcs[kv["doc"] SUBSEP kv["unit"], kv["checksum"]] = 1
    rowseenset[kv["doc"] SUBSEP kv["unit"]] = 1
    next
  }
  END {
    bad = 0
    ndocs = 0
    for (d in docseen) ndocs++
    ncpu = 0
    for (c2 in cpuset) ncpu++
    if (nkeys != ndocs * 5 * ncpu) {
      printf "FAIL: %d row(s) for %d document(s) x 5 units x %d CPU(s)\n",
        nkeys, ndocs, ncpu > "/dev/stderr"
      bad = 1
    }
    for (key in n) {
      m = n[key]
      for (i = 1; i <= m; i++) { g[i] = gbps[key, i]; c[i] = cyc[key, i]; s[i] = spread[key, i]; z[i] = ghz[key, i] }
      sortn(g, m); sortn(c, m); sortn(s, m); sortn(z, m)
      cnt = 0
      for (c2 in localcs) {
        split(c2, p, SUBSEP)
        if ((p[1] SUBSEP p[2] SUBSEP p[3]) == key) cnt++
      }
      if (cnt != 1) {
        printf "FAIL: %s printed %d distinct checksums across its trials\n", key, cnt > "/dev/stderr"
        bad = 1
      }
    }
    for (r in rowseenset) {
      delete cs
      cnt = 0
      for (c2 in rowcs) {
        split(c2, p, SUBSEP)
        if ((p[1] SUBSEP p[2]) == r) cs[p[3]] = 1
      }
      for (v in cs) cnt++
      if (cnt != 1) {
        printf "FAIL: %s produced %d distinct checksums across trials and CPUs\n", r, cnt > "/dev/stderr"
        bad = 1
      }
    }
    printf "SUMMARY cpu doc unit bytes trials gbps gbps_min gbps_max cycles_per_byte rep_spread_pct core_ghz\n"
    for (k = 1; k <= nkeys; k++) {
      key = order[k]
      m = n[key]
      for (i = 1; i <= m; i++) { g[i] = gbps[key, i]; c[i] = cyc[key, i]; s[i] = spread[key, i]; z[i] = ghz[key, i] }
      sortn(g, m); sortn(c, m); sortn(s, m); sortn(z, m)
      split(key, p, SUBSEP)
      printf "%s %s %s %d %d %.3f %.3f %.3f %.4f %.2f %.3f\n",
        p[1], p[2], p[3], bytes[key], m, med(g, m), g[1], g[m],
        med(c, m), med(s, m), med(z, m)
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
printf 'ok: every row checksum is stable across its trials, and across both core classes\n'
printf 'ok: entry_pos8 and entry_b8 returned the stream total on every document; the gated and ungated UTF-8 words agree\n'
printf 'note: cycles/byte = median ns/byte x the core clock calibrated immediately before the row; no PMU on this host\n'
