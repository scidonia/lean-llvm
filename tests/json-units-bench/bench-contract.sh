#!/usr/bin/env bash
# The contracted stage-1 prototype against the current pipeline and simdjson
# 5.0.5, paired in one process.
#
#   nix develop -c bash tests/json-units-bench/bench-contract.sh
#
# What is measured.  `tests/json-units-bench/bench-contract.c` is a bench-only
# single pass over the document: the classifier's six masks, both carries and
# the entry word stay in registers, the entry positions and the escape
# positions are written and nothing else.  It is compiled at the units'
# measured compiler line.  `bench-contract.cc` stages each document once,
# gates the prototype against the tree's own `leanllvm_json_pipeline` and the
# prototype's classifier against `leanllvm_json_s1_masks` on every block, then
# times eight arms from one warm buffer in one process:
#
#   contract_core  the prototype, escape list off
#   contract_list  the prototype, escape list on
#   contract_full  the prototype, escape list on, UTF-8 unit after the loop
#   staged_core    `kernel/json/pipeline.c`'s loop, escape list off
#   staged_list    the same loop, escape list on
#   staged_full    the same loop, escape list on, UTF-8 unit after the loop
#   split_core     masks and entry word into an `ent` array, one emitter call
#   stage1         simdjson 5.0.5's stage 1 (classification, strings, UTF-8,
#                  structural indexes)
#
# The ratios are per-round pairs, so a drift inside a round cancels: below 1
# the numerator takes less time.  `contract_full / stage1` is the parity row;
# `contract_core / staged_core` is the fusion delta at the same contract.
#
# Corpus.  The same eight documents `bench.sh` and `bench-simdjson.sh` use:
# the stage-1 route's six documents and the UTF-8 route's raw documents, each
# class tiled to 65,536 bytes, and the three fixed-seed synthetic shapes at
# 65,536 and 4,194,304 bytes.  Sizes and sha256 are printed.
#
# simdjson.  The realised 5.0.5 dev header and shared library, the same two
# store outputs `bench-simdjson.sh` names (`SIMDJSON_DEV`, `SIMDJSON_LIB`); the
# header version is checked before compiling and the run-time implementation
# name is printed.
#
# Exit status: 0 when every gate held and every row was measured, 1 on a gate
# or aggregation failure, 3 when the route is not usable.
set -uo pipefail
export LC_ALL=C

repo=$(cd "$(dirname "$0")/../.." && pwd)
here=$repo/tests/json-units-bench
work=${BENCH_DIR:-$here/build-contract}
corpus=$work/corpus
bin=$work/bin
cpus=${BENCH_CPUS:-"0"}
trials=${BENCH_TRIALS:-3}
rounds=${BENCH_ROUNDS:-15}
seed=${BENCH_SEED:-0x243F6A8885A308D3}
cc=${BENCH_CC:-clang}
cxx=${BENCH_CXX:-clang++}
dev=${SIMDJSON_DEV:-/nix/store/m2i8165bayxxgzj3fbvdg6gihz6na93d-simdjson-5.0.5-dev}
lib=${SIMDJSON_LIB:-/nix/store/jglxdk9y0yfk3mc9dbr675pfmv42a89y-simdjson-5.0.5}

die() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

[ -n "$work" ] && [ "$work" != "/" ] || die "refusing work directory '$work'"
for src in kernel/json/s1_block.c kernel/json/entry.c kernel/json/escape.c \
           kernel/json/utf8.c kernel/json/pipeline.c kernel/json/stage2.c \
           tests/json-units-bench/bench-contract.c \
           tests/json-units-bench/bench-contract.cc \
           tests/json-units-bench/gen.c; do
  [ -f "$repo/$src" ] || die "absent: $src"
done
command -v "$cc" >/dev/null 2>&1 || die "no $cc on PATH; run this under nix develop"
command -v "$cxx" >/dev/null 2>&1 || die "no $cxx on PATH; run this under nix develop"
command -v taskset >/dev/null 2>&1 || die "no taskset on PATH"

header=$dev/include/simdjson.h
[ -f "$header" ] || die "missing $header; realise it with: nix build --no-link --print-out-paths 'nixpkgs#simdjson.dev'"
[ -d "$lib/lib" ] || die "missing $lib/lib; realise it with: nix build --no-link --print-out-paths 'nixpkgs#simdjson'"
ver=$(awk '/#define SIMDJSON_VERSION / { gsub(/"/, "", $3); print $3; exit }' "$header")
[ "$ver" = "5.0.5" ] || die "header is simdjson '$ver', not 5.0.5"

rm -rf "$work"
mkdir -p "$bin" "$corpus" || die "cannot create $work"

kflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)
cxxflags=(-O3 -march=x86-64-v3 -mpclmul -std=c++17 -falign-loops=64 -falign-functions=64)

"$cc" -O2 -std=gnu11 -o "$bin/gen" "$here/gen.c" 2>"$work/gen.cc.err" ||
  { cat "$work/gen.cc.err" >&2; die "gen did not build"; }

for src in s1_block entry escape utf8 pipeline stage2; do
  "$cc" "${kflags[@]}" -I "$repo/kernel/json" -c "$repo/kernel/json/$src.c" \
    -o "$bin/$src.o" 2>"$work/$src.cc.err" ||
    { cat "$work/$src.cc.err" >&2; die "kernel/json/$src.c did not compile at the measured flags"; }
done

"$cc" "${kflags[@]}" -I "$repo/kernel/json" \
  -c "$here/bench-contract.c" -o "$bin/bench-contract.o" \
  2>"$work/proto.cc.err" ||
  { cat "$work/proto.cc.err" >&2; die "bench-contract.c did not compile at the measured flags"; }

"$cxx" "${cxxflags[@]}" -I "$dev/include" -I "$repo/kernel/json" \
  "$here/bench-contract.cc" "$bin/bench-contract.o" "$bin/s1_block.o" \
  "$bin/entry.o" "$bin/escape.o" "$bin/utf8.o" "$bin/pipeline.o" \
  "$bin/stage2.o" -L "$lib/lib" -Wl,-rpath,"$lib/lib" -lsimdjson \
  -o "$bin/bench-contract" 2>"$work/harness.cc.err" ||
  { cat "$work/harness.cc.err" >&2; die "bench-contract.cc did not build"; }

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

s1_docs=(); while IFS= read -r f; do s1_docs+=("$f"); done < <(
  find "$repo/tests/json-s1-masks/corpus" -mindepth 1 -maxdepth 1 -type f | sort)
u8_docs=(); while IFS= read -r f; do u8_docs+=("$f"); done < <(
  find "$repo/tests/json/corpus" -mindepth 1 -maxdepth 1 -name 'utf8-*.json' -type f | sort)
[ "${#s1_docs[@]}" -gt 0 ] || die "no stage-1 route documents"
[ "${#u8_docs[@]}" -gt 0 ] || die "no UTF-8 route documents"

tile "$corpus/route-s1-64k.json" 65536 "${s1_docs[@]}"
tile "$corpus/route-u8-64k.json" 65536 "${u8_docs[@]}"
for shape in dense strings utf8; do
  for size in 65536 4194304; do
    case $size in
      65536) tag=64k ;;
      4194304) tag=4m ;;
    esac
    "$bin/gen" --shape "$shape" --size "$size" --seed "$seed" \
      --out "$corpus/syn-$shape-$tag.json" || die "gen failed: $shape $tag"
  done
done

docargs=()
for f in "$corpus"/*.json; do docargs+=(--doc "$(basename "$f" .json)=$f"); done

# --- Header -----------------------------------------------------------------
printf 'command: nix develop -c bash tests/json-units-bench/bench-contract.sh\n'
printf 'compiler: %s (%s)\n' "$cc" "$("$cc" --version | head -1)"
printf 'compiler (harness): %s\n' "$("$cxx" --version | head -1)"
printf 'unit flags: %s\n' "${kflags[*]}"
printf 'harness flags: %s\n' "${cxxflags[*]}"
printf 'simdjson: %s header %s; library %s\n' "$ver" "$header" "$lib/lib/libsimdjson.so.34.0.0"
printf 'header sha256: %s\n' "$(sha256sum "$header" | cut -d' ' -f1)"
printf 'library sha256: %s\n' "$(sha256sum "$lib/lib/libsimdjson.so.34.0.0" | cut -d' ' -f1)"
printf 'prototype object sha256: %s\n' "$(sha256sum "$bin/bench-contract.o" | cut -d' ' -f1)"
printf 'host: %s\n' "$(uname -srm)"
printf 'cpu: %s\n' "$(awk -F: '/^model name/ { sub(/^ /, "", $2); print $2; exit }' /proc/cpuinfo)"
printf 'cpus online: %s; pinned to: %s\n' "$(nproc)" "$cpus"
printf 'governor: %s\n' "$(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null || echo unknown)"
printf 'load average at start: %s\n' "$(cut -d' ' -f1-3 /proc/loadavg)"
printf '\ncorpus seed: %s\n' "$seed"
printf '%-20s %10s %s\n' file bytes sha256
for f in "$corpus"/*.json; do
  printf '%-20s %10s %s\n' "$(basename "$f")" "$(stat -c %s "$f")" \
    "$(sha256sum "$f" | cut -d' ' -f1)"
done
printf '\n'

# --- Measure ----------------------------------------------------------------
for cpu in $cpus; do
  for t in $(seq 1 "$trials"); do
    printf 'trial=%s cpu=%s rounds=%s\n' "$t" "$cpu" "$rounds"
    taskset -c "$cpu" "$bin/bench-contract" --rounds "$rounds" "${docargs[@]}" \
      >"$work/run.cpu$cpu.t$t.out" 2>"$work/run.cpu$cpu.t$t.err"
    status=$?
    if [ "$status" -ne 0 ]; then
      cat "$work/run.cpu$cpu.t$t.err" >&2
      printf 'FAIL: bench-contract exited %s on cpu %s trial %s\n' \
        "$status" "$cpu" "$t" >&2
      exit 1
    fi
  done
done

# --- Aggregate --------------------------------------------------------------
# One row per (cpu, doc, arm): the median across trials of the trial median
# ns/byte, and the median and range of the per-round ratios.  A doc's row is
# printed with its entry-position and escape-position counts, so a row that
# measured a different amount of work cannot hide behind its arm name.
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
    if (n == 0) return 0
    if (n % 2) return arr[(n + 1) / 2]
    return 0.5 * (arr[n / 2] + arr[n / 2 + 1])
  }
  $1 == "instrument" { parse(); print "instrument", $0; next }
  $1 == "doc" {
    parse()
    key = kv["cpu"] SUBSEP kv["name"]
    if (!(key in seen)) {
      seen[key] = 1
      order[++ndocs] = key
      docs[kv["cpu"] SUBSEP kv["name"] "_bytes"] = kv["bytes"]
      docs[kv["cpu"] SUBSEP kv["name"] "_blocks"] = kv["blocks"]
      docs[kv["cpu"] SUBSEP kv["name"] "_emitter"] = kv["emitter"]
      docs[kv["cpu"] SUBSEP kv["name"] "_nk"] = kv["entry_positions"]
      docs[kv["cpu"] SUBSEP kv["name"] "_nxp"] = kv["escape_positions"]
      docs[kv["cpu"] SUBSEP kv["name"] "_u8"] = kv["utf8_word"]
      docs[kv["cpu"] SUBSEP kv["name"] "_s1"] = kv["stage1_status"]
      docs[kv["cpu"] SUBSEP kv["name"] "_s1n"] = kv["stage1_structurals"]
    } else {
      if (docs[key "_bytes"] != kv["bytes"] || docs[key "_nk"] != kv["entry_positions"])
        printf "FAIL: %s: document identity changed across trials\n", key > "/dev/stderr"
    }
    next
  }
  $1 == "row" {
    parse()
    rk = kv["cpu"] SUBSEP kv["doc"] SUBSEP kv["arm"]
    if (!(rk in n)) { rows[++nrows] = rk }
    n[rk]++
    m = n[rk]
    ns[rk, m] = kv["median_ns_per_byte"] + 0
    gb[rk, m] = kv["gbps"] + 0
    cy[rk, m] = kv["cycles_per_byte"] + 0
    if (kv["ratio"] != ".") {
      ra[rk, m] = kv["ratio"] + 0
      rl[rk, m] = kv["ratio_low"] + 0
      rh[rk, m] = kv["ratio_high"] + 0
      rt[rk] = kv["ratio_to"]
      haven[rk] = 1
    }
    if (kv["ratio2"] != ".") {
      rb[rk, m] = kv["ratio2"] + 0
      rc[rk, m] = kv["ratio2_low"] + 0
      rd[rk, m] = kv["ratio2_high"] + 0
      rt2[rk] = kv["ratio2_to"]
      haven2[rk] = 1
    }
    next
  }
  END {
    printf "SUMMARY cpu doc arm emitter bytes blocks entries escapes utf8_word stage1 ns_per_byte gbps cycles_per_byte ratio ratio_low ratio_high ratio_to ratio2 ratio2_low ratio2_high ratio2_to\n"
    for (i = 1; i <= nrows; i++) {
      split(rows[i], p, SUBSEP)
      k = rows[i]
      m = n[k]
      for (j = 1; j <= m; j++) { a[j] = ns[k, j]; b[j] = gb[k, j]; c[j] = cy[k, j] }
      sortn(a, m); sortn(b, m); sortn(c, m)
      dk = p[1] SUBSEP p[2]
      printf "%s %s %s %s %s %s %s %s %s %s %.6f %.3f %.4f",
        p[1], p[2], p[3], docs[dk "_emitter"], docs[dk "_bytes"],
        docs[dk "_blocks"], docs[dk "_nk"], docs[dk "_nxp"],
        docs[dk "_u8"], docs[dk "_s1"],
        med(a, m), med(b, m), med(c, m)
      if (haven[k]) {
        for (j = 1; j <= m; j++) { x[j] = ra[k, j]; y[j] = rl[k, j]; z[j] = rh[k, j] }
        sortn(x, m); sortn(y, m); sortn(z, m)
        printf " %.4f %.4f %.4f %s", med(x, m), y[1], z[m], rt[k]
      } else {
        printf " . . . -"
      }
      if (haven2[k]) {
        for (j = 1; j <= m; j++) { x2[j] = rb[k, j]; y2[j] = rc[k, j]; z2[j] = rd[k, j] }
        sortn(x2, m); sortn(y2, m); sortn(z2, m)
        printf " %.4f %.4f %.4f %s", med(x2, m), y2[1], z2[m], rt2[k]
      } else {
        printf " . . . -"
      }
      printf "\n"
    }
  }
' "$work"/run.cpu*.t*.out >"$work/summary.txt"
status=$?
if [ "$status" -ne 0 ]; then
  printf 'FAIL: aggregation failed\n' >&2
  exit 1
fi
cat "$work/summary.txt"
printf '\ntranscripts: %s\n' "$work/run.cpu"*.t*.out

printf '\nok: every arm gated against leanllvm_json_pipeline before the clock; every timed act checksum equal to its warm-up\n'
printf 'note: ratios are per-round pairs in one process; below 1 the numerator is faster\n'
printf 'note: stage1 is rejected on route-u8-64k, so its ratio row is absent there\n'
