#!/usr/bin/env bash
# The contracted block unit at its own boundary: the v2 fused body against the
# v1 probe-only body plus the separate UTF-8 call.
#
#   nix develop -c bash tests/json-units-bench/bench-s1-blocks.sh
#
# v1 is `tests/json-units-bench/s1_blocks_v1.c` (the frozen 64c3efe body); the
# composite is that call followed, when the document is not all ASCII, by
# `leanllvm_json_utf8` at `arm`'s bit 2, which is what `kernel/json/pipeline.c`
# does with the v1 unit.  v2 is `kernel/json/s1_blocks.c` as it stands, whose
# loop carries the DFA and whose return word is `ascii | (error << 1)`.
#
# Both are timed at the contracted boundary: a zeroed staging buffer with the
# document at offset four, the caller's entry array, escape stream and cursor,
# and the carry pair reset before every call.  Four arms are measured: gated and
# ungated (`arm & 4`), each without and with the escape list (`arm & 2`).  The
# driver gates the two actors' entry words, escape streams, carries and return
# words before timing a row, so a drift cannot produce a number.
#
# Documents: `syn-utf8-64k` is the acceptance row, with `syn-utf8-4m` as the
# working-set control; `route-u8-64k` is the route's raw UTF-8 class tiled from
# `tests/json/corpus/utf8-*.json`; `route-s1-64k` and `syn-dense-64k` price the
# ASCII-gated path where the DFA skips; `syn-strings-64k` is the string class.
#
# Measurement: medians of `--rounds` round medians of `--reps` repetitions,
# pinned to one core with `taskset`.  A ratio is v2's time over v1's in the same
# round.  The script writes the full transcript to
# `tests/json-units-bench/bench-s1-blocks-transcript.txt` and prints it.
#
# Exit status: 0 when every gate held and every row was measured, 1 on a gate
# failure, 3 when an input or tool is missing.
set -euo pipefail
export LC_ALL=C

repo=$(cd "$(dirname "$0")/../.." && pwd)
here=$repo/tests/json-units-bench
work=${BENCH_DIR:-$here/build-s1-blocks}
bin=$work/bin
corpus=$work/corpus
cpus=${BENCH_CPUS:-0}
rounds=${BENCH_ROUNDS:-11}
reps=${BENCH_REPS:-41}
seed=${BENCH_SEED:-0x243F6A8885A308D3}
cc=${BENCH_CC:-clang}

die() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }
for f in kernel/json/s1_blocks.c tests/json-units-bench/s1_blocks_v1.c \
         tests/json-units-bench/bench-s1-blocks.c tests/json-units-bench/gen.c \
         kernel/json/escape.c kernel/json/utf8.c; do
  [ -f "$repo/$f" ] || die "absent: $f"
done
command -v "$cc" >/dev/null 2>&1 || die "no $cc on PATH; run under nix develop"
command -v taskset >/dev/null 2>&1 || die "no taskset on PATH"

rm -rf "$work"
mkdir -p "$bin" "$corpus" || die "cannot create $work"

kflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)
"$cc" -O2 -std=gnu11 -o "$bin/gen" "$here/gen.c" || die "gen did not build"
for src in escape utf8; do
  "$cc" "${kflags[@]}" -I "$repo/kernel/json" -c "$repo/kernel/json/$src.c" \
    -o "$bin/$src.o" || die "kernel/json/$src.c did not compile"
done
"$cc" "${kflags[@]}" -I "$repo/kernel/json" -c "$repo/kernel/json/s1_blocks.c" \
  -o "$bin/s1_blocks.o" || die "s1_blocks.c did not compile"
"$cc" "${kflags[@]}" -I "$repo/kernel/json" \
  -c "$here/s1_blocks_v1.c" -o "$bin/s1_blocks_v1.o" || die "v1 did not compile"
"$cc" "${kflags[@]}" -I "$repo/kernel/json" \
  -c "$here/bench-s1-blocks.c" -o "$bin/bench.o" || die "driver did not compile"
"$cc" -O2 -o "$bin/bench" "$bin/bench.o" "$bin/s1_blocks.o" \
  "$bin/s1_blocks_v1.o" "$bin/escape.o" "$bin/utf8.o" || die "driver did not link"

# --- corpus ---------------------------------------------------------------
tile() { # <out> <size> <src>...
  local out=$1 size=$2; shift 2
  : > "$out"
  while [ "$(stat -c %s "$out")" -lt "$size" ]; do cat "$@" >> "$out"; done
  head -c "$size" "$out" > "$out.tmp" && mv "$out.tmp" "$out"
}
for shape in utf8 dense strings; do
  for size in 65536 4194304; do
    case $size in 65536) tag=64k ;; 4194304) tag=4m ;; esac
    "$bin/gen" --shape "$shape" --size "$size" --seed "$seed" \
      --out "$corpus/syn-$shape-$tag.json" || die "gen failed: $shape $tag"
  done
done
mapfile -t u8 < <(find "$repo/tests/json/corpus" -name 'utf8-*.json' -type f | sort)
mapfile -t s1 < <(find "$repo/tests/json-s1-masks/corpus" -type f | sort)
[ "${#u8[@]}" -gt 0 ] || die "no UTF-8 route documents"
[ "${#s1[@]}" -gt 0 ] || die "no stage-1 route documents"
tile "$corpus/route-u8-64k.json" 65536 "${u8[@]}"
tile "$corpus/route-s1-64k.json" 65536 "${s1[@]}"

docs=()
for f in "$corpus"/syn-utf8-64k.json "$corpus"/syn-utf8-4m.json \
         "$corpus"/route-u8-64k.json "$corpus"/syn-dense-64k.json \
         "$corpus"/syn-strings-64k.json "$corpus"/route-s1-64k.json; do
  docs+=("$f")
done

# --- run ------------------------------------------------------------------
out=$here/bench-s1-blocks-transcript.txt
{
  printf 'command: nix develop -c bash tests/json-units-bench/bench-s1-blocks.sh\n'
  printf 'compiler: %s (%s)\n' "$cc" "$("$cc" --version | head -1)"
  printf 'unit flags: %s\n' "${kflags[*]}"
  printf 'v1 baseline: tests/json-units-bench/s1_blocks_v1.c (kernel/json/s1_blocks.c at 64c3efe)\n'
  printf 'v2 subject: kernel/json/s1_blocks.c (worktree)\n'
  printf 'v2 sha256: %s\n' "$(sha256sum "$repo/kernel/json/s1_blocks.c" | cut -d' ' -f1)"
  printf 'v1 sha256: %s\n' "$(sha256sum "$here/s1_blocks_v1.c" | cut -d' ' -f1)"
  printf 'host: %s\n' "$(uname -srm)"
  printf 'cpu: %s\n' "$(awk -F: '/^model name/ { sub(/^ /, "", $2); print $2; exit }' /proc/cpuinfo)"
  printf 'cpus online: %s; pinned to: %s\n' "$(nproc)" "$cpus"
  printf 'governor: %s\n' "$(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null || echo unknown)"
  printf 'load average at start: %s\n' "$(cut -d' ' -f1-3 /proc/loadavg)"
  printf 'rounds: %s reps: %s seed: %s\n' "$rounds" "$reps" "$seed"
  printf '\ncorpus:\n'
  for f in "$corpus"/*.json; do
    printf '  %-24s %10s %s\n' "$(basename "$f")" "$(stat -c %s "$f")" \
      "$(sha256sum "$f" | cut -d' ' -f1)"
  done
  printf '\n'
  for cpu in $cpus; do
    taskset -c "$cpu" "$bin/bench" --rounds "$rounds" --reps "$reps" "${docs[@]}"
  done
} 2>&1 | tee "$out"
