#!/usr/bin/env bash
# Arm C: the extracted mask unit costs what the measured one costs.
#
#   nix develop -c bash kernel/json/bench/paired.sh
#   nix develop -c bash kernel/json/bench/paired.sh --core 3 --rounds 15
#   nix develop -c bash kernel/json/bench/paired.sh --self-control
#
# One binary holds both implementations under distinct symbols and is selected
# per process; both acts run in the same round, in rotated order, on the same
# data, and the reported number is the median of (extracted - measured) ns per
# block over the rounds.  The bound is +/-0.5 ns/block on every input: each
# committed corpus file and the three generated arms (every byte value in every
# lane, every 4-byte sequence of the 16-symbol class alphabet, and a fixed-seed
# random arm), each under the eight carry states.
#
# `--self-control` runs the measured unit against itself.  It must report
# exactly 0.0, which tests the harness's dispatch and subtraction — the two
# acts are the same recorded sample — not the clock.
#
# The core class is read from CPUID.1Ah.EAX[31:24] by the binary and printed
# with the result.  `--core N` pins the run with `taskset -c N`; without it the
# process is unpinned and the class printed is the one it observed.
#
# Exit status: 0 when every input holds, 1 when one is outside the bound,
# 3 on a setup fault (an absent input, tool or corpus, a build failure), so a
# missing dependency is never read as a measurement.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
src=$here/paired.c
corpus=$repo/tests/json-s1-masks/corpus
measured=$repo/kernel/json/measured
kernel_dir=$repo/kernel/json
cc=clang

# The measured compiler line (`build49.sh:17`) and P2 set (`build49.sh:21`).
cflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)
defs=(-DPSTAGE=32 -DPMODE=2 -DS1F_XS=5 -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1)

rounds=11
self_control=0
cores=()

while [ "$#" -gt 0 ]; do
  case "$1" in
    --rounds) shift; rounds=${1:-}; [ -n "$rounds" ] || { printf 'paired: --rounds needs a value\n' >&2; exit 3; } ;;
    --core) shift; cores+=("${1:-}"); [ -n "${1:-}" ] || { printf 'paired: --core needs a value\n' >&2; exit 3; } ;;
    --self-control) self_control=1 ;;
    -h|--help) sed -n '2,30p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) printf 'paired: unknown argument %s\n' "$1" >&2; exit 3 ;;
  esac
  shift
done

for path in "$src" "$measured/s1fuse.h" "$kernel_dir/s1_block.c" "$corpus"; do
  [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done
command -v "$cc" >/dev/null 2>&1 || { printf 'SETUP: no %s on PATH\n' "$cc" >&2; exit 3; }
if [ "${#cores[@]}" -gt 0 ] && ! command -v taskset >/dev/null 2>&1; then
  printf 'SETUP: --core needs taskset on PATH\n' >&2
  exit 3
fi

mkdir -p "$repo/.lake" || { printf 'SETUP: cannot create %s/.lake\n' "$repo" >&2; exit 3; }
work=$(mktemp -d "$repo/.lake/tmp-s1-bench.XXXXXX" 2>/dev/null) || {
  printf 'SETUP: cannot create a work directory under %s/.lake\n' "$repo" >&2
  exit 3
}
trap 'rm -rf "$work"' EXIT

build() { # <output> <args...>
  local out=$1
  shift
  if ! "$cc" "$@" -o "$out" 2>"$work/build.err"; then
    printf 'SETUP: %s did not build\n' "$out" >&2
    awk 'NR <= 40' "$work/build.err" >&2
    exit 3
  fi
}

build "$work/measured.o" "${cflags[@]}" "${defs[@]}" -DPAIRED_PROBE=measured \
  -DPAIRED_MEASURED -DPROBE_NAME=probe_measured -I "$measured" -c "$src"
build "$work/kernel.o" "${cflags[@]}" "${defs[@]}" -DPAIRED_PROBE=kernel \
  -DPROBE_NAME=probe_kernel -I "$kernel_dir" -c "$src"
build "$work/main.o" -O2 -DPAIRED_MAIN -c "$src"
build "$work/paired" -O2 "$work/main.o" "$work/measured.o" "$work/kernel.o"

# The two probes must sit at page boundaries, or the comparison measures their
# addresses' uop-cache and I-cache sets as well as their code (the source says
# why).  `nm` is not required; when it is present the placement is asserted.
if command -v nm >/dev/null 2>&1; then
  probe_addrs=$(nm "$work/paired" | awk '$3 ~ /^probe_(measured|kernel)$/ { print $1 }')
  bad=$(printf '%s\n' "$probe_addrs" | grep -cv '000$' || true)
  if [ "$(printf '%s\n' "$probe_addrs" | grep -c . || true)" -ne 2 ] || [ "$bad" -ne 0 ]; then
    printf 'SETUP: the probes are not page-aligned: %s\n' "$(echo $probe_addrs)" >&2
    exit 3
  fi
  printf 'probe addresses %s (page-aligned)\n' "$(echo $probe_addrs)"
else
  printf 'note: nm is absent, so the probes'"'"' page alignment is not asserted\n'
fi

printf 'binary      %s\n' "$work/paired"
printf 'binary sha256 %s\n' "$(sha256sum "$work/paired" | cut -d' ' -f1)"
printf 'measured obj sha256 %s\n' "$(sha256sum "$work/measured.o" | cut -d' ' -f1)"
printf 'extracted obj sha256 %s\n' "$(sha256sum "$work/kernel.o" | cut -d' ' -f1)"

mapfile -t corpus_files < <(find "$corpus" -mindepth 1 -maxdepth 1 -type f | LC_ALL=C sort)
[ "${#corpus_files[@]}" -gt 0 ] || { printf 'SETUP: no corpus files under %s\n' "$corpus" >&2; exit 3; }

args=()
for f in "${corpus_files[@]}"; do args+=(--corpus "$f"); done
args+=(--arms --rounds "$rounds")
[ "$self_control" -eq 1 ] && args+=(--self-control)

status=0
if [ "${#cores[@]}" -eq 0 ]; then
  "$work/paired" "${args[@]}" || status=$?
else
  for core in "${cores[@]}"; do
    printf '\n== pinned to CPU %s\n' "$core"
    taskset -c "$core" "$work/paired" "${args[@]}" || status=$?
  done
fi

if [ "$status" -eq 0 ]; then
  if [ "$self_control" -eq 1 ]; then
    printf '\nok: the harness reports 0.0 against itself\n'
  else
    printf '\nok: the extracted unit is within +/-0.5 ns/block of the measured one\n'
  fi
fi
exit "$status"
