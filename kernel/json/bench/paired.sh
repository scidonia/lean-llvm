#!/usr/bin/env bash
# Arm C: the extracted unit costs what the measured one costs.
#
#   nix develop -c bash kernel/json/bench/paired.sh                        # the mask unit
#   nix develop -c bash kernel/json/bench/paired.sh --core 3 --rounds 15
#   nix develop -c bash kernel/json/bench/paired.sh --self-control
#   nix develop -c bash kernel/json/bench/paired.sh --unit entry           # the entry unit
#
# Units (`--unit s1` is the default, so every existing invocation keeps its
# meaning and its exit codes):
#
#   s1     one binary holds the measured and the extracted `s1f_masks` under
#          distinct symbols, selected per process; both acts run in the same
#          round, in rotated order, on the same data, and the reported number is
#          the median of (extracted - measured) ns per block over the rounds.
#          The bound is +/-0.5 ns/block on every input: each committed corpus
#          file and the three generated arms (every byte value in every lane,
#          every 4-byte sequence of the 16-symbol class alphabet, and a
#          fixed-seed random arm), each under the eight carry states.
#   entry  one binary holds the measured and the extracted `s1f_k_pos8` and
#          `s1f_k_b8`, again selected per process; the four acts are the two
#          kernels on each side, run in the same round over the same mask stream
#          and twice per round in both orders (so a drift inside the round
#          cancels in the difference), and the report is one median difference
#          per input and kernel against the same +/-0.5 ns/block bound.  The
#          unit's own table is initialised by a constructor in each probe TU,
#          outside the timed region.
#
# `--self-control` runs the measured unit against itself.  It must report
# exactly 0.0, which tests the harness's dispatch and subtraction — the two
# acts are the same recorded sample — not the clock.
#
# The core class is read from CPUID.1Ah.EAX[31:24] by the binary and printed
# with the result.  `--core N` pins the run with `taskset -c N`; without it the
# process is unpinned and the class printed is the one it observed.  Repeat
# `--core` to run the same binary on more than one core class.
#
# Both units place their probes on 4 KiB boundaries (see each source file for
# why), and the entry unit additionally aligns every function to 4 KiB so the
# kernels it times have the same geometry on both sides; this script asserts the
# placement with `nm`.  For the entry unit it also prints the preprocessed text
# of the timed entry point and refuses to report a time unless that text names
# the extracted unit and calls both kernels -- a staged pipeline is not measured
# until its timed source is shown to reach the new code
# (`docs/json-pipeline-performance.md` §7.1).
#
# Exit status: 0 when every input holds, 1 when one is outside the bound,
# 3 on a setup fault (an absent input, tool or corpus, a build failure, a
# misaligned probe, a timed source that does not reach the extracted unit), so a
# missing dependency is never read as a measurement.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
measured=$repo/kernel/json/measured
kernel_dir=$repo/kernel/json
corpus=$repo/tests/json-s1-masks/corpus
cc=clang

# The measured compiler line (`build49.sh:17`) and P2 set (`build49.sh:21`).
cflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)
defs=(-DPSTAGE=32 -DPMODE=2 -DS1F_XS=5 -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1)
# The entry unit's measured set (`build49.sh:19-21`), with the UTF-8 switch at
# the header's default: `u8kl.h` is not vendored and no act here reaches it.
entry_defs=(-DSTAGE_PROBE -DS1F_ENT_PROBE=1 -DS1F_DENS=1 -DS1F_TWOPHASE=1
            -DS1F_EXP2=11 -DS1F_DISPATCH=1 -DS1F_UTF8=0 -DS1F_KL_DOC=0 -DPSTAGE=32
            -DPMODE=2 -DS1F_XS=5 -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1)

unit=s1
rounds=11
self_control=0
cores=()

usage() {
  awk 'NR > 1 && /^set -/ { exit } NR > 1 { print }' "$0" | sed 's/^# \{0,1\}//' 
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --unit) shift; unit=${1:-}; [ -n "$unit" ] || { printf 'paired: --unit needs a value\n' >&2; exit 3; } ;;
    --unit=*) unit=${1#--unit=} ;;
    --rounds) shift; rounds=${1:-}; [ -n "$rounds" ] || { printf 'paired: --rounds needs a value\n' >&2; exit 3; } ;;
    --core) shift; cores+=("${1:-}"); [ -n "${1:-}" ] || { printf 'paired: --core needs a value\n' >&2; exit 3; } ;;
    --self-control) self_control=1 ;;
    -h|--help) usage; exit 0 ;;
    *) printf 'paired: unknown argument %s\n' "$1" >&2; exit 3 ;;
  esac
  shift
done

case "$unit" in
  s1)
    src=$here/paired.c
    inputs=("$src" "$measured/s1fuse.h" "$kernel_dir/s1_block.c" "$corpus")
    ;;
  entry)
    src=$here/paired-entry.c
    inputs=("$src" "$measured/s1fuse.h" "$measured/xlist.h" "$kernel_dir/entry.c")
    ;;
  *)
    printf 'SETUP: unit %s has no paired timing arm; implemented units: s1 entry\n' "$unit" >&2
    exit 3
    ;;
esac

for path in "${inputs[@]}"; do
  [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done
command -v "$cc" >/dev/null 2>&1 || { printf 'SETUP: no %s on PATH\n' "$cc" >&2; exit 3; }
if [ "${#cores[@]}" -gt 0 ] && ! command -v taskset >/dev/null 2>&1; then
  printf 'SETUP: --core needs taskset on PATH\n' >&2
  exit 3
fi

mkdir -p "$repo/.lake" || { printf 'SETUP: cannot create %s/.lake\n' "$repo" >&2; exit 3; }
work=$(mktemp -d "$repo/.lake/tmp-$unit-bench.XXXXXX" 2>/dev/null) || {
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

if [ "$unit" = s1 ]; then
  build "$work/measured.o" "${cflags[@]}" "${defs[@]}" -DPAIRED_PROBE=measured \
    -DPAIRED_MEASURED -DPROBE_NAME=probe_measured -I "$measured" -c "$src"
  build "$work/kernel.o" "${cflags[@]}" "${defs[@]}" -DPAIRED_PROBE=kernel \
    -DPROBE_NAME=probe_kernel -I "$kernel_dir" -c "$src"
  build "$work/main.o" -O2 -DPAIRED_MAIN -c "$src"
  build "$work/paired" -O2 "$work/main.o" "$work/measured.o" "$work/kernel.o"
else
  # 4 KiB function alignment on both probe TUs: the kernels are measured text
  # and cannot carry an attribute, so the geometry is set by the flag, equally
  # for both sides, and asserted below.
  build "$work/measured.o" "${cflags[@]}" "${defs[@]}" "${entry_defs[@]}" \
    -falign-functions=4096 -DPAIRED_PROBE=measured -DPAIRED_MEASURED \
    -DPROBE_NAME=probe_entry_measured -I "$measured" -c "$src"
  build "$work/kernel.o" "${cflags[@]}" "${defs[@]}" "${entry_defs[@]}" \
    -falign-functions=4096 -DPAIRED_PROBE=extracted \
    -DPROBE_NAME=probe_entry_extracted -I "$kernel_dir" -c "$src"
  build "$work/main.o" -O2 -DPAIRED_MAIN -c "$src"
  build "$work/paired" -O2 "$work/main.o" "$work/measured.o" "$work/kernel.o"
fi

# The two probes must sit at page boundaries, or the comparison measures their
# addresses' uop-cache and I-cache sets as well as their code (the source says
# why).  `nm` is not required; when it is present the placement is asserted.
if command -v nm >/dev/null 2>&1; then
  if [ "$unit" = s1 ]; then
    probe_addrs=$(nm "$work/paired" | awk '$3 ~ /^probe_(measured|kernel)$/ { print $1 }')
    bad=$(printf '%s\n' "$probe_addrs" | grep -cv '000$' || true)
    if [ "$(printf '%s\n' "$probe_addrs" | grep -c . || true)" -ne 2 ] || [ "$bad" -ne 0 ]; then
      printf 'SETUP: the probes are not page-aligned: %s\n' "$(echo $probe_addrs)" >&2
      exit 3
    fi
    printf 'probe addresses %s (page-aligned)\n' "$(echo $probe_addrs)"
  else
    probe_addrs=$(nm "$work/paired" | awk '$3 ~ /^probe_entry_(measured|extracted)_(pos8|b8)$/ { print $1, $3 }')
    if [ "$(printf '%s\n' "$probe_addrs" | grep -c . || true)" -ne 4 ]; then
      printf 'SETUP: expected four probe symbols, found: %s\n' "$(echo $probe_addrs)" >&2
      exit 3
    fi
    bad=$(printf '%s\n' "$probe_addrs" | awk '$1 !~ /000$/ { print $1, $2 }')
    if [ -n "$bad" ]; then
      printf 'SETUP: a probe is not page-aligned: %s\n' "$(echo $bad)" >&2
      exit 3
    fi
    printf 'probe addresses (page-aligned):\n'
    printf '%s\n' "$probe_addrs" | awk '{ printf "  %s %s\n", $1, $2 }'
    # The kernels cannot carry the attribute, so their geometry is asserted as
    # congruence: the measured and the extracted copy of a kernel must have the
    # same offset inside its page, which is what the caches map by.
    for kname in s1f_k_pos8 s1f_k_b8; do
      low=$(nm "$work/paired" | awk -v n="^$kname$" '$3 ~ n { print substr($1, length($1) - 2) }' | LC_ALL=C sort -u)
      count=$(nm "$work/paired" | awk -v n="^$kname$" '$3 ~ n' | wc -l | tr -d ' ')
      if [ "$count" -ne 2 ] || [ "$(printf '%s\n' "$low" | grep -c .)" -ne 1 ]; then
        printf 'SETUP: %s: %s copies at page offsets {%s}; the geometry is not shared\n' \
          "$kname" "$count" "$(echo $low)" >&2
        exit 3
      fi
      printf 'kernel %s: 2 copies, both at page offset 0x%s\n' "$kname" "$(echo $low)"
    done
  fi
else
  printf 'note: nm is absent, so the probes'"'"' page alignment is not asserted\n'
fi

# §7.1: the timed entry point's preprocessed text must name the new code.
if [ "$unit" = entry ]; then
  "$cc" "${cflags[@]}" "${defs[@]}" "${entry_defs[@]}" -falign-functions=4096 \
    -DPAIRED_PROBE=extracted -DPROBE_NAME=probe_entry_extracted -I "$kernel_dir" \
    -E -P "$src" > "$work/timed.i" 2>"$work/timed.err" || {
    printf 'SETUP: the timed source did not preprocess\n' >&2
    awk 'NR <= 20' "$work/timed.err" >&2
    exit 3
  }
  if ! grep -q 'leanllvm_json_entry_pos8' "$work/timed.i"; then
    printf 'SETUP: the timed source does not name the extracted unit\n' >&2
    printf 'SETUP: docs/json-pipeline-performance.md 7.1: the timed path must reach the new code\n' >&2
    exit 3
  fi
  for pair in pos8:s1f_k_pos8 b8:s1f_k_b8; do
    suffix=${pair%%:*}
    kernel=${pair#*:}
    body=$(awk -v name="probe_entry_extracted_$suffix" '
      !infn && index($0, name "(") > 0 &&
        ($0 ~ /\([ \t]*$/ || $0 ~ /\{[ \t]*$/) { infn = 1 }
      infn {
        print
        probe = $0
        o = gsub(/\{/, "", probe); c = gsub(/\}/, "", probe)
        depth += o - c
        if (o > 0) opened = 1
        if (opened && depth == 0) exit
      }
    ' "$work/timed.i")
    if [ -z "$body" ] || ! printf '%s\n' "$body" | grep -qF "$kernel("; then
      printf 'SETUP: the timed probe %s does not call %s in its preprocessed text\n' \
        "probe_entry_extracted_$suffix" "$kernel" >&2
      printf 'SETUP: docs/json-pipeline-performance.md 7.1: the timed path must reach the new code\n' >&2
      exit 3
    fi
  done
  printf 'timed entry point reaches the extracted unit (docs/json-pipeline-performance.md 7.1):\n'
  printf '  the preprocessed TU names leanllvm_json_entry_pos8, and both probes call\n'
  printf '  their own kernel (s1f_k_pos8, s1f_k_b8)\n'
fi

printf 'unit        %s\n' "$unit"
printf 'binary      %s\n' "$work/paired"
printf 'binary sha256 %s\n' "$(sha256sum "$work/paired" | cut -d' ' -f1)"
printf 'measured obj sha256 %s\n' "$(sha256sum "$work/measured.o" | cut -d' ' -f1)"
printf 'extracted obj sha256 %s\n' "$(sha256sum "$work/kernel.o" | cut -d' ' -f1)"

args=()
if [ "$unit" = s1 ]; then
  mapfile -t corpus_files < <(find "$corpus" -mindepth 1 -maxdepth 1 -type f | LC_ALL=C sort)
  [ "${#corpus_files[@]}" -gt 0 ] || { printf 'SETUP: no corpus files under %s\n' "$corpus" >&2; exit 3; }
  for f in "${corpus_files[@]}"; do args+=(--corpus "$f"); done
fi
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
