#!/usr/bin/env bash
# A repeatable benchmark for the seam units already installed by the probe.
#
# Run through the flake, from the repository root:
#
#   nix develop -c bash probes/bench/bench.sh
#   nix develop -c bash probes/bench/bench.sh --iterations 200000 --repetitions 21
#
# It measures one thing: the wall-clock cost of one call to the seam as linked
# from `probes/install/build/<unit>.o`.  It reports medians and minima over
# repetitions and never presents a ratio as a proof of anything; the certificate
# says the units agree, this harness only says how fast each one ran here.
#
# Preconditions: the units exist, which `bash probes/install/check.sh` produces.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
build="$repo/probes/install/build"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

iterations=500000
repetitions=15
while [ "$#" -gt 0 ]; do
  case "$1" in
    --iterations) iterations=${2:?}; shift 2 ;;
    --repetitions) repetitions=${2:?}; shift 2 ;;
    *) echo "bench: unknown argument $1" >&2; exit 2 ;;
  esac
done
[ "$iterations" -gt 0 ] && [ "$repetitions" -gt 0 ] || {
  echo "bench: iterations and repetitions must be positive" >&2; exit 2; }

units=(baseline candidate)
for unit in "${units[@]}"; do
  [ -f "$build/$unit.o" ] || {
    echo "bench: missing $build/$unit.o; run 'bash probes/install/check.sh' first" >&2
    exit 3; }
done

cd "$repo"
printf 'bench: rev=%s lean=%s clang=%s\n' \
  "$(git rev-parse --short HEAD)" \
  "$(lean --version | sed -E 's/.*version (.*), Release.*/\1/')" \
  "$(clang --version | head -1 | sed -E 's/.*version ([^ ]+).*/\1/')"
printf 'bench: triple=%s\n' "$(clang -print-target-triple)"
for unit in "${units[@]}"; do
  printf 'bench: unit=%s sha256=%s\n' "$unit" "$(sha256sum "$build/$unit.o" | cut -d' ' -f1)"
done

for unit in "${units[@]}"; do
  clang -O2 -o "$work/$unit" "$here/driver.c" "$build/$unit.o"
done

median() { sort -n | awk '{v[NR]=$1} END { if (NR%2) print v[(NR+1)/2]; else print (v[NR/2]+v[NR/2+1])/2 }'; }
minimum() { sort -n | head -1; }

declare -A checksums
for unit in "${units[@]}"; do
  ns_file="$work/$unit.ns"
  : > "$ns_file"
  for _ in $(seq 1 "$repetitions"); do
    out=$("$work/$unit" "$iterations")
    checksums[$unit]=$(sed -E 's/.*state=([0-9a-f]+) checksum=([0-9a-f]+) ns=.*/\1 \2/' <<<"$out")
    sed -E 's/.*ns=([0-9.]+).*/\1/' <<<"$out" >> "$ns_file"
  done
  MED=$(median < "$ns_file"); MIN=$(minimum < "$ns_file")
  awk -v u="$unit" -v v="$MED" -v n="$iterations" 'BEGIN{printf "bench: %-9s median=%.2f ns/call\n", u, v/n}'
  echo "$MED $MIN" > "$work/$unit.summary"
done

# Both units must have computed the same results; a mismatch means the two runs
# did different work and the comparison is meaningless.
if [ "${checksums[baseline]}" != "${checksums[candidate]}" ]; then
  echo "bench: the units disagree on results (${checksums[baseline]} vs ${checksums[candidate]}); no comparison is reported" >&2
  exit 1
fi
printf 'bench: both units produced state=... checksum=%s\n' "${checksums[baseline]#* }"

read -r base_med _ < "$work/baseline.summary"
read -r cand_med _ < "$work/candidate.summary"
awk -v b="$base_med" -v c="$cand_med" 'BEGIN{printf "bench: candidate/baseline median ratio = %.3f\n", c/b}'
echo "bench: done (a ratio measured here is not a proof; the certificate covers agreement, not speed)"
