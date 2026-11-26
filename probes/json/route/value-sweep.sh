#!/usr/bin/env bash
# The value arm's size sweep on the dense shape.
#
#   nix develop -c bash probes/json/route/value-sweep.sh [reps]
#
# Build the route first (`probes/json/route/build.sh`, `TIMING=1` for the stage
# columns).  For each size from 64 KiB to 1 MiB the generator writes the
# fixed-seed dense document, and the script reports:
#
#   * `wall_ns` — the median of `reps` whole `--value` calls, timed from before
#     the program is spawned to after it exits with the value line discarded.
#     This is the caller-visible cost, printing included.
#   * `reader_ns` and `decode_ns` — `--stages`'s `value_bytes_ns` and
#     `value_decode_ns`, the indexed reader and the event decoder measured on
#     their own with the digests outside the interval.
#   * `fallbacks` — 1 when `--stages` reports the document outside the fast
#     path or the reader returning no events, else 0.
#
# `LABEL` names the build in every row (default `route`), so a baseline and a
# changed route can be swept in one table.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
build=${BUILD_DIR:-"$here/build"}
route="$build/leanllvm-json-route"
reps=${1:-3}
label=${LABEL:-route}
sizes=${SIZES:-"65536 131072 262144 524288 1048576"}
call_timeout=${CALL_TIMEOUT:-900}

if [ ! -x "$route" ]; then
  echo "value-sweep: no route at $route; run probes/json/route/build.sh first" >&2
  exit 3
fi

gen="$build/gen"
if [ ! -x "$gen" ]; then
  "${CC:-clang}" -O2 "$repo/tests/json-units-bench/gen.c" -o "$gen"
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

median() {
  sort -n | awk '
    { a[NR] = $1 }
    END {
      if (NR == 0) { print "-" }
      else if (NR % 2) { print a[(NR + 1) / 2] }
      else { printf "%.0f\n", (a[NR / 2] + a[NR / 2 + 1]) / 2 }
    }'
}

printf 'sweep label=%s host=%s reps=%s sizes=%s\n' "$label" "$(hostname)" "$reps" "$sizes"
for size in $sizes; do
  doc="$work/syn-dense-$size.json"
  "$gen" --shape dense --size "$size" --out "$doc"
  walls="$work/walls-$size"
  : > "$walls"
  for _ in $(seq "$reps"); do
    start=$(date +%s%N)
    timeout "$call_timeout" "$route" --value "$doc" > /dev/null 2>&1
    status=$?
    stop=$(date +%s%N)
    if [ "$status" -ne 0 ]; then
      echo "value-sweep: --value exited $status on size $size" >&2
    fi
    echo $((stop - start)) >> "$walls"
  done
  wall=$(median < "$walls")

  timeout "$call_timeout" "$route" --stages "$doc" "$reps" \
    > "$work/stage-out-$size" 2> "$work/stage-row-$size"
  # The row is on stderr, the payload lines on stdout.  Keeping the two apart
  # means a buffered payload line cannot interleave with the row.
  row=$(grep -a '^row ' "$work/stage-row-$size" | tail -1)
  reader=$(printf '%s\n' "$row" | sed -n 's/.* value_bytes_ns=\([^ ]*\).*/\1/p')
  decode=$(printf '%s\n' "$row" | sed -n 's/.* value_decode_ns=\([^ ]*\).*/\1/p')
  path=$(printf '%s\n' "$row" | sed -n 's/.* path=\([^ ]*\).*/\1/p')
  outcome=$(printf '%s\n' "$row" | sed -n 's/.* value_outcome=\([^ ]*\).*/\1/p')
  fallbacks=1
  if [ "$path" = "fast" ] && [ "$outcome" = "value" ]; then
    fallbacks=0
  fi
  # An uninstrumented adapter refuses `--stages` at exit 6 and prints no row;
  # the wall column is still the caller-visible measurement.
  [ -n "$reader" ] || reader="-"
  [ -n "$decode" ] || decode="-"
  [ -n "$path" ] || path="-"
  [ -n "$outcome" ] || outcome="-"
  printf 'sweep_row label=%s size=%s wall_ns=%s reader_ns=%s decode_ns=%s path=%s value_outcome=%s fallbacks=%s\n' \
    "$label" "$size" "$wall" "$reader" "$decode" "$path" "$outcome" "$fallbacks"
done
