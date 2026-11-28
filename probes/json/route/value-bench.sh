#!/usr/bin/env bash
# The full-value benchmark on the declared release artifact.
#
#   STAGE2_IR=probes/install/ir/stage2.production.ll \
#     nix develop -c bash probes/json/route/build.sh
#   nix develop -c bash probes/json/route/value-bench.sh
#
# The selection is the capture record's: the object compiled from
# `probes/install/ir/stage2.production.ll` with the middle end disabled.  This
# script refuses to report a row unless the route's `stage2.o`, the record's
# input `sha256` and `object_sha256`, and the executable it is about to run all
# agree -- the last through the `build-manifest.tsv` the route's link step wrote
# beside them.  Every number it prints therefore belongs to one named artifact,
# not to whichever object happened to be in the build directory or whichever
# binary `ROUTE` happened to point at.
#
# Documents: the generator's fixed seed (`0x243F6A8885A308D3`), dense at 64 KiB
# and 1 MiB, strings at 1 MiB, and the corpus's 23-byte `doc-nested` and 4-byte
# `esc-bad`.  Each row is `--value-bench`'s four arms on the same loaded bytes:
# the indexed `valueOf`, the previous list-materialising decode, the scalar
# canonical reference, and the fused event-reader prototype, with the digests
# required to agree (`equal=1`).  The fused arm is a benchmark arm only; it is
# not the route's value path.  The aggregate line reports which answer the
# route's value arm takes on the same bytes (`path=fast` or `path=fallback`), so
# coverage and throughput are separate fields of the same run.
#
# Every run is `taskset`-pinned.  `BENCH_CPU` selects the CPU (default 2),
# `REPS_BIG` the 1 MiB repetition count (default 3) and `REPS_SMALL` the rest
# (default 5); `CALL_TIMEOUT` bounds each call (default 900 s).
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
build=${BUILD_DIR:-"$here/build"}
route=${ROUTE:-"$build/leanllvm-json-route"}
object=$build/stage2.o
manifest=$build/build-manifest.tsv
record=$repo/probes/install/ir/stage2.production.tsv
input=$repo/probes/install/ir/stage2.production.ll
gen=$build/gen
cpu=${BENCH_CPU:-2}
reps_big=${REPS_BIG:-3}
reps_small=${REPS_SMALL:-5}
call_timeout=${CALL_TIMEOUT:-900}

die() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

[ -x "$route" ] || die "absent route '$route'; build it with STAGE2_IR=$input probes/json/route/build.sh"
[ -f "$object" ] || die "absent '$object'; the route was not built against the release artifact"
[ -f "$manifest" ] ||
  die "absent '$manifest'; the link step's record of what it built is missing (rebuild the route)"
[ -f "$record" ] || die "absent '$record'"
[ -f "$input" ] || die "absent '$input'"
command -v taskset >/dev/null 2>&1 || die "no taskset on PATH; run this under nix develop"

recorded_input=$(awk -F'\t' '$1=="sha256"{print $2}' "$record")
recorded_object=$(awk -F'\t' '$1=="object_sha256"{print $2}' "$record")
[ -n "$recorded_input" ] && [ -n "$recorded_object" ] ||
  die "'$record' does not name both hashes"

manifest_input=$(awk -F'\t' '$1=="input_ir"{print $3; exit}' "$manifest")
manifest_object=$(awk -F'\t' '$1=="object"{print $3; exit}' "$manifest")
manifest_exe=$(awk -F'\t' '$1=="executable"{print $3; exit}' "$manifest")
[ -n "$manifest_input" ] ||
  die "'$manifest' names no input IR; the build did not compile the release artifact (rebuild with STAGE2_IR=$input)"
[ -n "$manifest_object" ] && [ -n "$manifest_exe" ] ||
  die "'$manifest' does not name both its object and its executable"

input_sha=$(sha256sum "$input" | awk '{print $1}')
object_sha=$(sha256sum "$object" | awk '{print $1}')
binary_sha=$(sha256sum "$route" | awk '{print $1}')
[ "$manifest_input" = "$recorded_input" ] ||
  die "the build's input IR hashes $manifest_input, the record names $recorded_input"
[ "$input_sha" = "$recorded_input" ] ||
  die "'$input' hashes $input_sha, the record names $recorded_input"
[ "$manifest_object" = "$recorded_object" ] ||
  die "the build's object hashes $manifest_object, not the recorded release object $recorded_object"
[ "$object_sha" = "$recorded_object" ] ||
  die "'$object' hashes $object_sha, not the recorded release object $recorded_object"
# The executable is the third file, and the only one that runs.  Without this
# check a stale binary or a `ROUTE` override would be timed beside a current
# object and reported under the object's digest.
[ "$binary_sha" = "$manifest_exe" ] ||
  die "'$route' hashes $binary_sha, not the executable this build linked ($manifest_exe)"

work=$(mktemp -d) || die "cannot create a work directory"
trap 'rm -rf "$work"' EXIT

if [ ! -x "$gen" ]; then
  "${CC:-clang}" -O2 "$repo/tests/json-units-bench/gen.c" -o "$gen" ||
    die "cannot build the document generator"
fi

dense64=$work/dense-65536.json
dense1m=$work/dense-1048576.json
strings1m=$work/strings-1048576.json
"$gen" --shape dense --size 65536 --out "$dense64" || die "generator refused the 64 KiB dense document"
"$gen" --shape dense --size 1048576 --out "$dense1m" || die "generator refused the 1 MiB dense document"
"$gen" --shape strings --size 1048576 --out "$strings1m" || die "generator refused the 1 MiB strings document"
nested=$repo/tests/json/corpus/doc-nested.json
bad=$repo/tests/json/corpus/esc-bad.json
[ -f "$nested" ] || die "absent '$nested'"
[ -f "$bad" ] || die "absent '$bad'"

printf 'build manifest: %s (input, object and executable agree)\n' "$manifest"
printf 'release artifact: object %s sha256 %s\n' "$object" "$object_sha"
printf 'release input: %s sha256 %s\n' "$input" "$input_sha"
printf 'route binary: %s sha256 %s\n' "$route" "$binary_sha"
printf 'host: %s; cpu: %s; reps: big=%s small=%s\n' \
  "$(uname -srm)" \
  "$(awk -F: '/^model name/ { sub(/^ /, "", $2); print $2; exit }' /proc/cpuinfo)" \
  "$reps_big" "$reps_small"

row() { # <path> <label> <reps>
  local path=$1 label=$2 reps=$3 out status size indexed indexed_min indexed_max
  local listed reference reference_min reference_max fused fused_min fused_max
  local equal digest pathkind
  out=$(taskset -c "$cpu" timeout "$call_timeout" "$route" --value-bench "$path" "$reps" 2>&1)
  status=$?
  if [ "$status" -ne 0 ]; then
    printf 'valuebench artifact_sha256=%s route_sha256=%s doc=%s status=%s\n' \
      "$object_sha" "$binary_sha" "$label" "$status" >&2
    printf '%s\n' "$out" >&2
    return 1
  fi
  field() { # <arm> <field>
    printf '%s\n' "$out" | awk -v a=" arm=$1 " -v k="$2=" \
      'index($0, a) {for (i = 1; i <= NF; i++) if (index($i, k) == 1) print substr($i, length(k) + 1)}'
  }
  indexed=$(field indexed median_ns)
  indexed_min=$(field indexed min_ns)
  indexed_max=$(field indexed max_ns)
  listed=$(field listed median_ns)
  reference=$(field reference median_ns)
  reference_min=$(field reference min_ns)
  reference_max=$(field reference max_ns)
  fused=$(field fused median_ns)
  fused_min=$(field fused min_ns)
  fused_max=$(field fused max_ns)
  equal=$(printf '%s\n' "$out" | sed -n 's/^valuebench .* equal=\([^ ]*\).*/\1/p')
  digest=$(printf '%s\n' "$out" | awk '/ arm=indexed /{for (i = 1; i <= NF; i++) if ($i ~ /^digest=/) print substr($i, 8)}')
  pathkind=$(printf '%s\n' "$out" | sed -n 's/^valuebench .* path=\([^ ]*\).*/\1/p')
  size=$(printf '%s\n' "$out" | sed -n 's/^valuebench doc=[^ ]* size=\([0-9]*\).*/\1/p' | head -1)
  [ -n "$indexed" ] && [ -n "$listed" ] && [ -n "$reference" ] && [ -n "$fused" ] ||
    { printf 'valuebench artifact_sha256=%s route_sha256=%s doc=%s malformed-row\n' \
        "$object_sha" "$binary_sha" "$label" >&2
      printf '%s\n' "$out" >&2; return 1; }
  [ "$equal" = 1 ] ||
    { printf 'valuebench artifact_sha256=%s route_sha256=%s doc=%s equal=%s\n' \
        "$object_sha" "$binary_sha" "$label" "$equal" >&2
      printf '%s\n' "$out" >&2; return 1; }
  printf 'valuebench artifact_sha256=%s route_sha256=%s doc=%s size=%s reps=%s path=%s indexed_ns=%s indexed_min_ns=%s indexed_max_ns=%s fused_ns=%s fused_min_ns=%s fused_max_ns=%s reference_ns=%s reference_min_ns=%s reference_max_ns=%s listed_ns=%s equal=%s digest=%s\n' \
    "$object_sha" "$binary_sha" "$label" "${size:--}" "$reps" "${pathkind:--}" \
    "$indexed" "$indexed_min" "$indexed_max" \
    "$fused" "$fused_min" "$fused_max" \
    "$reference" "$reference_min" "$reference_max" \
    "$listed" "$equal" "$digest"
  rows_total=$((rows_total + 1))
  rows_equal=$((rows_equal + 1))
  case "$pathkind" in
    fast) fast_total=$((fast_total + 1)) ;;
    fallback) fallback_total=$((fallback_total + 1)) ;;
    *) failed_total=$((failed_total + 1)) ;;
  esac
}

status=0
rows_total=0
rows_equal=0
fast_total=0
fallback_total=0
failed_total=0
row "$dense1m" dense-1MiB "$reps_big" || status=1
row "$strings1m" strings-1MiB "$reps_big" || status=1
row "$dense64" dense-64KiB "$reps_small" || status=1
row "$nested" doc-nested "$reps_small" || status=1
row "$bad" esc-bad "$reps_small" || status=1
printf 'coverage docs=%s fast=%s fallback=%s failed=%s\n' \
  "$rows_total" "$fast_total" "$fallback_total" "$failed_total"
printf 'agreement rows=%s equal=%s artifact_sha256=%s route_sha256=%s\n' \
  "$rows_total" "$rows_equal" "$object_sha" "$binary_sha"
exit "$status"
