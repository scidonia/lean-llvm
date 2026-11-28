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
# `object_sha256` and the record's input `sha256` all agree, so every number it
# prints belongs to one named artifact and not to whichever object happened to
# be in the build directory.
#
# Documents: the generator's fixed seed (`0x243F6A8885A308D3`), dense at 64 KiB
# and 1 MiB, strings at 1 MiB, and the corpus's 23-byte `doc-nested` and 4-byte
# `esc-bad`.  Each row is `--value-bench`'s three arms on the same loaded bytes:
# the indexed `valueOf`, the previous list-materialising decode, and the scalar
# canonical reference, with the digests required to agree (`equal=1`).
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
[ -f "$record" ] || die "absent '$record'"
[ -f "$input" ] || die "absent '$input'"
command -v taskset >/dev/null 2>&1 || die "no taskset on PATH; run this under nix develop"

recorded_input=$(awk -F'\t' '$1=="sha256"{print $2}' "$record")
recorded_object=$(awk -F'\t' '$1=="object_sha256"{print $2}' "$record")
[ -n "$recorded_input" ] && [ -n "$recorded_object" ] ||
  die "'$record' does not name both hashes"
input_sha=$(sha256sum "$input" | awk '{print $1}')
object_sha=$(sha256sum "$object" | awk '{print $1}')
[ "$input_sha" = "$recorded_input" ] ||
  die "'$input' hashes $input_sha, the record names $recorded_input"
[ "$object_sha" = "$recorded_object" ] ||
  die "'$object' hashes $object_sha, not the recorded release object $recorded_object"

binary_sha=$(sha256sum "$route" | awk '{print $1}')

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

printf 'release artifact: object %s sha256 %s\n' "$object" "$object_sha"
printf 'release input: %s sha256 %s\n' "$input" "$input_sha"
printf 'route binary: %s sha256 %s\n' "$route" "$binary_sha"
printf 'host: %s; cpu: %s; reps: big=%s small=%s\n' \
  "$(uname -srm)" \
  "$(awk -F: '/^model name/ { sub(/^ /, "", $2); print $2; exit }' /proc/cpuinfo)" \
  "$reps_big" "$reps_small"

row() { # <path> <label> <reps>
  local path=$1 label=$2 reps=$3 out status size indexed listed reference equal digest
  out=$(taskset -c "$cpu" timeout "$call_timeout" "$route" --value-bench "$path" "$reps" 2>&1)
  status=$?
  if [ "$status" -ne 0 ]; then
    printf 'valuebench artifact_sha256=%s doc=%s status=%s\n' "$object_sha" "$label" "$status" >&2
    printf '%s\n' "$out" >&2
    return 1
  fi
  arm() { printf '%s\n' "$out" | awk -v a=" arm=$1 " 'index($0, a) {for (i = 1; i <= NF; i++) if ($i ~ /^median_ns=/) print substr($i, 11)}'; }
  indexed=$(arm indexed)
  listed=$(arm listed)
  reference=$(arm reference)
  equal=$(printf '%s\n' "$out" | sed -n 's/^valuebench .* equal=\([^ ]*\).*/\1/p')
  digest=$(printf '%s\n' "$out" | awk '/ arm=indexed /{for (i = 1; i <= NF; i++) if ($i ~ /^digest=/) print substr($i, 8)}')
  size=$(printf '%s\n' "$out" | sed -n 's/^valuebench doc=[^ ]* size=\([0-9]*\).*/\1/p' | head -1)
  [ -n "$indexed" ] && [ -n "$listed" ] && [ -n "$reference" ] ||
    { printf 'valuebench artifact_sha256=%s doc=%s malformed-row\n' "$object_sha" "$label" >&2
      printf '%s\n' "$out" >&2; return 1; }
  [ "$equal" = 1 ] ||
    { printf 'valuebench artifact_sha256=%s doc=%s equal=%s\n' "$object_sha" "$label" "$equal" >&2
      printf '%s\n' "$out" >&2; return 1; }
  printf 'valuebench artifact_sha256=%s doc=%s size=%s reps=%s indexed_ns=%s listed_ns=%s reference_ns=%s equal=%s digest=%s\n' \
    "$object_sha" "$label" "${size:--}" "$reps" "$indexed" "$listed" "$reference" "$equal" "$digest"
}

status=0
row "$dense1m" dense-1MiB "$reps_big" || status=1
row "$strings1m" strings-1MiB "$reps_big" || status=1
row "$dense64" dense-64KiB "$reps_small" || status=1
row "$nested" doc-nested "$reps_small" || status=1
row "$bad" esc-bad "$reps_small" || status=1
exit "$status"
