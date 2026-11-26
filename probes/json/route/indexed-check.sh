#!/usr/bin/env bash
# The indexed event reader's corpus differential.
#
#   nix develop -c bash probes/json/route/indexed-check.sh
#
# Build the route first (`probes/json/route/build.sh`).  For every document in
# the value and route corpora, and for the three 64 KiB synthetic shapes, the
# route's `--indexed-check` takes the native call's returned buffers and reads
# them with both the index-based reader and the list specification: the two
# event lists and the two decoded values must be equal.  A document outside the
# fast path has no returned stream to compare and is counted separately, so the
# summary cannot pass on a corpus where no comparison ran.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
build=${BUILD_DIR:-"$here/build"}
route="$build/leanllvm-json-route"

if [ ! -x "$route" ]; then
  echo "indexed-check: no route at $route; run probes/json/route/build.sh first" >&2
  exit 3
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

gen="$build/gen"
if [ ! -x "$gen" ]; then
  "${CC:-clang}" -O2 "$repo/tests/json-units-bench/gen.c" -o "$gen"
fi
for shape in dense strings utf8; do
  "$gen" --shape "$shape" --size 65536 --out "$work/syn-$shape-64k.json"
done

fail=0
fast=0
fallback=0
total=0

check_doc() {
  local doc=$1
  total=$((total + 1))
  local out status
  out=$("$route" --indexed-check "$doc" 2>&1)
  status=$?
  printf '%s\n' "$out"
  if [ "$status" -ne 0 ]; then
    fail=$((fail + 1))
    return
  fi
  case "$out" in
    *path=fast*) fast=$((fast + 1)) ;;
    *path=fallback*) fallback=$((fallback + 1)) ;;
    *) echo "indexed-check: unclassified row for '$doc'" >&2; fail=$((fail + 1)) ;;
  esac
}

for dir in "$repo/tests/json-value/corpus" "$repo/tests/json/corpus"; do
  for doc in "$dir"/*; do
    [ -f "$doc" ] || continue
    check_doc "$doc"
  done
done
for doc in "$work"/*.json; do
  check_doc "$doc"
done

if [ "$fail" -ne 0 ]; then
  echo "indexed-check: $fail disagreement(s)" >&2
  exit 1
fi
if [ "$fast" -eq 0 ]; then
  echo "indexed-check: no fast-path stream was compared; the check is vacuous" >&2
  exit 1
fi
echo "indexed-check: ok — $total documents, $fast fast-path streams compared, \
$fallback outside the fast path"
