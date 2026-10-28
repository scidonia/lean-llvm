#!/usr/bin/env bash
# End-to-end application check: a real caller is linked against each proved
# unit through the shared selector, runs, and must produce the same answer.
#
#   nix develop -c bash probes/app/check.sh
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
install=$(cd "$here/../install" && pwd)
select=$install/select.sh
build=${BUILD_DIR:-"$here/build"}

"$here/build.sh" >/dev/null

echo "== candidate unit"
MANIFEST=$build/manifest.env OUT=$build/app_candidate \
  RECORD=$build/selection_candidate.env "$select" >/dev/null
"$build/app_candidate" > "$build/out_candidate.txt"
grep -q '^selected=candidate$' "$build/selection_candidate.env"

echo "== baseline unit (stale candidate falls back)"
cp "$build/manifest.env" "$build/manifest_bad.env"
sed -i 's/^candidate_sha256=.*/candidate_sha256=0000000000000000000000000000000000000000000000000000000000000000/' \
  "$build/manifest_bad.env"
MANIFEST=$build/manifest_bad.env OUT=$build/app_fallback \
  RECORD=$build/selection_fallback.env "$select" >/dev/null
"$build/app_fallback" > "$build/out_fallback.txt"
grep -q '^selected=baseline$' "$build/selection_fallback.env"

echo "== strict mode rejects the stale candidate"
if STRICT=1 MANIFEST=$build/manifest_bad.env OUT=$build/app_strict \
    RECORD=$build/selection_strict.env "$select" >/dev/null 2>&1; then
  echo "app: strict mode accepted a stale candidate" >&2
  exit 1
fi

echo "== the application behaves the same under both bodies"
cmp "$build/out_candidate.txt" "$build/out_fallback.txt"

echo "== the linked bodies are distinct"
objdump -d --disassemble=leanllvm_comma_mask8 "$build/app_candidate" \
  > "$build/dis_candidate.txt"
objdump -d --disassemble=leanllvm_comma_mask8 "$build/app_fallback" \
  > "$build/dis_baseline.txt"
if cmp -s "$build/dis_candidate.txt" "$build/dis_baseline.txt"; then
  echo "app: both executables contain the same body" >&2
  exit 1
fi

cat "$build/out_candidate.txt"
echo "app probe: ok"
