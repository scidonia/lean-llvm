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

echo "== the loop unit has no covering theorem and is refused"
if UNIT=loop STRICT=1 MANIFEST=$build/manifest.env OUT=$build/app_loop_strict \
    RECORD=$build/selection_loop_strict.env "$select" >/dev/null 2>&1; then
  echo "app: strict mode accepted the loop unit" >&2
  exit 1
fi
if [ -e "$build/app_loop_strict" ]; then
  echo "app: a loop executable was emitted" >&2
  exit 1
fi
echo "select: refused the loop unit"

echo "== the same request without strict mode installs the baseline"
UNIT=loop MANIFEST=$build/manifest.env OUT=$build/app_loop \
  RECORD=$build/selection_loop.env "$select" >/dev/null
grep -q '^selected=baseline$' "$build/selection_loop.env"
"$build/app_loop" > "$build/out_loop.txt"
cmp "$build/out_candidate.txt" "$build/out_loop.txt"

echo "== the application behaves the same under both bodies"
cmp "$build/out_candidate.txt" "$build/out_fallback.txt"

echo "== the linked bodies are distinct"
# Compare the seam's own instruction lines.  The whole objdump listing is not a
# comparison of bodies: its first line names the object's path, and the function
# need not be placed at the same address in the two executables.  The address
# column is therefore stripped, as are the file and symbol headers and the
# sections that follow the function.
dis_body() { # executable out
  if ! objdump -d --disassemble=leanllvm_comma_mask8 "$1" > "$2.full" 2>/dev/null; then
    echo "app: objdump failed on $1" >&2
    return 1
  fi
  awk '/<leanllvm_comma_mask8>:/ { body = 1; next }
       body && /^Disassembly of section/ { exit }
       body { print }' "$2.full" \
    | sed 's/^[[:space:]]*[0-9a-f]*:[[:space:]]*//' > "$2"
  rm -f "$2.full"
  if [ ! -s "$2" ]; then
    echo "app: no disassembly of leanllvm_comma_mask8 in $1" >&2
    return 1
  fi
}
dis_body "$build/app_candidate" "$build/dis_candidate.txt"
dis_body "$build/app_fallback" "$build/dis_baseline.txt"
dis_body "$build/app_candidate" "$build/dis_candidate_control.txt"
# The same detector must find the candidate listing equal to itself, otherwise a
# failing or empty extraction would make any pair of bodies look distinct.
if ! cmp -s "$build/dis_candidate.txt" "$build/dis_candidate_control.txt"; then
  echo "app: the instruction-body extraction is not reproducible" >&2
  exit 1
fi
if cmp -s "$build/dis_candidate.txt" "$build/dis_baseline.txt"; then
  echo "app: both executables contain the same body" >&2
  exit 1
fi

cat "$build/out_candidate.txt"
echo "app probe: ok"
