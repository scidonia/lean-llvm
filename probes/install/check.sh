#!/usr/bin/env bash
# End-to-end installation probe:
#   1. build caller, baseline, candidate and the differential certificate;
#   2. select the candidate, link and run;
#   3. corrupt the manifest's candidate hash, select the baseline, link and run;
#   4. strict mode rejects the stale candidate;
#   5. the semantic outputs of both binaries agree.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
build=$here/build

"$here/build.sh"

OUT=$build/app_candidate RECORD=$build/selection_candidate.env "$here/select.sh"
"$build/app_candidate" > "$build/out_candidate.txt"
grep -q '^impl=2$' "$build/out_candidate.txt"
grep -q '^selected=candidate$' "$build/selection_candidate.env"

cp "$build/manifest.env" "$build/manifest_bad.env"
sed -i 's/^candidate_sha256=.*/candidate_sha256=0000000000000000000000000000000000000000000000000000000000000000/' \
  "$build/manifest_bad.env"

MANIFEST=$build/manifest_bad.env OUT=$build/app_fallback \
  RECORD=$build/selection_fallback.env "$here/select.sh"
"$build/app_fallback" > "$build/out_fallback.txt"
grep -q '^impl=1$' "$build/out_fallback.txt"
grep -q '^selected=baseline$' "$build/selection_fallback.env"

if STRICT=1 MANIFEST=$build/manifest_bad.env OUT=$build/app_strict \
    RECORD=$build/selection_strict.env "$here/select.sh" >/dev/null 2>&1; then
  echo "check: strict mode accepted a stale candidate" >&2
  exit 1
fi

grep -v '^impl=' "$build/out_candidate.txt" > "$build/sem_candidate.txt"
grep -v '^impl=' "$build/out_fallback.txt" > "$build/sem_baseline.txt"
cmp "$build/sem_candidate.txt" "$build/sem_baseline.txt"

echo "install probe: ok"
