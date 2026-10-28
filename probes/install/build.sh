#!/usr/bin/env bash
# Build the caller, baseline and candidate objects, the differential
# certificate, and the manifest. Run from anywhere; writes to
# probes/install/build/.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
build=${BUILD_DIR:-"$here/build"}
rm -rf "$build"
mkdir -p "$build"

cd "$here"
lean -c "$build/Caller.c" Caller.lean
lean -c "$build/Baseline.c" Baseline.lean
lean -c "$build/Candidate.c" Candidate.lean

cd "$build"
leanc -c Caller.c -o caller.o 2>>leanc.log
leanc -c Baseline.c -o baseline.o 2>>leanc.log
leanc -c Candidate.c -o candidate.o 2>>leanc.log

leanc "$here/diff.c" baseline.o -o diff_baseline 2>>leanc.log
leanc "$here/diff.c" candidate.o -o diff_candidate 2>>leanc.log

./diff_baseline > diff_baseline.txt
./diff_candidate > diff_candidate.txt
if ! cmp -s diff_baseline.txt diff_candidate.txt; then
  echo "build: differential test failed" >&2
  diff -u diff_baseline.txt diff_candidate.txt >&2 || true
  exit 1
fi

{
  echo "kind: differential"
  echo "symbol: leanllvm_comma_mask8"
  echo "corpus: probes/install/diff.c"
  echo "baseline_sha256: $(sha256sum baseline.o | cut -d' ' -f1)"
  echo "candidate_sha256: $(sha256sum candidate.o | cut -d' ' -f1)"
  echo "RESULT: PASS"
} > differential.txt

target="$(uname -m)-unknown-linux-gnu"
cat > manifest.env <<EOF
target=$target
caller=$build/caller.o
baseline=$build/baseline.o
candidate=$build/candidate.o
certificate=$build/differential.txt
caller_sha256=$(sha256sum caller.o | cut -d' ' -f1)
baseline_sha256=$(sha256sum baseline.o | cut -d' ' -f1)
candidate_sha256=$(sha256sum candidate.o | cut -d' ' -f1)
certificate_sha256=$(sha256sum differential.txt | cut -d' ' -f1)
EOF

echo "build: $build/manifest.env"
