#!/usr/bin/env bash
# Drives the three counterexamples against the reviewed revision.
#
#   F1  the negative lemma in `LeanLLVMTest/Counterexamples.lean`, checked by
#       building `LeanLLVMTest` (the module pins its own axiom footprint);
#   F2  the two-register `phi` swap, model against clang;
#   F3  the `getelementptr` round trip, parsed, printed and assembled.
#
# F2 and F3 are failing-then-passing regression inputs: they exit nonzero while
# the defect they name is present, and pass once it is repaired.  This driver
# therefore exits nonzero on a revision where either is red, and prints one
# summary line per finding.
#
# Run from the repository root:
#
#     nix develop -c bash tests/counterexamples/check.sh
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
cd "$repo"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

echo "HEAD $(git rev-parse HEAD)"
echo "index $(git write-tree)"

echo "== F1: the universally quantified parser half is false =="
if probes/install/mem-capped.sh --cap 6G -- lake build LeanLLVMTest \
    >"$work/f1.log" 2>&1; then
  echo "F1 BUILD ok (the lemmas and their axiom pins elaborated)"
  f1=0
else
  sed 's/^/f1: /' "$work/f1.log" | tail -40
  echo "F1 BUILD failed"
  f1=2
fi

echo "== F1: the replacement holds at an accepting and a refusing run =="
if probes/install/mem-capped.sh --cap 6G -- lake env lean \
    tests/counterexamples/parser-half-outcome.lean >"$work/f1i.log" 2>&1; then
  echo "F1 INSTANCE ok (ParserHalfForOutcome at both runs, pins matched)"
  f1i=0
else
  sed 's/^/f1i: /' "$work/f1i.log" | tail -40
  echo "F1 INSTANCE failed"
  f1i=2
fi

echo "== F2: the two-register phi swap =="
bash "$here/phi-swap.sh" >"$work/f2.log" 2>&1
f2=$?
sed 's/^/f2: /' "$work/f2.log"

echo "== F3: the getelementptr round trip =="
bash "$here/gep-roundtrip.sh" >"$work/f3.log" 2>&1
f3=$?
sed 's/^/f3: /' "$work/f3.log"

verdict() { sed -n 's/^RESULT: //p' "$1" | awk 'NR == 1'; }
f2v=$(verdict "$work/f2.log")
f3v=$(verdict "$work/f3.log")

echo "== SUMMARY =="
if [ "$f1" -eq 0 ] && [ "$f1i" -eq 0 ]; then
  echo "F1 proved: the retired premise implies False, and the replacement holds at both runs"
else
  echo "F1 did not build or did not instantiate"
fi
echo "F2 ${f2v:-no result}"
echo "F3 ${f3v:-no result}"

if [ "$f1" -ne 0 ] || [ "$f1i" -ne 0 ] || [ "$f2" -gt 1 ] || [ "$f3" -gt 1 ]; then
  echo "DRIVER: NOT EXECUTABLE (a check could not run)"
  exit 2
fi
if [ "$f2" -ne 0 ] || [ "$f3" -ne 0 ]; then
  echo "DRIVER: red regression input present (expected until the defects are repaired)"
  exit 1
fi
echo "DRIVER: all three checks green"
exit 0
