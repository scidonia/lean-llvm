#!/usr/bin/env bash
# End-to-end installation check.  Run from the repository root through the
# flake, which provides lean, leanc, clang, ld and lake:
#
#   nix develop -c bash probes/install/check.sh
#
#   1. regenerate the emitted-IR fixtures from the Lean emission;
#   2. build the units, provenance objects and differential transcript; the
#      transcript's specification detector is shown to reject a known-wrong
#      seam before its verdict is used;
#   3. check the proof modules that pin the fixtures -- `CommaMaskIR` for the
#      baseline and candidate, `CommaMaskLoop` for the printed loop;
#   4. select the candidate, link and run;
#   5. corrupt the manifest's candidate hash, select the baseline, link and run;
#   6. strict mode rejects the stale candidate;
#   7. the loop unit has no covering theorem: strict mode refuses it, and
#      non-strict mode installs the baseline for the same request;
#   8. mutate the candidate fixture: the proof no longer checks and selection
#      falls back, then restore and confirm the proof checks again;
#   9. mutate the loop fixture: its pin no longer checks, then restore.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
build=${BUILD_DIR:-"$here/build"}

# `lake build` does not track `include_str` inputs, so a changed fixture alone
# does not invalidate a cached module.  The gate elaborates the module from
# source every time; `lake build` only warms the dependency oleans.  The loop's
# pin is a `#guard` over its own `include_str`, so it needs the same treatment
# after the fixture is printed again.
proof() { (cd "$repo" && lake env lean LeanLLVM/Vellum/CommaMaskIR.lean); }
warm() { (cd "$repo" && lake build LeanLLVM.Vellum.CommaMaskIR); }
loop_proof() { (cd "$repo" && lake env lean LeanLLVM/Vellum/CommaMaskLoop.lean); }
warm_loop() { (cd "$repo" && lake build LeanLLVM.Vellum.CommaMaskLoop); }

echo "== fixtures"
"$here/build.sh" >/dev/null
"$here/ir/capture.sh" >/dev/null
"$here/build.sh" >/dev/null

echo "== proof"
warm >/dev/null
proof >/dev/null
echo "proof: LeanLLVM.Vellum.CommaMaskIR checks"
warm_loop >/dev/null
loop_proof >/dev/null
echo "proof: LeanLLVM.Vellum.CommaMaskLoop checks against the printed loop fixture"

echo "== select candidate"
OUT=$build/app_candidate RECORD=$build/selection_candidate.env "$here/select.sh" >/dev/null
"$build/app_candidate" > "$build/out_candidate.txt"
grep -q '^impl=2$' "$build/out_candidate.txt"
grep -q '^selected=candidate$' "$build/selection_candidate.env"

echo "== stale candidate falls back"
cp "$build/manifest.env" "$build/manifest_bad.env"
sed -i 's/^candidate_sha256=.*/candidate_sha256=0000000000000000000000000000000000000000000000000000000000000000/' \
  "$build/manifest_bad.env"

MANIFEST=$build/manifest_bad.env OUT=$build/app_fallback \
  RECORD=$build/selection_fallback.env "$here/select.sh" >/dev/null
"$build/app_fallback" > "$build/out_fallback.txt"
grep -q '^impl=1$' "$build/out_fallback.txt"
grep -q '^selected=baseline$' "$build/selection_fallback.env"

echo "== strict rejects the stale candidate"
if STRICT=1 MANIFEST=$build/manifest_bad.env OUT=$build/app_strict \
    RECORD=$build/selection_strict.env "$here/select.sh" >/dev/null 2>&1; then
  echo "check: strict mode accepted a stale candidate" >&2
  exit 1
fi

echo "== semantic outputs agree"
grep -v '^impl=' "$build/out_candidate.txt" > "$build/sem_candidate.txt"
grep -v '^impl=' "$build/out_fallback.txt" > "$build/sem_baseline.txt"
cmp "$build/sem_candidate.txt" "$build/sem_baseline.txt"

echo "== the loop unit has no covering theorem and is refused"
if UNIT=loop STRICT=1 MANIFEST=$build/manifest.env OUT=$build/app_loop \
    RECORD=$build/selection_loop.env "$here/select.sh" >/dev/null 2>&1; then
  echo "check: strict mode accepted the loop unit" >&2
  exit 1
fi
if [ -e "$build/app_loop" ]; then
  echo "check: a loop executable was emitted" >&2
  exit 1
fi
if [ -f "$build/selection_loop.env" ] &&
    grep -qx 'selected=loop' "$build/selection_loop.env"; then
  echo "check: the selection record names the loop" >&2
  exit 1
fi
echo "select: refused the loop unit"

echo "== the same request without strict mode installs the baseline"
UNIT=loop MANIFEST=$build/manifest.env OUT=$build/app_loop_fallback \
  RECORD=$build/selection_loop_fallback.env "$here/select.sh" >/dev/null
grep -q '^selected=baseline$' "$build/selection_loop_fallback.env"
"$build/app_loop_fallback" > "$build/out_loop_fallback.txt"
grep -q '^impl=1$' "$build/out_loop_fallback.txt"
grep -v '^impl=' "$build/out_loop_fallback.txt" > "$build/sem_loop.txt"
cmp "$build/sem_candidate.txt" "$build/sem_loop.txt"

echo "== a mutated fixture invalidates the certificate"
cp "$here/ir/candidate.ll" "$build/candidate.ll.bak"
restore() { cp "$build/candidate.ll.bak" "$here/ir/candidate.ll"; }
trap restore EXIT
sed -i 's/or i64 %i5, 32768/or i64 %i5, 32769/' "$here/ir/candidate.ll"

if proof >/dev/null 2>&1; then
  echo "check: the proof module still checks after a fixture change" >&2
  exit 1
fi
echo "proof: rejected the mutated fixture"

if STRICT=1 OUT=$build/app_mutated RECORD=$build/selection_mutated.env \
    "$here/select.sh" >/dev/null 2>&1; then
  echo "check: selection accepted a mutated fixture" >&2
  exit 1
fi
echo "select: rejected the mutated fixture"

restore
trap - EXIT
proof >/dev/null
echo "proof: restored fixture checks again"

echo "== a mutated loop fixture invalidates the loop pin"
cp "$here/ir/loop.ll" "$build/loop.ll.bak"
restore_loop() { cp "$build/loop.ll.bak" "$here/ir/loop.ll"; }
trap restore_loop EXIT
sed -i 's/xor i64 %arg, 3182967604875373612/xor i64 %arg, 3182967604875373613/' \
  "$here/ir/loop.ll"
if ! grep -q '3182967604875373613' "$here/ir/loop.ll"; then
  echo "check: the loop mutation did not apply to $here/ir/loop.ll" >&2
  exit 1
fi

if loop_proof >/dev/null 2>&1; then
  echo "check: the loop pin still checks after a fixture change" >&2
  exit 1
fi
echo "proof: rejected the mutated loop fixture"

restore_loop
trap - EXIT
loop_proof >/dev/null
echo "proof: restored loop fixture checks again"

echo "install probe: ok"
