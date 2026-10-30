#!/usr/bin/env bash
# Build the installation units the certificate covers, the provenance objects,
# the differential transcript and the manifest.  Run from anywhere; writes to
# probes/install/build/.
#
# The installed units are compiled from the emitted IR in probes/install/ir/.
# `LeanLLVM/Vellum/CommaMaskIR.lean` parses and pins `baseline.ll` and
# `candidate.ll`, so those objects are the programs the refinement theorem is
# about.  `Baseline.lean` and `Candidate.lean` are still compiled, as provenance
# objects: the differential transcript checks that each proved unit agrees with
# the Lean-emitted body on the corpus.
#
# `loop.ll` is printed from the `loopFunction` AST by
# `lake exe leanllvm-loop-emit` (the framework's printer, not `lean -c`), and
# `LeanLLVM/Vellum/CommaMaskLoop.lean` parses and pins it.  The loop is built
# and compared too, but no checked theorem binds the loop object to the seam's
# contract: `theorem=` below covers the candidate and the baseline only, so
# `select.sh` refuses `UNIT=loop` and the transcript records that.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
build=${BUILD_DIR:-"$here/build"}
rm -rf "$build"
mkdir -p "$build"

# Basenames are part of the build input: clang records the module name in the
# object, so `select.sh` has to rebuild under the same names to compare.
units=$build/units
mkdir -p "$units/baseline" "$units/candidate" "$units/loop"

# 1. The caller sees only opaque declarations.
lean -c "$build/Caller.c" "$here/Caller.lean"
(cd "$build" && leanc -c Caller.c -o caller.o 2>>"$build/leanc.log")

# 2. Provenance: the Lean-emitted bodies, not installed.
lean -c "$build/Baseline.c" "$here/Baseline.lean"
lean -c "$build/Candidate.c" "$here/Candidate.lean"
(cd "$build" &&
  leanc -c Baseline.c -o lean_baseline.o 2>>"$build/leanc.log" &&
  leanc -c Candidate.c -o lean_candidate.o 2>>"$build/leanc.log")

# 3. Installed units: the proved fixture plus its marker object.
for unit in baseline candidate loop; do
  dir=$units/$unit
  cp "$here/ir/$unit.ll" "$dir/$unit.ll"
  if [ "$unit" = loop ]; then
    cp "$here/ir/marker_loop.ll" "$dir/marker_$unit.ll"
  else
    cp "$here/ir/marker_$unit.ll" "$dir/marker_$unit.ll"
  fi
  (cd "$dir" &&
    clang -c "$unit.ll" -o "$unit.o" 2>>"$build/clang.log" &&
    clang -c "marker_$unit.ll" -o "marker_$unit.o" 2>>"$build/clang.log" &&
    ld -r "$unit.o" "marker_$unit.o" -o unit.o)
  cp "$dir/unit.o" "$build/$unit.o"
done

# 4. Differential transcript: every body must agree with every other on the
#    corpus, and each must agree with the lane-wise specification `diff.c`
#    computes itself.  A `mismatch` line makes the program exit nonzero, so
#    agreement between two bodies cannot hide a shared error.
#
#    The detector is shown to detect before its verdict is used: a seam that
#    returns zero for every input is linked against the same `diff.c` and must
#    be reported on 0x2C, where the comma-XOR word has a zero byte and the
#    specification is 0x80.  That object is a build artefact for this control;
#    no manifest names it.
cat > "$build/wrong_seam.c" <<'C'
#include <stdint.h>

/* Zero for every input: wrong for any word with a comma byte. */
uint64_t leanllvm_comma_mask8(uint64_t x) { (void)x; return 0; }
C
leanc -c "$build/wrong_seam.c" -o "$build/wrong_seam.o" 2>>"$build/leanc.log"
leanc "$here/diff.c" "$build/wrong_seam.o" -o "$build/diff_wrong" 2>>"$build/leanc.log"
if "$build/diff_wrong" > "$build/diff_wrong.txt"; then
  echo "build: the specification detector accepted a seam that returns zero for every input" >&2
  exit 1
fi
if ! grep -q '^mismatch 44 ' "$build/diff_wrong.txt"; then
  echo "build: the specification detector did not report the comma-byte input 0x2C" >&2
  cat "$build/diff_wrong.txt" >&2
  exit 1
fi

leanc "$here/diff.c" "$build/baseline.o" -o "$build/diff_baseline" 2>>"$build/leanc.log"
leanc "$here/diff.c" "$build/candidate.o" -o "$build/diff_candidate" 2>>"$build/leanc.log"
leanc "$here/diff.c" "$build/lean_baseline.o" -o "$build/diff_lean_baseline" 2>>"$build/leanc.log"
leanc "$here/diff.c" "$build/loop.o" -o "$build/diff_loop" 2>>"$build/leanc.log"
leanc "$here/diff.c" "$build/lean_candidate.o" -o "$build/diff_lean_candidate" 2>>"$build/leanc.log"

for body in baseline candidate loop lean_baseline lean_candidate; do
  if ! "$build/diff_$body" > "$build/diff_$body.txt"; then
    echo "build: $body does not match the specification on the corpus" >&2
    grep '^mismatch ' "$build/diff_$body.txt" >&2 || true
    exit 1
  fi
done
for out in diff_candidate diff_loop diff_lean_baseline diff_lean_candidate; do
  if ! cmp -s "$build/diff_baseline.txt" "$build/$out.txt"; then
    echo "build: differential test failed against $out" >&2
    diff -u "$build/diff_baseline.txt" "$build/$out.txt" >&2 || true
    exit 1
  fi
done

{
  echo "kind: differential"
  echo "symbol: leanllvm_comma_mask8"
  echo "corpus: probes/install/diff.c"
  echo "specification: probes/install/diff.c (lane-wise mask, independent of the bodies)"
  echo "bodies: proved-baseline proved-candidate proved-loop lean-baseline lean-candidate"
  echo "covers: candidate-vs-baseline"
  echo "not-covered: loop (no checked theorem for the loop body)"
  echo "baseline_sha256: $(sha256sum "$build/baseline.o" | cut -d' ' -f1)"
  echo "candidate_sha256: $(sha256sum "$build/candidate.o" | cut -d' ' -f1)"
  echo "loop_sha256: $(sha256sum "$build/loop.o" | cut -d' ' -f1)"
  echo "RESULT: PASS"
} > "$build/differential.txt"

# The target the objects were built for, and the data layout clang uses for it.
target="$(clang -print-target-triple)"
datalayout="$(printf '' | clang -O0 -S -emit-llvm -x c - -o - \
  | sed -n 's/^target datalayout = "\(.*\)"$/\1/p')"
triple="$target"
sha() { sha256sum "$1" | cut -d' ' -f1; }
cat > "$build/manifest.env" <<EOF
kind=proof-bound
target=$target
triple=$target
symbol=leanllvm_comma_mask8
marker=leanllvm_impl_id
contract=LeanLLVM.Vellum.commaContract
theorem=LeanLLVM.Vellum.CommaMaskIR.IR_refines
attributes=reject
datalayout=$datalayout
target_features=none
baseline_fixture=$here/ir/baseline.ll
candidate_fixture=$here/ir/candidate.ll
loop_fixture=$here/ir/loop.ll
baseline_marker=$here/ir/marker_baseline.ll
candidate_marker=$here/ir/marker_candidate.ll
loop_marker=$here/ir/marker_loop.ll
baseline_fixture_sha256=$(sha "$here/ir/baseline.ll")
candidate_fixture_sha256=$(sha "$here/ir/candidate.ll")
loop_fixture_sha256=$(sha "$here/ir/loop.ll")
baseline_marker_sha256=$(sha "$here/ir/marker_baseline.ll")
candidate_marker_sha256=$(sha "$here/ir/marker_candidate.ll")
loop_marker_sha256=$(sha "$here/ir/marker_loop.ll")
caller=$build/caller.o
baseline=$build/baseline.o
candidate=$build/candidate.o
loop=$build/loop.o
certificate=$build/differential.txt
caller_sha256=$(sha "$build/caller.o")
baseline_sha256=$(sha "$build/baseline.o")
candidate_sha256=$(sha "$build/candidate.o")
loop_sha256=$(sha "$build/loop.o")
certificate_sha256=$(sha "$build/differential.txt")
lean_baseline_sha256=$(sha "$build/lean_baseline.o")
lean_candidate_sha256=$(sha "$build/lean_candidate.o")
EOF

echo "build: $build/manifest.env"
