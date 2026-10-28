#!/usr/bin/env bash
# Build a real application caller, the installation units it links against,
# and the manifest the shared selector verifies.  Writes to probes/app/build/.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
install=$(cd "$here/../install" && pwd)
build=${BUILD_DIR:-"$here/build"}
rm -rf "$build"
mkdir -p "$build"

# 1. Compile the application.  `-c App.c` needs the file under the working
#    directory, so it runs from here.
(cd "$here" && lean -c "$build/App.c" App.lean)
(cd "$build" && leanc -c App.c -o app.o 2>>"$build/leanc.log")

# 2. The call must survive the compiler: the extern has no body in this unit.
(cd "$build" && clang -O2 -S -emit-llvm App.c -o app.ll 2>>clang.log)
if ! grep -q 'call i64 @leanllvm_comma_mask8' "$build/app.ll"; then
  echo "app: the seam call did not survive compilation" >&2
  exit 1
fi
if ! nm -u "$build/app.o" | grep -q 'leanllvm_comma_mask8'; then
  echo "app: the application object does not import the seam" >&2
  exit 1
fi

# 3. The two installation units, built from the proved fixtures.  Basenames
#    are part of the input, as in probes/install/build.sh.
units=$build/units
mkdir -p "$units/baseline" "$units/candidate" "$units/loop"
for unit in baseline candidate loop; do
  dir=$units/$unit
  cp "$install/ir/$unit.ll" "$dir/$unit.ll"
  if [ "$unit" = loop ]; then
    cp "$install/ir/marker_loop.ll" "$dir/marker_$unit.ll"
  else
    cp "$install/ir/marker_$unit.ll" "$dir/marker_$unit.ll"
  fi
  (cd "$dir" &&
    clang -c "$unit.ll" -o "$unit.o" 2>>"$build/clang.log" &&
    clang -c "marker_$unit.ll" -o "marker_$unit.o" 2>>"$build/clang.log" &&
    ld -r "$unit.o" "marker_$unit.o" -o unit.o)
  cp "$dir/unit.o" "$build/$unit.o"
done

# 4. The units must agree on the differential corpus before either is used.
leanc "$install/diff.c" "$build/baseline.o" -o "$build/diff_baseline" 2>>"$build/leanc.log"
leanc "$install/diff.c" "$build/candidate.o" -o "$build/diff_candidate" 2>>"$build/leanc.log"
"$build/diff_baseline" > "$build/diff_baseline.txt"
"$build/diff_candidate" > "$build/diff_candidate.txt"
if ! cmp -s "$build/diff_baseline.txt" "$build/diff_candidate.txt"; then
  echo "app: the two units disagree on the differential corpus" >&2
  exit 1
fi
{
  echo "kind: differential"
  echo "symbol: leanllvm_comma_mask8"
  echo "corpus: probes/install/diff.c"
  echo "baseline_sha256: $(sha256sum "$build/baseline.o" | cut -d' ' -f1)"
  echo "candidate_sha256: $(sha256sum "$build/candidate.o" | cut -d' ' -f1)"
  echo "RESULT: PASS"
} > "$build/differential.txt"

# 5. Manifest in the shape probes/install/select.sh verifies.
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
baseline_fixture=$install/ir/baseline.ll
candidate_fixture=$install/ir/candidate.ll
loop_fixture=$install/ir/loop.ll
baseline_marker=$install/ir/marker_baseline.ll
candidate_marker=$install/ir/marker_candidate.ll
loop_marker=$install/ir/marker_loop.ll
baseline_fixture_sha256=$(sha "$install/ir/baseline.ll")
candidate_fixture_sha256=$(sha "$install/ir/candidate.ll")
loop_fixture_sha256=$(sha "$install/ir/loop.ll")
baseline_marker_sha256=$(sha "$install/ir/marker_baseline.ll")
candidate_marker_sha256=$(sha "$install/ir/marker_candidate.ll")
loop_marker_sha256=$(sha "$install/ir/marker_loop.ll")
caller=$build/app.o
baseline=$build/baseline.o
candidate=$build/candidate.o
loop=$build/loop.o
certificate=$build/differential.txt
caller_sha256=$(sha "$build/app.o")
baseline_sha256=$(sha "$build/baseline.o")
candidate_sha256=$(sha "$build/candidate.o")
loop_sha256=$(sha "$build/loop.o")
certificate_sha256=$(sha "$build/differential.txt")
EOF

echo "app: $build/manifest.env"
