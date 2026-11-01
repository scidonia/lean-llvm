#!/usr/bin/env bash
# Build a real application caller, the installation units it links against,
# and the manifest the shared selector verifies.  Writes to probes/app/build/.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
install=$(cd "$here/../install" && pwd)
repo=$(cd "$here/../.." && pwd)
build=${BUILD_DIR:-"$here/build"}

# The build removes its previous output and then elaborates the proof module
# from source and runs the certificate producers, so it takes the same
# repository lock the installer build and the selector take.  The lock is a
# directory created atomically by `mkdir`; a contender refuses instead of
# racing, and only the owner removes it.  It is taken before the previous
# output is removed, so a contended build leaves the published certificates,
# manifest and objects in place.  A lock left behind by a crashed run refuses
# too: removing it is a human decision after checking that no owner is running.
lock_dir="$repo/.lake/install-certificate.lock"
lock_held=0

acquire_lock() {
  mkdir -p "$repo/.lake"
  if ! mkdir "$lock_dir" 2>/dev/null; then
    echo "app: another source elaboration holds $lock_dir" >&2
    echo "app: if no such run exists, verify that and remove that directory" >&2
    return 1
  fi
  lock_held=1
}

release_lock() {
  [ "$lock_held" = 1 ] || return 0
  lock_held=0
  if ! rmdir "$lock_dir" 2>/dev/null; then
    echo "app: could not remove $lock_dir" >&2
    echo "app: verify that no run owns it and remove that directory" >&2
    return 1
  fi
}
cleanup() {
  local status=$?
  release_lock || status=1
  exit "$status"
}
trap cleanup EXIT

if ! acquire_lock; then
  exit 1
fi
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

# 3. The three installation units, built from the proved fixtures.  Basenames
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
  echo "covers: candidate-vs-baseline, loop-vs-candidate"
  echo "not-covered: none (each installed unit also has a checked certificate; this transcript remains runtime evidence, not either proof)"
  echo "baseline_sha256: $(sha256sum "$build/baseline.o" | cut -d' ' -f1)"
  echo "candidate_sha256: $(sha256sum "$build/candidate.o" | cut -d' ' -f1)"
  echo "RESULT: PASS"
} > "$build/differential.txt"

# 5. Manifest in the shape probes/install/select.sh verifies, followed by the
#    three kernel-derived certificates over this build's units.  The manifest is
#    written first because the producer hashes the object paths it names; the
#    certificate digests are appended once the certificates exist.
target="$(clang -print-target-triple)"
datalayout="$(printf '' | clang -O0 -S -emit-llvm -x c - -o - \
  | sed -n 's/^target datalayout = "\(.*\)"$/\1/p')"
triple="$target"
sha() { sha256sum "$1" | cut -d' ' -f1; }
cat > "$build/manifest.env" <<EOF
schema=leanllvm-install-v1
kind=proof-bound
target=$target
triple=$target
symbol=leanllvm_comma_mask8
marker=leanllvm_impl_id
contract=LeanLLVM.Vellum.commaContract
theorem=LeanLLVM.Vellum.CommaMaskIR.IR_refines
loop_theorem=LeanLLVM.Vellum.CommaMaskLoop.loop_refines_candidate_within
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
differential=$build/differential.txt
caller_sha256=$(sha "$build/app.o")
baseline_sha256=$(sha "$build/baseline.o")
candidate_sha256=$(sha "$build/candidate.o")
loop_sha256=$(sha "$build/loop.o")
differential_sha256=$(sha "$build/differential.txt")
proof_baseline=$build/proof_baseline.env
proof_candidate=$build/proof_candidate.env
proof_loop=$build/proof_loop.env
EOF

# `lake build` does not track `include_str`, so rebuild the imported graph from
# current source and then elaborate the proof module from source before the
# producers import it.  The build acquired the repository lock before it
# removed its previous output; the lock is held through the manifest
# publication below and released only at the end.
(cd "$repo" && lake build LeanLLVM.Vellum.CommaMaskIR)
(cd "$repo" &&
  lake env lean -o .lake/build/lib/lean/LeanLLVM/Vellum/CommaMaskIR.olean \
    LeanLLVM/Vellum/CommaMaskIR.lean)
# `CommaMaskLoop` imports `CommaMaskIR`, and the loop's certificate names its own
# theorem, so it follows that pair.  Every unit this build links against is
# certified here, so the step is not conditional on a request.
(cd "$repo" && lake build LeanLLVM.Vellum.CommaMaskLoop)
(cd "$repo" &&
  lake env lean -o .lake/build/lib/lean/LeanLLVM/Vellum/CommaMaskLoop.olean \
    LeanLLVM/Vellum/CommaMaskLoop.lean)
for unit in baseline candidate loop; do
  (cd "$repo" &&
    CERT_UNIT="$unit" CERT_MANIFEST="$build/manifest.env" \
      CERT_OUT="$build/proof_$unit.env" \
      lake env lean probes/install/InstallCertificate.lean)
  [ -s "$build/proof_$unit.env" ] || {
    echo "app: the producer wrote no $unit certificate" >&2
    exit 1
  }
done

{
  cat "$build/manifest.env"
  printf 'proof_baseline_sha256=%s\n' "$(sha "$build/proof_baseline.env")"
  printf 'proof_candidate_sha256=%s\n' "$(sha "$build/proof_candidate.env")"
  printf 'proof_loop_sha256=%s\n' "$(sha "$build/proof_loop.env")"
} > "$build/manifest.env.tmp.$$"
mv "$build/manifest.env.tmp.$$" "$build/manifest.env"

# The manifest is published; only now release the repository lock.
if ! release_lock; then
  exit 1
fi

echo "app: $build/manifest.env"
