#!/usr/bin/env bash
# Build the installation units the certificate covers, the provenance objects,
# the kernel-derived certificates, the differential transcript and the
# manifest.  Run from anywhere; writes to probes/install/build/.
#
# Everything is built in a private staging directory under the output
# directory and published only after every check has passed, one file at a
# time with the manifest last.  A failure before publication leaves the
# published set untouched; a failure during the per-file publication sequence
# is fail-closed, because the manifest is renamed last and a selector that
# meets a mismatched object refuses it.
#
# The installed units are compiled from the emitted IR in probes/install/ir/.
# `LeanLLVM/Vellum/CommaMaskIR.lean` parses and pins `baseline.ll` and
# `candidate.ll`; the compiled objects are hash-bound to those fixtures by
# rebuild, not proved equivalent to them as compiled or running code.
# `Baseline.lean` and `Candidate.lean` are still compiled, as provenance
# objects: the differential transcript checks that each proved unit agrees with
# the Lean-emitted body on the corpus.
#
# `loop.ll` is printed from the `loopFunction` AST by
# `lake exe leanllvm-loop-emit` (the framework's printer, not `lean -c`), and
# `LeanLLVM/Vellum/CommaMaskLoop.lean` parses and pins it.  The loop is built,
# compared and certified: its own `loop_theorem=` field names
# `loop_refines_candidate_within`, the loop's certificate records that statement
# and `select.sh` installs `UNIT=loop` from it exactly as it installs the other
# two units from `theorem=`.
#
# The three kernel-derived certificates are produced before the differential
# detector runs, so a fixture-pin failure is reported by the source
# elaboration that has to see it, not masked by a runtime comparison.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
build=${BUILD_DIR:-"$here/build"}
mkdir -p "$build"

# One source-elaboration writer at a time in this repository.  The build and
# the selector both rebuild the proof module's imported graph, rewrite its olean
# and then import it, so the graph rebuild, the source elaboration, both
# certificate producers and the publication below run under one lock.  The lock
# is a directory created atomically by `mkdir`; a contender refuses before this
# build mutates any published output, and only the owner removes it.  A lock
# left behind by a crashed run refuses too: removing it is a human decision
# after checking that no owner is running.
lock_dir="$repo/.lake/install-certificate.lock"
lock_held=0

acquire_lock() {
  mkdir -p "$repo/.lake"
  if ! mkdir "$lock_dir" 2>/dev/null; then
    echo "build: another source elaboration holds $lock_dir" >&2
    echo "build: if no such run exists, verify that and remove that directory" >&2
    return 1
  fi
  lock_held=1
}

release_lock() {
  [ "$lock_held" = 1 ] || return 0
  lock_held=0
  if ! rmdir "$lock_dir" 2>/dev/null; then
    echo "build: could not remove $lock_dir" >&2
    echo "build: verify that no run owns it and remove that directory" >&2
    return 1
  fi
}

# A private staging directory in the output's own filesystem, so the final
# rename is atomic.  It is created only after the lock is held, so a contended
# build does not even stage anything under the output directory.
staging=
# Cleanup must not hide a failure: if the lock cannot be removed, retain it and
# exit nonzero rather than reporting success.
cleanup() {
  local status=$?
  release_lock || status=1
  if [ -n "$staging" ]; then
    rm -rf "$staging"
  fi
  exit "$status"
}
trap cleanup EXIT

if ! acquire_lock; then
  exit 1
fi
staging=$(mktemp -d "$build/staging.XXXXXX")

sha() { sha256sum "$1" | cut -d' ' -f1; }

# Publish one file by renaming a copy from the staging directory, so a reader
# sees the old bytes or the new bytes and never a partial file.
publish() { # name
  local name=$1
  cp "$staging/$name" "$build/$name.tmp.$$"
  mv "$build/$name.tmp.$$" "$build/$name"
}

# Basenames are part of the build input: clang records the module name in the
# object, so `select.sh` has to rebuild under the same names to compare.
units=$staging/units
mkdir -p "$units/baseline" "$units/candidate" "$units/loop"

# 1. The caller sees only opaque declarations.
lean -c "$staging/Caller.c" "$here/Caller.lean"
(cd "$staging" && leanc -c Caller.c -o caller.o 2>>"$staging/leanc.log")

# 2. Provenance: the Lean-emitted bodies, not installed.
lean -c "$staging/Baseline.c" "$here/Baseline.lean"
lean -c "$staging/Candidate.c" "$here/Candidate.lean"
(cd "$staging" &&
  leanc -c Baseline.c -o lean_baseline.o 2>>"$staging/leanc.log" &&
  leanc -c Candidate.c -o lean_candidate.o 2>>"$staging/leanc.log")

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
    clang -c "$unit.ll" -o "$unit.o" 2>>"$staging/clang.log" &&
    clang -c "marker_$unit.ll" -o "marker_$unit.o" 2>>"$staging/clang.log" &&
    ld -r "$unit.o" "marker_$unit.o" -o unit.o)
  cp "$dir/unit.o" "$staging/$unit.o"
done

# 4. The target the objects were built for, and the data layout clang uses.
target="$(clang -print-target-triple)"
datalayout="$(printf '' | clang -O0 -S -emit-llvm -x c - -o - \
  | sed -n 's/^target datalayout = "\(.*\)"$/\1/p')"
triple="$target"

# The manifest's common fields.  `$1` is the directory whose object paths the
# record binds: the staging directory for the preliminary record the certificate
# producer hashes, the output directory for the published record.  `$2` is the
# directory whose bytes the hashes describe; the final record names the
# published paths but hashes the staged bytes being published.
manifest_common() { # object directory, hash directory
  local objects=$1 hashes=${2:-$1}
  cat <<EOF
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
caller=$objects/caller.o
baseline=$objects/baseline.o
candidate=$objects/candidate.o
loop=$objects/loop.o
caller_sha256=$(sha "$hashes/caller.o")
baseline_sha256=$(sha "$hashes/baseline.o")
candidate_sha256=$(sha "$hashes/candidate.o")
loop_sha256=$(sha "$hashes/loop.o")
EOF
}

# 5. The preliminary record names the staged object bytes; the certificate
#    producer hashes those bytes, and they are the bytes published below.
{
  manifest_common "$staging"
  printf 'proof_baseline=%s\n' "$staging/proof_baseline.env"
  printf 'proof_candidate=%s\n' "$staging/proof_candidate.env"
  printf 'proof_loop=%s\n' "$staging/proof_loop.env"
} > "$staging/manifest.env"

# 6. The kernel-derived certificates.  `lake build` does not track
#    `include_str` inputs, so the proof module is elaborated from source first;
#    the producer then imports that fresh module, checks the theorem statement,
#    the contract link and the axiom footprint, and writes the certificate.
#    Lake tracks imported project source but not the `include_str` fixtures, so
#    the imported graph is rebuilt from current source first, then the proof
#    module is re-elaborated from source to force the fixture guards.  The
#    source elaboration must succeed before any certificate is produced, and
#    every command runs from the repository root under the held lock.
#    `CommaMaskLoop` imports `CommaMaskIR` and the loop's certificate names its
#    own theorem, so it is reconciled and re-elaborated after that pair: its
#    proof module must see the already-freshened `CommaMaskIR` olean.
source_check() {
  (cd "$repo" && lake build LeanLLVM.Vellum.CommaMaskIR) &&
  (cd "$repo" &&
    lake env lean -o .lake/build/lib/lean/LeanLLVM/Vellum/CommaMaskIR.olean \
      LeanLLVM/Vellum/CommaMaskIR.lean) &&
  (cd "$repo" && lake build LeanLLVM.Vellum.CommaMaskLoop) &&
  (cd "$repo" &&
    lake env lean -o .lake/build/lib/lean/LeanLLVM/Vellum/CommaMaskLoop.olean \
      LeanLLVM/Vellum/CommaMaskLoop.lean)
}
certificate() { # unit
  local unit=$1
  (cd "$repo" &&
    CERT_UNIT="$unit" CERT_MANIFEST="$staging/manifest.env" \
      CERT_OUT="$staging/proof_$unit.env" \
      lake env lean probes/install/InstallCertificate.lean)
  [ -s "$staging/proof_$unit.env" ] || {
    echo "build: the producer wrote no $unit certificate" >&2
    exit 1
  }
}
source_check
certificate baseline
certificate candidate
certificate loop

# 7. Differential transcript: every body must agree with every other on the
#    corpus, and each must agree with the lane-wise specification `diff.c`
#    computes itself.  A `mismatch` line makes the program exit nonzero, so
#    agreement between two bodies cannot hide a shared error.  This is runtime
#    evidence, not a proof; the certificates above are the installation proof.
#
#    The detector is shown to detect before its verdict is used: a seam that
#    returns zero for every input is linked against the same `diff.c` and must
#    be reported on 0x2C, where the comma-XOR word has a zero byte and the
#    specification is 0x80.  That object is a build artefact for this control;
#    no manifest names it.
cat > "$staging/wrong_seam.c" <<'C'
#include <stdint.h>

/* Zero for every input: wrong for any word with a comma byte. */
uint64_t leanllvm_comma_mask8(uint64_t x) { (void)x; return 0; }
C
leanc -c "$staging/wrong_seam.c" -o "$staging/wrong_seam.o" 2>>"$staging/leanc.log"
leanc "$here/diff.c" "$staging/wrong_seam.o" -o "$staging/diff_wrong" 2>>"$staging/leanc.log"
if "$staging/diff_wrong" > "$staging/diff_wrong.txt"; then
  echo "build: the specification detector accepted a seam that returns zero for every input" >&2
  exit 1
fi
if ! grep -q '^mismatch 44 ' "$staging/diff_wrong.txt"; then
  echo "build: the specification detector did not report the comma-byte input 0x2C" >&2
  cat "$staging/diff_wrong.txt" >&2
  exit 1
fi

leanc "$here/diff.c" "$staging/baseline.o" -o "$staging/diff_baseline" 2>>"$staging/leanc.log"
leanc "$here/diff.c" "$staging/candidate.o" -o "$staging/diff_candidate" 2>>"$staging/leanc.log"
leanc "$here/diff.c" "$staging/lean_baseline.o" -o "$staging/diff_lean_baseline" 2>>"$staging/leanc.log"
leanc "$here/diff.c" "$staging/loop.o" -o "$staging/diff_loop" 2>>"$staging/leanc.log"
leanc "$here/diff.c" "$staging/lean_candidate.o" -o "$staging/diff_lean_candidate" 2>>"$staging/leanc.log"

for body in baseline candidate loop lean_baseline lean_candidate; do
  if ! "$staging/diff_$body" > "$staging/diff_$body.txt"; then
    echo "build: $body does not match the specification on the corpus" >&2
    grep '^mismatch ' "$staging/diff_$body.txt" >&2 || true
    exit 1
  fi
done
for out in diff_candidate diff_loop diff_lean_baseline diff_lean_candidate; do
  if ! cmp -s "$staging/diff_baseline.txt" "$staging/$out.txt"; then
    echo "build: differential test failed against $out" >&2
    diff -u "$staging/diff_baseline.txt" "$staging/$out.txt" >&2 || true
    exit 1
  fi
done

{
  echo "kind: differential"
  echo "symbol: leanllvm_comma_mask8"
  echo "corpus: probes/install/diff.c"
  echo "specification: probes/install/diff.c (lane-wise mask, independent of the bodies)"
  echo "bodies: proved-baseline proved-candidate proved-loop lean-baseline lean-candidate"
  echo "covers: candidate-vs-baseline, loop-vs-candidate"
  echo "not-covered: none (each installed unit also has a checked certificate; this transcript remains runtime evidence, not either proof)"
  echo "baseline_sha256: $(sha "$staging/baseline.o")"
  echo "candidate_sha256: $(sha "$staging/candidate.o")"
  echo "loop_sha256: $(sha "$staging/loop.o")"
  echo "RESULT: PASS"
} > "$staging/differential.txt"

# 8. The published manifest binds the published object bytes, the differential
#    transcript as ancillary evidence, and the two certificates.  It is
#    assembled from the same bytes that are published below.
{
  manifest_common "$build" "$staging"
  printf 'differential=%s\n' "$build/differential.txt"
  printf 'differential_sha256=%s\n' "$(sha "$staging/differential.txt")"
  printf 'proof_baseline=%s\n' "$build/proof_baseline.env"
  printf 'proof_candidate=%s\n' "$build/proof_candidate.env"
  printf 'proof_loop=%s\n' "$build/proof_loop.env"
  printf 'proof_baseline_sha256=%s\n' "$(sha "$staging/proof_baseline.env")"
  printf 'proof_candidate_sha256=%s\n' "$(sha "$staging/proof_candidate.env")"
  printf 'proof_loop_sha256=%s\n' "$(sha "$staging/proof_loop.env")"
} > "$staging/manifest.final.env"

# 9. Publish.  Every object and evidence file first, then the certificates,
#    then the manifest, all while this build holds the repository lock.  A
#    selector takes the same lock, so it cannot observe the transition: it
#    refuses while the lock is held, and never sees a new manifest pointing at
#    old bytes.
for name in Caller.c Baseline.c Candidate.c caller.o lean_baseline.o \
  lean_candidate.o baseline.o candidate.o loop.o wrong_seam.c wrong_seam.o \
  diff_wrong diff_wrong.txt diff_baseline diff_baseline.txt diff_candidate \
  diff_candidate.txt diff_loop diff_loop.txt diff_lean_baseline \
  diff_lean_baseline.txt diff_lean_candidate diff_lean_candidate.txt \
  clang.log leanc.log; do
  [ -e "$staging/$name" ] && publish "$name"
done
publish differential.txt
publish proof_baseline.env
publish proof_candidate.env
publish proof_loop.env
cp "$staging/manifest.final.env" "$build/manifest.env.tmp.$$"
mv "$build/manifest.env.tmp.$$" "$build/manifest.env"

# Every staged file and the manifest are published; only now release the lock
# that kept a selector from observing the transition.  A failed release is a
# fault in the run, not a warning.
if ! release_lock; then
  exit 1
fi

echo "build: $build/manifest.env"
