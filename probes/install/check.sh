#!/usr/bin/env bash
# End-to-end installation check.  Run from the repository root through the
# flake, which provides lean, leanc, clang, ld and lake:
#
#   nix develop -c bash probes/install/check.sh
#
#   1. warm the dependency oleans, regenerate the emitted-IR fixtures from the
#      Lean emission, and build the units, provenance objects, certificates,
#      differential transcript and manifest;
#   2. check the proof modules that pin the fixtures -- `CommaMaskIR` for the
#      baseline and candidate, `CommaMaskLoop` for the printed loop;
#   3. select the candidate, link and run;
#   4. corrupt the manifest's candidate hash, select the baseline, link and run;
#   5. strict mode rejects the stale candidate;
#   6. the loop unit installs from its own certificate in strict and non-strict
#      mode; a stale loop hash falls back to the baseline in non-strict mode and
#      is rejected in strict mode;
#   7. mutate the candidate fixture: the real build route fails at the source
#      elaboration's `#guard`, publishes no new certificate or manifest, and
#      leaves the published certificate bytes untouched; restore, rebuild and
#      require the same certificate bytes as the positive control;
#   8. mutate the loop fixture: its pin no longer checks, then restore;
#   9. transiently append an invalid Lean line to the imported proof source
#      `CommaMaskKernel.lean` under a restoring trap: the real build refuses and
#      publishes nothing, the strict selector refuses, the non-strict selector
#      falls back with the rejection reason, and after restoring the source a
#      fresh build reproduces the certificate;
#  10. run the certificate gate matrix: one invocation per certificate field in
#      strict and non-strict mode, the absent-artifact routes, the four
#      structural malformations and the two stale-import routes;
#  11. show the repository source-elaboration lock serializes the build and the
#      selector: while a lock directory is held both routes refuse without
#      reaching the proof checker, and after the owner removes it they proceed;
#  12. show the Lake warm-up wrapper takes the same lock, refusing while it is
#      held and reaching Lake after release, and that a lock release which fails
#      makes the warm-up wrapper, the install builder and the strict selector
#      exit nonzero while leaving the published bytes unchanged.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
build=${BUILD_DIR:-"$here/build"}

fail() {
  echo "check: $*" >&2
  exit 1
}

# `lake build` does not track `include_str` inputs, so a changed fixture alone
# does not invalidate a cached module.  The gate elaborates the module from
# source every time; `lake build` only warms the dependency oleans the
# certificate producer imports, and it writes the same build state a
# source-elaboration writer does, so it runs under the repository lock through
# `lake-locked.sh` and releases it before the builder runs.  The loop's pin is a
# `#guard` over its own `include_str`, so it needs the same treatment after the
# fixture is printed again.
warm() { bash "$here/lake-locked.sh" build LeanLLVM.Vellum.CommaMaskIR; }
proof() { (cd "$repo" && lake env lean LeanLLVM/Vellum/CommaMaskIR.lean); }
loop_proof() { (cd "$repo" && lake env lean LeanLLVM/Vellum/CommaMaskLoop.lean); }
warm_loop() { bash "$here/lake-locked.sh" build LeanLLVM.Vellum.CommaMaskLoop; }

echo "== fixtures and build"
warm >/dev/null
"$here/build.sh" >/dev/null
"$here/ir/capture.sh" >/dev/null
"$here/build.sh" >/dev/null
[ -s "$build/proof_baseline.env" ] || fail "no baseline certificate was published"
[ -s "$build/proof_candidate.env" ] || fail "no candidate certificate was published"
[ -s "$build/proof_loop.env" ] || fail "no loop certificate was published"

echo "== proof"
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
  fail "strict mode accepted a stale candidate"
fi

echo "== semantic outputs agree"
grep -v '^impl=' "$build/out_candidate.txt" > "$build/sem_candidate.txt"
grep -v '^impl=' "$build/out_fallback.txt" > "$build/sem_baseline.txt"
cmp "$build/sem_candidate.txt" "$build/sem_baseline.txt"

echo "== the loop unit installs from its own certificate"
UNIT=loop STRICT=1 MANIFEST=$build/manifest.env OUT=$build/app_loop \
  RECORD=$build/selection_loop.env "$here/select.sh" >/dev/null
grep -qx 'selected=loop' "$build/selection_loop.env"
"$build/app_loop" > "$build/out_loop.txt"
grep -q '^impl=3$' "$build/out_loop.txt"
grep -v '^impl=' "$build/out_loop.txt" > "$build/sem_loop.txt"
cmp "$build/sem_candidate.txt" "$build/sem_loop.txt"
echo "select: installed the loop unit"

echo "== the same request without strict mode also installs the loop"
UNIT=loop MANIFEST=$build/manifest.env OUT="$build/app_loop_unstrict" \
  RECORD="$build/selection_loop_unstrict.env" "$here/select.sh" >/dev/null
grep -qx 'selected=loop' "$build/selection_loop_unstrict.env"
"$build/app_loop_unstrict" > "$build/out_loop_unstrict.txt"
grep -q '^impl=3$' "$build/out_loop_unstrict.txt"

echo "== a stale loop hash falls back to the baseline"
cp "$build/manifest.env" "$build/manifest_bad_loop.env"
sed -i 's/^loop_sha256=.*/loop_sha256=0000000000000000000000000000000000000000000000000000000000000000/' \
  "$build/manifest_bad_loop.env"
UNIT=loop MANIFEST=$build/manifest_bad_loop.env OUT="$build/app_loop_stale" \
  RECORD="$build/selection_loop_stale.env" "$here/select.sh" >/dev/null
grep -qx 'selected=baseline' "$build/selection_loop_stale.env"
"$build/app_loop_stale" > "$build/out_loop_stale.txt"
grep -q '^impl=1$' "$build/out_loop_stale.txt"

echo "== strict mode rejects the stale loop"
if UNIT=loop STRICT=1 MANIFEST=$build/manifest_bad_loop.env \
    OUT="$build/app_loop_strict" RECORD="$build/selection_loop_strict.env" \
    "$here/select.sh" >/dev/null 2>&1; then
  fail "strict mode accepted a stale loop"
fi
if [ -e "$build/app_loop_strict" ]; then
  fail "a loop executable was emitted for a stale loop"
fi

# --- a changed fixture fails at the source guard, before any other detector --
echo "== a mutated fixture fails at the source guard and publishes nothing"
saved_proof=$build/proof_candidate.saved
saved_manifest=$build/manifest.saved
cp "$build/proof_candidate.env" "$saved_proof"
cp "$build/manifest.env" "$saved_manifest"
cp "$here/ir/candidate.ll" "$build/candidate.ll.bak"
restore() { cp "$build/candidate.ll.bak" "$here/ir/candidate.ll"; }
trap restore EXIT
sed -i 's/or i64 %i5, 32768/or i64 %i5, 32769/' "$here/ir/candidate.ll"
if cmp -s "$build/candidate.ll.bak" "$here/ir/candidate.ll"; then
  fail "the fixture mutation did not change the fixture bytes"
fi

build_status=0
"$here/build.sh" >"$build/build_mutated.stdout" 2>"$build/build_mutated.stderr" ||
  build_status=$?
if [ "$build_status" -eq 0 ]; then
  fail "the build accepted a mutated candidate fixture"
fi
# The failure must be the proof module's own `#guard`, reported before the
# differential detector runs, not a stale-hash or runtime comparison failure.
# Lake may write the diagnostic to either stream, so both are inspected.
grep -q 'firstFunction candidateSrc' \
  "$build/build_mutated.stdout" "$build/build_mutated.stderr" ||
  fail "the build did not fail at the candidate fixture guard"
grep -q 'did not evaluate to' \
  "$build/build_mutated.stdout" "$build/build_mutated.stderr" ||
  fail "the build failure is not a failed guard"
if grep -q 'differential test failed' \
    "$build/build_mutated.stdout" "$build/build_mutated.stderr"; then
  fail "the differential detector ran before the source guard failed"
fi
# A failed build publishes nothing: the certificate and manifest bytes are the
# positive control's, byte for byte.
cmp -s "$build/proof_candidate.env" "$saved_proof" ||
  fail "the failed build changed the published candidate certificate"
cmp -s "$build/manifest.env" "$saved_manifest" ||
  fail "the failed build changed the published manifest"
echo "build: failed at the source guard and left the published bytes unchanged"

restore
trap - EXIT
"$here/build.sh" >/dev/null
[ -s "$build/proof_candidate.env" ] || fail "the rebuilt tree published no certificate"
cmp -s "$build/proof_candidate.env" "$saved_proof" ||
  fail "the restored tree did not reproduce the certificate bytes"
echo "build: the restored fixture reproduces the certificate"

echo "== a mutated loop fixture invalidates the loop pin"
cp "$here/ir/loop.ll" "$build/loop.ll.bak"
restore_loop() { cp "$build/loop.ll.bak" "$here/ir/loop.ll"; }
trap restore_loop EXIT
sed -i 's/xor i64 %arg, 3182967604875373612/xor i64 %arg, 3182967604875373613/' \
  "$here/ir/loop.ll"
if ! grep -q '3182967604875373613' "$here/ir/loop.ll"; then
  fail "the loop mutation did not apply to $here/ir/loop.ll"
fi

if loop_proof >/dev/null 2>&1; then
  fail "the loop pin still checks after a fixture change"
fi
echo "proof: rejected the mutated loop fixture"

restore_loop
trap - EXIT
loop_proof >/dev/null
echo "proof: restored loop fixture checks again"

# --- a stale imported proof source is refused by the real routes ------------
echo "== a stale imported proof source is refused and restored"
imported_source=$repo/LeanLLVM/Vellum/CommaMaskKernel.lean
saved_import=$build/CommaMaskKernel.lean.saved
saved_proof=$build/proof_candidate.stale-import.saved
saved_manifest=$build/manifest.stale-import.saved
cp "$imported_source" "$saved_import"
cp "$build/proof_candidate.env" "$saved_proof"
cp "$build/manifest.env" "$saved_manifest"
restore_import() { cp "$saved_import" "$imported_source"; }
trap restore_import EXIT
printf '\n#stale-import-sentinel\n' >> "$imported_source"
if cmp -s "$saved_import" "$imported_source"; then
  fail "the stale-import marker did not change the imported source"
fi
grep -qxF '#stale-import-sentinel' "$imported_source" ||
  fail "the imported source does not carry the marker once"

stale_build_status=0
"$here/build.sh" >"$build/stale_build.stdout" 2>"$build/stale_build.stderr" ||
  stale_build_status=$?
[ "$stale_build_status" -ne 0 ] ||
  fail "the real build accepted a stale imported proof source"
grep -q 'CommaMaskKernel' "$build/stale_build.stdout" "$build/stale_build.stderr" ||
  fail "the build failure does not name the imported proof source"
[ "$(sha256sum "$build/proof_candidate.env" | cut -d' ' -f1)" = "$(sha256sum "$saved_proof" | cut -d' ' -f1)" ] ||
  fail "the stale-import build changed the candidate certificate"
[ "$(sha256sum "$build/manifest.env" | cut -d' ' -f1)" = "$(sha256sum "$saved_manifest" | cut -d' ' -f1)" ] ||
  fail "the stale-import build changed the manifest"

rm -f "$build/app_stale_import" "$build/selection_stale_import.env"
stale_strict_status=0
STRICT=1 MANIFEST="$build/manifest.env" OUT="$build/app_stale_import" \
  RECORD="$build/selection_stale_import.env" "$here/select.sh" \
  >"$build/stale_select.stdout" 2>"$build/stale_select.stderr" ||
  stale_strict_status=$?
[ "$stale_strict_status" -ne 0 ] ||
  fail "the strict selector accepted a stale imported proof source"
[ ! -e "$build/app_stale_import" ] ||
  fail "the strict selector emitted an executable for a stale imported source"
if [ -f "$build/selection_stale_import.env" ] &&
    grep -qx 'selected=candidate' "$build/selection_stale_import.env"; then
  fail "the strict selector recorded the candidate for a stale imported source"
fi

STRICT=0 MANIFEST="$build/manifest.env" OUT="$build/app_stale_fallback" \
  RECORD="$build/selection_stale_fallback.env" "$here/select.sh" \
  >"$build/stale_fallback.stdout" 2>"$build/stale_fallback.stderr"
grep -qx 'selected=baseline' "$build/selection_stale_fallback.env" ||
  fail "the non-strict selector did not fall back for a stale imported source"
grep -qx 'reason=proof rejected: invalid certificate; installed baseline fallback' \
  "$build/selection_stale_fallback.env" ||
  fail "the stale-import fallback does not carry the rejection reason"

restore_import
trap - EXIT
"$here/build.sh" >/dev/null
cmp -s "$build/proof_candidate.env" "$saved_proof" ||
  fail "the restored imported source did not reproduce the certificate"
STRICT=1 MANIFEST="$build/manifest.env" OUT="$build/app_stale_restored" \
  RECORD="$build/selection_stale_restored.env" "$here/select.sh" >/dev/null
grep -qx 'selected=candidate' "$build/selection_stale_restored.env" ||
  fail "the selector did not accept the candidate after the source was restored"
echo "stale import: the real build and both selector modes refused, then restored"

# --- the certificate gate: every field, both modes, and the malformed forms --
echo "== certificate gate matrix"
gate=$repo/tests/m3-certificate-gate.sh
certificate_fields=(
  schema
  unit
  unit_object_sha256
  unit_fixture_sha256
  unit_marker_sha256
  baseline_object_sha256
  candidate_object_sha256
  baseline_fixture_sha256
  candidate_fixture_sha256
  baseline_marker_sha256
  candidate_marker_sha256
  theorem
  axioms
  contract
  target_triple
  data_layout
  toolchain_revision
)
gate_log=$build/gate.log
: > "$gate_log"
for field in "${certificate_fields[@]}"; do
  if ! bash "$gate" --strict "$field" >>"$gate_log" 2>&1; then
    echo "check: the certificate gate refused the changed field '$field'" >&2
    tail -20 "$gate_log" >&2
    exit 1
  fi
  if ! bash "$gate" --fallback "$field" >>"$gate_log" 2>&1; then
    echo "check: the certificate gate did not fall back for '$field'" >&2
    tail -20 "$gate_log" >&2
    exit 1
  fi
done
for absence in "--strict proof_candidate" "--fallback proof_candidate" \
  "--strict-baseline proof_baseline"; do
  # shellcheck disable=SC2086
  if ! bash "$gate" $absence >>"$gate_log" 2>&1; then
    echo "check: the certificate gate failed for '$absence'" >&2
    tail -20 "$gate_log" >&2
    exit 1
  fi
done
for variant in duplicate missing reordered extra; do
  if ! bash "$gate" --strict-malformed "$variant" >>"$gate_log" 2>&1; then
    echo "check: the certificate gate accepted '$variant'" >&2
    tail -20 "$gate_log" >&2
    exit 1
  fi
  if ! bash "$gate" --fallback-malformed "$variant" >>"$gate_log" 2>&1; then
    echo "check: the certificate gate did not fall back for '$variant'" >&2
    tail -20 "$gate_log" >&2
    exit 1
  fi
done
for stale in --strict-stale-import --fallback-stale-import; do
  if ! bash "$gate" "$stale" CommaMaskKernel >>"$gate_log" 2>&1; then
    echo "check: the certificate gate failed for '$stale'" >&2
    tail -20 "$gate_log" >&2
    exit 1
  fi
done
# The loop's own gate: a matching certificate installs the loop, a mismatched
# theorem or object hash is refused, and a non-strict mismatch falls back.
loop_gate=$repo/tests/m4-loop-install-gate.sh
for mode in --strict --strict-theorem --strict-hash --fallback-hash; do
  if ! bash "$loop_gate" "$mode" >>"$gate_log" 2>&1; then
    echo "check: the loop installation gate failed for '$mode'" >&2
    tail -20 "$gate_log" >&2
    exit 1
  fi
done
echo "gate: 17 fields in both modes, three absence routes, four malformations and two stale-import routes held"
echo "gate: the loop installed from its own certificate, refused a wrong theorem and a wrong hash, and fell back"

# --- one source-elaboration writer at a time across the two routes -----------
echo "== the source-elaboration lock serializes the build and the selector"
lock=$repo/.lake/install-certificate.lock
mkdir -p "$repo/.lake"
if [ -e "$lock" ]; then
  fail "$lock already exists; verify that no run owns it, then remove that directory"
fi
if ! mkdir "$lock" 2>/dev/null; then
  fail "cannot take $lock for the contention check"
fi
# This check owns the directory and is its only remover.  The trap releases it
# even when an assertion fails; a removal that fails leaves the lock in place
# and makes the check fail, so it can never be mistaken for a clean run.
lock_owned=1
release_test_lock() {
  [ "$lock_owned" = 1 ] || return 0
  if rmdir "$lock" 2>/dev/null; then
    lock_owned=0
    return 0
  fi
  echo "check: could not remove $lock; verify that no run owns it" >&2
  return 1
}
trap release_test_lock EXIT

# The lock directory now present is exactly what a crashed run's stale lock
# looks like: neither route may proceed while it exists.
manifest_before=$(sha256sum "$build/manifest.env" | cut -d' ' -f1)
proof_baseline_before=$(sha256sum "$build/proof_baseline.env" | cut -d' ' -f1)
proof_candidate_before=$(sha256sum "$build/proof_candidate.env" | cut -d' ' -f1)
differential_before=$(sha256sum "$build/differential.txt" | cut -d' ' -f1)

# Pre-existing output and record bytes, so the refusal is judged on what the
# files still contain rather than on their absence.
printf 'previous output\n' > "$build/app_locked"
printf 'selected=candidate\nreason=previous selection\n' > "$build/selection_locked.env"
out_before=$(sha256sum "$build/app_locked" | cut -d' ' -f1)
record_before=$(sha256sum "$build/selection_locked.env" | cut -d' ' -f1)

build_lock_status=0
"$here/build.sh" >"$build/lock_build.stdout" 2>"$build/lock_build.stderr" ||
  build_lock_status=$?
[ "$build_lock_status" -ne 0 ] || fail "the build ran while the lock was held"
grep -q 'another source elaboration holds' "$build/lock_build.stderr" ||
  fail "the build did not report the held lock"

# The selector is driven through a local `lake` shim that records every time
# the proof checker is reached.  While the lock is held the shim must never
# run; after release it must, so the absence assertion has its control.
shim=$build/contention-bin
rm -rf "$shim"
mkdir -p "$shim"
real_lake=$(command -v lake)
{
  printf '#!/usr/bin/env bash\n'
  printf 'touch %q\n' "$build/lake_invoked"
  printf 'exec %q "$@"\n' "$real_lake"
} > "$shim/lake"
chmod +x "$shim/lake"
rm -f "$build/lake_invoked"
select_lock_status=0
PATH="$shim:$PATH" MANIFEST="$build/manifest.env" STRICT=1 \
  OUT="$build/app_locked" RECORD="$build/selection_locked.env" \
  "$here/select.sh" >"$build/lock_select.stdout" 2>"$build/lock_select.stderr" ||
  select_lock_status=$?
[ "$select_lock_status" -ne 0 ] || fail "the selector ran while the lock was held"
grep -q 'another source elaboration holds' "$build/lock_select.stderr" ||
  fail "the selector did not report the held lock"
[ ! -e "$build/lake_invoked" ] ||
  fail "the selector reached the proof checker while the lock was held"

[ "$(sha256sum "$build/manifest.env" | cut -d' ' -f1)" = "$manifest_before" ] ||
  fail "the refused build changed the manifest"
[ "$(sha256sum "$build/proof_baseline.env" | cut -d' ' -f1)" = "$proof_baseline_before" ] ||
  fail "the refused build changed the baseline certificate"
[ "$(sha256sum "$build/proof_candidate.env" | cut -d' ' -f1)" = "$proof_candidate_before" ] ||
  fail "the refused build changed the candidate certificate"
[ "$(sha256sum "$build/differential.txt" | cut -d' ' -f1)" = "$differential_before" ] ||
  fail "the refused build changed the differential transcript"
[ "$(sha256sum "$build/app_locked" | cut -d' ' -f1)" = "$out_before" ] ||
  fail "the refused selector changed a pre-existing output"
[ "$(sha256sum "$build/selection_locked.env" | cut -d' ' -f1)" = "$record_before" ] ||
  fail "the refused selector changed a pre-existing record"

# The owner removes the lock; with it gone both routes proceed.
release_test_lock || fail "the contention lock could not be released"
trap - EXIT

PATH="$shim:$PATH" STRICT=1 MANIFEST="$build/manifest.env" \
  OUT="$build/app_after_lock" RECORD="$build/selection_after_lock.env" \
  "$here/select.sh" >/dev/null
[ -e "$build/lake_invoked" ] ||
  fail "the selector never reached the proof checker after the lock was released"
grep -q '^selected=candidate$' "$build/selection_after_lock.env" ||
  fail "the selector did not accept the candidate after the lock was released"
"$here/build.sh" >/dev/null
[ "$(sha256sum "$build/proof_candidate.env" | cut -d' ' -f1)" = "$proof_candidate_before" ] ||
  fail "the build after release did not reproduce the candidate certificate"
echo "lock: both routes refused while held; both proceeded after the owner released it"

# --- the warm-up wrapper takes the same lock -------------------------------
echo "== the lake warm-up wrapper uses the same lock"
warm_shim=$build/warm-shim
rm -rf "$warm_shim"
mkdir -p "$warm_shim"
# A Lake that records its invocation and does no work.
cat > "$warm_shim/lake" <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail
: > "${WARM_SHIM_MARKER:?}"
exit 0
SHIM
chmod +x "$warm_shim/lake"
warm_marker=$build/warm_lake_invoked
rm -f "$warm_marker"

if ! mkdir "$lock" 2>/dev/null; then
  fail "cannot take $lock for the warm-up case"
fi
lock_owned=1
trap release_test_lock EXIT
warm_status=0
PATH="$warm_shim:$PATH" WARM_SHIM_MARKER="$warm_marker" \
  bash "$here/lake-locked.sh" build LeanLLVM.Vellum.CommaMaskIR \
  >"$build/lock_warm.stdout" 2>"$build/lock_warm.stderr" || warm_status=$?
[ "$warm_status" -ne 0 ] || fail "the warm-up wrapper ran while the lock was held"
[ ! -e "$warm_marker" ] ||
  fail "the warm-up wrapper reached Lake while the lock was held"
grep -q 'another source elaboration holds' "$build/lock_warm.stderr" ||
  fail "the warm-up wrapper did not report the held lock"
release_test_lock || fail "the warm-up lock could not be released"
trap - EXIT

PATH="$warm_shim:$PATH" WARM_SHIM_MARKER="$warm_marker" \
  bash "$here/lake-locked.sh" build LeanLLVM.Vellum.CommaMaskIR >/dev/null
[ -e "$warm_marker" ] ||
  fail "the warm-up wrapper never reached Lake after the lock was released"
echo "warm-up: refused while held and reached Lake after release"

# --- a failed lock release fails the route that held it --------------------
echo "== a failed lock release is a nonzero exit in every route"
real_rmdir=$(command -v rmdir)
rmdir_shim=$build/rmdir-shim
rm -rf "$rmdir_shim"
mkdir -p "$rmdir_shim"
{
  printf '#!/usr/bin/env bash\n'
  printf 'for a in "$@"; do\n'
  printf '  if [ "$a" = %q ]; then\n' "$lock"
  printf '    echo "rmdir shim: refusing the lock directory" >&2\n'
  printf '    exit 1\n'
  printf '  fi\n'
  printf 'done\n'
  printf 'exec %q "$@"\n' "$real_rmdir"
} > "$rmdir_shim/rmdir"
chmod +x "$rmdir_shim/rmdir"

# The check is the owner of the lock the failed route left behind: verify it is
# the empty directory this case created, then remove it with the real rmdir.
clear_failed_lock() { # case name
  [ -d "$lock" ] || fail "$1 left no lock directory to clean up"
  if [ -n "$(ls -A "$lock")" ]; then
    fail "$1 left a non-empty lock directory"
  fi
  "$real_rmdir" "$lock" || fail "could not remove $lock after $1"
}

rm -f "$warm_marker"
warm_fail_status=0
PATH="$warm_shim:$rmdir_shim:$PATH" WARM_SHIM_MARKER="$warm_marker" \
  bash "$here/lake-locked.sh" build LeanLLVM.Vellum.CommaMaskIR \
  >"$build/rmdir_warm.stdout" 2>"$build/rmdir_warm.stderr" || warm_fail_status=$?
[ "$warm_fail_status" -ne 0 ] ||
  fail "the warm-up wrapper reported success after a failed release"
[ -e "$warm_marker" ] ||
  fail "the warm-up wrapper never reached Lake in the release-failure case"
grep -q 'could not remove' "$build/rmdir_warm.stderr" ||
  fail "the warm-up wrapper did not report the failed release"
clear_failed_lock "the warm-up wrapper"

manifest_release_before=$(sha256sum "$build/manifest.env" | cut -d' ' -f1)
proof_release_before=$(sha256sum "$build/proof_candidate.env" | cut -d' ' -f1)
build_fail_status=0
PATH="$rmdir_shim:$PATH" "$here/build.sh" \
  >"$build/rmdir_build.stdout" 2>"$build/rmdir_build.stderr" || build_fail_status=$?
[ "$build_fail_status" -ne 0 ] ||
  fail "the install builder reported success after a failed release"
grep -q 'could not remove' "$build/rmdir_build.stderr" ||
  fail "the install builder did not report the failed release"
[ "$(sha256sum "$build/manifest.env" | cut -d' ' -f1)" = "$manifest_release_before" ] ||
  fail "the failed-release build changed the manifest"
[ "$(sha256sum "$build/proof_candidate.env" | cut -d' ' -f1)" = "$proof_release_before" ] ||
  fail "the failed-release build changed the candidate certificate"
clear_failed_lock "the install builder"

rm -f "$build/app_rmdir_fail" "$build/selection_rmdir_fail.env"
select_fail_status=0
PATH="$rmdir_shim:$PATH" STRICT=1 MANIFEST="$build/manifest.env" \
  OUT="$build/app_rmdir_fail" RECORD="$build/selection_rmdir_fail.env" \
  "$here/select.sh" >"$build/rmdir_select.stdout" 2>"$build/rmdir_select.stderr" ||
  select_fail_status=$?
[ "$select_fail_status" -ne 0 ] ||
  fail "the strict selector reported success after a failed release"
grep -q 'could not remove' "$build/rmdir_select.stderr" ||
  fail "the selector did not report the failed release"
# The selector releases only after the link and the record write, so the
# release-specific failure is the nonzero status itself; the link and record
# prove the failure was not an earlier certificate refusal.
[ -e "$build/app_rmdir_fail" ] ||
  fail "the selector did not reach the link in the release-failure case"
grep -qx 'selected=candidate' "$build/selection_rmdir_fail.env" ||
  fail "the selector did not reach the record write in the release-failure case"
clear_failed_lock "the selector"
echo "release: the warm-up, the install builder and the selector each failed loudly"

echo "install probe: ok"
