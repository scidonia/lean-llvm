#!/usr/bin/env bash
# End-to-end application check: a real caller is linked against each proved
# unit through the shared selector, runs, and must produce the same answer.
# It also shows the repository lock covers this route: while the lock is held
# the build refuses before removing its output and the selector refuses before
# linking, leaving the prior certificates, manifest, output and record bytes
# unchanged; after release both proceed, and a failed release fails the build.
#
#   nix develop -c bash probes/app/check.sh
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
install=$(cd "$here/../install" && pwd)
repo=$(cd "$here/../.." && pwd)
select=$install/select.sh
build=${BUILD_DIR:-"$here/build"}

# The application build produces the unit certificates, and both it and the
# selector elaborate the proof module from source. Warm its dependency oleans
# first through the repository lock; `lake build` does not track the
# `include_str` fixtures themselves.
bash "$install/lake-locked.sh" build LeanLLVM.Vellum.CommaMaskIR >/dev/null

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

# --- the repository lock covers the app build and selection ----------------
echo "== the repository lock covers the app build and selection"
lock=$repo/.lake/install-certificate.lock
real_rmdir=$(command -v rmdir)
mkdir -p "$repo/.lake"
prior_proof_baseline=$(sha256sum "$build/proof_baseline.env" | cut -d' ' -f1)
prior_proof_candidate=$(sha256sum "$build/proof_candidate.env" | cut -d' ' -f1)
prior_manifest=$(sha256sum "$build/manifest.env" | cut -d' ' -f1)
prior_output=$(sha256sum "$build/app_candidate" | cut -d' ' -f1)
prior_record=$(sha256sum "$build/selection_candidate.env" | cut -d' ' -f1)

if [ -e "$lock" ]; then
  echo "app: $lock already exists; verify that no run owns it and remove it" >&2
  exit 1
fi
if ! mkdir "$lock" 2>/dev/null; then
  echo "app: cannot take $lock for the contention check" >&2
  exit 1
fi
lock_owned=1
release_test_lock() {
  [ "$lock_owned" = 1 ] || return 0
  if rmdir "$lock" 2>/dev/null; then
    lock_owned=0
    return 0
  fi
  echo "app: could not remove $lock; verify that no run owns it" >&2
  return 1
}
trap release_test_lock EXIT

# The build must refuse before it removes its previous output, so the app's
# certificates, manifest, output and record keep their exact bytes.
app_build_held_status=0
"$here/build.sh" >"$build/lock_build.stdout" 2>"$build/lock_build.stderr" ||
  app_build_held_status=$?
[ "$app_build_held_status" -ne 0 ] || {
  echo "app: the build ran while the lock was held" >&2
  exit 1
}
grep -q 'another source elaboration holds' "$build/lock_build.stderr" || {
  echo "app: the build did not report the held lock" >&2
  exit 1
}
app_select_held_status=0
MANIFEST=$build/manifest.env STRICT=1 OUT=$build/app_candidate \
  RECORD=$build/selection_candidate.env "$select" \
  >"$build/lock_select.stdout" 2>"$build/lock_select.stderr" ||
  app_select_held_status=$?
[ "$app_select_held_status" -ne 0 ] || {
  echo "app: the selector ran while the lock was held" >&2
  exit 1
}
grep -q 'another source elaboration holds' "$build/lock_select.stderr" || {
  echo "app: the selector did not report the held lock" >&2
  exit 1
}

app_byte_preserved() { # path expected what
  if [ "$(sha256sum "$1" | cut -d' ' -f1)" != "$2" ]; then
    echo "app: the refused route changed the $3" >&2
    exit 1
  fi
}
app_byte_preserved "$build/proof_baseline.env" "$prior_proof_baseline" \
  "baseline certificate"
app_byte_preserved "$build/proof_candidate.env" "$prior_proof_candidate" \
  "candidate certificate"
app_byte_preserved "$build/manifest.env" "$prior_manifest" "manifest"
app_byte_preserved "$build/app_candidate" "$prior_output" \
  "pre-existing output"
app_byte_preserved "$build/selection_candidate.env" "$prior_record" \
  "pre-existing record"
release_test_lock || exit 1
trap - EXIT

# With the lock released the same build runs and reproduces the certificates,
# and the selector accepts the candidate.
"$here/build.sh" >/dev/null
app_byte_preserved "$build/proof_baseline.env" "$prior_proof_baseline" \
  "baseline certificate after release"
app_byte_preserved "$build/proof_candidate.env" "$prior_proof_candidate" \
  "candidate certificate after release"
MANIFEST=$build/manifest.env STRICT=1 OUT=$build/app_after_lock \
  RECORD=$build/selection_after_lock.env "$select" >/dev/null
grep -q '^selected=candidate$' "$build/selection_after_lock.env" || {
  echo "app: the selector did not accept the candidate after release" >&2
  exit 1
}
echo "lock: the app build and selection refused while held and proceeded after release"

# --- a failed lock release fails the app build -----------------------------
echo "== a failed lock release fails the app build"
# The shim lives outside the app build directory, which the build removes.
rmdir_shim=$(mktemp -d)
trap 'rm -rf "$rmdir_shim"' EXIT
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

release_proof=$(sha256sum "$build/proof_candidate.env" | cut -d' ' -f1)
release_manifest=$(sha256sum "$build/manifest.env" | cut -d' ' -f1)
app_release_status=0
PATH="$rmdir_shim:$PATH" "$here/build.sh" \
  >"$rmdir_shim/app-build.stdout" 2>"$rmdir_shim/app-build.stderr" ||
  app_release_status=$?
if [ "$app_release_status" -eq 0 ]; then
  echo "app: the build reported success after a failed release" >&2
  exit 1
fi
grep -q 'could not remove' "$rmdir_shim/app-build.stderr" || {
  echo "app: the build did not report the failed release" >&2
  exit 1
}
app_byte_preserved "$build/proof_candidate.env" "$release_proof" \
  "candidate certificate in the release-failure case"
app_byte_preserved "$build/manifest.env" "$release_manifest" \
  "manifest in the release-failure case"
# The failed route left the lock behind; this check owns it, verifies it is the
# empty directory the case created, and removes it with the real rmdir.
[ -d "$lock" ] || {
  echo "app: the failed-release build left no lock directory" >&2
  exit 1
}
[ -z "$(ls -A "$lock")" ] || {
  echo "app: the failed-release build left a non-empty lock directory" >&2
  exit 1
}
"$real_rmdir" "$lock" || {
  echo "app: could not remove $lock after the release-failure case" >&2
  exit 1
}
echo "release: the app build failed loudly and kept the published bytes"

echo "app probe: ok"
