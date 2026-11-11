#!/usr/bin/env bash
# The route scenario.
#
#   nix develop -c bash probes/json/route/check.sh
#
# Two claims are asserted:
#
#   1. fidelity: for every default-profile corpus document the Lean route's
#      first output line equals the C driver's, where the driver stages the
#      document exactly as `LeanLLVM.JsonCallRoute.stagedStore` does and calls
#      `leanllvm_json_pipeline` directly.  Agreement is evidence that the Lean
#      wrapper builds the record's staging and reports the object's outputs;
#   2. the shell refuses the empty document and an over-bound document with
#      their reasons, before any call; and the record's domain excludes the
#      empty document that the manifest calls `invalid`.
#
# The reference comparison is reported, not asserted: the native object accepts
# documents the reference parser refuses for its own policy (unpaired
# surrogates and noncharacters, which are RFC texts).  `DomainCheck.lean` names
# that policy; the divergence set is printed here and is a finding about the
# object, not about the route.  An object that refused an `accept` row would be
# a different class and fails the scenario.
#
# Exit status: 0 when the assertions hold, 1 when one fails, 3 when a fixture
# is absent.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
route=${ROUTE:-"$here/build/leanllvm-json-route"}
driver=${DRIVER:-"$here/build/driver"}
corpus=$repo/tests/json/corpus
manifest=$repo/tests/json/manifest.tsv

for path in "$route" "$driver" "$corpus" "$manifest"; do
  [ -e "$path" ] || {
    printf 'SETUP: absent: %s\n  build the route with: nix develop -c bash probes/json/route/build.sh\n' "$path" >&2
    exit 3
  }
done

work=$(mktemp -d) || { echo "SETUP: cannot create a temporary directory" >&2; exit 3; }
trap 'rm -rf "$work"' EXIT

first_line() { sed -n '1p' "$1"; }
verdict_of() { sed -n 's/^verdict=\([0-9]*\) .*/\1/p' "$1"; }

rows=0; failed=0; skipped=0; accepts=0; invalids=0; excluded=0; diverged=0
divergent=

while IFS=$'\t' read -r path expected rendering profile; do
  [ -n "${path:-}" ] || continue
  if [ "$profile" != default ]; then
    skipped=$((skipped + 1))
    continue
  fi
  rows=$((rows + 1))
  out=$work/out; errf=$work/err; dout=$work/dout
  if [ ! -s "$corpus/$path" ]; then
    excluded=$((excluded + 1))
    "$route" --doc "$corpus/$path" >"$out" 2>"$errf"
    status=$?
    if [ "$status" -ne 2 ] || ! grep -q 'refused: empty input' "$errf"; then
      printf 'FAIL: %s: expected the empty-input refusal, exit %s\n' "$path" "$status" >&2
      failed=$((failed + 1))
    fi
    continue
  fi
  "$route" --doc "$corpus/$path" >"$out" 2>"$errf"
  status=$?
  if [ "$status" -ne 0 ]; then
    printf 'FAIL: %s: the route exited %s\n' "$path" "$status" >&2
    cat "$errf" >&2
    failed=$((failed + 1))
    continue
  fi
  "$driver" "$corpus/$path" >"$dout" 2>/dev/null
  if [ "$(first_line "$out")" != "$(first_line "$dout")" ]; then
    printf 'FAIL: %s: the Lean route and the C driver disagree\n  lean: %s\n  c:    %s\n' \
      "$path" "$(first_line "$out")" "$(first_line "$dout")" >&2
    failed=$((failed + 1))
    continue
  fi
  got=$(verdict_of "$out")
  case "$expected" in
    accept)
      accepts=$((accepts + 1))
      if [ "$got" != "1" ]; then
        printf 'FAIL: %s: the object refused an accept row (verdict %s)\n' "$path" "$got" >&2
        failed=$((failed + 1))
      fi
      ;;
    invalid)
      invalids=$((invalids + 1))
      if [ "$got" != "0" ]; then
        diverged=$((diverged + 1))
        divergent="$divergent $path"
      fi
      ;;
    *)
      printf 'FAIL: %s: unexpected default-profile verdict %s\n' "$path" "$expected" >&2
      failed=$((failed + 1))
      ;;
  esac
done <"$manifest"

: >"$work/empty"
"$route" --doc "$work/empty" >"$work/out" 2>"$work/err"
status=$?
if [ "$status" -ne 2 ] || ! grep -q 'refused: empty input' "$work/err"; then
  printf 'FAIL: the empty document was not refused with its reason (exit %s)\n' "$status" >&2
  failed=$((failed + 1))
fi

head -c 1048577 /dev/zero >"$work/long"
"$route" --doc "$work/long" >"$work/out" 2>"$work/err"
status=$?
if [ "$status" -ne 2 ] || ! grep -q 'refused: input too long' "$work/err"; then
  printf 'FAIL: the over-bound document was not refused with its reason (exit %s)\n' "$status" >&2
  failed=$((failed + 1))
fi

if [ "$accepts" -eq 0 ] || [ "$invalids" -eq 0 ]; then
  printf 'FAIL: the corpus arm is empty (accept %s, invalid %s)\n' "$accepts" "$invalids" >&2
  failed=$((failed + 1))
fi
if [ "$skipped" -eq 0 ]; then
  printf 'FAIL: the manifest carries no non-default-profile row to skip\n' >&2
  failed=$((failed + 1))
fi

if [ "$failed" -ne 0 ]; then
  printf 'FAIL: %s assertion(s) failed over %s default-profile rows\n' "$failed" "$rows" >&2
  exit 1
fi
printf 'ok: %s default-profile rows: route and driver agree; accept %s, invalid %s (object accepts %s policy refusals); empty excluded %s; %s non-default-profile rows skipped\n' \
  "$rows" "$accepts" "$invalids" "$diverged" "$excluded" "$skipped"
if [ "$diverged" -ne 0 ]; then
  printf 'divergence (object accepts, reference refuses on policy):%s\n' "$divergent"
fi
exit 0
