#!/usr/bin/env bash
# The route scenario.
#
#   nix develop -c bash probes/json/route/check.sh
#
# Three claims are asserted:
#
#   1. fidelity: for every default-profile corpus document the Lean route's
#      first output line equals the C driver's, where the driver stages the
#      document exactly as `LeanLLVM.JsonCallRoute.stagedStore` does and calls
#      `leanllvm_json_pipeline` directly.  Agreement is evidence that the Lean
#      wrapper builds the record's staging and reports the object's outputs;
#   2. the shell refuses the empty document and an over-bound document with
#      their reasons, before any call; and the record's domain excludes the
#      empty document that the manifest calls `invalid`;
#   3. the shell refuses the reference parser's character-policy class — the
#      fourteen documents the native object accepts and the reference refuses —
#      with the reference's own reason and byte.  The class is pinned below; the
#      route's verdict therefore agrees with the reference on every
#      default-profile row (divergence 0), and the object's own verdict on those
#      rows is still measured: the driver accepts all fourteen, so the refusal
#      is the wrapper's.
#
# The policy class is the one `DomainCheck.lean` pins against `documentRefusal`
# and `parseBytes`; this scenario pins the same fourteen names and asserts the
# executable's reason and byte for each.
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
policy_of() { sed -n 's/^refused: invalid: \([A-Za-z]*\) at \([0-9][0-9]*\):.*/\1@\2/p' "$1"; }

rows=0; failed=0; skipped=0; accepts=0; invalids=0; excluded=0; policy=0; diverged=0
divergent=
: >"$work/policy-got"

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
  if [ "$status" -ne 0 ] && [ "$status" -ne 2 ]; then
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
  if [ "$status" -eq 2 ]; then
    # The wrapper refused a document it had already called the object on.
    reason=$(policy_of "$errf")
    if [ -z "$reason" ]; then
      printf 'FAIL: %s: exit 2 without a policy reason:\n' "$path" >&2
      cat "$errf" >&2
      failed=$((failed + 1))
      continue
    fi
    if [ "$expected" != invalid ]; then
      printf 'FAIL: %s: the route refused an %s row as a policy refusal (%s)\n' \
        "$path" "$expected" "$reason" >&2
      failed=$((failed + 1))
      continue
    fi
    if [ "$(verdict_of "$dout")" != 1 ]; then
      printf 'FAIL: %s: the object refused a document the route refused for policy\n' \
        "$path" >&2
      failed=$((failed + 1))
      continue
    fi
    policy=$((policy + 1))
    printf '%s\t%s\n' "$path" "$reason" >>"$work/policy-got"
    continue
  fi
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

# The class the wrapper refuses for the reference's reason: the fourteen corpus
# rows the object accepts and the reference refuses.  A missing row, an extra
# row, or a different reason or byte is a failure, not a report.
cat >"$work/policy-expected" <<'EOF'
double-high.json	unpairedSurrogate@1
high-char.json	unpairedSurrogate@1
lone-d800.json	unpairedSurrogate@1
lone-dc00.json	unpairedSurrogate@1
lone-dead.json	unpairedSurrogate@1
nc-fdd0.json	noncharacter@1
nc-fffe.json	noncharacter@1
nc-ffff.json	noncharacter@1
nc-pair-max.json	noncharacter@1
nc-raw-10ffff.json	noncharacter@1
nc-raw-1fffe.json	noncharacter@1
nc-raw-fdd0.json	noncharacter@1
nc-raw-fffe.json	noncharacter@1
reversed-pair.json	unpairedSurrogate@1
EOF
sort -o "$work/policy-got" "$work/policy-got"
if ! diff -u "$work/policy-expected" "$work/policy-got" >"$work/policy-diff" 2>&1; then
  printf 'FAIL: the route refuses a different policy class than the one pinned:\n' >&2
  cat "$work/policy-diff" >&2
  failed=$((failed + 1))
fi
if [ "$policy" -ne 14 ]; then
  printf 'FAIL: expected 14 policy refusals, saw %s\n' "$policy" >&2
  failed=$((failed + 1))
fi

# The class's documents are the bytes `DomainCheck.lean` pins.  Without this
# binding a corpus edit that kept a name would leave the reference's verdict in
# `DomainCheck.lean` talking about different bytes than the ones the route read.
cat >"$work/policy-bytes" <<'EOF'
double-high.json	225c75443830305c754438303022
high-char.json	225c75443830306122
lone-d800.json	225c754438303022
lone-dc00.json	225c754443303022
lone-dead.json	225c754445414422
nc-fdd0.json	225c754644443022
nc-fffe.json	225c754646464522
nc-ffff.json	225c754646464622
nc-pair-max.json	225c75444246465c754446464622
nc-raw-10ffff.json	22f48fbfbf22
nc-raw-1fffe.json	22f09fbfbe22
nc-raw-fdd0.json	22efb79022
nc-raw-fffe.json	22efbfbe22
reversed-pair.json	225c75444330305c754438303022
EOF
while IFS=$'\t' read -r name want; do
  [ -n "${name:-}" ] || continue
  got_bytes=$(od -An -tx1 -v "$corpus/$name" | tr -d ' \n')
  if [ "$got_bytes" != "$want" ]; then
    printf 'FAIL: %s: corpus bytes %s are not the pinned %s\n' \
      "$name" "$got_bytes" "$want" >&2
    failed=$((failed + 1))
  fi
done <"$work/policy-bytes"

if [ "$diverged" -ne 0 ]; then
  printf 'FAIL: %s default-profile rows still diverge from the reference:%s\n' \
    "$diverged" "$divergent" >&2
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
printf 'ok: %s default-profile rows: route and driver agree; accept %s, invalid %s, policy refusals %s; divergence %s; empty excluded %s; %s non-default-profile rows skipped\n' \
  "$rows" "$accepts" "$invalids" "$policy" "$diverged" "$excluded" "$skipped"
exit 0
