#!/usr/bin/env bash
# The route scenario.
#
#   nix develop -c bash probes/json/route/check.sh
#
# The route decides with the library's `admission` predicate and has three
# outcomes: the fast path (`verdict=` on stdout, the native object's
# observation), the fallback's acceptance (`fallback=accepted`), and the
# fallback's refusal (`refused: ...` on stderr, exit 2).  Five claims are
# asserted:
#
#   1. fidelity on the fast path: for every default-profile corpus document the
#      route admits, the Lean route and the C driver print the same three lines —
#      the observation (verdict, the four cursors and the error offset), the
#      arena and the event stream — and the two payload lines are compared byte
#      for byte.  The driver stages the document exactly as
#      `LeanLLVM.JsonCallRoute.stagedStore` does and calls
#      `leanllvm_json_pipeline` directly.
#   2. every fallback answer agrees with the manifest: a document the route does
#      not admit is either `refused` (the manifest says invalid) or accepted by
#      the reference (the manifest says accept); a fallback answer that
#      contradicts the row is a failure.
#   3. the empty document, an over-bound document and the reference's
#      character-policy class fall back, and their fallback answers are the
#      reference parser's own: `unexpected end`, `input too long`, and the
#      fourteen policy reasons with their bytes.
#   4. the two depth boundaries are measured rather than inherited from the
#      corpus: the reference parser's 128 levels (`Limits.default.maxDepth`, 128
#      admitted and 129 falling back with `depthExceeded`) and the native walk's
#      520-frame stack (`stage2.c`'s `MAXD`, 520 pushed and the 521st refused
#      with its offset).  The fast path is measured at 128 only: 129 and above
#      are outside the certified domain, so the route does not call the object
#      there, and the driver is still run to record what the object would have
#      answered.
#   5. the three outcomes are distinct in the output: a fast-path row prints no
#      `fallback=` line, a fallback row prints no `verdict=` line, and both arms
#      are non-empty.
#
# A comparison that fails names its class: a verdict disagreement, a value
# disagreement (the arena or event bytes, with the first differing byte), or a
# metadata disagreement (a cursor or the error offset).  Between the route and
# the driver no difference is allowed on an admitted document — both call the
# same object with the same staging.
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

verdict_of() { sed -n 's/^verdict=\([0-9]*\) .*/\1/p' "$1"; }
err_of() {
  sed -n 's/^verdict=[0-9]* nk=[0-9]* nxp=[0-9]* ndst=[0-9]* nev=[0-9]* err=\([0-9]*\)$/\1/p' "$1"
}
policy_of() { sed -n 's/^refused: invalid: \([A-Za-z]*\) at \([0-9][0-9]*\):.*/\1@\2/p' "$1"; }
fallback_of() { sed -n 's/^fallback=\([a-z]*\).*/\1/p' "$1"; }

# The observation as six numbers, or empty when the line is not in the pinned
# form (which is itself a disagreement the comparison reports).
observation_of() {
  awk 'NR == 1 && /^verdict=[0-9]+ nk=[0-9]+ nxp=[0-9]+ ndst=[0-9]+ nev=[0-9]+ err=[0-9]+$/ {
         gsub(/[a-z]+=/, ""); print; exit }' "$1"
}

# One payload's hex digits, or empty.
payload_of() { sed -n "s/^$2=//p" "$1"; }

# The first half-byte at which two equal-length hex strings differ, as a byte
# index; used only on a mismatch, so the scan is not on the per-row path.
first_diff_byte() {
  awk -v a="$1" -v b="$2" 'BEGIN {
    n = length(a) < length(b) ? length(a) : length(b)
    for (i = 1; i <= n; i++)
      if (substr(a, i, 1) != substr(b, i, 1)) { printf "%d", int((i - 1) / 2); exit }
    printf "%d", int(n / 2)
  }'
}

failed=0
rows_compared=0
compared_arena=0
compared_events=0
rows_with_arena=0
rows_with_events=0

# Compare the route's three lines with the driver's.  Returns non-zero and
# counts the failure when the observation disagrees; the class is in the
# diagnostic.
compare_observation() { # <row label> <route output> <driver output>
  local name=$1 lf=$2 df=$3
  local lv dv stream lh dh at k f
  lv=$(observation_of "$lf")
  dv=$(observation_of "$df")
  if [ -z "$lv" ]; then
    printf 'FAIL: %s: the route did not print the observation in the pinned form:\n' \
      "$name" >&2
    sed -n '1p' "$lf" >&2
    failed=$((failed + 1))
    return 1
  fi
  if [ -z "$dv" ]; then
    printf 'FAIL: %s: the driver did not print the observation in the pinned form:\n' \
      "$name" >&2
    sed -n '1p' "$df" >&2
    failed=$((failed + 1))
    return 1
  fi
  local -a l=($lv) d=($dv)
  if [ "${l[0]}" != "${d[0]}" ]; then
    printf 'FAIL: %s: verdict disagreement: route %s, driver %s\n' \
      "$name" "${l[0]}" "${d[0]}" >&2
    failed=$((failed + 1))
    return 1
  fi
  for stream in arena events; do
    lh=$(payload_of "$lf" "$stream")
    dh=$(payload_of "$df" "$stream")
    if [ "${#lh}" != "${#dh}" ]; then
      printf 'FAIL: %s: value disagreement: the %s streams differ in length: route %s byte(s), driver %s\n' \
        "$name" "$stream" "$((${#lh} / 2))" "$((${#dh} / 2))" >&2
      failed=$((failed + 1))
      return 1
    fi
    if [ "$lh" != "$dh" ]; then
      at=$(first_diff_byte "$lh" "$dh")
      printf 'FAIL: %s: value disagreement: the %s streams first differ at byte %s: route 0x%s, driver 0x%s\n' \
        "$name" "$stream" "$at" "${lh:$((at * 2)):2}" "${dh:$((at * 2)):2}" >&2
      failed=$((failed + 1))
      return 1
    fi
    if [ "$stream" = arena ]; then
      compared_arena=$((compared_arena + ${#lh} / 2))
      [ -n "$lh" ] && rows_with_arena=$((rows_with_arena + 1))
    else
      compared_events=$((compared_events + ${#lh} / 2))
      [ -n "$lh" ] && rows_with_events=$((rows_with_events + 1))
    fi
  done
  for k in 1 2 3 4 5; do
    [ "${l[$k]}" = "${d[$k]}" ] && continue
    case $k in
      1) f=nk ;;
      2) f=nxp ;;
      3) f=ndst ;;
      4) f=nev ;;
      5) f=err ;;
    esac
    if [ "$f" = err ]; then
      printf 'FAIL: %s: error-offset disagreement: route err=%s, driver err=%s\n' \
        "$name" "${l[$k]}" "${d[$k]}" >&2
    else
      printf 'FAIL: %s: metadata disagreement: %s: route %s, driver %s\n' \
        "$name" "$f" "${l[$k]}" "${d[$k]}" >&2
    fi
    failed=$((failed + 1))
    return 1
  done
  rows_compared=$((rows_compared + 1))
  return 0
}

rows=0; skipped=0; fast=0; fallback_refusals=0; fallback_accepts=0
accepts=0; invalids=0; excluded=0; diverged=0
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
    # The empty document is outside the domain, and the fallback answers it.
    excluded=$((excluded + 1))
    "$route" --doc "$corpus/$path" >"$out" 2>"$errf"
    status=$?
    if [ "$status" -ne 2 ] || ! grep -q '^refused: invalid: unexpected end at 0' "$errf"; then
      printf 'FAIL: %s: expected the fallback refusal "unexpected end at 0", exit %s\n' "$path" "$status" >&2
      cat "$errf" >&2
      failed=$((failed + 1))
    fi
    continue
  fi
  "$route" --doc "$corpus/$path" >"$out" 2>"$errf"
  status=$?
  if [ "$status" -eq 5 ] || [ "$status" -eq 3 ] || [ "$status" -eq 4 ]; then
    printf 'FAIL: %s: the route reported an adapter failure (exit %s):\n' "$path" "$status" >&2
    cat "$errf" >&2
    failed=$((failed + 1))
    continue
  fi
  if [ -n "$(observation_of "$out")" ]; then
    # Outcome one: the fast path.  Compare with the driver, and with the row.
    fast=$((fast + 1))
    "$driver" "$corpus/$path" >"$dout" 2>/dev/null
    compare_observation "$path" "$out" "$dout" || continue
    if [ -n "$(fallback_of "$out")" ]; then
      printf 'FAIL: %s: a fast-path row printed a fallback answer\n' "$path" >&2
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
    continue
  fi
  # Outcome two or three: the fallback answered.  A fallback row must not print
  # the fast path's observation, and its answer must agree with the row.
  if [ -n "$(verdict_of "$out")" ]; then
    printf 'FAIL: %s: a fallback row printed a fast-path observation\n' "$path" >&2
    failed=$((failed + 1))
    continue
  fi
  case "$(fallback_of "$out")" in
    accepted)
      fallback_accepts=$((fallback_accepts + 1))
      if [ "$expected" != accept ]; then
        printf 'FAIL: %s: the fallback accepted an %s row\n' "$path" "$expected" >&2
        failed=$((failed + 1))
      fi
      ;;
    *)
      if [ "$status" -ne 2 ] || ! grep -q '^refused: ' "$errf"; then
        printf 'FAIL: %s: the fallback reported neither acceptance nor refusal (exit %s):\n' \
          "$path" "$status" >&2
        cat "$errf" >&2
        failed=$((failed + 1))
        continue
      fi
      fallback_refusals=$((fallback_refusals + 1))
      if [ "$expected" != invalid ]; then
        printf 'FAIL: %s: the fallback refused an %s row\n' "$path" "$expected" >&2
        failed=$((failed + 1))
        continue
      fi
      reason=$(policy_of "$errf")
      [ -n "$reason" ] && printf '%s\t%s\n' "$path" "$reason" >>"$work/policy-got"
      ;;
  esac
done <"$manifest"

: >"$work/empty"
"$route" --doc "$work/empty" >"$work/out" 2>"$work/err"
status=$?
if [ "$status" -ne 2 ] || ! grep -q '^refused: invalid: unexpected end at 0' "$work/err"; then
  printf 'FAIL: the empty document was not the fallback'"'"'s refusal (exit %s)\n' "$status" >&2
  cat "$work/err" >&2
  failed=$((failed + 1))
fi

head -c 1048577 /dev/zero >"$work/long"
"$route" --doc "$work/long" >"$work/out" 2>"$work/err"
status=$?
if [ "$status" -ne 2 ] || ! grep -q '^refused: input too long' "$work/err"; then
  printf 'FAIL: the over-bound document was not the fallback'"'"'s refusal (exit %s)\n' "$status" >&2
  cat "$work/err" >&2
  failed=$((failed + 1))
fi

# The opener-rich document: balanced, accepted by the reference, and outside the
# domain because the opener-count clause counts bytes rather than nesting.  The
# fallback must accept it, with a value — the clause's conservatism narrows the
# domain and never changes an answer.
printf '"' >"$work/rich"
for _ in $(seq 129); do printf '[' >>"$work/rich"; done
printf '"' >>"$work/rich"
"$route" --doc "$work/rich" >"$work/out" 2>"$work/err"
status=$?
if [ "$status" -ne 0 ] || [ "$(fallback_of "$work/out")" != accepted ] ||
   ! grep -q 'decoded=true' "$work/out"; then
  printf 'FAIL: the opener-rich document was not the fallback'"'"'s acceptance (exit %s):\n' "$status" >&2
  cat "$work/out" "$work/err" >&2
  failed=$((failed + 1))
fi

# ---------------------------------------------------------------------------
# The depth boundary
#
# The reference parser's bound is `Limits.default.maxDepth` = 128: 128 nested
# containers parse and the document is admitted, so the object answers it (and
# must accept it); 129 exhausts the reference's bound, the opener-count clause
# refuses the document, and the fallback reports the reference's own
# `depthExceeded`.  The native walk's stack is `stage2.c`'s `MAXD` = 520; 129 and
# 520 are outside the domain, so the route does not call the object there and
# the driver is run only to record what it would have answered.
# ---------------------------------------------------------------------------
depth_doc() { # <depth>
  local d=$1 i
  for ((i = 0; i < d; i++)); do printf '['; done
  for ((i = 0; i < d; i++)); do printf ']'; done
}

for d in 128 129 520 521; do
  depth_doc "$d" >"$work/depth-$d.json"
  "$route" --doc "$work/depth-$d.json" >"$work/out" 2>"$work/err"
  status=$?
  "$driver" "$work/depth-$d.json" >"$work/dout" 2>/dev/null
  if [ "$d" = 128 ]; then
    if [ "$status" -ne 0 ]; then
      printf 'FAIL: depth %s: the route exited %s\n' "$d" "$status" >&2
      cat "$work/err" >&2
      failed=$((failed + 1))
      continue
    fi
    compare_observation "depth $d" "$work/out" "$work/dout" || continue
    if [ "$(verdict_of "$work/out")" != 1 ]; then
      printf 'FAIL: depth %s: the object refused a document inside both bounds\n' "$d" >&2
      failed=$((failed + 1))
    fi
    continue
  fi
  if [ "$status" -ne 2 ] || ! grep -q '^refused: depthExceeded' "$work/err"; then
    printf 'FAIL: depth %s: expected the fallback'"'"'s depthExceeded refusal (exit %s):\n' \
      "$d" "$status" >&2
    cat "$work/err" >&2
    failed=$((failed + 1))
    continue
  fi
  # The measurement, not an assertion: the object would have accepted 129..520.
  if [ "$d" = 129 ] || [ "$d" = 520 ]; then
    if [ "$(verdict_of "$work/dout")" != 1 ]; then
      printf 'WARN: depth %s: the driver did not accept; the divergence class moved\n' "$d" >&2
    fi
  fi
done

# The class the fallback refuses for the reference's reason: the fourteen corpus
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
  printf 'FAIL: the fallback refuses a different policy class than the one pinned:\n' >&2
  cat "$work/policy-diff" >&2
  failed=$((failed + 1))
fi
if [ "$(sort -u "$work/policy-got" | wc -l)" -ne 14 ]; then
  printf 'FAIL: expected 14 policy refusals, saw %s\n' "$(sort -u "$work/policy-got" | wc -l)" >&2
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

# Every row's answer agrees with the reference: the fast path's verdict matches
# the row (the object and the reference agree on every syntactic class), and the
# fallback's answer is the reference's by construction.
if [ "$diverged" -ne 0 ]; then
  printf 'FAIL: %s default-profile rows still diverge from the reference:%s\n' \
    "$diverged" "$divergent" >&2
  failed=$((failed + 1))
fi

if [ "$accepts" -eq 0 ] || [ "$invalids" -eq 0 ]; then
  printf 'FAIL: the fast-path arm is empty (accept %s, invalid %s)\n' "$accepts" "$invalids" >&2
  failed=$((failed + 1))
fi
if [ "$fast" -eq 0 ] || [ "$fallback_refusals" -eq 0 ]; then
  printf 'FAIL: the outcome arms are empty (fast %s, fallback refusals %s, fallback accepts %s)\n' \
    "$fast" "$fallback_refusals" "$fallback_accepts" >&2
  failed=$((failed + 1))
fi
if [ "$skipped" -eq 0 ]; then
  printf 'FAIL: the manifest carries no non-default-profile row to skip\n' >&2
  failed=$((failed + 1))
fi

# The byte comparison is only a comparison if some row carries payload bytes:
# two empty payloads agree whatever the object wrote.  Both arms must be
# non-empty, so a route that stopped printing them cannot pass.
if [ "$rows_with_arena" -eq 0 ]; then
  printf 'FAIL: no compared row carried arena bytes; the value comparison is vacuous\n' >&2
  failed=$((failed + 1))
fi
if [ "$rows_with_events" -eq 0 ]; then
  printf 'FAIL: no compared row carried event bytes; the value comparison is vacuous\n' >&2
  failed=$((failed + 1))
fi

if [ "$failed" -ne 0 ]; then
  printf 'FAIL: %s assertion(s) failed over %s default-profile rows\n' "$failed" "$rows" >&2
  exit 1
fi
printf 'ok: %s default-profile rows: %s fast-path row(s) agree with the driver on the observation, arena and events (%s arena byte(s) over %s row(s), %s event byte(s) over %s row(s)); fast path accept %s, invalid %s; fallback refusals %s, fallback accepts %s; divergence %s; empty excluded %s; %s non-default-profile rows skipped; depth 128 fast, 129/520/521 fall back with depthExceeded; 14 policy rows fall back with the reference reasons\n' \
  "$rows" "$fast" "$compared_arena" "$rows_with_arena" "$compared_events" "$rows_with_events" \
  "$accepts" "$invalids" "$fallback_refusals" "$fallback_accepts" "$diverged" "$excluded" "$skipped"
exit 0
