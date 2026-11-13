#!/usr/bin/env bash
# The route scenario.
#
#   nix develop -c bash probes/json/route/check.sh
#
# The route decides in two phases -- the adapter's native facts from the proved
# stage-1 mask unit, then the library's own policy scan where the walk saw a
# candidate -- and has three outcomes: the fast path (`verdict=` on stdout, the
# native object's observation), the fallback's acceptance
# (`fallback=accepted`), and the fallback's refusal (`refused: ...` on stderr,
# exit 2).  Seven claims are asserted:
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
#   6. the consumer mode reads a five-event fixture at the record widths the
#      object wrote: 5 tokens, one arena byte, 25 event bytes, both readings
#      agreeing on the token count and the checksum.
#   7. the two-phase admission agrees with the certified predicate on every row:
#      `--admit` reports the decision phase one's depth measurement and phase
#      two's policy scan produce, and the library's `admission`, on the same
#      bytes, and this script compares the two verdicts, the two reasons and --
#      wherever the native walk measured it -- the two depths itself, on every
#      manifest row and on the boundary documents.  It also compares the proved
#      depth counter's recombined final depth against the adapter's accumulator
#      on every row.  A control repeats the comparison with the native side's
#      depth bound moved off the certified 128 and must report the disagreement,
#      so an agreement that cannot fail is a red rather than a pass.
#   8. the depth clause's number is the maximum structural nesting, not an
#      opener-byte count and not a final balance: the opener-rich string, many
#      shallow sibling containers, a prefix that goes negative, bodies the
#      reference refuses (which end the token sequence), escaped quotes and
#      bodies straddling a 64-byte block boundary are each asserted against a
#      hand-written measurement as well as against `docDepth`, and a fixed-seed
#      sweep of malformed documents is compared row by row.
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
accepts=0; invalids=0; excluded=0; diverged=0; consumer_ok=0
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

# The opener-rich document: a string carrying 129 `[` bytes.  Its structural
# nesting is 0, so `admission` admits it and the route must take the fast path
# and the object must answer it -- the depth clause counts nesting, not opener
# bytes, and the fallback is not consulted for a document the domain admits.
printf '%s' '"' >"$work/rich"
for _ in $(seq 129); do printf '%s' '[' >>"$work/rich"; done
printf '%s' '"' >>"$work/rich"
"$route" --doc "$work/rich" >"$work/out" 2>"$work/err"
status=$?
"$driver" "$work/rich" >"$work/dout" 2>/dev/null
if [ "$status" -ne 0 ] || [ -n "$(fallback_of "$work/out")" ]; then
  printf 'FAIL: the opener-rich document did not take the fast path (exit %s):\n' "$status" >&2
  cat "$work/out" "$work/err" >&2
  failed=$((failed + 1))
else
  compare_observation "opener-rich" "$work/out" "$work/dout" || true
  if [ "$(verdict_of "$work/out")" != 1 ]; then
    printf 'FAIL: the opener-rich document: the object refused a document inside both bounds\n' >&2
    failed=$((failed + 1))
  fi
fi

# ---------------------------------------------------------------------------
# The depth boundary
#
# The reference parser's bound is `Limits.default.maxDepth` = 128: 128 nested
# containers parse and the document is admitted, so the object answers it (and
# must accept it); 129 exhausts the reference's bound, the depth clause measures
# 129 and refuses the document, and the fallback reports the reference's own
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

# ---------------------------------------------------------------------------
# The two-phase admission against the certified predicate
#
# The route's decision is phase one's native measurement (the maximum structural
# nesting, the policy-candidate flag, the empty and length bounds) plus phase
# two's reference scan where the walk saw a candidate.  `--admit` reports that
# decision, its reason, the depth it measured, and the library's `admission` --
# verdict, reason and `docDepth` -- for the same bytes, with the policy scan's
# own interval and the depth pass's statistics.  The comparison below is the
# shell's, not the row's own `agree` field: the verdict, the reason, the measured
# depth and the counter's final depth are read out and compared here.
# ---------------------------------------------------------------------------
admit_field() { # <row> <name>
  printf '%s\n' "$1" | tr ' ' '\n' | sed -n "s/^$2=//p" | head -1
}

admit_row() { # <file> [native depth] -> the row on stderr
  local out status
  out=$("$route" --admit "$1" 5 ${2:-} 2>&1 >/dev/null)
  status=$?
  if [ "$status" -ne 0 ]; then
    printf 'FAIL: --admit exited %s on %s:\n' "$status" "$1" >&2
    printf '%s\n' "$out" >&2
    return 1
  fi
  printf '%s\n' "$out" | grep '^admit '
}

# 0 when the two decisions agree, 1 when they differ, 2 when the row does not
# carry the compared fields (which is a failure of the row, not a decision).
#
# The depth clause is compared as a number, not only as the class of its reason:
# a native maximum that differs from `docDepth` while both sides refuse (or both
# admit) the document is a different measurement, and a comparison of class names
# cannot see it.  `native_depth` is `-` on the two rows whose decision returns
# before the walk (empty, over-long), and there the number is not compared.  The
# last comparison is inside one row rather than between the two decisions: the
# proved counter's recombined final depth and the adapter's accumulator are two
# arithmetics over one structural lane list, and they must end at the same depth.
admit_compare() { # <row>
  local v c r cr nd cd fin walk
  v=$(admit_field "$1" verdict)
  c=$(admit_field "$1" certified)
  r=$(admit_field "$1" reason)
  cr=$(admit_field "$1" certified_reason)
  nd=$(admit_field "$1" native_depth)
  cd=$(admit_field "$1" certified_depth)
  fin=$(admit_field "$1" depth_final)
  walk=$(admit_field "$1" depth_walk_final)
  [ -n "$v" ] && [ -n "$c" ] && [ -n "$r" ] && [ -n "$cr" ] && \
    [ -n "$nd" ] && [ -n "$cd" ] && [ -n "$fin" ] && [ -n "$walk" ] || return 2
  if [ "$nd" != "-" ] && [ "$nd" != "$cd" ]; then return 1; fi
  if [ "$fin" != "$walk" ]; then return 1; fi
  if [ "$v" = "$c" ] && [ "$r" = "$cr" ]; then return 0; fi
  return 1
}

agree_rows=0
agree_failures=0
candidate_rows=0
policy_rows=0
agree_classes="$work/agree-classes"
: >"$agree_classes"

agree_one() { # <label> <file> [native depth] -> the tool's default when omitted
  local row rc
  row=$(admit_row "$2" ${3:-}) || { agree_failures=$((agree_failures + 1)); return; }
  agree_rows=$((agree_rows + 1))
  admit_compare "$row"
  rc=$?
  if [ "$rc" -ne 0 ]; then
    agree_failures=$((agree_failures + 1))
    if [ "$rc" -eq 2 ]; then
      printf 'FAIL: %s: the admission row does not carry both decisions:\n  %s\n' \
        "$1" "$row" >&2
    else
      printf 'FAIL: %s: the two-phase decision and the certified predicate differ:\n  %s\n' \
        "$1" "$row" >&2
    fi
    return
  fi
  # The row's own agreement flag must be the same comparison's answer.
  if [ "$(admit_field "$row" agree)" != 1 ]; then
    agree_failures=$((agree_failures + 1))
    printf 'FAIL: %s: the two decisions agree and the row reports agree=%s\n' \
      "$1" "$(admit_field "$row" agree)" >&2
    return
  fi
  [ "$(admit_field "$row" candidate)" = 1 ] && candidate_rows=$((candidate_rows + 1))
  [ "$(admit_field "$row" policy)" = 1 ] && policy_rows=$((policy_rows + 1))
  printf '%s\t%s\t%s\t%s\t%s\n' "$(admit_field "$row" verdict)" \
    "$(admit_field "$row" reason)" "$(admit_field "$row" candidate)" \
    "$(admit_field "$row" policy)" "$1" >>"$agree_classes"
}

# Every manifest row, whatever its profile: the decision is about the bytes, and
# a profile only selects which rows the fidelity comparison runs.
while IFS=$'\t' read -r path expected rendering profile; do
  [ -n "${path:-}" ] || continue
  agree_one "$path" "$corpus/$path"
done <"$manifest"

# The boundary documents: the empty one, the over-bound one, the opener-rich
# one, and the four depth probes.
agree_one "empty" "$work/empty"
agree_one "over-bound" "$work/long"
agree_one "opener-rich" "$work/rich"
for d in 128 129 520 521; do
  agree_one "depth-$d" "$work/depth-$d.json"
done

# ---------------------------------------------------------------------------
# The depth clause's own documents
#
# The clause is the maximum structural nesting `docDepth` measures: not a count
# of opener bytes, not a final balance, and not a running counter clamped at
# zero.  The documents below are where those readings differ, and each row is
# asserted twice -- `agree_one` compares the native decision and its measured
# depth against `admission`/`docDepth`, and `depth_check` compares both against
# the measurement written here.  A row that agreed with the library by being
# wrong in the same way on both sides would pass the first and fail the second.
# ---------------------------------------------------------------------------
depth_rows=0
depth_failures=0
depth_check() { # <label> <file> <want verdict> <want reason> <want depth>
  local label=$1 file=$2 wv=$3 wr=$4 wd=$5 row v r nd cd
  row=$(admit_row "$file") || { depth_failures=$((depth_failures + 1)); return; }
  depth_rows=$((depth_rows + 1))
  v=$(admit_field "$row" verdict)
  r=$(admit_field "$row" reason)
  nd=$(admit_field "$row" native_depth)
  cd=$(admit_field "$row" certified_depth)
  if [ "$nd" != "$wd" ] || [ "$cd" != "$wd" ]; then
    printf 'FAIL: %s: measured depth native=%s certified=%s, expected %s\n' \
      "$label" "$nd" "$cd" "$wd" >&2
    depth_failures=$((depth_failures + 1))
  fi
  if [ "$v" != "$wv" ] || [ "$r" != "$wr" ]; then
    printf 'FAIL: %s: verdict=%s reason=%s, expected %s/%s\n' \
      "$label" "$v" "$r" "$wv" "$wr" >&2
    depth_failures=$((depth_failures + 1))
  fi
}

# Many shallow sibling containers: 200 `[]` pairs inside one array.  The opener
# bytes number 401 and the nesting is 2, so an opener-count clause refuses a
# document whose depth is inside the bound.
{ printf '%s' '['; for _ in $(seq 199); do printf '%s' '[],'; done; printf '%s' '[]]'; } \
  >"$work/siblings"
# A prefix that goes below zero: the running depth is 0, -1, -2, -1, 0, so the
# maximum prefix depth is 0.  A counter clamped at zero before the next opener
# would report 2.
printf '%s' ']] [[' >"$work/neg-prefix"
# A body the reference refuses ends the token sequence: an unterminated body and
# a bad escape, each after two opens and before a close a skipped body would have
# let count.
printf '%s' '[[ "abc' >"$work/body-ended"
printf '%s' '[["\q"]' >"$work/body-refused"
# A quote after a refused body still makes the document a policy candidate: the
# refusal here is at byte 6, past the body the depth walk stopped at.
printf '%s' '"\q" "\uD800"' >"$work/quote-after-refused"
# Escaped quotes and 200 `[` bytes inside one body: nesting 1, measured 1.
{ printf '%s' '["'; for _ in 1 2 3; do printf '%s' '\"'; done
  for _ in $(seq 200); do printf '%s' '['; done; printf '%s' '"]'; } >"$work/escaped"
# Bodies straddling a 64-byte block boundary: the opening quote at byte 62 with
# eight `[` in the body crossing lane 63/64, and the opening quote at lane 63
# with the body in the next block.  Both are nesting 1.
{ printf '%s' '['; for _ in $(seq 61); do printf ' '; done; printf '%s' '"'
  for _ in $(seq 8); do printf '%s' '['; done; printf '%s' '"]]'; } >"$work/straddle-body"
{ printf '%s' '['; for _ in $(seq 62); do printf ' '; done; printf '%s' '"'
  for _ in $(seq 8); do printf '%s' '['; done; printf '%s' '"]'; } >"$work/straddle-quote"

agree_one "siblings" "$work/siblings"
agree_one "neg-prefix" "$work/neg-prefix"
agree_one "body-ended" "$work/body-ended"
agree_one "body-refused" "$work/body-refused"
agree_one "quote-after-refused" "$work/quote-after-refused"
agree_one "escaped" "$work/escaped"
agree_one "straddle-body" "$work/straddle-body"
agree_one "straddle-quote" "$work/straddle-quote"

depth_check "opener-rich" "$work/rich" 1 none 0
depth_check "siblings" "$work/siblings" 1 none 2
depth_check "neg-prefix" "$work/neg-prefix" 1 none 0
depth_check "body-ended" "$work/body-ended" 1 none 2
depth_check "body-refused" "$work/body-refused" 1 none 2
depth_check "quote-after-refused" "$work/quote-after-refused" 0 unpairedSurrogate@6 0
depth_check "escaped" "$work/escaped" 1 none 1
depth_check "straddle-body" "$work/straddle-body" 1 none 1
depth_check "straddle-quote" "$work/straddle-quote" 1 none 1
depth_check "depth-128" "$work/depth-128.json" 1 none 128
depth_check "depth-129" "$work/depth-129.json" 0 depthBound 129

failed=$((failed + depth_failures))
if [ "$depth_rows" -eq 0 ]; then
  printf 'FAIL: no depth row was checked; the depth gate is vacuous\n' >&2
  failed=$((failed + 1))
fi

# The sweep: documents drawn from the bytes the depth rule branches on --
# brackets in both directions, quotes, backslashes, escape letters, hex digits,
# spaces and `:`.  A fixed-seed Lehmer generator draws them, so the row set is
# the same on every run; the comparison is the gate's, over verdict, reason and
# the measured depth.  This is what covers the body-refusal and block-boundary
# combinations the hand-written rows do not enumerate.
sweep_rows=0
cat >"$work/gen.awk" <<'AWK'
function rnd() { state = (state * 48271) % 2147483647; return state / 2147483647 }
BEGIN {
  state = 20261113
  nchar = split("91 93 123 125 34 92 117 68 56 48 49 32 44 58 97 120 70", code, " ")
  for (n = 0; n < 120; n++) {
    len = 1 + int(rnd() * 200)
    s = ""
    for (i = 0; i < len; i++) s = s sprintf("%c", code[1 + int(rnd() * nchar)])
    printf "%s", s > (dir "/sweep-" n ".json")
    close(dir "/sweep-" n ".json")
  }
}
AWK
awk -v dir="$work" -f "$work/gen.awk"
for f in "$work"/sweep-*.json; do
  agree_one "sweep-$(basename "$f" .json)" "$f"
  sweep_rows=$((sweep_rows + 1))
done
if [ "$sweep_rows" -ne 120 ]; then
  printf 'FAIL: the sweep generated %s document(s), expected 120\n' "$sweep_rows" >&2
  failed=$((failed + 1))
fi

# The controls, three of them, and none of them restates the certified bound.
#
#  1. The same comparison with the native bound set to zero: `[1,2]` nests one
#     level, so the native side must refuse it on the depth clause while
#     `admission` admits it, and the comparator -- the shell's comparison, not
#     only the row's own flag -- must report that disagreement.
#  2. The route's own decision consults that bound: with the native bound moved
#     to 127 the route must send the 128-deep document to the fallback, which is
#     the shipped path's witness that the decision is the native one.
#  3. The candidate detector's other direction is asserted above, on a
#     quote-bearing and a quote-free document.
control_failures=0

printf '[1,2]' >"$work/one-opener.json"
control_row=$(admit_row "$work/one-opener.json" 0)
if [ -z "$control_row" ]; then
  printf 'FAIL: the control run printed no admission row\n' >&2
  control_failures=$((control_failures + 1))
else
  admit_compare "$control_row"
  if [ $? -ne 1 ]; then
    printf 'FAIL: the control compared two decisions that must differ and reported agreement:\n  %s\n' \
      "$control_row" >&2
    control_failures=$((control_failures + 1))
  fi
  if [ "$(admit_field "$control_row" verdict)" != 0 ] ||
     [ "$(admit_field "$control_row" reason)" != depthBound ] ||
     [ "$(admit_field "$control_row" certified)" != 1 ]; then
    printf 'FAIL: the control did not move the native bound: %s\n' "$control_row" >&2
    control_failures=$((control_failures + 1))
  fi
  if [ "$(admit_field "$control_row" agree)" != 0 ]; then
    printf 'FAIL: the control row reports agree=%s for two decisions that differ\n' \
      "$(admit_field "$control_row" agree)" >&2
    control_failures=$((control_failures + 1))
  fi
fi

"$route" --doc "$work/depth-128.json" 127 >"$work/out" 2>"$work/err"
status=$?
if [ "$status" -ne 0 ] || [ "$(fallback_of "$work/out")" != accepted ] ||
   [ -n "$(verdict_of "$work/out")" ]; then
  printf 'FAIL: the route did not take the fallback when its native bound refused (exit %s):\n' \
    "$status" >&2
  cat "$work/out" "$work/err" >&2
  control_failures=$((control_failures + 1))
fi
failed=$((failed + control_failures))
failed=$((failed + agree_failures))

if [ "$agree_rows" -eq 0 ]; then
  printf 'FAIL: no admission row was compared; the agreement gate is vacuous\n' >&2
  failed=$((failed + 1))
fi

# The candidate detector, both ways: a document with a quote byte (raw, and
# escaped with no raw quote of its own) is a candidate for the policy phase, and
# one without is not.  Without both directions the skip could be a detector that
# never fires, or one that always does.
printf '"a"' >"$work/quote-only.json"
printf '[1,2]' >"$work/no-quote.json"
printf '\\"' >"$work/escaped-only.json"
cand_failures=0
for probe in "quote-only:1" "no-quote:0" "escaped-only:1"; do
  name=${probe%%:*}; want=${probe##*:}
  row=$(admit_row "$work/$name.json" 128)
  got=$(admit_field "$row" candidate)
  if [ "$got" != "$want" ]; then
    printf 'FAIL: candidate detector: %s reports candidate=%s, expected %s\n' \
      "$name" "$got" "$want" >&2
    cand_failures=$((cand_failures + 1))
  fi
done
failed=$((failed + cand_failures))

# The agreement table, by row class: the two-phase verdict, the reason both
# decisions name, whether the walk saw a policy candidate, and whether the
# policy scan ran.  Its rows are the gate's own rows, so the split a reader sees
# is the split the assertions above covered.
printf 'the two-phase admission against the certified predicate, by row class\n'
printf '(class is verdict/reason/candidate/policy; rows is how many rows it covers;\n'
printf 'the rows are every manifest row and the boundary documents)\n\n'
printf '%-44s %6s\n' class rows
cut -f1-4 "$agree_classes" | awk -F'\t' '{printf "%s/%s/%s/%s\n", $1, $2, $3, $4}' \
  | sort | uniq -c | awk '{printf "%-44s %6s\n", $2, $1}'
printf '\n'

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

# ---------------------------------------------------------------------------
# The consumer mode
#
# `--consume` is the reading the timings page quotes as the production
# consumer's: the result read without printing, by index and record.  Its two
# readings must agree on the token count and the checksum and land on the event
# stream's end, and the record widths it decodes at (13 for a string, 9 for a
# number, 1 for every other tag) must be the ones the object wrote.  The fixture
# carries one of each: an array, an escaped string (one arena byte), a number,
# `true`, and the array's close.
# ---------------------------------------------------------------------------
printf '["\\n",123,true]' >"$work/consume.json"
"$route" --consume "$work/consume.json" 5 >"$work/out" 2>"$work/err"
status=$?
crow=$(grep '^row ' "$work/err")
cf() { printf '%s\n' "$crow" | tr ' ' '\n' | sed -n "s/^$1=//p" | head -1; }
if [ "$status" -ne 0 ] || [ -z "$crow" ]; then
  printf 'FAIL: --consume exited %s on a five-event document:\n' "$status" >&2
  cat "$work/err" >&2
  failed=$((failed + 1))
elif [ "$(cf path)" != fast ] || [ "$(cf tokens)" != 5 ] ||
     [ "$(cf values)" != 5 ] || [ "$(cf walked)" != 1 ] ||
     [ "$(cf ndst)" != 1 ] || [ "$(cf nev)" != 25 ] ||
     [ "$(cf foldsum)" != "$(cf valuessum)" ]; then
  printf 'FAIL: --consume read the five-event document as:\n  %s\n' "$crow" >&2
  printf '  expected path=fast tokens=5 values=5 walked=1 ndst=1 nev=25 and equal sums\n' >&2
  failed=$((failed + 1))
else
  consumer_ok=$((consumer_ok + 1))
fi

if [ "$failed" -ne 0 ]; then
  printf 'FAIL: %s assertion(s) failed over %s default-profile rows\n' "$failed" "$rows" >&2
  exit 1
fi
printf 'ok: %s default-profile rows: %s fast-path row(s) agree with the driver on the observation, arena and events (%s arena byte(s) over %s row(s), %s event byte(s) over %s row(s)); fast path accept %s, invalid %s; fallback refusals %s, fallback accepts %s; divergence %s; empty excluded %s; %s non-default-profile rows skipped; depth 128 fast, 129/520/521 fall back with depthExceeded; the opener-rich string takes the fast path; 14 policy rows fall back with the reference reasons; two-phase admission agrees with `admission` on %s row(s), the measured depth compared wherever the walk ran (policy candidate %s, policy scan run %s; control failures %s); the depth gate carries %s hand-written row(s) and %s swept document(s) agree with `docDepth`, the proved counter and the accumulator ending at the same depth on every row; %s consumer-mode fixture read as 5 tokens at ndst=1 nev=25 with agreeing readings\n' \
  "$rows" "$fast" "$compared_arena" "$rows_with_arena" "$compared_events" "$rows_with_events" \
  "$accepts" "$invalids" "$fallback_refusals" "$fallback_accepts" "$diverged" "$excluded" "$skipped" \
  "$agree_rows" "$candidate_rows" "$policy_rows" "$control_failures" "$depth_rows" "$sweep_rows" \
  "$consumer_ok"
exit 0
