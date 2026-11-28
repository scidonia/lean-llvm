#!/usr/bin/env bash
# Validate `opt -passes=lower-switch` per switch for the production stage-2
# emission.
#
#   nix develop -c bash probes/install/ir/check-switch-lowering.sh
#
# The emission carries twenty `switch` instructions (seventeen in
# `leanllvm_json_stage2`, three in `num_scan`).  The importer does not model
# `switch`, so the import descent replaces them with `opt -passes=lower-switch`
# and trusts the transform.  This script discharges that trust for this
# module: it pins the emission's digest, lowers it with the recorded pass, and
# checks every switch's successor over an exhaustive domain (all 256 i8 bit
# patterns; representative constants for the one i32 switch, whose lowered tree
# branches only on `icmp` of the condition against constants).
#
# The per-switch table is written beside the emission as
# `stage2.production.switch.tsv`; stdout records the two digests, the switch
# count and the verdict.
#
# Exit status: 0 when every switch corresponds, 1 on a mismatch or unreadable
# lowering, 3 on a setup fault (missing tool, wrong artifact digest).
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)

module=${1:-$here/stage2.production.ll}
record=${2:-$here/stage2.production.switch.tsv}
expected=9e8975a41d466126136575102f5b5bb660eb6cf9e04427eedc612203677e51f4

fail() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }
reject() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }

[ -f "$module" ] || fail "absent: $module"
command -v opt >/dev/null 2>&1 || fail "opt is not on PATH"
command -v python3 >/dev/null 2>&1 || fail "python3 is not on PATH"

sha=$(sha256sum "$module" | awk '{print $1}')
if [ "$module" = "$here/stage2.production.ll" ]; then
  [ "$sha" = "$expected" ] ||
    fail "$module is $sha, not the captured $expected"
fi

work=$(mktemp -d "${TMPDIR:-/tmp}/switch-lowering.XXXXXX")
trap 'rm -rf "$work"' EXIT

# `opt -S` writes the input's spelling into `; ModuleID`, so invoke it from the
# repository root with the repository-relative path when the module is inside
# the tree: the lowered digest must not depend on where the caller stands.
rel=${module#"$repo"/}
if [ "$rel" != "$module" ]; then
  ( cd "$repo" && opt -S -passes=lower-switch "$rel" -o "$work/lowered.ll" )
else
  opt -S -passes=lower-switch "$module" -o "$work/lowered.ll"
fi
lowered_sha=$(sha256sum "$work/lowered.ll" | awk '{print $1}')
opt -passes=verify -disable-output "$work/lowered.ll" ||
  fail "the lowered module is not well-formed IR"
remaining=$(grep -c '^ *switch .*label ' "$work/lowered.ll" || true)
[ "$remaining" = 0 ] || fail "$remaining switch instructions survived the pass"

set +e
python3 "$here/check-switch-lowering.py" "$module" "$work/lowered.ll" "$work/rows.tsv"
status=$?
set -e
if [ -f "$work/rows.tsv" ]; then
  cp "$work/rows.tsv" "$record"
fi
[ "$status" -eq 0 ] ||
  reject "the switch check exited $status; rows in $record when it produced a table"


# The correspondence needs every switch to have at least two distinct
# successors: with one, the lowering emits a bare branch that never reads the
# condition, which is defined where a switch on a poison condition is undefined.
# That gap is invisible to the successor table, so the checker refuses the shape.
# This is the negative fixture for that refusal.
cat > "$work/single.ll" <<'IR'
define i32 @single(i32 %x) {
entry:
  switch i32 %x, label %a [
  ]
a:
  ret i32 1
}
IR
opt -S -passes=lower-switch "$work/single.ll" -o "$work/single.lowered.ll" 2>/dev/null ||
  fail "opt refused the single-successor fixture"
set +e
python3 "$here/check-switch-lowering.py" "$work/single.ll" "$work/single.lowered.ll" \
  "$work/single.tsv" >/dev/null 2>"$work/single.err"
single_status=$?
set -e
[ "$single_status" -ne 0 ] ||
  reject "the checker accepted a single-successor switch; its premise is not enforced"
grep -q 'single successor' "$work/single.err" ||
  reject "the checker refused the single-successor fixture for the wrong reason: $(cat "$work/single.err")"

nswitch=$(grep -c '^ *switch .*label ' "$module" || true)
tested=$(awk -F'\t' '$1 != "summary" && $1 != "index" {n += $9} END {print n+0}' "$record")
printf 'module\t%s\t%s\n' "$module" "$sha"
printf 'lowered\t%s\n' "$lowered_sha"
printf 'switches\t%s\tvalues tested\t%s\n' "$nswitch" "$tested"
printf 'rows\t%s\n' "$record"
tail -1 "$record"
