#!/usr/bin/env bash
# The negative build: the POS8 wrapper with its headline theorem removed.
#
#   nix develop -c bash tests/json-unit-contracts/negative.sh
#
# `entry_pos8_satisfies` takes `entry_pos8_refines` as its only substantive
# input.  The record's `pre` supplies every hypothesis of that theorem, and the
# theorem supplies the conclusion — `∃ k' mem', runFuel … = some (.ret …) ∧ …` —
# which no conjunct of `pre` can produce.  This check copies the module, replaces
# the single line marked `-- negative-build-anchor` (the line that applies the
# headline) with a hole of the enclosing `have`'s type, and builds the copy **by
# name**.
#
# The control passes only when the build fails **inside the wrapper** and the
# diagnostics say which declaration was left unproved:
#
#   * a placeholder diagnostic whose residual goal is the headline's conclusion,
#   * a footprint-pin diagnostic naming `entry_pos8_satisfies` with the `sorryAx`
#     carrier the hole introduces.
#
# A build that succeeds, or one that fails for any other reason — a substitution
# that broke the syntax, a missing import, an error in another module — fails the
# control: a control that fires for the wrong reason certifies nothing.
#
# Nothing outside the copy and its build products is written, and both are
# removed on exit.
#
# Exit status: 0 when the assertions hold, 1 when one fails, 3 when the fixture
# itself is not usable.
set -uo pipefail

repo=$(cd "$(dirname "$0")/../.." && pwd)
src=$repo/LeanLLVM/Vellum/JsonUnitContracts.lean
dst=$repo/LeanLLVM/Vellum/JsonUnitContractsNegative.lean
marker='-- negative-build-anchor'
wrapper='entry_pos8_satisfies'

[ -f "$src" ] || { echo "SETUP: $src is missing" >&2; exit 3; }
if [ -e "$dst" ]; then
  echo "SETUP: $dst already exists; refusing to overwrite it" >&2
  exit 3
fi

cleanup() {
  rm -f "$dst"
  rm -f "$repo"/.lake/build/lib/lean/LeanLLVM/Vellum/JsonUnitContractsNegative.*
}
trap cleanup EXIT

marked=$(grep -c -- "$marker" "$src")
if [ "$marked" -ne 1 ]; then
  echo "SETUP: expected exactly one '$marker' line in $src, found $marked" >&2
  exit 3
fi

# The substitution is anchored to the marker and is one line: the marked line
# becomes a hole whose expected type is the enclosing `have`'s.
awk -v marker="$marker" '
  index($0, marker) { print "    exact ?_ " marker; next }
  { print }
' "$src" > "$dst" || { echo "SETUP: cannot write $dst" >&2; exit 3; }

log=$(mktemp) || { echo "SETUP: cannot create a log file" >&2; exit 3; }
trap 'rm -f "$log"; cleanup' EXIT

( cd "$repo" && lake build LeanLLVM.Vellum.JsonUnitContractsNegative ) >"$log" 2>&1
status=$?

fail=0
report() { echo "FAIL: $1"; fail=1; }

# 1. The build must fail.
[ "$status" -ne 0 ] || report "the build succeeded: removing the headline did not break the wrapper"

# 2. It must fail at the hole, with the headline's conclusion as the residual goal.
grep -q "don't know how to synthesize placeholder" "$log" \
  || report "no placeholder diagnostic: the marked line was not replaced or not reached"
grep -q "∃ k' mem'," "$log" \
  || report "the residual goal is not the headline's conclusion"

# 3. The diagnostics must name the wrapper's declaration and the carrier the hole
#    introduces, so the failure is attributed rather than merely present.
grep -q "LeanLLVM\.Vellum\.${wrapper}' depends on axioms: \[propext, sorryAx, Quot\.sound\]" "$log" \
  || report "no pin diagnostic names LeanLLVM.Vellum.${wrapper} with the sorryAx carrier"

# 4. It must not fail elsewhere: every error that names a source file must name
#    the copy, and none may name another module.
if grep -E '^error: .*\.lean:' "$log" | grep -v "JsonUnitContractsNegative\.lean" >/dev/null; then
  report "the build also failed outside the copy:"
  grep -E '^error: .*\.lean:' "$log" | grep -v "JsonUnitContractsNegative\.lean" | sed 's/^/  /'
fi
if ! grep -E '^error: .*JsonUnitContractsNegative\.lean:' "$log" >/dev/null; then
  report "no error names the copy: the failure came from somewhere else"
fi

if [ "$fail" -ne 0 ]; then
  echo "--- build log ---"
  cat "$log"
  exit 1
fi

echo "negative build: the wrapper fails to close with its headline removed (exit $status),"
echo "residual goal is the headline's conclusion, and the pin names ${wrapper}."
