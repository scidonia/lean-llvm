#!/usr/bin/env bash
# The identity dispatcher: one unit's boundary, three arms, one command.
#
#   nix develop -c bash kernel/json/identity/final-identity.sh entry
#   nix develop -c bash kernel/json/identity/final-identity.sh s1
#   nix develop -c bash kernel/json/identity/final-identity.sh entry --tree-only
#
# The three arms, in this order:
#
#   1. the unit's token identity, with its mutation controls
#      (`source-identity.sh --unit <unit>`);
#   2. the unit's emitted-code identity, with its controls
#      (`ir-identity.sh --unit <unit>`);
#   3. the unit's paired timing arm (`bench/paired.sh --unit <unit>`).
#
# `s1` (the classification mask unit) and `entry` (the entry unit) are the units
# that have all three.  Any other unit is a setup fault and exits 3 naming it,
# because an arm that does not exist cannot pass; a control runs that path on
# every invocation, since no implemented unit reaches it in normal use.
#
# `--tree-only` is passed to the two identity scripts: every input path must be
# inside this repository, so the claim reproduces from a checkout.  The timing
# arm reads nothing, so it takes no such flag.
#
# Exit status: the first arm that fails, or 0 when all three hold; 3 on a setup
# fault (no unit named, an unimplemented unit, an absent arm script).
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
source_arm=$here/source-identity.sh
ir_arm=$here/ir-identity.sh
timing_arm=$repo/kernel/json/bench/paired.sh

usage() {
  awk 'NR > 1 && /^set -/ { exit } NR > 1 { print }' "$0" | sed 's/^# \{0,1\}//' 
}

tree_only=0
unit=""
for arg in "$@"; do
  case "$arg" in
    --tree-only) tree_only=1 ;;
    -h|--help) usage; exit 0 ;;
    -*) printf 'final-identity: unknown option %s\n' "$arg" >&2; exit 3 ;;
    *)
      if [ -n "$unit" ]; then
        printf 'final-identity: one unit at a time; given %s and %s\n' "$unit" "$arg" >&2
        exit 3
      fi
      unit=$arg
      ;;
  esac
done

for path in "$source_arm" "$ir_arm" "$timing_arm"; do
  [ -e "$path" ] || { printf 'SETUP: absent arm: %s\n' "$path" >&2; exit 3; }
done

# dispatch <unit> -- run the three arms at that unit's boundary.
dispatch() {
  local u=$1
  case "$u" in
    s1|entry) : ;;
    *)
      printf 'SETUP: unit %s has no identity arms here; implemented units: s1 entry\n' "$u" >&2
      return 3
      ;;
  esac

  local -a tree=()
  [ "$tree_only" -eq 1 ] && tree=(--tree-only)

  printf '\n== %s: 1/3 token identity\n' "$u"
  printf '   bash kernel/json/identity/source-identity.sh --unit %s %s\n' "$u" "${tree[*]:-}"
  bash "$source_arm" --unit "$u" "${tree[@]}" || return $?

  printf '\n== %s: 2/3 emitted-code identity\n' "$u"
  printf '   bash kernel/json/identity/ir-identity.sh --unit %s %s\n' "$u" "${tree[*]:-}"
  bash "$ir_arm" --unit "$u" "${tree[@]}" || return $?

  printf '\n== %s: 3/3 paired timing\n' "$u"
  printf '   bash kernel/json/bench/paired.sh --unit %s\n' "$u"
  bash "$timing_arm" --unit "$u" || return $?
}

# The refusal path, exercised on every run: no implemented unit reaches it, so
# without this control the exit-3 branch would be untested code in the one
# script a reader is told to run.
refusal_control() {
  local out st
  out=$(dispatch no-such-unit 2>&1)
  st=$?
  if [ "$st" -ne 3 ]; then
    printf 'FAIL: control: an unimplemented unit exited %s, not 3\n' "$st" >&2
    printf '      output: %s\n' "$(printf '%s' "$out" | head -1)" >&2
    return 1
  fi
  if ! printf '%s' "$out" | grep -q 'no-such-unit has no identity arms'; then
    printf 'FAIL: control: the refusal did not name the missing unit\n' >&2
    printf '      output: %s\n' "$(printf '%s' "$out" | head -1)" >&2
    return 1
  fi
  printf 'ok: control: an unimplemented unit exits 3 and names it\n'
  printf '   %s\n' "$(printf '%s' "$out" | head -1)"
}

if [ -z "$unit" ]; then
  usage
  printf 'final-identity: give a unit: s1 or entry\n' >&2
  exit 3
fi

refusal_control || exit $?
printf '\n== %s: the three arms\n' "$unit"
dispatch "$unit" || exit $?
printf '\nok: %s: token identity, emitted-code identity and paired timing all hold\n' "$unit"
