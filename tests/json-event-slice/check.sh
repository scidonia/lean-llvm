#!/usr/bin/env bash
# The `[1]` event slice's caller fixture.
#
#   nix develop -c bash tests/json-event-slice/check.sh
#
# The decoder side is `JsonEventPremisesOneParse.evb_sliceOne_value_closed`: the
# event decoder's value at `[1]` is the reference parser's canonical value,
# unconditionally.  The runtime/ABI step is the declared assumption `EvbEmission`
# in `LeanLLVM/Refinement/JsonEventEmission.lean` — that the selected object
# (`leanllvm_json_pipeline`, built by `probes/json/route/build.sh`, called through
# `shim.c`) leaves the empty arena and the trace's event bytes at the destination
# and event buffers; `evb_events_of_post` derives the event half from the post and
# `evb_arena_not_empty` shows the arena half is the open datum.  This scenario is
# the caller side of that step, over two documents:
#
#   one    `[1]` — a genuine native success: admission admits it, the object is
#          called, its verdict is `1`, and `--value` decodes the emitted stream
#          to the reference's canonical value (the same value `[1.0]` has: the
#          number record carries the binary64 bits, not the source lexeme);
#   empty  the zero-byte document — a reference fallback: admission declines it,
#          so the scalar reference parser answers, and its refusal is reported
#          with the reference's own class and offset (`invalid:unexpectedEnd` at
#          0).  No native call is made.
#
# What this asserts:
#
#   ES1  `--doc one` exits 0, writes nothing to stderr, and its first line is the
#        fast path's observation with `verdict=1` and an empty arena (`ndst=0`).
#        This is what makes the success *native*: the fallback never prints a
#        `verdict=` line.
#   ES2  `--value one` exits 0 and prints exactly the oracle's line:
#        `value: verdict=1 value=5b23303030303030303030303030663033665d`
#        — the UTF-8 hex of `[#000000000000f03f]`, which is
#        `renderValue (canonValue v)` for the reference's `v` at `[1]`.
#        The same row is pinned in `tests/json-value/expected.tsv` (`one`), so
#        the value oracle and this scenario compare one answer.
#   ES3  `--doc empty` exits 2, writes nothing to stdout, and its stderr is
#        exactly `refused: invalid: unexpected end at 0`.
#   ES4  `--value empty` exits 2 and prints exactly
#        `value: refused class=invalid:unexpectedEnd offset=0`.
#
# A control runs first: the value line form must be the one the route prints
# today for a document that is already in the oracle's corpus, so a detector
# that reads nothing fails as an absence rather than passing vacuously.
#
# Exit status: 0 when the assertions hold, 1 when one fails, 3 when a fixture is
# absent.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
route=${ROUTE:-"$repo/probes/json/route/build/leanllvm-json-route"}
one=$here/corpus/one
empty=$here/corpus/empty

setup() { printf 'json-event-slice: %s\n' "$1" >&2; exit 3; }
fail() { printf 'FAIL: json-event-slice: %s\n' "$1" >&2; exit 1; }

[ -f "$one" ] || setup "absent: $one"
[ -f "$empty" ] || setup "absent: $empty"
[ "$(cat "$one")" = '[1]' ] || setup "the native-success fixture is not [1]"
[ ! -s "$empty" ] || setup "the fallback fixture is not empty"

if [ ! -x "$route" ]; then
  # The fixture is the caller, so the route binary is its prerequisite: build it
  # with the probe's own link step rather than a second recipe.
  ( cd "$repo" && nix develop -c bash probes/json/route/build.sh >/dev/null ) ||
    setup "cannot build the route: nix develop -c bash probes/json/route/build.sh"
fi
[ -x "$route" ] || setup "absent: $route"

work=$(mktemp -d) || setup "cannot create a temporary directory"
trap 'rm -rf "$work"' EXIT

# Control: the value line's form, read from a document the oracle already pins.
ctl=$repo/tests/json-value/corpus/refused-empty
[ -f "$ctl" ] || setup "absent: $ctl"
"$route" --value "$ctl" >"$work/ctl.out" 2>"$work/ctl.err"
ctl_status=$?
ctl_line=$(cat "$work/ctl.out")
[ "$ctl_status" -eq 2 ] &&
  [ "$ctl_line" = 'value: refused class=invalid:unexpectedEnd offset=0' ] || {
  printf 'FAIL: json-event-slice: the control read (%s) is not the value line\n' \
    "$ctl_status" >&2
  printf '  line: %s\n' "$ctl_line" >&2
  exit 1
}
printf 'ok: the value line is the route'"'"'s own (%s)\n' "$ctl_line"

# ES1: the native success, from the fast path's observation.
"$route" --doc "$one" >"$work/one.doc.out" 2>"$work/one.doc.err"
status=$?
[ "$status" -eq 0 ] || {
  printf 'FAIL: --doc [1] exited %s (want 0)\n' "$status" >&2
  sed -n '1,5p' "$work/one.doc.err" >&2
  exit 1
}
[ ! -s "$work/one.doc.err" ] || {
  printf 'FAIL: --doc [1] wrote to stderr: %s\n' "$(cat "$work/one.doc.err")" >&2
  exit 1
}
line=$(sed -n '1p' "$work/one.doc.out")
case $line in
  'verdict=1 nk='*' ndst=0 '*) ;;
  *)
    printf 'FAIL: --doc [1] did not take the native path: %s\n' "$line" >&2
    exit 1
    ;;
esac
printf 'ok: [1] is a native success: %s\n' "$line"

# ES2: the decoded canonical value through the same call.
"$route" --value "$one" >"$work/one.val.out" 2>"$work/one.val.err"
status=$?
want='value: verdict=1 value=5b23303030303030303030303030663033665d'
got=$(cat "$work/one.val.out")
[ "$status" -eq 0 ] && [ "$got" = "$want" ] || {
  printf 'FAIL: --value [1] exited %s, printed %s\n' "$status" "$got" >&2
  printf '  want: %s\n' "$want" >&2
  sed -n '1,5p' "$work/one.val.err" >&2
  exit 1
}
[ ! -s "$work/one.val.err" ] || {
  printf 'FAIL: --value [1] wrote to stderr: %s\n' "$(cat "$work/one.val.err")" >&2
  exit 1
}
printf 'ok: [1]'"'"'s canonical value: %s\n' "$got"

# ES3: the reference fallback at the empty document, with its exact diagnostic.
"$route" --doc "$empty" >"$work/empty.doc.out" 2>"$work/empty.doc.err"
status=$?
want='refused: invalid: unexpected end at 0'
got=$(cat "$work/empty.doc.err")
[ "$status" -eq 2 ] && [ ! -s "$work/empty.doc.out" ] && [ "$got" = "$want" ] || {
  printf 'FAIL: --doc (empty) exited %s, stdout %s bytes, stderr %s\n' \
    "$status" "$(wc -c <"$work/empty.doc.out")" "$got" >&2
  printf '  want: %s\n' "$want" >&2
  exit 1
}
printf 'ok: the reference fallback: %s\n' "$got"

# ES4: the value arm's refusal line, the same refusal at the parser's vocabulary.
"$route" --value "$empty" >"$work/empty.val.out" 2>"$work/empty.val.err"
status=$?
want='value: refused class=invalid:unexpectedEnd offset=0'
got=$(cat "$work/empty.val.out")
[ "$status" -eq 2 ] && [ "$got" = "$want" ] || {
  printf 'FAIL: --value (empty) exited %s, printed %s\n' "$status" "$got" >&2
  printf '  want: %s\n' "$want" >&2
  sed -n '1,5p' "$work/empty.val.err" >&2
  exit 1
}
printf 'ok: the fallback'"'"'s value line: %s\n' "$got"

printf 'ok: the [1] event slice'"'"'s two caller fixtures\n'
