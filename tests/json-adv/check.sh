#!/usr/bin/env bash
# An adversarial and refusal corpus for the JSON reference parser.
#
#   nix develop -c bash tests/json-adv/check.sh
#
# The corpus in `tests/json-adv/corpus` is a set of deterministic documents that
# sit on the parser's refusal boundaries: the empty and whitespace-only text,
# truncated strings and escapes, truncated and invalid UTF-8, lone surrogates,
# noncharacters, duplicate keys, nesting at 127/128/129, large numbers, `01`,
# `1e`, `-`, trailing data, a byte-order mark, and strings whose escapes and
# multibyte tails straddle a 64-byte window.
#
# `manifest.tsv` has the same four tab-separated columns as
# `tests/json/manifest.tsv` -- path relative to the corpus, expected verdict,
# expected rendering (`-` unless the verdict is `accept`), and limits profile --
# and `leanllvm-json` is run over it directly, so the decisions and accepted
# renderings are compared by the parser's own corpus driver.
#
# `expect.tsv` carries one row per document: the path, the reference parser's
# refusal class, its refusal position (`-` for the byte-order-mark rule and the
# limit outcomes, which carry no position), and how the position is checked.
#
# Error positions.  `leanllvm-json` prints a verdict and a rendering and no
# position, so a position cannot be read from it.  A document that begins with
# a structural delimiter reaches the reference parser through the route probe's
# fallback: `leanllvm-json-route --doc <file> 0` sets the native depth bound to
# zero, the depth clause refuses the document, and the fallback answers it with
# `parseBytes`, printing the reference's own `refused: invalid: <class> at <p>`
# on stderr.  Those rows are marked `route` and the class and position are
# compared here.  A document whose root is a scalar (a top-level literal,
# number, string, the empty text, or a leading invalid UTF-8 byte) never reaches
# the depth clause, so its position is recorded but cannot be machine-checked on
# this path; those rows are marked `unverified` and are printed as such, never
# counted as verified.  The byte-order-mark and limit rows carry no position.
#
# The controls.  The unchanged manifest must agree with the driver and every
# `route` row must agree with the fallback.  A copy of the manifest with one
# accepted row's rendering changed must be refused by the driver with a
# `mismatch:` line, and a copy of `expect.tsv` with one `route` row's position
# changed must be refused by the comparison below.  A corpus whose offset
# expectations cannot fail is a red, not a pass.
#
# Exit status: 0 when every assertion holds, 1 when one fails, 3 when a fixture
# is not usable (an absent file or binary, a missing final newline, a row set
# that does not match the corpus, or no `route` or `unverified` row to control).

set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
corpus=$here/corpus
manifest=$here/manifest.tsv
expect=$here/expect.tsv
driver=$repo/.lake/build/bin/leanllvm-json
route=$repo/probes/json/route/build/leanllvm-json-route
driver_hint='nix develop -c bash probes/install/lake-locked.sh build leanllvm-json'
route_hint='nix develop -c bash probes/json/route/build.sh'

setup() { printf 'SETUP: %s\n' "$1" >&2; exit 3; }

[ -d "$corpus" ] || setup "absent: $corpus"
[ -f "$manifest" ] || setup "absent: $manifest"
[ -f "$expect" ] || setup "absent: $expect"
[ -x "$driver" ] || setup "absent: $driver
  build it with: $driver_hint"
[ -x "$route" ] || setup "absent: $route
  build it with: $route_hint"

for file in "$manifest" "$expect"; do
  if [ -s "$file" ] && [ -n "$(tail -c 1 "$file")" ]; then
    setup "the last line of $file has no newline"
  fi
done

corpus_files=$(ls "$corpus" | LC_ALL=C sort)
manifest_paths=$(cut -f 1 "$manifest" | LC_ALL=C sort)
expect_paths=$(cut -f 1 "$expect" | LC_ALL=C sort)
[ "$corpus_files" = "$manifest_paths" ] || setup "the corpus and manifest name different files"
[ "$corpus_files" = "$expect_paths" ] || setup "the corpus and expect.tsv name different files"

while IFS=$'\t' read -r path verdict rendering profile; do
  [ "$profile" = default ] || setup "the corpus uses only the default profile: $path"
done < "$manifest"

# The expectation rows are checked for well-formedness before any document is
# run: a typo in a class or a row that names a position without saying how it is
# checked is a fixture defect, not a passing row.
# The refusal class -> the words the reference's fallback prints before ` at `.
declare -A class_text=(
  [unexpectedEnd]='unexpected end'
  [unexpectedByte]='unexpected byte 0x[0-9a-f][0-9a-f]'
  [badLiteral]='bad literal'
  [badNumber]='bad number'
  [unterminatedString]='unterminated string'
  [badEscape]='bad escape'
  [badUTF8]='bad UTF-8'
  [unpairedSurrogate]='unpairedSurrogate'
  [noncharacter]='noncharacter'
  [controlCharacter]='control character'
  [expectedColon]='expected a colon'
  [expectedComma]='expected a comma'
  [expectedCloseBracket]='expected a close bracket'
  [expectedCloseBrace]='expected a close brace'
  [trailingData]='trailing data'
)

while IFS=$'\t' read -r path klass pos check; do
  case $klass in
    accept)
      [ "$pos" = - ] && [ "$check" = - ] ||
        setup "$path: an accepted row must carry '-\t-' expectations" ;;
    byteOrderMark|inputTooLong|depthExceeded|outOfCapacity)
      [ "$pos" = - ] && [ "$check" = - ] ||
        setup "$path: '$klass' carries no position" ;;
    *)
      [ -n "${class_text[$klass]:-}" ] || setup "$path: unknown refusal class '$klass'"
      case $check in
        route|unverified) ;;
        *) setup "$path: a refusal position must be 'route' or 'unverified', not '$check'" ;;
      esac
      [[ $pos =~ ^[0-9]+$ ]] || setup "$path: a refusal position must be a number, not '$pos'" ;;
  esac
done < "$expect"

work=$(mktemp -d) || setup "cannot create a temporary directory"
trap 'rm -rf "$work"' EXIT

failures=0
rows=0
verified=0
unverified=0
positionless=0

# One document's position, from the reference parser's fallback.  Sets
# `observed_offset` to `verified at <p>` or returns nonzero after printing the
# disagreement.
observed_offset=
verify_route() {
  local path=$1 want_class=$2 want_pos=$3
  local errf=$work/route.err stderr_line prefix pos pattern
  "$route" --doc "$corpus/$path" 0 >/dev/null 2>"$errf"
  local status=$?
  if [ "$status" -ne 2 ]; then
    printf 'mismatch: %s: the fallback exited %s, not 2\n' "$path" "$status" >&2
    return 1
  fi
  stderr_line=$(sed -n '1p' "$errf")
  case $stderr_line in
    'refused: invalid: '*) ;;
    *)
      printf 'mismatch: %s: the fallback did not refuse the document: %s\n' \
        "$path" "$stderr_line" >&2
      return 1 ;;
  esac
  prefix=$(printf '%s' "$stderr_line" |
    sed -E 's/^refused: invalid: (.*) at [0-9]+.*$/\1/')
  pos=$(printf '%s' "$stderr_line" |
    sed -E 's/^refused: invalid: .* at ([0-9]+).*$/\1/')
  pattern=${class_text[$want_class]:-}
  if [ -z "$pattern" ]; then
    setup "$path: unknown refusal class '$want_class'"
  fi
  if ! [[ $prefix =~ ^$pattern$ ]]; then
    printf 'mismatch: %s: expected refusal class %s, got %s\n' \
      "$path" "$want_class" "$stderr_line" >&2
    return 1
  fi
  if [ "$pos" != "$want_pos" ]; then
    printf 'mismatch: %s: expected refusal at %s, got %s\n' \
      "$path" "$want_pos" "$pos" >&2
    return 1
  fi
  observed_offset="verified at $pos"
  verified=$((verified + 1))
  return 0
}

# Compare one output transcript against the manifest and expectation files.
compare_transcript() {
  local transcript=$1 expect_file=$2
  local declared_pos declared_check declared_class
  local path klass pos check verdict rendering want_line got_line
  local -A got_verdict got_rendering
  local -A want_pos want_check want_class
  local out_rows
  rows=0
  verified=0
  unverified=0
  positionless=0
  failures=0

  while IFS=$'\t' read -r path klass pos check; do
    want_class[$path]=$klass
    want_pos[$path]=$pos
    want_check[$path]=$check
  done < "$expect_file"

  out_rows=$(wc -l < "$transcript")
  local listed
  listed=$(wc -l < "$manifest")
  if [ "$out_rows" -ne "$listed" ]; then
    printf 'mismatch: the transcript has %s lines for %s manifest rows\n' \
      "$out_rows" "$listed" >&2
    return 1
  fi

  while IFS=$'\t' read -r path verdict rendering; do
    got_verdict[$path]=$verdict
    got_rendering[$path]=$rendering
  done < "$transcript"

  while IFS=$'\t' read -r path verdict rendering profile; do
    rows=$((rows + 1))
    declared_class=${want_class[$path]:-}
    declared_pos=${want_pos[$path]:-}
    declared_check=${want_check[$path]:-}
    if [ -z "$declared_check" ]; then
      printf 'mismatch: %s: no expectation row\n' "$path" >&2
      failures=$((failures + 1))
      continue
    fi

    observed_offset=
    case $declared_check:$declared_pos in
      -:-)
        observed_offset='-'
        positionless=$((positionless + 1)) ;;
      unverified:[0-9]*)
        observed_offset="unverified $declared_class@$declared_pos"
        unverified=$((unverified + 1)) ;;
      route:[0-9]*)
        if ! verify_route "$path" "$declared_class" "$declared_pos"; then
          failures=$((failures + 1))
          observed_offset='unverified'
        fi ;;
      *)
        printf 'mismatch: %s: malformed expectation row (%s, %s)\n' \
          "$path" "$declared_check" "$declared_pos" >&2
        failures=$((failures + 1))
        observed_offset='malformed' ;;
    esac

    want_line=$(printf '%s\t%s\t%s\t%s' \
      "$path" "$verdict" "$rendering" \
      "$(case $declared_check:$declared_pos in
           -:-) printf -- '-' ;;
           unverified:*) printf 'unverified %s@%s' "$declared_class" "$declared_pos" ;;
           route:*) printf 'verified at %s' "$declared_pos" ;;
           *) printf 'malformed' ;;
         esac)")
    got_line=$(printf '%s\t%s\t%s\t%s' \
      "$path" "${got_verdict[$path]:-<absent>}" "${got_rendering[$path]:-<absent>}" \
      "$observed_offset")

    printf '%s\n' "$want_line"
    if [ "$got_line" != "$want_line" ]; then
      printf 'mismatch: %s: expected %s, got %s\n' \
        "$path" "$(printf '%s' "$want_line" | cut -f2-)" \
        "$(printf '%s' "$got_line" | cut -f2-)" >&2
      failures=$((failures + 1))
    fi
  done < "$manifest"

  [ "$failures" -eq 0 ]
}

cd "$repo" || setup "cannot enter $repo"

# Control: the unchanged manifest and expectation agree, row for row.
"$driver" --corpus "$corpus" --manifest "$manifest" >"$work/out" 2>"$work/driver.err"
status=$?
if [ "$status" -ne 0 ]; then
  printf 'mismatch: the unchanged manifest exited %s\n' "$status" >&2
  cat "$work/driver.err" >&2
  exit 1
fi

if [ "$(wc -l < "$work/out")" -ne "$(wc -l < "$manifest")" ]; then
  printf 'mismatch: the driver printed %s lines for %s manifest rows\n' \
    "$(wc -l < "$work/out")" "$(wc -l < "$manifest")" >&2
  exit 1
fi

if ! compare_transcript "$work/out" "$expect" >"$work/rows"; then
  cat "$work/rows" >&2
  exit 1
fi
cat "$work/rows"
summary_rows=$rows
summary_verified=$verified
summary_unverified=$unverified
summary_positionless=$positionless

# The corpus must exercise both half-states: at least one position the fallback
# verifies, and at least one recorded position the scalar-only path cannot.
if [ "$verified" -eq 0 ]; then
  printf 'FAIL: no offset was verified through the fallback\n' >&2
  exit 1
fi
if [ "$unverified" -eq 0 ]; then
  printf 'FAIL: no scalar-only offset is recorded as unverified\n' >&2
  exit 1
fi

# Control: change one accepted row's expected rendering.  The driver must
# refuse the manifest and say `mismatch:`.
awk -F '\t' -v OFS='\t' '
  !done && $2 == "accept" { $3 = $3 "0"; done = 1 }
  { print }
' "$manifest" > "$work/tampered-manifest.tsv"

if cmp -s "$manifest" "$work/tampered-manifest.tsv"; then
  setup "the manifest has no accepted row to tamper"
fi

"$driver" --corpus "$corpus" --manifest "$work/tampered-manifest.tsv" \
  >"$work/tampered.out" 2>"$work/tampered.err"
status=$?
if [ "$status" -eq 0 ]; then
  printf 'FAIL: the tampered rendering exited 0\n' >&2
  exit 1
fi
if ! grep -q '^mismatch:' "$work/tampered.err"; then
  printf 'FAIL: the tampered rendering exited %s without a mismatch line\n' \
    "$status" >&2
  cat "$work/tampered.err" >&2
  exit 1
fi

# Control: move one verified position off by one.  The comparison must refuse
# it even though the driver's transcript is unchanged.
awk -F '\t' -v OFS='\t' '
  !done && $4 == "route" { $3 = $3 + 1; done = 1 }
  { print }
' "$expect" > "$work/tampered-expect.tsv"

if cmp -s "$expect" "$work/tampered-expect.tsv"; then
  setup "expect.tsv has no route row to tamper"
fi

if compare_transcript "$work/out" "$work/tampered-expect.tsv" \
    >"$work/tampered-rows" 2>"$work/tampered-offset.err"; then
  printf 'FAIL: the tampered offset expectation passed\n' >&2
  exit 1
fi
if ! grep -q '^mismatch:' "$work/tampered-offset.err"; then
  printf 'FAIL: the tampered offset failed without a mismatch line\n' >&2
  cat "$work/tampered-offset.err" >&2
  exit 1
fi

printf 'ok: %s rows agree; %s offsets verified through the reference fallback, %s recorded but unverified, %s rows without a position\n' \
  "$summary_rows" "$summary_verified" "$summary_unverified" "$summary_positionless"
