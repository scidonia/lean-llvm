#!/usr/bin/env bash
# Arm D: the specification's `ent` word is the measured statements' word.
#
#   nix develop -c bash kernel/json/identity/ent-identity.sh
#   nix develop -c bash kernel/json/identity/ent-identity.sh --text-only
#   nix develop -c bash kernel/json/identity/ent-identity.sh --tree-only
#
# The word has no measured *function*: the block loop computes it inline in
# three places, so there is no body to lift and compare the way the mask unit's
# and the entry unit's bodies are compared.  What it has is text, and this arm
# checks that the text is one text and that `ent_oracle.c` is it:
#
#   --text   each of the three vendored sites (`measured/s1fuse.h:519-536`,
#            `:873-894`, `:1706-1722`) is extracted from `uint64_t ent = qm | (sm
#            & ~im);` through the grain guard's `#endif` plus its two `lim`
#            lines, with brace-only lines dropped and the `S1F_CTAB` arms
#            resolved by the preprocessor to the measured table path
#            (`-DS1F_CTAB=1`), and the same extraction from `ent_oracle.c`;
#            all four token streams must be equal.  A control rewrites one
#            numeral in a copy of the oracle and requires the same comparison
#            to report a difference.  The oracle is also compiled at the
#            measured compiler line, so a copy that is not valid C where it
#            moved fails as a setup fault rather than passing as text.
#
#   --rows   the row comparison: the oracle's `S`, `ent` and tail-masked `ent`
#            against the specification's `specScalar64`, `entryMask64` and its
#            tail application, row by row.  The specification route's
#            `JsonEntryMain --ent` mode emits `label qm sm im ws prevS n bi S
#            ent tailed` for the corpus's document blocks, a fixed-seed arm and
#            one block per named class; `ent_rows.c` reads those rows, drives
#            `ent_oracle_row` over the same seven inputs and prints the same
#            line shape, and the two streams are compared whole line by line.
#            One control per class asserts that the oracle's `S` differs from
#            the complement of the eight-byte structural set, and the count of
#            distinguishing rows is asserted in both directions.
#
# The default is both halves, so an invocation with no flags does not report
# success for a word whose rows were never compared.  `--text-only` runs the
# half that is here.
#
# Exit status: 0 when every requested half holds, 1 when the text comparison or
# the row comparison fails, and 3 on a setup fault (an absent input, tool or
# runner, a site that cannot be extracted, an unwritable work directory, a
# `--ent` mode that is absent, and so the rows cannot be compared here).
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
header=$repo/kernel/json/measured/s1fuse.h
oracle=$here/ent_oracle.c
route=$repo/JsonEntryMain.lean
cc=clang
cflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)
sites=3

run_text=0
run_rows=1
tree_only=0
any_mode=0

usage() {
  awk 'NR > 1 && /^set -/ { exit } NR > 1 { print }' "$0" | sed 's/^# \{0,1\}//' 
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --text) run_text=1; any_mode=1 ;;
    --text-only) run_text=1; run_rows=0; any_mode=1 ;;
    --rows) run_rows=1; any_mode=1 ;;
    --tree-only) tree_only=1 ;;
    -h|--help) usage; exit 0 ;;
    *) printf 'ent-identity: unknown argument %s\n' "$1" >&2; exit 3 ;;
  esac
  shift
done
if [ "$any_mode" -eq 0 ]; then run_text=1; run_rows=1; fi

for path in "$header" "$oracle"; do
  [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done
command -v "$cc" >/dev/null 2>&1 || {
  printf 'SETUP: no %s on PATH\n' "$cc" >&2
  exit 3
}
if [ "$tree_only" -eq 1 ]; then
  for path in "$header" "$oracle"; do
    case "$path" in
      "$repo"/*) ;;
      *) printf 'REFUSED: %s is outside %s and --tree-only was given\n' "$path" "$repo" >&2; exit 3 ;;
    esac
  done
fi

mkdir -p "$repo/.lake" || { printf 'SETUP: cannot create %s/.lake\n' "$repo" >&2; exit 3; }
work=$(mktemp -d "$repo/.lake/tmp-ent-identity.XXXXXX" 2>/dev/null) || {
  printf 'SETUP: cannot create a work directory under %s/.lake\n' "$repo" >&2
  exit 3
}
trap 'rm -rf "$work"' EXIT

# The statements, from `ent = qm | (sm & ~im)` through the `#endif` that closes
# the grain guard it is inside: `at_end` is set by `ent |= stm;`, and the site's
# own `#endif` is the next one.  Site `nth` is the nth occurrence, which is what
# makes the three sites separately addressable without naming line numbers that
# a vendor update would silently invalidate.
extract_ent() { # <file> <nth>
  awk -v nth="$2" '
    index($0, "uint64_t ent = qm | (sm & ~im);") > 0 { seen++; if (seen == nth) in_site = 1 }
    in_site { buf[++n] = $0 }
    in_site && index($0, "ent |= stm;") > 0 { at_end = 1 }
    in_site && at_end && $0 ~ /^[ \t]*#endif[ \t]*$/ {
      for (i = 1; i <= n; i++) print buf[i]
      found = 1
      exit
    }
    END { if (!found) exit 1 }
  ' "$1"
}

# The tail mask's two lines, at the same site.
extract_lim() { # <file> <nth>
  awk -v nth="$2" '
    index($0, "uint64_t lim = n - (bi << 6);") > 0 {
      seen++
      if (seen == nth) { print; getline; print; found = 1; exit }
    }
    END { if (!found) exit 1 }
  ' "$1"
}

# The normal form of a site: its statements with the structural braces of the
# grain block dropped (they group statements; the oracle places them at one
# scope so `S` can be returned), and with the preprocessor's `S1F_CTAB` arms
# resolved to the measured table path.  Comments and whitespace are
# representation.
normalise_site() {
  grep -v -E '^[[:space:]]*[{}][[:space:]]*$' \
    | "$cc" -E -P -DS1F_CTAB=1 -x c - 2>/dev/null \
    | tr '\n\t' '  ' | tr -s ' ' | sed -e 's/^ //' -e 's/ $//'
}

site_text() { # <file> <nth>
  local file=$1 nth=$2
  { extract_ent "$file" "$nth" && extract_lim "$file" "$nth"; } | normalise_site
}

site_lines() { # <file> <nth>
  local a b
  a=$(awk -v nth="$2" '
    index($0, "uint64_t ent = qm | (sm & ~im);") > 0 { seen++; if (seen == nth) { print NR; exit } }
  ' "$1")
  b=$(awk -v nth="$2" '
    index($0, "uint64_t lim = n - (bi << 6);") > 0 { seen++; if (seen == nth) { print NR + 1; exit } }
  ' "$1")
  printf '%s-%s' "$a" "$b"
}

arm_text() {
  local i text ref rc=0 got
  printf '\n== Arm D: the `ent` word'"'"'s statements are one text\n'
  ref=$(site_text "$oracle" 1)
  if [ -z "$ref" ]; then
    printf 'SETUP: cannot extract the statements from %s\n' "$oracle" >&2
    return 3
  fi

  # The copy is valid C in the place it moved to.
  if ! "$cc" "${cflags[@]}" -c "$oracle" -o "$work/ent_oracle.o"; then
    printf 'FAIL: %s does not compile at the measured line\n' "$oracle" >&2
    return 1
  fi
  printf 'ok: %s compiles at the measured compiler line\n' "$oracle"

  for i in $(seq 1 "$sites"); do
    if ! text=$(site_text "$header" "$i"); then
      printf 'SETUP: cannot extract site %s from %s\n' "$i" "$header" >&2
      return 3
    fi
    if [ "$text" = "$ref" ]; then
      printf 'ok: site %s (s1fuse.h:%s) is the oracle'"'"'s text (%s token bytes)\n' \
        "$i" "$(site_lines "$header" "$i")" "${#ref}"
    else
      rc=1
      printf 'DIFF: site %s (s1fuse.h:%s) differs from the oracle\n' \
        "$i" "$(site_lines "$header" "$i")" >&2
      diff -u <(printf '%s\n' "$ref" | tr ' ' '\n') \
              <(printf '%s\n' "$text" | tr ' ' '\n') \
        | sed -e '1,2d' -e 's/^/      /' | awk 'NR <= 20' >&2
    fi
  done
  [ "$rc" -eq 0 ] || return 1

  # The control: one numeral, in the tail mask's expression.
  cp "$oracle" "$work/ent_oracle.mutated.c"
  awk '{ if (!done && index($0, "(1ULL << lim)") > 0) { sub(/1ULL/, "2ULL"); done = 1 } print }' \
    "$oracle" > "$work/ent_oracle.mutated.c"
  if cmp -s "$oracle" "$work/ent_oracle.mutated.c"; then
    printf 'SETUP: the control could not rewrite a numeral in %s\n' "$oracle" >&2
    return 3
  fi
  printf '\n== Control: one numeral of the oracle rewrite changed\n'
  got=$(site_text "$work/ent_oracle.mutated.c" 1)
  if [ -z "$got" ]; then
    printf 'SETUP: the control copy could not be extracted\n' >&2
    return 3
  fi
  moved=0
  for i in $(seq 1 "$sites"); do
    text=$(site_text "$header" "$i")
    [ "$text" = "$got" ] || moved=$((moved + 1))
  done
  if [ "$moved" -eq 0 ]; then
    printf 'FAIL: the comparison did not see the changed numeral; it is not evidence\n' >&2
    return 1
  fi
  printf 'ok: the control is reported as a difference by %s of %s sites\n' "$moved" "$sites"
  return 0
}

# The eight-byte structural set `IsStructuralB` reads: `"`, `\`, `:`, `,`,
# `{`, `}`, `[`, `]`.
structural_set="22 5c 3a 2c 7b 7d 5b 5d"

# A class block's 64 bytes, one two-digit hex symbol per lane: the block the
# class row is the word's statement about.  These are the instrument's own
# copies; the row's four masks are the specification's and are not restated.
class_block() { # <class name>
  local name=$1 i
  case "$name" in
    string-interior)              printf '22 61 78 22'; i=4 ;;
    backslash-outside-string)     printf '5c 78';       i=2 ;;
    escaped-quote-outside-string) printf '5c 22 78';    i=3 ;;
    *) return 1 ;;
  esac
  while [ "$i" -lt 64 ]; do printf ' 78'; i=$((i + 1)); done
}

# The lanes of a class block whose byte is not one of the eight structural
# bytes, as a 64-bit word.  A word built on the structural set sets exactly
# these; the measured word's `S` is what differs from it.
structural_complement() { # <class name>
  local want bytes b i comp=0
  want=$(class_block "$1") || return 1
  read -r -a bytes <<< "$want"
  for i in $(seq 0 63); do
    b=${bytes[$i]}
    case " $structural_set " in
      *" $b "*) ;;
      *) comp=$((comp | (1 << i))) ;;
    esac
  done
  printf '%s\n' "$comp"
}

arm_rows() {
  printf '\n== Arm D: the word, row by row\n'
  local runner=$repo/.lake/build/bin/leanllvm-json-entry
  local reader=$here/ent_rows.c

  if [ ! -e "$route" ]; then
    printf 'SETUP: the row comparison reads the specification route'"'"'s `--ent` mode,\n' >&2
    printf 'SETUP: and %s is absent in this tree; the rows are uncompared here\n' "$route" >&2
    return 3
  fi
  if ! grep -q -- '--ent' "$route"; then
    printf 'SETUP: %s carries no `--ent` mode; the rows are uncompared here\n' "$route" >&2
    return 3
  fi
  if [ ! -e "$reader" ]; then
    printf 'SETUP: absent: %s\n' "$reader" >&2
    return 3
  fi
  if [ ! -x "$runner" ]; then
    printf 'SETUP: absent runner: %s\n' "$runner" >&2
    printf 'SETUP: build it with: nix develop -c lake build leanllvm-json-entry\n' >&2
    return 3
  fi

  # The corpus files the route compares over.  Their `"source"` fields name the
  # documents the rows' blocks are read from, so the runner is run from the
  # repository root.
  local corpus=() f rel
  for f in "$repo"/tests/json-entry/corpus/*.json; do
    [ -e "$f" ] || continue
    rel=${f#"$repo"/}
    corpus+=(--corpus "$rel")
  done
  if [ "${#corpus[@]}" -eq 0 ]; then
    printf 'SETUP: no entry corpus files under %s\n' "$repo/tests/json-entry/corpus" >&2
    return 3
  fi

  if ! "$cc" "${cflags[@]}" -c "$oracle" -o "$work/ent_oracle.o"; then
    printf 'FAIL: %s does not compile at the measured line\n' "$oracle" >&2
    return 1
  fi
  if ! "$cc" "${cflags[@]}" "$reader" "$work/ent_oracle.o" -o "$work/ent_rows"; then
    printf 'FAIL: the oracle row reader does not build\n' >&2
    return 1
  fi

  if ! ( cd "$repo" && "$runner" --ent "${corpus[@]}" ) \
      >"$work/ent.spec" 2>"$work/ent.spec.err"; then
    printf 'FAIL: the specification route'"'"'s `--ent` mode did not emit its rows\n' >&2
    cat "$work/ent.spec.err" >&2
    return 1
  fi
  if [ ! -s "$work/ent.spec" ]; then
    printf 'FAIL: the specification route'"'"'s `--ent` mode emitted no rows\n' >&2
    return 1
  fi
  if ! "$work/ent_rows" <"$work/ent.spec" >"$work/ent.oracle" \
      2>"$work/ent.oracle.err"; then
    printf 'FAIL: the oracle row reader did not read the stream\n' >&2
    cat "$work/ent.oracle.err" >&2
    return 1
  fi
  if ! cmp -s "$work/ent.spec" "$work/ent.oracle"; then
    printf 'DIFF: the specification'"'"'s word and the oracle disagree\n' >&2
    diff -u "$work/ent.oracle" "$work/ent.spec" | awk 'NR <= 40' >&2
    return 1
  fi
  local rows
  rows=$(wc -l < "$work/ent.spec")
  printf 'ok: %s row(s) agree with the oracle, word for word\n' "$rows"

  # A row per class asserts that the measured word differs from the
  # complement of the eight-byte structural set, and the count is asserted in
  # both directions -- every class row distinguishes, and there are three.
  local label qm sm im ws prev n bi s ent tailed
  local class_rows=0 distinguished=0 seed_rows=0 comp
  while read -r label qm sm im ws prev n bi s ent tailed; do
    case "$label" in
      arm:seed*:blk*) seed_rows=$((seed_rows + 1)) ;;
      class:*)
        class_rows=$((class_rows + 1))
        if ! comp=$(structural_complement "${label#class:}"); then
          printf 'SETUP: the class row %s has no block in this script\n' "$label" >&2
          return 3
        fi
        if [ "$((s))" -ne "$comp" ]; then
          distinguished=$((distinguished + 1))
        else
          printf 'FAIL: %s does not distinguish the measured word from the eight-byte structural set\n' \
            "$label" >&2
        fi
        ;;
    esac
  done < "$work/ent.oracle"

  if [ "$class_rows" -ne 3 ]; then
    printf 'FAIL: %s class row(s), 3 expected\n' "$class_rows" >&2
    return 1
  fi
  if [ "$distinguished" -ne "$class_rows" ]; then
    printf 'FAIL: %s of %s class row(s) distinguish; the count is asserted in both directions\n' \
      "$distinguished" "$class_rows" >&2
    return 1
  fi
  if [ "$seed_rows" -eq 0 ]; then
    printf 'FAIL: the fixed-seed arm emitted no row, so its seed is not printed with the result\n' >&2
    return 1
  fi
  printf 'ok: %s of %s class row(s) distinguish the measured word from the eight-byte structural set\n' \
    "$distinguished" "$class_rows"
  printf 'ok: the fixed-seed arm carries its seed in its label on %s row(s)\n' "$seed_rows"
  return 0
}

if [ "$run_text" -eq 1 ]; then arm_text || exit $?; fi
if [ "$run_rows" -eq 1 ]; then arm_rows || exit $?; fi
printf '\nok: the `ent` word'"'"'s identity holds\n'
