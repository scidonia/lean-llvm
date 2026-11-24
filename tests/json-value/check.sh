#!/usr/bin/env bash
# The value oracle: the reference parser's canonical printed value per corpus
# document, pinned and compared.
#
#   nix develop -c bash tests/json-value/check.sh
#
# The program is `tests/json-value.lean`, run over `tests/json-value/corpus`.
# For each document it prints one tab-separated row, the first five columns of
# the pinned table: the document, its verdict (`accept` or `refuse`), the
# lowercase hex of the UTF-8 bytes of `renderValue (canonValue v)` where
# `v = decodeTape (parseBytes Limits.default doc)` or `-`, the refusal class
# from `parseErrorName` or `-`, and the offset from `parseErrorOffset` or `-`.
# The rendering, the canonicalisation and the refusal vocabulary are library
# exports; the script never spells a value or a class itself, so a
# disagreement is a library rendering bug rather than a second
# implementation's.
#
# `expected.tsv` carries six tab-separated columns per document:
#
#   path  verdict  value  class  offset  sha256
#
# where the first five are the program's row and `sha256` is the document's
# digest.  Lines beginning `#` are the header and are skipped.  The check
# asserts, in order:
#
#   1. the corpus directory holds exactly the documents `expected.tsv` names,
#      one file per document at its root (no subdirectory is silently skipped);
#   2. every document's SHA-256 matches its pinned digest, and every row's
#      fields agree with its verdict;
#   3. the program's rows equal the table's first five columns;
#   4. a tampered expectation is rejected — two hex digits appended to the
#      first acceptance's value make the tampered copy differ from the
#      original, keep the pinned grammar, and fail the same comparison.  A
#      check that kept passing on a changed expectation would be comparing
#      nothing.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
corpus=${1:-"$here/corpus"}
expected="$here/expected.tsv"

cd "$repo"

# The library modules the oracle imports.  A no-op once built, and the reason a
# fresh checkout can elaborate the program without a separate `lake build`.
lake build LeanLLVM.JSON.Render LeanLLVM.Refinement.JsonEventValue \
  LeanLLVM.Refinement.JsonPipelineSpec

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
actual="$work/actual.tsv"
tampered="$work/tampered.tsv"

fail() { echo "json-value: $*" >&2; exit 1; }

# The table's document rows, header lines removed.
rows() { grep -v '^#' "$1"; }

# 1. The corpus is exactly the pinned document set, flat.
expected_docs=$(rows "$expected" | cut -f1 | sort)
found_docs=$(find "$corpus" -maxdepth 1 -type f -printf '%f\n' | sort)
if [ "$expected_docs" != "$found_docs" ]; then
  echo "json-value: corpus does not match expected.tsv" >&2
  diff -u <(printf '%s\n' "$expected_docs") <(printf '%s\n' "$found_docs") >&2 || true
  exit 1
fi

# 2. Every row's fields agree with its verdict, and every digest is the pinned
#    one.
while IFS=$'\t' read -r doc verdict value class offset digest; do
  case "$doc" in \#*|'') continue ;; esac
  [ -n "$digest" ] && [ -n "$verdict" ] || fail "malformed expected row for '$doc'"
  case "$verdict" in
    accept)
      [ -n "$value" ] && [ "$value" != '-' ] ||
        fail "'$doc': an acceptance must carry its value"
      [ "$class" = '-' ] && [ "$offset" = '-' ] ||
        fail "'$doc': an acceptance must not carry a refusal field"
      case "$value" in
        *[!0-9a-f]*) fail "'$doc': value is not lowercase hex: $value" ;;
      esac
      ;;
    refuse)
      [ "$value" = '-' ] || fail "'$doc': a refusal's value field must be '-'"
      [ -n "$class" ] && [ "$class" != '-' ] ||
        fail "'$doc': a refusal must carry its class"
      [ -n "$offset" ] || fail "'$doc': a refusal must carry its offset ('-' if none)"
      ;;
    *) fail "'$doc': unknown verdict '$verdict'" ;;
  esac
  got=$(sha256sum "$corpus/$doc" | cut -d' ' -f1)
  [ "$got" = "$digest" ] || fail "digest of '$doc': expected $digest, got $got"
done < "$expected"

# 3. The program's rows equal the table's first five columns.
lake env lean --run tests/json-value.lean "$corpus" > "$actual"
if ! diff -u <(rows "$expected" | cut -f1-5) "$actual"; then
  fail "the oracle's rows differ from expected.tsv"
fi

# 4. A tampered expectation must fail the same comparison.  Two hex digits are
#    appended to the first acceptance's value, so the tampered row keeps the
#    pinned grammar and only its asserted value changes.
awk -F'\t' 'BEGIN { OFS = "\t" }
  /^#/ { print; next }
  !done && $2 == "accept" { $3 = $3 "00"; done = 1 }
  { print }' "$expected" > "$tampered"
[ "$(rows "$expected")" != "$(rows "$tampered")" ] ||
  fail "control: the tampered copy is identical to expected.tsv"
if diff -q <(rows "$tampered" | cut -f1-5) "$actual" >/dev/null 2>&1; then
  fail "control: the comparison accepted a tampered expectation"
fi

echo "json-value: ok — $(rows "$expected" | wc -l) documents, digests match, tampered expectation rejected"
