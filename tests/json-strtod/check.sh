#!/usr/bin/env bash
# The number specification's agreement with glibc's `strtod`.
#
#   nix develop -c bash tests/json-strtod/check.sh
#
# Two actors, one corpus: `oracle.c` converts each lexeme with the C library's
# `strtod` and prints the double's eight bytes as a little-endian integer;
# `check.lean` converts the same lexeme with `strtodSpec` (over the lexeme's
# decomposition) and prints the encoding's bits.  A row agrees when the two
# integers are equal, and the script fails on any row that does not.
#
# This is evidence about the specification, not a proof about the emitted body:
# the corpus is a finite set, chosen to carry the forms where a wrong reading
# shows -- the subnormal boundaries and the tie at `2 ^ -1075`, the smallest and
# largest normals, the largest finite value, the overflow midpoint `2 ^ 1024 -
# 2 ^ 970`, the exact ties `9007199254740993` and `9007199254740995`, a
# seventeen-digit decimal whose nearest is not its truncation, and negative
# zeros.
set -uo pipefail
here=$(cd "$(dirname "$0")/../.." && pwd)
cd "$here"

cc=${CC:-cc}
$cc -O2 -std=c11 -o /tmp/json-strtod-oracle tests/json-strtod/oracle.c || exit 2
/tmp/json-strtod-oracle tests/json-strtod/corpus.txt > /tmp/json-strtod-oracle.tsv || exit 2

lake build LeanLLVM.JSON.Strtod || exit 2
lake env lean tests/json-strtod/check.lean > /tmp/json-strtod-spec.tsv 2>/tmp/json-strtod-spec.err
status=$?
if [ $status -ne 0 ]; then
  echo "the specification driver failed:" >&2
  cat /tmp/json-strtod-spec.err >&2
  exit 2
fi

if diff -u /tmp/json-strtod-oracle.tsv /tmp/json-strtod-spec.tsv > /tmp/json-strtod.diff; then
  rows=$(grep -c . /tmp/json-strtod-oracle.tsv)
  echo "strtod agreement: $rows/$rows rows"
else
  echo "strtod disagreement:" >&2
  cat /tmp/json-strtod.diff >&2
  exit 1
fi
