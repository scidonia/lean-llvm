#!/usr/bin/env bash
# Corpus check for the JSON runner.
#
#   bash tests/json/check.sh
#
# The runner reads tests/json/manifest.tsv, prints one tab-separated
# <path>\t<verdict>\t<rendering> line per row and exits 0 when every line
# agrees with the manifest.  This scenario runs the built binary twice: over
# the corpus and the repository manifest, and over a copy of the manifest with
# one accept row's expected rendering changed.  The first run must exit 0 and
# print one line per manifest row; the second must exit nonzero and say
# `mismatch:` on stderr.
#
# The binary is the artifact `probes/install/lake-locked.sh build leanllvm-json`
# builds; this scenario does not invoke `lake`, so a corpus check does not
# build or contest the certificate lock.  The tampered manifest is written in a
# private temporary directory and the corpus and repository manifest are only
# read.
#
# Exit status: 0 when the assertions hold, 1 when one fails, 3 when the fixture
# is not usable (a missing corpus or manifest without a final newline, or the
# runner binary is absent), so a setup fault is never read as an assertion
# result.
set -uo pipefail

repo=$(cd "$(dirname "$0")/../.." && pwd)
corpus=$repo/tests/json/corpus
manifest=$repo/tests/json/manifest.tsv
runner=$repo/.lake/build/bin/leanllvm-json
build_hint='nix develop -c bash probes/install/lake-locked.sh build leanllvm-json'

for path in "$corpus" "$manifest"; do
  [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done

if [ ! -x "$runner" ]; then
  printf 'SETUP: absent: %s\n  build it with: %s\n' "$runner" "$build_hint" >&2
  exit 3
fi

if [ -s "$manifest" ] && [ -n "$(tail -c 1 "$manifest")" ]; then
  echo "SETUP: the manifest's last line has no newline" >&2
  exit 3
fi
manifest_rows=$(wc -l < "$manifest")

# Every contract outcome must have a row.  A verdict the manifest never names is
# a missing case, not a silent pass: the corpus is the fixture that exercises
# the four outcomes, and the three resource outcomes are distinguishable from
# `invalid` only where a row carries them.
for verdict in accept invalid inputTooLong depthExceeded outOfCapacity; do
  if ! awk -F '\t' -v v="$verdict" '$2 == v { found = 1 } END { exit !found }' \
      "$manifest"; then
    printf 'FAIL: the manifest has no %s row\n' "$verdict" >&2
    exit 1
  fi
done

work=$(mktemp -d) || { echo "SETUP: cannot create a temporary directory" >&2; exit 3; }
trap 'rm -rf "$work"' EXIT

tampered=$work/manifest.tsv
stderr=$work/stderr
out_file=$work/out

cd "$repo" || exit 3

# Control: the unchanged manifest agrees with the runner's output, row for row.
"$runner" --corpus "$corpus" --manifest "$manifest" >"$out_file" 2>"$stderr"
status=$?
if [ "$status" -ne 0 ]; then
  printf 'FAIL: the unchanged manifest exited %s\n' "$status" >&2
  cat "$out_file" >&2
  cat "$stderr" >&2
  exit 1
fi

out_rows=$(wc -l < "$out_file")

if [ "$out_rows" -ne "$manifest_rows" ]; then
  printf 'FAIL: the runner printed %s lines for %s manifest rows\n' \
    "$out_rows" "$manifest_rows" >&2
  cat "$out_file" >&2
  exit 1
fi

# Tamper: change the first accepted row's expected rendering.  The verdict,
# the path and every other row keep their bytes, so the manifest is still
# well formed and only one expectation changes.
awk -F '\t' -v OFS='\t' '
  !done && $2 == "accept" { $3 = $3 "0"; done = 1 }
  { print }
' "$manifest" > "$tampered"

if cmp -s "$manifest" "$tampered"; then
  echo "SETUP: the manifest has no accepted row to tamper" >&2
  exit 3
fi

"$runner" --corpus "$corpus" --manifest "$tampered" >"$out_file" 2>"$stderr"
status=$?

if [ "$status" -eq 0 ]; then
  printf 'FAIL: the tampered manifest exited 0\n' >&2
  cat "$out_file" >&2
  exit 1
fi

if ! grep -q '^mismatch:' "$stderr"; then
  printf 'FAIL: the tampered run exited %s without a mismatch line\n' "$status" >&2
  cat "$stderr" >&2
  exit 1
fi

printf 'ok: the corpus agrees with the manifest; a tampered expectation is a mismatch\n'
