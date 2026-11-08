#!/usr/bin/env bash
# The UTF-8 specification's tables are the vendored header's bytes.
#
#   nix develop -c bash tests/json-utf8/check.sh
#
# The stage's tables are `kl_t1`, `kl_t2` and `kl_t3`, thirty-two bytes each, and
# the claim this scenario asserts is that `LeanLLVM/Vellum/JsonUtf8Spec.lean`
# states those bytes rather than a transcription that agrees with itself.  The
# two arms are:
#
#   * the vendored header — `probes/json/u8kl_tables.c` includes
#     `kernel/json/measured/u8kl.h` and prints the three arrays the header
#     declares, so the bytes printed are the ones the header's own text fixes;
#   * the specification — `leanllvm-json-utf8 --tables` prints `klT1`, `klT2` and
#     `klT3` as `JsonUtf8Spec.lean` defines them.
#
# Both print `<name> <b00> … <b31>`, one line per table, each byte two lowercase
# hexadecimal digits, and the scenario compares the two files row for row.
#
# What the scenario asserts, in order:
#
#   1. Each arm prints three rows of thirty-two byte values, so the compared
#      surface is the 3 × 32 = 96 bytes the claim names and nothing narrower.
#   2. The rows are byte-identical, table for table.
#   3. The detector bites: one byte of the specification's first row changed by
#      hand must be reported, naming the row and the lane, while the header's
#      output is unchanged.
#
# `clang` builds the arm that includes the header into a private temporary
# directory.  No `lake` target builds the vendored file: this script names the
# executable it needs (`lake build leanllvm-json-utf8`) and compiles the header
# itself, which is what keeps `measured/PROVENANCE.md`'s "no `lake` target builds
# these files" true.
#
# Exit status: 0 when the assertions hold, 1 when one fails, 2 when this
# script's own argument handling is wrong, 3 when a needed input is absent or the
# compiler is not on PATH, so a setup fault is never read as an assertion result.
set -uo pipefail

repo=$(cd "$(dirname "$0")/../.." && pwd)
header=$repo/kernel/json/measured/u8kl.h
driver_src=$repo/probes/json/u8kl_tables.c
runner=$repo/.lake/build/bin/leanllvm-json-utf8
build_hint='nix develop -c lake build leanllvm-json-utf8'
cc=clang

for path in "$header" "$driver_src"; do
  [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done

if [ ! -x "$runner" ]; then
  printf 'SETUP: absent: %s\n  build it with: %s\n' "$runner" "$build_hint" >&2
  exit 3
fi

if ! command -v "$cc" >/dev/null 2>&1; then
  printf 'SETUP: no C compiler: %s is not on PATH\n' "$cc" >&2
  printf '  run this scenario through the dev shell: nix develop -c bash tests/json-utf8/check.sh\n' >&2
  exit 3
fi

work=$(mktemp -d) || { echo "SETUP: cannot create a temporary directory" >&2; exit 3; }
trap 'rm -rf "$work"' EXIT

cd "$repo" || exit 3

# The header's own bytes.  `-mavx2` is what the header's `static inline` bodies
# need in order to be parsed; none of them is called, so nothing but the three
# arrays is emitted.
if ! "$cc" -O2 -mavx2 -I "$repo/kernel/json/measured" -o "$work/u8kl_tables" \
    "$driver_src" 2>"$work/cc.err"; then
  echo 'FAIL: the header-reading translation unit does not build' >&2
  cat "$work/cc.err" >&2
  exit 1
fi

"$work/u8kl_tables" >"$work/header.out" 2>"$work/header.err"
status=$?
if [ "$status" -ne 0 ]; then
  printf 'FAIL: the header-reading translation unit exited %s\n' "$status" >&2
  cat "$work/header.err" >&2
  exit 1
fi

"$runner" --tables >"$work/spec.out" 2>"$work/spec.err"
status=$?
if [ "$status" -ne 0 ]; then
  printf 'FAIL: the specification runner exited %s\n' "$status" >&2
  cat "$work/spec.err" >&2
  exit 1
fi

# --- 1. Each arm prints the surface the claim names. -----------------------
for arm in header spec; do
  rows=$(wc -l < "$work/$arm.out")
  if [ "$rows" -ne 3 ]; then
    printf 'FAIL: the %s arm printed %s row(s), not 3\n' "$arm" "$rows" >&2
    exit 1
  fi
  bad_fields=$(awk 'NF != 33 { print FNR }' "$work/$arm.out")
  if [ -n "$bad_fields" ]; then
    printf 'FAIL: the %s arm printed a row that is not a name and 32 byte values (rows: %s)\n' \
      "$arm" "$bad_fields" >&2
    cat "$work/$arm.out" >&2
    exit 1
  fi
  bad_names=$(awk '$1 != "kl_t1" && $1 != "kl_t2" && $1 != "kl_t3" { print FNR }' "$work/$arm.out")
  if [ -n "$bad_names" ]; then
    printf 'FAIL: the %s arm named a table that is not kl_t1, kl_t2 or kl_t3 (rows: %s)\n' \
      "$arm" "$bad_names" >&2
    cat "$work/$arm.out" >&2
    exit 1
  fi
done

# The 96 bytes the claim is about, derived from the rows just counted rather
# than recalled: three rows of thirty-two values.
bytes=$(awk '{ n += NF - 1 } END { print n }' "$work/header.out")
if [ "$bytes" -ne 96 ]; then
  printf 'FAIL: the header arm printed %s byte value(s), not 96\n' "$bytes" >&2
  exit 1
fi

# --- 2. The two arms agree, table for table. ------------------------------
# The comparison prints one line per disagreement, naming the row and the lane.
compare_rows() { # expected actual
  awk '
    NR == FNR { for (k = 1; k <= NF; k++) want[FNR, k] = $k; name[FNR] = $1; next }
    {
      for (k = 1; k <= NF; k++)
        if (want[FNR, k] != $k)
          printf "mismatch: row %s lane %d expected %s got %s\n",
            name[FNR], k - 2, want[FNR, k], $k
    }
  ' "$1" "$2"
}

mismatches=$(compare_rows "$work/header.out" "$work/spec.out")
if [ -n "$mismatches" ]; then
  echo 'FAIL: the specification tables are not the vendored header'"'"'s bytes' >&2
  printf '%s\n' "$mismatches" >&2
  exit 1
fi

# --- 3. The detector bites on a changed specification byte. ---------------
awk 'NR == 1 { $5 = ($5 == "e7") ? "e6" : "e7" } { print }' \
  "$work/spec.out" > "$work/spec.tampered"
if cmp -s "$work/spec.out" "$work/spec.tampered"; then
  echo 'SETUP: the specification output has no first-row lane 3 to tamper' >&2
  exit 3
fi

tampered=$(compare_rows "$work/header.out" "$work/spec.tampered")
if [ -z "$tampered" ]; then
  echo 'FAIL: a changed specification byte was accepted' >&2
  exit 1
fi
if ! printf '%s\n' "$tampered" | grep -q '^mismatch: row kl_t1 lane 3 '; then
  echo 'FAIL: the changed byte was not reported at its own row and lane' >&2
  printf '%s\n' "$tampered" >&2
  exit 1
fi
# The change is the specification's: the header's output is the same as the run
# the accepted comparison used.
"$work/u8kl_tables" >"$work/header2.out" 2>"$work/header2.err"
if [ "$?" -ne 0 ] || ! cmp -s "$work/header.out" "$work/header2.out"; then
  echo 'FAIL: the header output changed during the tamper control' >&2
  cat "$work/header2.err" >&2
  exit 1
fi

# --- Report ---------------------------------------------------------------
printf 'ok: %s is the vendored header'"'"'s %s bytes, table for table\n' \
  "${runner#"$repo"/}" "$bytes"
printf 'ok: a changed specification byte is reported at its row and lane\n'
