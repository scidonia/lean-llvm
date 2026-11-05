#!/usr/bin/env bash
# Numeric agreement for the installed depth counter.
#
#   nix develop -c bash tests/depth-count/check.sh
#
# The route has two arms that must agree, case for case, on the same index
# arrays:
#
#   * the specification — `depthSpec` in
#     `LeanLLVM/Vellum/DepthCountRefine.lean`, printed by
#     `leanllvm-depth-check` over `probes/install/depth-corpus.tsv`;
#   * the installed object — the depth unit as the installer builds it, from
#     the committed fixture `tests/v16/depth_count.ll` plus its marker, called
#     through `probes/install/depth_driver.c`, which prints the returned word
#     and both statistics words.
#
# The object's return, `stats[0]` and `stats[1]` must each be the
# specification's value for the case: the expected row `name depth sum` is
# expanded to `name depth depth sum` before comparison, so a return and a stored
# word are compared independently of one another.  Step 5's return-only defect
# exercises that separation; the same row comparison would report a wrong stored
# word with a right return, which this scenario does not separately control.
#
# What this scenario asserts, in order:
#
#   1. The installed object is exactly what a rebuild from the committed fixture
#      and marker produces, and — when the install build has published a
#      manifest — its digest and the fixture's are the manifest's.  The
#      rebuild uses the same basenames and command sequence `build.sh` and
#      `select.sh` use, so the object is the one the selector would install.
#   2. The two arms agree on every corpus case, and the row count is the
#      corpus's.
#   3. The detector bites on a tampered expectation: one expected value changed
#      by hand must be reported, naming the case, while the object's output is
#      unchanged.
#   4. The detector bites on a defect object: a depth counter that reads the
#      token buffer sequentially and ignores the index array must be reported
#      on the cases whose index arrays are not 0 .. n-1, and nowhere else.
#   5. The detector separates the returned word from the stored words: an
#      object that stores the specification's two words and returns `stats[0]+1`
#      must be reported on every case, and its stored words must be asserted to
#      be the specification's.
#
# `clang` builds the object and the driver from committed sources into a
# private temporary directory; `CC` is not consulted because the dev shell's
# `CC` is gcc, which does not compile LLVM IR.  The corpus, the fixture, the
# marker, the driver source and the Lean binary are only read.
#
# Exit status: 0 when the assertions hold, 1 when one fails, 3 when the fixture
# is not usable (an absent corpus, fixture, marker, driver or runner binary, or
# no `clang` on PATH), so a setup fault is never read as an assertion result.
set -uo pipefail

repo=$(cd "$(dirname "$0")/../.." && pwd)
corpus=$repo/probes/install/depth-corpus.tsv
fixture=$repo/tests/v16/depth_count.ll
marker=$repo/probes/install/ir/marker_depth_count.ll
driver_src=$repo/probes/install/depth_driver.c
runner=$repo/.lake/build/bin/leanllvm-depth-check
manifest=$repo/probes/install/build/manifest.env
build_hint='nix develop -c bash probes/install/lake-locked.sh build leanllvm-depth-check'
cc=clang

for path in "$corpus" "$fixture" "$marker" "$driver_src"; do
  [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done

if [ ! -x "$runner" ]; then
  printf 'SETUP: absent: %s\n  build it with: %s\n' "$runner" "$build_hint" >&2
  exit 3
fi

if ! command -v "$cc" >/dev/null 2>&1; then
  printf 'SETUP: no LLVM compiler: %s is not on PATH\n' "$cc" >&2
  printf '  run this scenario through the dev shell: nix develop -c bash tests/depth-count/check.sh\n' >&2
  exit 3
fi

if ! command -v ld >/dev/null 2>&1; then
  printf 'SETUP: no linker: ld is not on PATH\n' >&2
  printf '  run this scenario through the dev shell: nix develop -c bash tests/depth-count/check.sh\n' >&2
  exit 3
fi

work=$(mktemp -d) || { echo "SETUP: cannot create a temporary directory" >&2; exit 3; }
trap 'rm -rf "$work"' EXIT

cd "$repo" || exit 3

cases=$(awk 'NF && $0 !~ /^#/' "$corpus" | wc -l)
if [ "$cases" -le 0 ]; then
  echo 'SETUP: the corpus has no cases' >&2
  exit 3
fi

sha() { sha256sum "$1" | cut -d' ' -f1; }

# --- 1. The installed object, rebuilt by the installer's command sequence. ---
mkdir -p "$work/unit"
cp "$fixture" "$work/unit/depth_count.ll"
cp "$marker" "$work/unit/marker_depth_count.ll"
if ! (cd "$work/unit" &&
      "$cc" -c depth_count.ll -o depth_count.o 2>"$work/cc.err" &&
      "$cc" -c marker_depth_count.ll -o marker_depth_count.o 2>>"$work/cc.err" &&
      ld -r depth_count.o marker_depth_count.o -o unit.o); then
  echo 'FAIL: the committed fixture, marker or their link does not build' >&2
  cat "$work/cc.err" >&2
  exit 1
fi

fixture_sha=$(sha "$fixture")
object_sha=$(sha "$work/unit/unit.o")

if [ -f "$manifest" ] && grep -q '^depth_count_sha256=' "$manifest"; then
  manifest_object=$(sed -n 's/^depth_count_sha256=//p' "$manifest" | sed -n '1p')
  manifest_fixture=$(sed -n 's/^depth_count_fixture_sha256=//p' "$manifest" | sed -n '1p')
  if [ "$manifest_object" != "$object_sha" ]; then
    printf 'FAIL: the published manifest binds depth_count_sha256 %s, but the fixture rebuild is %s\n' \
      "$manifest_object" "$object_sha" >&2
    exit 1
  fi
  if [ "$manifest_fixture" != "$fixture_sha" ]; then
    printf 'FAIL: the published manifest binds depth_count_fixture_sha256 %s, but the fixture is %s\n' \
      "$manifest_fixture" "$fixture_sha" >&2
    exit 1
  fi
  manifest_note="the published manifest binds this object and fixture"
elif [ -f "$manifest" ]; then
  manifest_note="the published manifest predates the depth unit; rebuild it with probes/install/build.sh to bind this object"
else
  manifest_note="no published manifest"
fi

if ! "$cc" -o "$work/depth_driver" "$driver_src" "$work/unit/unit.o" \
    2>"$work/link.err"; then
  echo 'FAIL: the driver does not link against the installed depth object' >&2
  cat "$work/link.err" >&2
  exit 1
fi

# --- The two arms. --------------------------------------------------------
"$runner" "$corpus" >"$work/expected.out" 2>"$work/expected.err"
status=$?
if [ "$status" -ne 0 ]; then
  printf 'FAIL: the specification runner exited %s\n' "$status" >&2
  cat "$work/expected.err" >&2
  exit 1
fi

"$work/depth_driver" "$corpus" >"$work/object.out" 2>"$work/object.err"
status=$?
if [ "$status" -ne 0 ]; then
  printf 'FAIL: the driver exited %s over the installed object\n' "$status" >&2
  cat "$work/object.err" >&2
  exit 1
fi

# The specification prints `<name>\t<depth>\t<sum>`; the object prints
# `<name>\t<return>\t<stats[0]>\t<stats[1]>`.  The expected return and the
# expected recorded depth are the same value, which is the statement the
# kernel's refinement makes; the expansion is where a wrong recorded depth
# would show.
awk -F '\t' 'NF == 3 { print $1 "\t" $2 "\t" $2 "\t" $3 }' \
  "$work/expected.out" > "$work/expected.expanded"

expected_rows=$(wc -l < "$work/expected.expanded")
object_rows=$(wc -l < "$work/object.out")
if [ "$expected_rows" -ne "$cases" ] || [ "$object_rows" -ne "$cases" ]; then
  printf 'FAIL: %s corpus cases produced %s expected row(s) and %s object row(s)\n' \
    "$cases" "$expected_rows" "$object_rows" >&2
  exit 1
fi

# The comparison the scenario's verdict rests on.  It prints one line per case
# whose rows disagree, naming the case; an empty result means agreement.  The
# same function is used for the real comparison and for both controls, so the
# controls test this detector and not a stand-in.
compare_rows() { # expected actual
  awk -F '\t' '
    NR == FNR { expected[$1] = $0; order[++n] = $1; next }
    { actual[$1] = $0 }
    END {
      for (i = 1; i <= n; i++) {
        k = order[i]
        if (!(k in actual))
          print "mismatch: " k " is missing from the object output"
        else if (expected[k] != actual[k])
          print "mismatch: " k " expected [" expected[k] "] got [" actual[k] "]"
      }
      for (k in actual)
        if (!(k in expected))
          print "mismatch: " k " is an unexpected object row"
    }
  ' "$1" "$2"
}

mismatches=$(compare_rows "$work/expected.expanded" "$work/object.out")
if [ -n "$mismatches" ]; then
  echo 'FAIL: the installed object disagrees with depthSpec' >&2
  printf '%s\n' "$mismatches" >&2
  exit 1
fi

# --- 3. The detector bites on a tampered expectation. ---------------------
awk -F '\t' -v OFS='\t' '
  !done && $1 == "nested" { $3 = $3 + 1; done = 1 }
  { print }
' "$work/expected.expanded" > "$work/expected.tampered"

if cmp -s "$work/expected.expanded" "$work/expected.tampered"; then
  echo 'SETUP: the expected output has no nested case to tamper' >&2
  exit 3
fi

tampered=$(compare_rows "$work/expected.tampered" "$work/object.out")
if [ -z "$tampered" ]; then
  echo 'FAIL: a changed expectation was accepted' >&2
  exit 1
fi
if ! printf '%s\n' "$tampered" | grep -q '^mismatch: nested expected '; then
  echo 'FAIL: the tampered expectation was not reported by name' >&2
  printf '%s\n' "$tampered" >&2
  exit 1
fi
# The mismatch is the expectation's: a second run of the same object prints the
# same rows as the accepted run.
"$work/depth_driver" "$corpus" >"$work/object2.out" 2>"$work/object2.err"
if [ "$?" -ne 0 ] || ! cmp -s "$work/object.out" "$work/object2.out"; then
  echo 'FAIL: the object output changed during the tamper control' >&2
  cat "$work/object2.err" >&2
  exit 1
fi

# --- 4. The detector bites on a defect object. ----------------------------
cat > "$work/defect.c" <<'C'
#include <stdint.h>

/* Reads the token buffer sequentially and ignores the index array: right only
 * when the indices are 0 .. n-1, wrong on the rows whose index arrays are not
 * a prefix. */
int64_t depth_count(const unsigned char *buf, const uint32_t *idx,
                    int64_t nidx, int64_t *stats) {
  (void)idx;
  int64_t sp = 0, sum = 0;
  for (int64_t k = 0; k < nidx; k++) {
    unsigned char c = buf[k];
    int64_t delta = (c == 123 || c == 91) ? 1 : (c == 125 || c == 93) ? -1 : 0;
    sp += delta;
    sum += sp;
  }
  stats[0] = sp;
  stats[1] = sum;
  return sp;
}
C

if ! "$cc" -c "$work/defect.c" -o "$work/defect.o" 2>"$work/cc.err"; then
  echo 'FAIL: the defect object does not compile' >&2
  cat "$work/cc.err" >&2
  exit 1
fi
if ! "$cc" -o "$work/depth_driver_defect" "$driver_src" "$work/defect.o" \
    2>"$work/link.err"; then
  echo 'FAIL: the driver does not link against the defect object' >&2
  cat "$work/link.err" >&2
  exit 1
fi
"$work/depth_driver_defect" "$corpus" >"$work/defect.out" 2>"$work/defect.err"
if [ "$?" -ne 0 ]; then
  echo 'FAIL: the driver failed over the defect object' >&2
  cat "$work/defect.err" >&2
  exit 1
fi

defect=$(compare_rows "$work/expected.expanded" "$work/defect.out")
if [ -z "$defect" ]; then
  echo 'FAIL: the sequential-reader defect object passed the comparison' >&2
  exit 1
fi
# The defect differs exactly on the cases whose index arrays are not a prefix.
for case_name in shuffled revisited offset16; do
  if ! printf '%s\n' "$defect" | grep -q "^mismatch: $case_name "; then
    printf 'FAIL: the defect object was not reported on %s\n' "$case_name" >&2
    printf '%s\n' "$defect" >&2
    exit 1
  fi
done
if printf '%s\n' "$defect" | grep -Evq '^mismatch: (shuffled|revisited|offset16) '; then
  printf 'FAIL: the defect object was reported on a case whose indices are a prefix\n' >&2
  printf '%s\n' "$defect" >&2
  exit 1
fi
# The defect's disagreement with the installed object is a numeric one: its
# report is non-empty and the accepted object's was empty.
if [ -n "$mismatches" ]; then
  echo 'FAIL: the accepted comparison was not empty' >&2
  exit 1
fi

# --- 5. The detector separates the returned word from the stored words. ----
# The row comparison is exact, so a disagreement in one column is visible.  This
# object stores the specification's two words and returns one above the depth it
# stored, so every case differs and only the return column does.
cat > "$work/return_only.c" <<'C'
#include <stdint.h>

/* The fold and both stored words are the specification's; only the returned
 * word is one above the depth it stored. */
int64_t depth_count(const unsigned char *buf, const uint32_t *idx,
                    int64_t nidx, int64_t *stats) {
  int64_t sp = 0, sum = 0;
  for (int64_t k = 0; k < nidx; k++) {
    unsigned char c = buf[idx[k]];
    int64_t delta = (c == 123 || c == 91) ? 1 : (c == 125 || c == 93) ? -1 : 0;
    sp += delta;
    sum += sp;
  }
  stats[0] = sp;
  stats[1] = sum;
  return sp + 1;
}
C

if ! "$cc" -c "$work/return_only.c" -o "$work/return_only.o" 2>"$work/cc.err"; then
  echo 'FAIL: the return-only object does not compile' >&2
  cat "$work/cc.err" >&2
  exit 1
fi
if ! "$cc" -o "$work/depth_driver_return_only" "$driver_src" \
    "$work/return_only.o" 2>"$work/link.err"; then
  echo 'FAIL: the driver does not link against the return-only object' >&2
  cat "$work/link.err" >&2
  exit 1
fi
"$work/depth_driver_return_only" "$corpus" >"$work/return_only.out" \
  2>"$work/return_only.err"
if [ "$?" -ne 0 ]; then
  echo 'FAIL: the driver failed over the return-only object' >&2
  cat "$work/return_only.err" >&2
  exit 1
fi

return_only=$(compare_rows "$work/expected.expanded" "$work/return_only.out")
if [ -z "$return_only" ]; then
  echo 'FAIL: a return-only disagreement was accepted' >&2
  exit 1
fi
return_only_rows=$(printf '%s\n' "$return_only" | grep -c '^mismatch: ')
if [ "$return_only_rows" -ne "$cases" ]; then
  printf 'FAIL: the return-only object was reported on %s of %s cases\n' \
    "$return_only_rows" "$cases" >&2
  printf '%s\n' "$return_only" >&2
  exit 1
fi
# Exactly one side: both stored words are the specification's and the returned
# word is its depth plus one, on every row.
if ! awk -F '\t' '
    NR == FNR { depth[$1] = $2; total[$1] = $4; seen[$1] = 1; next }
    !($1 in seen) { print "unexpected row: " $0; bad = 1; next }
    $2 != depth[$1] + 1 || $3 != depth[$1] || $4 != total[$1] {
      print "not a return-only mismatch: " $0
      bad = 1
      next
    }
    { got[$1] = 1 }
    END {
      for (k in seen) if (!(k in got)) { print "missing row: " k; bad = 1 }
      exit bad
    }
  ' "$work/expected.expanded" "$work/return_only.out"; then
  echo 'FAIL: the return-only object did not differ only in the returned word' >&2
  exit 1
fi

# --- Report ---------------------------------------------------------------

printf 'ok: installed object %s is the rebuild of %s (%s)\n' \
  "$object_sha" "${fixture#"$repo"/}" "$manifest_note"
printf 'ok: %s corpus cases agree with depthSpec %s\n' \
  "$cases" "$(sha "$runner")"
printf 'ok: a tampered expectation is reported by name\n'
printf 'ok: the sequential-reader defect is reported on shuffled, revisited and offset16 only\n'
printf 'ok: a return-only defect is reported on every case, with both stored words correct\n'
