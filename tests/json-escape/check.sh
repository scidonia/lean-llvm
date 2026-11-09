#!/usr/bin/env bash
# Route check for the stage-1 escape-position list.
#
#   nix develop -c bash tests/json-escape/check.sh
#
# The route puts one corpus under three claims.  Two derivations are compared:
#
#   * the measured emitter -- `probes/json/escape_measured.c`, compiled from
#     `kernel/json/measured/s1fuse.h` at the measured compiler line and the
#     measured `-D` set, which returns the stream the measured builder left in
#     `s1f_esc_list` and its count;
#   * the reference -- `probes/json/escape_driver.c`'s own byte scan, written
#     from the escape rule: an in-string control byte, or a backslash at an
#     even offset inside its run, is a position.
#
# A row is `<source>\t<label>\t<n>\t<count>\t<positions or ->`, with the
# positions space-separated in document order.  The corpus is the three-column
# TSV `tests/json-escape/corpus.tsv` (`label`, lowercase hex, `n`); its line
# count is its row count.
#
# What the route asserts, in order:
#
#   0. The corpus rows are the documents their labels name: the measured,
#      reference and class transcripts have one line per row and follow the
#      same labels, at least one row of each class is present, and both a
#      suppressed and a listed row are present, so neither an empty corpus nor
#      a comparison over nothing can pass.
#   1. The detector bites, sample one: a defect object built from a copy of
#      `kernel/json/measured/` whose per-document gate is forced on moves
#      exactly the rows the measured gate suppressed (measured count 0 while
#      the reference has positions) and no other row; two runs of it name the
#      same first differing row.
#   2. The detector bites, sample two: the measured transcript with one row's
#      position list changed by hand, fed back as an expectation, exits
#      nonzero and reports `mismatch:` at that row.
#   3. Clause (c): the class the driver re-derives from the document's bytes
#      (the per-document gate written from `kernel/json/measured/dens.h`)
#      equals the class the measured actor exhibits -- a list left, or none --
#      on every row.  The per-row table is printed, since this is a row-level
#      relation.
#   4. Clause (a): on every row the rule calls listed, the emitted stream's
#      count entries, in order, are the reference's tuple.
#   5. Clause (b): on every row the rule calls plain, the emitted count is
#      zero and no position is claimed.  It does not assert that a plain
#      document has no escape: the rule's backslash sample is the low 32 bytes
#      of each sampled block, so a document can carry an escape the reference
#      names and the gate still suppresses.
#
# The controls precede the clauses because they are the claim under
# observation: a failing clause must not hide whether the comparison itself is
# live.
#
# `clang` compiles committed sources into a private temporary directory; `CC`
# is not consulted because the dev shell's `CC` is gcc.  The measured tree is
# copied into that directory before the defect is made, so nothing under
# `kernel/json/measured/` is edited, and the corpus is only read.
#
# Exit status: 0 when all three clauses hold and both controls bite, 1 when a
# clause or a control fails, 3 when the route is not usable (an absent source
# or corpus, no `clang` on PATH, a compile that fails, or a transcript with
# the wrong row count), so a setup fault is never read as an assertion.
set -uo pipefail

repo=$(cd "$(dirname "$0")/../.." && pwd)
corpus=$repo/tests/json-escape/corpus.tsv
corpus_rel=tests/json-escape/corpus.tsv
probe_src=$repo/probes/json/escape_measured.c
driver_src=$repo/probes/json/escape_driver.c
measured_dir=$repo/kernel/json/measured
cc=clang

# The measured compiler line (`build49.sh:17`) and configuration (`:19-21`).
cflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)
defs=(-DSTAGE_PROBE -DS1F_ENT_PROBE=1 -DS1F_DENS=1 -DS1F_TWOPHASE=1
      -DS1F_EXP2=11 -DS1F_DISPATCH=1 -DS1F_UTF8=7 -DS1F_KL_DOC=1 -DPSTAGE=32
      -DPMODE=2 -DS1F_XS=5 -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1)

for path in "$corpus" "$probe_src" "$driver_src" "$measured_dir/s1fuse.h" \
            "$measured_dir/xlist.h" "$measured_dir/dens.h" "$measured_dir/u8kl.h"; do
  [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done

# The driver re-derives the gate's threshold from the header, which is what the
# measured build's own translation unit sees (none of `defs` sets it).
dens_plain_num=$(awk '$1 == "#define" && $2 == "DENS_PLAIN_NUM" { print $3; exit }' \
  "$measured_dir/dens.h")
case $dens_plain_num in
  ''|*[!0-9]*) echo 'SETUP: dens.h does not define DENS_PLAIN_NUM as a number' >&2
               exit 3 ;;
esac

if ! command -v "$cc" >/dev/null 2>&1; then
  printf 'SETUP: %s is not on PATH\n' "$cc" >&2
  exit 3
fi

work=$(mktemp -d) || { echo "SETUP: cannot create a temporary directory" >&2; exit 3; }
trap 'rm -rf "$work"' EXIT

cd "$repo" || exit 3

fail() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }

# --- Build the measured actor and the driver. ---

if ! "$cc" "${cflags[@]}" "${defs[@]}" -I "$measured_dir" -c "$probe_src" \
    -o "$work/probe.o" 2>"$work/probe.err"; then
  printf 'SETUP: the measured probe did not compile:\n' >&2
  sed 's/^/  /' "$work/probe.err" >&2
  exit 3
fi

if ! "$cc" -O2 -DDENS_PLAIN_NUM="$dens_plain_num" -o "$work/driver" \
    "$driver_src" "$work/probe.o" 2>"$work/driver.err"; then
  printf 'SETUP: the driver did not compile:\n' >&2
  sed 's/^/  /' "$work/driver.err" >&2
  exit 3
fi

# --- 0. All three transcripts, and the corpus's own row count. ---

if ! "$work/driver" --corpus "$corpus_rel" --measured \
    >"$work/measured.tsv" 2>"$work/measured.err"; then
  printf 'SETUP: the measured actor did not run:\n' >&2
  sed 's/^/  /' "$work/measured.err" >&2
  exit 3
fi

if ! "$work/driver" --corpus "$corpus_rel" --reference \
    >"$work/reference.tsv" 2>"$work/reference.err"; then
  printf 'SETUP: the reference did not run:\n' >&2
  sed 's/^/  /' "$work/reference.err" >&2
  exit 3
fi

if ! "$work/driver" --corpus "$corpus_rel" --class \
    >"$work/class.tsv" 2>"$work/class.err"; then
  printf 'SETUP: the class transcript did not run:\n' >&2
  sed 's/^/  /' "$work/class.err" >&2
  exit 3
fi

corpus_rows=$(wc -l < "$corpus")
measured_rows=$(wc -l < "$work/measured.tsv")
reference_rows=$(wc -l < "$work/reference.tsv")
class_rows=$(wc -l < "$work/class.tsv")
if [ "$corpus_rows" -le 0 ]; then
  echo 'SETUP: the corpus is empty' >&2
  exit 3
fi
if [ "$measured_rows" -ne "$corpus_rows" ] || \
   [ "$reference_rows" -ne "$corpus_rows" ] || \
   [ "$class_rows" -ne "$corpus_rows" ]; then
  printf 'SETUP: %s corpus row(s), %s measured, %s reference, %s class\n' \
    "$corpus_rows" "$measured_rows" "$reference_rows" "$class_rows" >&2
  exit 3
fi

# The class rows are the measured rows in the same order.
if ! awk -F '\t' 'FNR == NR { k[FNR] = $1 "/" $2; next }
                  k[FNR] != $1 "/" $2 { exit 1 }' \
    "$work/measured.tsv" "$work/class.tsv"; then
  echo 'SETUP: the class transcript does not follow the measured rows' >&2
  exit 3
fi

# Both classes must be present, or clause (c) would be a relation over one
# side only.
class_listed=$(awk -F '\t' '$3 == "listed"' "$work/class.tsv" | wc -l)
class_plain=$(awk -F '\t' '$3 == "plain"' "$work/class.tsv" | wc -l)
if [ "$class_listed" -le 0 ] || [ "$class_plain" -le 0 ]; then
  printf 'SETUP: %s listed and %s plain row(s); both classes must be present\n' \
    "$class_listed" "$class_plain" >&2
  exit 3
fi

# The two directions the comparison must distinguish: a row the measured
# actor lists and a row it suppresses.  A corpus that has only one of them
# would make the controls meaningless.
listed=$(awk -F '\t' '$4 > 0' "$work/measured.tsv" | wc -l)
suppressed=$(awk -F '\t' 'NR == FNR { m[FNR] = $4; next } m[FNR] == 0 && $4 > 0' \
  "$work/measured.tsv" "$work/reference.tsv" | wc -l)
if [ "$listed" -le 0 ] || [ "$suppressed" -le 0 ]; then
  printf 'SETUP: %s listed and %s suppressed row(s); the corpus must carry both\n' \
    "$listed" "$suppressed" >&2
  exit 3
fi

# --- 1. The detector bites: the per-document gate is forced on. ---
#
# The measured builder decides once per document whether to build the list at
# all (`s1f_xs_on`), and a PLAIN document is handed NULL.  The defect object
# is compiled from a copy of the measured tree in which that assignment is the
# constant 1; both builders' assignments are the same line and both are
# substituted.  The copy is made here, so no vendored file is edited.

mkdir -p "$work/measured" || exit 3
cp -a "$measured_dir"/. "$work/measured/" || exit 3

if ! awk '
  {
    if ($0 ~ /^[[:space:]]*s1f_xs_on = \(dens_doc_class != DENS_PLAIN\);[[:space:]]*$/) {
      sub(/s1f_xs_on = \(dens_doc_class != DENS_PLAIN\);/, "s1f_xs_on = 1;")
      n++
    }
    print
  }
  END { exit (n == 2) ? 0 : 1 }
' "$work/measured/s1fuse.h" > "$work/s1fuse.defect.h"; then
  echo 'SETUP: the gate assignment was not the two sites the defect expects' >&2
  exit 3
fi
mv "$work/s1fuse.defect.h" "$work/measured/s1fuse.h" || exit 3

if ! "$cc" "${cflags[@]}" "${defs[@]}" -I "$work/measured" -c "$probe_src" \
    -o "$work/probe.defect.o" 2>"$work/probe.defect.err"; then
  printf 'SETUP: the defect probe did not compile:\n' >&2
  sed 's/^/  /' "$work/probe.defect.err" >&2
  exit 3
fi

if ! "$cc" -O2 -DDENS_PLAIN_NUM="$dens_plain_num" -o "$work/driver_defect" \
    "$driver_src" "$work/probe.defect.o" 2>"$work/driver_defect.err"; then
  printf 'SETUP: the defect driver did not compile:\n' >&2
  sed 's/^/  /' "$work/driver_defect.err" >&2
  exit 3
fi

if ! "$work/driver_defect" --corpus "$corpus_rel" --measured \
    >"$work/defect.tsv" 2>"$work/defect.err"; then
  printf 'SETUP: the defect actor did not run:\n' >&2
  sed 's/^/  /' "$work/defect.err" >&2
  exit 3
fi

if ! "$work/driver_defect" --corpus "$corpus_rel" --measured \
    >"$work/defect2.tsv" 2>"$work/defect2.err"; then
  printf 'SETUP: the second defect run did not run:\n' >&2
  sed 's/^/  /' "$work/defect2.err" >&2
  exit 3
fi

if cmp -s "$work/measured.tsv" "$work/defect.tsv"; then
  fail 'the gate defect did not move a row, so the comparison is not live'
fi
if ! cmp -s "$work/defect.tsv" "$work/defect2.tsv"; then
  fail 'two defect runs disagree, so the first differing row is not stable'
fi

# Per row: `moved` compares the defect with the measured actor, `suppressed`
# compares the measured actor with the reference.  The defect must move exactly
# the suppressed rows.
awk 'NR == FNR { m[FNR] = $0; next }
     { print ($0 != m[FNR]) ? "moved" : "kept" }' \
  "$work/measured.tsv" "$work/defect.tsv" > "$work/defect.status"
awk 'NR == FNR { m[FNR] = $4; next }
     { print (m[FNR] == 0 && $4 > 0) ? "suppressed" : "listed" }' \
  "$work/measured.tsv" "$work/reference.tsv" > "$work/gate.status"
if ! awk 'NR == FNR { g[FNR] = $0; next }
          {
            want = (g[FNR] == "suppressed") ? "moved" : "kept"
            if ($0 != want) {
              printf "FAIL: the gate defect %s row %lu (%s), the gate %s it\n",
                     $0, FNR, g[FNR], want > "/dev/stderr"
              bad = 1
            }
          }
          END { exit bad }' "$work/gate.status" "$work/defect.status"; then
  exit 1
fi

defect_first=$(awk 'NR == FNR { m[FNR] = $0; next }
                    $0 != m[FNR] { print FNR; exit }' \
  "$work/measured.tsv" "$work/defect.tsv")
gate_first=$(awk 'NR == FNR { m[FNR] = $4; next }
                  m[FNR] == 0 && $4 > 0 { print FNR; exit }' \
  "$work/measured.tsv" "$work/reference.tsv")
if [ -z "$defect_first" ] || [ "$defect_first" != "$gate_first" ]; then
  printf 'FAIL: the gate defect'"'"'s first differing row is %s, the gate ships row %s\n' \
    "${defect_first:-none}" "${gate_first:-none}" >&2
  exit 1
fi
defect_label=$(awk -F '\t' -v n="$defect_first" 'NR == n { print $1 "/" $2 }' \
  "$work/measured.tsv")
printf 'ok: the gate defect moves exactly the %s suppressed row(s), first is %s\n' \
  "$suppressed" "$defect_label"

# --- 2. The detector bites: a tampered expectation names its row. ---

tamper_label=$(awk -F '\t' '$4 > 0 { print $2; exit }' "$work/measured.tsv")
if [ -z "$tamper_label" ]; then
  echo 'SETUP: no measured row lists a position, so nothing can be tampered' >&2
  exit 3
fi

awk -F '\t' -v OFS='\t' -v label="$tamper_label" '
  $2 == label { $5 = $5 " 999" }
  { print }' "$work/measured.tsv" > "$work/tampered.tsv"
if cmp -s "$work/measured.tsv" "$work/tampered.tsv"; then
  echo 'SETUP: the tampered expectation is unchanged' >&2
  exit 3
fi

"$work/driver" --corpus "$corpus_rel" --measured --expect "$work/tampered.tsv" \
  >"$work/tamper.out" 2>"$work/tamper.err"
status=$?
if [ "$status" -eq 0 ]; then
  fail 'a tampered expectation exited 0'
fi
if ! grep -q '^mismatch:' "$work/tamper.err"; then
  fail "a tampered expectation did not report a mismatch: $(cat "$work/tamper.err")"
fi
if ! grep -qF "mismatch: $tamper_label" "$work/tamper.err"; then
  fail "the mismatch did not name $tamper_label: $(cat "$work/tamper.err")"
fi
if ! cmp -s "$work/measured.tsv" "$work/tamper.out"; then
  fail 'the tampered run'"'"'s rows differ from the control'"'"'s'
fi
printf 'ok: a tampered expectation is a mismatch naming %s\n' "$tamper_label"

# --- 3. Clause (c): the gate's rule is a checked relation. ---
#
# `--class` prints, per row, the class re-derived from the document bytes and
# the class the measured actor exhibits.  The table is the transcript of a
# row-level relation, so it is printed in full before it is checked.

awk -F '\t' '{ printf "row: %-24s derived=%-6s exhibited=%s\n", $2, $3, $4 }' \
  "$work/class.tsv"
if ! awk -F '\t' '$3 != $4 {
      printf "FAIL: (c) %s: re-derived class %s, the actor exhibits %s\n",
             $2, $3, $4 > "/dev/stderr"
      exit 1
    }' "$work/class.tsv"; then
  exit 1
fi
printf 'ok: (c) the re-derived class and the actor'"'"'s exhibited class agree on %s row(s)\n' \
  "$corpus_rows"

# --- 4. Clause (a): the listed rows emit the reference tuple. ---

if ! awk -F '\t' -v c="$work/class.tsv" -v r="$work/reference.tsv" '
      FILENAME == c { cls[$2] = $3; next }
      FILENAME == r { rc[$2] = $4; rp[$2] = $5; next }
      cls[$2] == "listed" && ($4 != rc[$2] || $5 != rp[$2]) {
        printf "FAIL: (a) %s: emitted count %s positions [%s], reference count %s positions [%s]\n",
               $2, $4, $5, rc[$2], rp[$2] > "/dev/stderr"
        bad = 1
        if (!first) first = 1
      }
      END { exit bad }
    ' "$work/class.tsv" "$work/reference.tsv" "$work/measured.tsv"; then
  exit 1
fi
printf 'ok: (a) the emitted stream is the reference tuple on the %s listed row(s)\n' \
  "$class_listed"

# --- 5. Clause (b): the plain rows claim no position. ---

if ! awk -F '\t' -v c="$work/class.tsv" '
      FILENAME == c { cls[$2] = $3; next }
      cls[$2] == "plain" && ($4 != "0" || $5 != "-") {
        printf "FAIL: (b) %s: emitted count %s positions [%s] on a document the rule calls plain\n",
               $2, $4, $5 > "/dev/stderr"
        bad = 1
      }
      END { exit bad }
    ' "$work/class.tsv" "$work/measured.tsv"; then
  exit 1
fi
printf 'ok: (b) the actor claims no position on the %s plain row(s)\n' "$class_plain"

exit 0
