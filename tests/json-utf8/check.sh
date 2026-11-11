#!/usr/bin/env bash
# The UTF-8 stage's route: three actors and a reference over a counted corpus,
# and the specifications tables against the vendored headers bytes.
#
#   nix develop -c bash tests/json-utf8/check.sh
#
# One command, two subjects: the stages tables (the section "the tables" below)
# and the stage itself (every section after it).  The second is the route.
#
# --- The route ------------------------------------------------------------
#
# Three actors must agree row for row, and all three must equal a scalar
# reference:
#
#   * the object — `kernel/json/utf8.c` compiled with the measured compiler line
#     and called through `probes/json/utf8_driver.c`;
#   * the Lean body — `utf8Function`, the AST
#     `LeanLLVM/Refinement/JsonUtf8IR.lean` pins to
#     `probes/install/ir/json-utf8.candidate.ll`, run by `leanllvm-json-utf8`
#     through `runFuel` under the repositorys semantics;
#   * the measured statements — `probes/json/utf8_measured.c`, which includes
#     the vendored `s1fuse.h` at the measured `-D` set and calls the measured
#     `s1f_build2`, reporting its `uerr`.
#
# The reference is `utf8_driver.c`s own scalar valid-prefix predicate, in two
# forms: over the staged window (three prefix bytes, the document, zero padding
# to the 64-byte boundary), which is the expectation on every row, and over the
# document alone, whose disagreement with the window form is asserted arm by
# arm.  The predicate is not a copy of the stage: it is a byte scan, and the
# Lean bodys expectation is the specifications relation, so the comparison is
# between derivations and not between a text and its copy.
#
# A row is one line of nine tab-separated columns:
#
#   <source> <label> <n> <gate> <path> <word> <skip> <eval> <padded>
#
# `source` is the corpus argument as given, or `arm:<arm>`; `label` is the rows
# identity inside its source; `n` is the documents length in bytes; `gate` is
# the gate value the row was run at and `path` the effective path the actor
# used, in the same letters — `g` for the gated arm (the per-block ASCII test),
# `u` for the ungated one; `word` is the stages error word, 0 accepted and 1
# rejected; `padded` is `n % 64 != 0`.  `skip` and `eval` are **derived** from
# the staged windows bytes by `probes/json/utf8_skip.h`s one function (and, on
# the Lean side, by the same rule written in Lean), never read out of the code
# under test: the two arms verdicts are equal on every document of this
# matrix, so the counts are the gates only per-document trace.
#
# Each actor is run twice, once per gate value, so one transcript is one gate
# value throughout.  The measured actors two transcripts are two builds,
# `-DDENS_U8_FORCE=0` and `=1`, each binding the constant through the measured
# `dens_pick_u8(0, 0, 0, 0)` under `#ifdef DENS_U8_FORCE` before `s1f_build2`:
# `dens_pick_u8` is otherwise reached only from `dens_probe`, which returns
# before it for `nb = 0`, so without the binding a `=1` build would report the
# gated arm on all 65,792 documents under 64 bytes.
#
# The rows.  The corpus `tests/json-utf8/corpus.tsv` is a four-column TSV with
# no header — `label`, the documents bytes as lowercase hex pairs (`-` for the
# empty document), `n`, and the expectation in the stages units — so its line
# count is its row count.  Its curated rows are derived from committed bytes and
# this script re-derives them: the six documents under `tests/json-s1-masks/corpus/`
# contribute their own first 64 bytes, the committed `tests/json/corpus/utf8-*.json`
# documents contribute every 64-byte block that carries a byte above 0x7F, the
# `tail:` rows are the truncated-lead boundary at 63, 64 and 65 bytes, the
# `flip:` rows are the pair whose difference is exactly the three staged bytes
# before the document, and `ascii:200-c3a9` is the document the gates skip
# count is about.
#
# The generated arms, enumerated by `probes/json/utf8_rows.h` on the C side and
# independently in Lean:
#
#   arm:empty   1      the empty document
#   arm:b1      256    every one-byte document
#   arm:b2      65,536 every two-byte document
#   arm:b3      486    six three-byte leads × nine continuation values × nine
#   arm:b4      5,103  seven four-byte leads × nine × nine × nine
#   arm:tail    1,671  eight suffixes at every length they fit in three layouts
#   arm:prefix  18     six documents under three values of the prefix bytes
#   arm:place   512    eight sequences at every block-boundary offset
#
# **One total, derived from the enumeration beside it.**  The arms sum to
# 1 + 256 + 65,536 + 6·9² + 7·9³ + 3·(6·70 + 69 + 68) + 6·3 + 8·64 = 73,583
# documents, and with the corpuss 27 label rows the route is 73,610 rows per
# gate value.  This script computes that total from the formula and separately
# by enumerating every rows identity, and requires the transcript to match
# both — so a missing arm or a truncated corpus cannot pass.
#
# What the route asserts, in order:
#
#   0. The fixture regenerates from `kernel/json/utf8.c` by
#      `probes/install/ir/capture-utf8.sh` and is byte-identical to the
#      committed copy; a difference is a setup failure, not an assertion.
#   1. The tables: the specifications three rows are the vendored headers
#      ninety-six bytes, and a changed byte is reported at its row and lane.
#   2. Every rows identity, `n`, `padded` and both block counts are the ones
#      this script derives from the arms rules and from the corpus file — for
#      every actor, at both gate values.  The derivation is a second
#      implementation, in `awk`, of the same rules, so a count is checked
#      against an independent derivation and not against itself.
#   3. The three actors transcripts are byte-identical at each gate value.
#   4. Every rows word is the references window form; the corpuss own
#      expectation column agrees with the reference on every curated row
#      (two derivations); the document forms disagreements are 51 on the
#      one-byte arm, 7,744 on the two-byte arm, 342 on the tail arms `raw`
#      layout and none on the three- and four-byte arms; the window form never
#      rejects where the document form accepts; the per-lead rejection counts
#      are the RFC 3629 range restrictions; every transcript carries at least
#      one accept and one reject (the liveness control, because the measured
#      code is deleted by the compiler when its input is constant).
#   5. The gate: the two gate values return the same word on all 73,053
#      documents of the counted matrix; each transcripts gate and path
#      columns are that transcripts gate letter on every row, including the
#      65,792 one- and two-byte documents; exactly two documents verdicts move
#      across the three prefix values; `ascii:200-c3a9` reports 3 skipped and 1
#      evaluated block gated and 0 and 4 ungated; and `tail:63/64/65` reports
#      the boundary — rejected, accepted, rejected.
#   6. A defect object — the compiled unit with its document-end tail term
#      removed — moves exactly the rows whose length is a multiple of 64 and
#      whose last byte is `C0`, `C1` or at least `F5`, on both gate values, and
#      two runs of it name the same first differing row.
#   7. A tampered expectation is a mismatch naming its row.
#
# `clang` builds every C side into a private temporary directory (`CC` is not
# consulted because the dev shells `CC` is gcc), and the script names the
# executable it needs (`lake build leanllvm-json-utf8`) rather than invoking
# `lake`.  The capture writes its four artefacts in place, so the committed
# bytes are copied aside and the exit trap puts them back whatever happens.
#
# Exit status: 0 when the assertions hold, 1 when one fails, 3 when a needed
# input is absent, the compiler is not on PATH, or the fixture does not
# regenerate, so a setup fault is never read as an assertion result.  The
# script takes no arguments.
set -uo pipefail

repo=$(cd "$(dirname "$0")/../.." && pwd)
header=$repo/kernel/json/measured/u8kl.h
tables_driver=$repo/probes/json/u8kl_tables.c
fixture=$repo/probes/install/ir/json-utf8.candidate.ll
capture=$repo/probes/install/ir/capture-utf8.sh
driver_src=$repo/probes/json/utf8_driver.c
measured_src=$repo/probes/json/utf8_measured.c
rows_hdr=$repo/probes/json/utf8_rows.h
skip_hdr=$repo/probes/json/utf8_skip.h
kernel_src=$repo/kernel/json/utf8.c
kernel_hdr=$repo/kernel/json/utf8.h
corpus=$repo/tests/json-utf8/corpus.tsv
corpus_rel=tests/json-utf8/corpus.tsv
runner=$repo/.lake/build/bin/leanllvm-json-utf8
build_hint='nix develop -c lake build leanllvm-json-utf8'
cc=clang

# The measured compiler line (`build49.sh:17`).
cflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)
# The UTF-8 units measured `-D` set (`build49.sh:19-21`, stage selected).
utf8_defs=(-DSTAGE_PROBE -DS1F_ENT_PROBE=1 -DS1F_DENS=1 -DS1F_TWOPHASE=1
           -DS1F_EXP2=11 -DS1F_DISPATCH=1 -DS1F_UTF8=7 -DS1F_KL_DOC=1 -DPSTAGE=32
           -DPMODE=2 -DS1F_XS=5 -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1)

for path in "$header" "$tables_driver" "$fixture" "$capture" "$driver_src" \
            "$measured_src" "$rows_hdr" "$skip_hdr" "$kernel_src" "$kernel_hdr" \
            "$corpus"; do
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
restore_fixture() {
  if [ -d "$work/fixture.committed" ]; then
    cp -a "$work/fixture.committed/." "$repo/probes/install/ir/"
  fi
}
trap 'restore_fixture; rm -rf "$work"' EXIT

cd "$repo" || exit 3

# ======================================================================
# 0. The fixture is the units emission at the pinned flags.
# ======================================================================
#
# The fixture is the theorems subject: the Lean body runs the AST
# `JsonUtf8IR` pins to it, so a fixture that is not the sources emission would
# make the comparison about a text this script compiled and nothing else.  The
# capture writes four artefacts in place, so the committed set is copied aside
# first and the exit trap restores it whatever happens.
mkdir -p "$work/fixture.committed"
cp -a probes/install/ir/json-utf8.candidate.ll \
      probes/install/ir/json-utf8.inventory \
      probes/install/ir/json-utf8.strip.tsv \
      probes/install/ir/json-utf8.rewrites.tsv "$work/fixture.committed/" \
  2>/dev/null || { echo 'SETUP: the committed fixture set is incomplete' >&2; exit 3; }

rm -f probes/install/ir/json-utf8.candidate.ll
if ! bash "$capture" >"$work/capture.out" 2>"$work/capture.err"; then
  printf 'SETUP: %s exited nonzero; the fixture did not regenerate\n' "$capture" >&2
  cat "$work/capture.err" >&2
  exit 3
fi
if [ ! -f "$fixture" ]; then
  printf 'SETUP: %s wrote no fixture at %s\n' "$capture" "$fixture" >&2
  exit 3
fi
for artefact in candidate.ll inventory strip.tsv rewrites.tsv; do
  if ! cmp -s "$work/fixture.committed/json-utf8.$artefact" \
      "probes/install/ir/json-utf8.$artefact"; then
    printf 'SETUP: the committed json-utf8.%s is not the emission at the pinned flags\n' \
      "$artefact" >&2
    diff -u "$work/fixture.committed/json-utf8.$artefact" \
      "probes/install/ir/json-utf8.$artefact" | awk 'NR <= 40' >&2
    exit 3
  fi
done

# ======================================================================
# 1. The tables are the vendored headers bytes.
# ======================================================================
# `-mavx2` is what the headers `static inline` bodies need in order to be
# parsed; none of them is called, so nothing but the three arrays is emitted.
if ! "$cc" -O2 -mavx2 -I "$repo/kernel/json/measured" -o "$work/u8kl_tables" \
    "$tables_driver" 2>"$work/cc.err"; then
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

# ======================================================================
# 2. The actors: the object, the Lean body, the measured statements.
# ======================================================================

if ! "$cc" "${cflags[@]}" -I kernel/json -c kernel/json/utf8.c \
    -o "$work/kernel.o" 2>"$work/kernel.cc.err"; then
  echo 'FAIL: the UTF-8 unit did not compile with the measured flags' >&2
  cat "$work/kernel.cc.err" >&2
  exit 1
fi

if ! "$cc" -O2 -I kernel/json -I probes/json -o "$work/driver" \
    probes/json/utf8_driver.c "$work/kernel.o" 2>"$work/driver.cc.err"; then
  echo 'FAIL: the driver did not link against the object' >&2
  cat "$work/driver.cc.err" >&2
  exit 1
fi

for force in 0 1; do
  if ! "$cc" "${cflags[@]}" "${utf8_defs[@]}" -DDENS_U8_FORCE=$force \
      -I kernel/json/measured -I probes/json -o "$work/measured$force" \
      probes/json/utf8_measured.c 2>"$work/measured$force.cc.err"; then
    printf 'FAIL: the measured actor did not build at -DDENS_U8_FORCE=%s\n' "$force" >&2
    cat "$work/measured$force.cc.err" >&2
    exit 1
  fi
done

run_actor() { # <output> <argv...>
  local out=$1
  shift
  if ! "$@" >"$out" 2>"$out.err"; then
    printf 'FAIL: %s exited nonzero\n' "$*" >&2
    cat "$out.err" >&2
    exit 1
  fi
}

run_actor "$work/object.g"  "$work/driver" --corpus "$corpus_rel" --arms --ungated 0
run_actor "$work/object.u"  "$work/driver" --corpus "$corpus_rel" --arms --ungated 1
run_actor "$work/lean.g"    "$runner" --corpus "$corpus_rel" --arms --ungated 0
run_actor "$work/lean.u"    "$runner" --corpus "$corpus_rel" --arms --ungated 1
run_actor "$work/measured.g" "$work/measured0" --corpus "$corpus_rel" --arms
run_actor "$work/measured.u" "$work/measured1" --corpus "$corpus_rel" --arms
run_actor "$work/reference" "$work/driver" --corpus "$corpus_rel" --arms --reference

# ======================================================================
# 3. The expected rows, derived from the arms' rules and the corpus file.
# ======================================================================
#
# This is a second implementation of the arm enumeration and of the block-count
# rule, in awk over the rows own bytes, so the columns the actors print are
# checked against something that is not the code they run.  Output columns:
#
#   source label n skip_gated eval_gated skip_ungated eval_ungated padded lastbyte
awk -v counts="$work/derive.counts" -v corpus_path="$corpus_rel" '
function hex2(v) { return substr("0123456789abcdef", int(v / 16) + 1, 1) substr("0123456789abcdef", v % 16 + 1, 1) }
function hexval(h,   i, v) {
  v = 0
  for (i = 1; i <= length(h); i++) {
    c = substr(h, i, 1)
    v = v * 16 + index("0123456789abcdef", c) - 1
  }
  return v
}
function rep(h, k,   s, i) { s = ""; for (i = 0; i < k; i++) s = s h; return s }
# A block is all-ASCII when every high nibble is below 8; the window pads past
# the document with zeros, and a missing character reads as "" which is below
# "8", so the last block needs no special case.
function ascii_block(hex, bi,   i, c) {
  for (i = 0; i < 64; i++) {
    c = substr(hex, 128 * bi + 2 * i + 1, 1)
    if (c >= "8") return 0
  }
  return 1
}
function emit(source, label, hex, n,   nb, bi, sg, eg, prev, ascii, lastb) {
  nb = int((n + 63) / 64)
  sg = 0; eg = 0; prev = 1
  for (bi = 0; bi < nb; bi++) {
    ascii = ascii_block(hex, bi)
    if (ascii && prev) sg++; else eg++
    prev = ascii
  }
  lastb = n > 0 ? hexval(substr(hex, 2 * n - 1, 2)) : -1
  printf "%s\t%s\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n", source, label, n,
         sg, eg, 0, nb, (n % 64 != 0), lastb
}
{ # the corpus rows, in file order
  split($0, f, "\t")
  hex = (f[2] == "-") ? "" : f[2]
  emit(corpus_path, f[1], hex, f[3] + 0)
  corpus_rows++
}
END {
  emit("arm:empty", "empty", "", 0); arm_empty = 1
  for (a = 0; a < 256; a++) {
    emit("arm:b1", hex2(a), hex2(a), 1)
  }
  arm_b1 = 256
  for (a = 0; a < 256; a++)
    for (b = 0; b < 256; b++)
      emit("arm:b2", hex2(a) hex2(b), hex2(a) hex2(b), 2)
  arm_b2 = 65536
  split("e0 e1 ec ed ee ef", l3, " ")
  for (i = 1; i <= 6; i++)
    for (x = 0; x < 9; x++)
      for (y = 0; y < 9; y++) {
        h = l3[i] cls[x + 1] cls[y + 1]
        emit("arm:b3", h, h, 3)
      }
  arm_b3 = 6 * 9 * 9
  split("f0 f1 f3 f4 f5 f7 ff", l4, " ")
  for (i = 1; i <= 7; i++)
    for (x = 0; x < 9; x++)
      for (y = 0; y < 9; y++)
        for (z = 0; z < 9; z++) {
          h = l4[i] cls[x + 1] cls[y + 1] cls[z + 1]
          emit("arm:b4", h, h, 4)
        }
  arm_b4 = 7 * 9 * 9 * 9
  split("f0:1 f090:2 f09080:3 e2:1 c3:1 c0:1 f5:1 80:1", pats, " ")
  split("raw pad pre", layouts, " ")
  n_tail = 0
  for (pi = 1; pi <= 8; pi++) {
    pname = pats[pi]; sub(/:.*/, "", pname)
    k = pats[pi]; sub(/^[^:]*:/, "", k); k = k + 0
    for (L = k; L <= 70; L++) {
      lp = int((L + 63) / 64) * 64
      for (vi = 1; vi <= 3; vi++) {
        layout = layouts[vi]
        if (layout == "raw")      { h = rep("41", L - k) pname; n = L }
        else if (layout == "pad") { h = rep("41", L - k) pname rep("41", lp - L); n = lp }
        else                      { h = rep("41", lp - k) pname; n = lp }
        emit("arm:tail", pname "/" layout "/L" L, h, n)
        n_tail++
      }
    }
  }
  arm_tail = n_tail
  split("80 a0 e08080 eda080 f4908080 c0af", pdocs, " ")
  split("zero:000000 a3:414141 f09080:f09080", ppres, " ")
  for (di = 1; di <= 6; di++)
    for (pi = 1; pi <= 3; pi++) {
      pre = ppres[pi]; sub(/^[^:]*:/, "", pre)
      prename = ppres[pi]; sub(/:.*/, "", prename)
      emit("arm:prefix", pdocs[di] "/" prename, pdocs[di], length(pdocs[di]) / 2)
    }
  arm_prefix = 6 * 3
  split("c3a9 e282ac f09f9880 f4908080 e08080 eda080 c0af 80", seqs, " ")
  for (si = 1; si <= 8; si++) {
    k = length(seqs[si]) / 2
    for (o = 0; o < 64; o++) {
      n = 64 + o
      emit("arm:place", "seq" si - 1 "/off" o, rep("41", n - k) seqs[si], n)
    }
  }
  arm_place = 8 * 64
  print "corpus " corpus_rows    > counts
  print "arm:empty " arm_empty   > counts
  print "arm:b1 " arm_b1         > counts
  print "arm:b2 " arm_b2         > counts
  print "arm:b3 " arm_b3         > counts
  print "arm:b4 " arm_b4         > counts
  print "arm:tail " arm_tail     > counts
  print "arm:prefix " arm_prefix > counts
  print "arm:place " arm_place   > counts
  close(counts)
}
BEGIN { split("7f 80 8f 90 9f a0 bf c0 ff", cls, " ") }
' "$corpus" > "$work/expected.tsv" || { echo 'SETUP: the expected-row derivation did not run' >&2; exit 3; }

expected_rows=$(wc -l < "$work/expected.tsv")

# The one total, from the formula of the enumeration above.
arm_total=$((1 + 256 + 65536 + 6*9*9 + 7*9*9*9 + 3*(6*70 + 69 + 68) + 6*3 + 8*64))
corpus_rows=$(wc -l < "$corpus")
if [ "$arm_total" -ne 73583 ]; then
  printf 'FAIL: the arms sum to %s, not 73,583\n' "$arm_total" >&2
  exit 1
fi
if [ "$expected_rows" -ne $((corpus_rows + arm_total)) ]; then
  printf 'FAIL: the enumeration has %s row(s), %s corpus + %s arm\n' \
    "$expected_rows" "$corpus_rows" "$arm_total" >&2
  exit 1
fi

# The enumerations own counts must be the formulas, arm by arm.
while read -r name count; do
  case "$name" in
    corpus) want=$corpus_rows ;;
    arm:empty) want=1 ;;
    arm:b1) want=256 ;;
    arm:b2) want=65536 ;;
    arm:b3) want=$((6*9*9)) ;;
    arm:b4) want=$((7*9*9*9)) ;;
    arm:tail) want=$((3*(6*70 + 69 + 68))) ;;
    arm:prefix) want=$((6*3)) ;;
    arm:place) want=$((8*64)) ;;
    *) printf 'FAIL: the enumeration reported an unknown arm %s\n' "$name" >&2; exit 1 ;;
  esac
  if [ "$count" -ne "$want" ]; then
    printf 'FAIL: %s enumerated %s row(s), the formula gives %s\n' \
      "$name" "$count" "$want" >&2
    exit 1
  fi
done < "$work/derive.counts"

# ======================================================================
# 4. Every actors rows are the expected rows.
# ======================================================================
#
# The comparison names the first few disagreements and fails; the word column is
# checked against the reference in section 5, so this pass is about identity,
# `n`, `padded` and the two block counts.
check_actor() { # <transcript> <gate>
  awk -F '\t' -v file="$1" -v gate="$2" '
    NR == FNR { split($0, e, "\t"); want[FNR] = $0; rows = FNR; next }
    {
      if (!(FNR <= rows)) { printf "FAIL: %s: row %d has no expected row\n", file, FNR; bad = 1; exit }
      split(want[FNR], e, "\t")
      if ($1 != e[1] || $2 != e[2] || $3 != e[3]) {
        printf "FAIL: %s: row %d is %s/%s/%s, expected %s/%s/%s\n", file, FNR,
          $1, $2, $3, e[1], e[2], e[3]
        bad = 1
      }
      if ($4 != gate) { printf "FAIL: %s: row %d gate %s, not %s\n", file, FNR, $4, gate; bad = 1 }
      if ($5 != gate) { printf "FAIL: %s: row %d path %s, not %s\n", file, FNR, $5, gate; bad = 1 }
      ws = (gate == "g") ? e[4] : e[6]
      we = (gate == "g") ? e[5] : e[7]
      if ($7 != ws || $8 != we) {
        printf "FAIL: %s: row %d counts %s/%s, expected %s/%s\n", file, FNR,
          $7, $8, ws, we
        bad = 1
      }
      if ($9 != e[8]) { printf "FAIL: %s: row %d padded %s, expected %s\n", file, FNR, $9, e[8]; bad = 1 }
      if (bad && ++shown >= 8) exit
    }
    END {
      if (FNR < rows) { printf "FAIL: %s: %d row(s), expected %d\n", file, FNR, rows; bad = 1 }
      exit bad
    }
  ' "$work/expected.tsv" "$1"
  return $?
}

check_actor "$work/object.g" g || exit 1
check_actor "$work/object.u" u || exit 1
check_actor "$work/lean.g" g || exit 1
check_actor "$work/lean.u" u || exit 1
check_actor "$work/measured.g" g || exit 1
check_actor "$work/measured.u" u || exit 1

for gate in g u; do
  reference_out=$work/object.$gate
  for other in lean measured; do
    if ! cmp -s "$reference_out" "$work/$other.$gate"; then
      printf 'FAIL: the %s actor and the object disagree at gate %s\n' "$other" "$gate" >&2
      diff -u "$reference_out" "$work/$other.$gate" | awk 'NR <= 40' >&2
      exit 1
    fi
  done
done

# ======================================================================
# 5. The reference, the splits, the per-lead counts, the gate.
# ======================================================================
#
# The reference transcript is one row per row, both gate values at once:
# `source label n <window> <document>`.

fail() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }

# 5a. The corpuss own expectation column is the references window form.
check_expectations() { # <corpus> <reference>
  local n
  n=$(wc -l < "$1")
  awk -F '\t' -v n="$n" '
    NR == FNR { want[FNR] = $4; label[FNR] = $1; next }
    FNR <= n && $4 != want[FNR] {
      printf "mismatch: %s: expectation %s, window reference %s\n", label[FNR], want[FNR], $4
      bad = 1
    }
    END { exit bad }
  ' "$1" "$2"
}
if ! check_expectations "$corpus" "$work/reference" > "$work/expect.err" 2>&1; then
  cat "$work/expect.err" >&2
  fail "the corpus's expectation column is not the reference's window form"
fi

# The tamper control: one rows expectation changed by hand must be reported at
# its own label.  The row is the first with a word of 1, so the change flips a
# verdict rather than filling an empty field.
tamper_line=$(awk -F '\t' '$4 == 1 { print NR; exit }' "$corpus")
[ -n "$tamper_line" ] || { echo 'SETUP: no corpus row rejects, so nothing can be tampered' >&2; exit 3; }
tamper_label=$(awk -F '\t' -v n="$tamper_line" 'NR == n { print $1 }' "$corpus")
awk -F '\t' -v OFS='\t' -v n="$tamper_line" '{ if (NR == n) $4 = "0" } { print }' \
  "$corpus" > "$work/corpus.tampered"
if cmp -s "$corpus" "$work/corpus.tampered"; then
  echo 'SETUP: the corpus tamper changed nothing' >&2
  exit 3
fi
if check_expectations "$work/corpus.tampered" "$work/reference" \
    > "$work/tamper.err" 2>&1; then
  fail "a tampered expectation was accepted"
fi
if ! grep -qF "mismatch: $tamper_label:" "$work/tamper.err"; then
  cat "$work/tamper.err" >&2
  fail "the tampered expectation was not reported at its own row ($tamper_label)"
fi

# 5c. The reference against the gated and ungated words, the splits, the
#     per-lead counts, and the gates coverage — one pass, by line number.
if ! awk -F '\t' '
  function fail(msg) { printf "FAIL: %s\n", msg > "/dev/stderr"; bad = 1 }
  # file 1 expected, file 2 reference, file 3 gated, file 4 ungated
  NR == FNR { split($0, e, "\t"); ex[FNR] = $0; total = FNR; next }
  FILENAME == ARGV[2] { rwin[FNR] = $4; rdoc[FNR] = $5; next }
  FILENAME == ARGV[3] { wg[FNR] = $6; next }
  FILENAME == ARGV[4] { wu[FNR] = $6; next }
  END {
    counted = 0; gate_rows = 0
    for (i = 1; i <= total; i++) {
      split(ex[i], e, "\t")
      src = e[1]; label = e[2]
      if (rwin[i] != wg[i] || rwin[i] != wu[i]) {
        fail("row " i " (" src "/" label "): word " wg[i] "/" wu[i] " is not the window reference " rwin[i])
      }
      # The document forms disagreements, arm by arm.
      split(src, a, ":")
      if (rwin[i] != rdoc[i]) {
        splitcount[a[2]]++
        if (a[2] == "tail") { split(label, t, "/"); splitcount["tail-" t[2]]++ }
      }
      if (rwin[i] == "0" && rdoc[i] == "1" && (a[2] == "empty" || a[2] == "b1" ||
          a[2] == "b2" || a[2] == "b3" || a[2] == "b4" || a[2] == "tail"))
        fail("row " i " (" src "/" label "): the window accepts where the document rejects")
      if (a[2] == "empty" || a[2] == "b1" || a[2] == "b2" || a[2] == "b3" ||
          a[2] == "b4" || a[2] == "tail") {
        counted++
        if (wg[i] != wu[i]) fail("row " i " (" src "/" label "): the gate values differ")
      }
      # Per-lead rejection counts over the three- and four-byte arms.
      if (a[2] == "b3" || a[2] == "b4") {
        lead = substr(label, 1, 2)
        leadrows[lead]++
        if (wg[i] == "1") leadrej[lead]++
      }
      # Liveness of each arms verdicts.
      acc[src] += (wg[i] == "0"); rej[src] += (wg[i] == "1")
      # The 200-byte all-ASCII document the gates counts are about.
      if (label == "ascii:200-c3a9") {
        gated_counts = e[4] "/" e[5]; ungated_counts = e[6] "/" e[7]
        gated_word = wg[i]
      }
      # The tail boundary.
      if (src == "arm:tail" && label ~ /^e2\/raw\/L6[345]$/) tailword[label] = wg[i]
    }
    if (splitcount["b1"] != 51)
      fail("the one-byte arm reports " splitcount["b1"] + 0 " document-form disagreements, not 51")
    if (splitcount["b2"] != 7744)
      fail("the two-byte arm reports " splitcount["b2"] + 0 " document-form disagreements, not 7744")
    if ((splitcount["b3"] + 0) != 0 || (splitcount["b4"] + 0) != 0 || (splitcount["empty"] + 0) != 0)
      fail("the three-byte, four-byte or empty arm has a document-form disagreement")
    if (splitcount["tail-raw"] != 342)
      fail("the tail arm'"'"'s raw layout has " splitcount["tail-raw"] + 0 " disagreements, not 342")
    if ((splitcount["tail-pad"] + 0) != 0 || (splitcount["tail-pre"] + 0) != 0)
      fail("a tail layout other than raw has a document-form disagreement")
    # The per-lead counts: the range restrictions of RFC 3629 section 4.
    split("e0:69 e1:45 ec:45 ed:57 ee:45 ef:45", t3, " ")
    for (i = 1; i <= 6; i++) {
      split(t3[i], kv, ":")
      if (leadrows[kv[1]] != 81) fail("lead " kv[1] " has " leadrows[kv[1]] + 0 " rows, not 81")
      if (leadrej[kv[1]] != kv[2])
        fail("lead " kv[1] " rejects " leadrej[kv[1]] + 0 " of 81, not " kv[2])
    }
    split("f0:585 f1:513 f3:513 f4:657 f5:729 f7:729 ff:729", t4, " ")
    for (i = 1; i <= 7; i++) {
      split(t4[i], kv, ":")
      if (leadrows[kv[1]] != 729) fail("lead " kv[1] " has " leadrows[kv[1]] + 0 " rows, not 729")
      if (leadrej[kv[1]] != kv[2])
        fail("lead " kv[1] " rejects " leadrej[kv[1]] + 0 " of 729, not " kv[2])
    }
    if (gated_counts != "3/1" || ungated_counts != "0/4")
      fail("ascii:200-c3a9 reports " gated_counts " gated and " ungated_counts " ungated, not 3/1 and 0/4")
    if (tailword["e2/raw/L63"] != 1 || tailword["e2/raw/L64"] != 0 || tailword["e2/raw/L65"] != 1)
      fail("the tail boundary is not rejected/accepted/rejected at 63/64/65")
    nacc = 0; nrej = 0
    for (s in acc) nacc += acc[s]
    for (s in rej) nrej += rej[s]
    if (nacc == 0) fail("the gated transcript has no accepting row")
    if (nrej == 0) fail("the gated transcript has no rejecting row")
    if (bad) exit 1
    printf "gate-coverage %d\n", counted > "/dev/stdout"
    printf "splits %d %d %d\n", splitcount["b1"], splitcount["b2"], splitcount["tail-raw"]
    exit 0
  }
' "$work/expected.tsv" "$work/reference" "$work/object.g" "$work/object.u" \
  > "$work/facts" 2>"$work/facts.err"; then
  cat "$work/facts.err" >&2
  exit 1
fi
# `73,071` is the counted matrix: the route's one total without the placement
# arm, which is a separate instrument for where a sequence sits inside a block.
# The gate-side coverage is that matrix without the prefix arm, because a
# non-ASCII prefix is outside the staging obligation the gate is sound under.
matrix=$((arm_total - 512))
gate_expected=$((matrix - 18))
if [ "$matrix" -ne 73071 ]; then
  fail "the counted matrix is $matrix documents, not 73,071"
fi
gate_coverage=$(awk '$1 == "gate-coverage" { print $2 }' "$work/facts")
if [ "$gate_coverage" -ne "$gate_expected" ]; then
  fail "the gate's coverage is $gate_coverage documents, not $gate_expected"
fi

# 5d. The prefix is load-bearing: exactly two documents' verdicts move across
#     the three staged values of the three bytes before them.
moved=$(awk -F '\t' '
  $1 != "arm:prefix" { next }
  {
    split($2, p, "/")
    key = p[1]
    if (!(key in first)) { first[key] = $6; count[key] = 0 }
    else if ($6 != first[key] && !(key in changed)) { changed[key] = 1; n++ }
  }
  END { print n + 0 }
' "$work/object.g")
if [ "$moved" -ne 2 ]; then
  fail "the prefix moves $moved document verdicts, not 2"
fi

# ======================================================================
# 6. The rows the corpus names are the committed bytes.
# ======================================================================
#
# The curated rows are derived from files, so this reconstructs them from those
# files and compares: the six documents own first 64 bytes, and every 64-byte
# block of the committed `utf8-*.json` documents that carries a byte above
# 0x7f.
: > "$work/corpus.derived"
for f in tests/json-s1-masks/corpus/*.json; do
  name=$(basename "$f" .json)
  hex=$(od -An -v -tx1 "$f" | tr -d ' \n')
  printf 'doc:%s/blk0\t%s\n' "$name" "$(printf '%s' "$hex" | cut -c1-128)"
done >> "$work/corpus.derived"
for f in tests/json/corpus/utf8-*.json; do
  name=$(basename "$f" .json)
  hex=$(od -An -v -tx1 "$f" | tr -d ' \n')
  bi=0
  pos=1
  while [ "$pos" -le "${#hex}" ]; do
    block=$(printf '%s' "$hex" | cut -c"$pos-$((pos + 127))")
    # A byte is above 0x7f exactly when its high nibble is 8..f, i.e. when the
    # first character of its pair is one of 89abcdef.
    above=$(printf '%s' "$block" | cut -c1-128 | fold -w2 | grep -cE '^[89abcdef]' || true)
    if [ "$above" -gt 0 ]; then
      printf 'blk:%s/blk%s\t%s\n' "$name" "$bi" "$block"
    fi
    bi=$((bi + 1))
    pos=$((pos + 128))
  done >> "$work/corpus.derived"
done

# Both sides are compared in byte order: the shell sorts its globs by the
# locale's collation, and the corpus file was written in byte order.
LC_ALL=C sort "$work/corpus.derived" > "$work/corpus.derived.sorted"
cut -f1,2 "$corpus" | grep -E '^(doc:|blk:)' | LC_ALL=C sort > "$work/corpus.claimed" || true
if ! diff -u "$work/corpus.derived.sorted" "$work/corpus.claimed" > "$work/corpus.diff"; then
  echo 'FAIL: the corpus rows are not the committed documents they name' >&2
  awk 'NR <= 40' "$work/corpus.diff" >&2
  exit 1
fi
derived_rows=$(wc -l < "$work/corpus.derived")
if [ "$derived_rows" -ne 21 ]; then
  fail "$derived_rows document row(s) derived, not 21 (six first blocks + fifteen high-byte blocks)"
fi

# ======================================================================
# 7. The defect object moves exactly the tail rules rows.
# ======================================================================
#
# The document-end rule `err |= kl_tail_byte(b[n - 1])` is the stages only
# statement about the position after the last block, so removing it moves the
# rows whose length is a multiple of 64 and whose last byte is `C0`, `C1` or at
# least `F5` — and no others.  The substitution is textual because the unit owns
# the spelling, and the number of sites it lands on is counted.
if ! awk '
  BEGIN {
    pat = "if (n && !(n & 63)) err |= (uint64_t)kl_tail_byte(b[n - 1]);"
    repl = "/* the document-end tail term is cut */"
  }
  {
    line = $0
    p = index(line, pat)
    if (p > 0) {
      hits++
      line = substr(line, 1, p - 1) repl substr(line, p + length(pat))
    }
    print line
  }
  END {
    if (hits != 1) {
      printf "SETUP: the tail-term cut applied to %d site(s), not 1\n", hits > "/dev/stderr"
      exit 3
    }
  }
' kernel/json/utf8.c > "$work/utf8.tail.c"; then
  echo 'SETUP: the tail-term cut did not apply' >&2
  exit 3
fi
if cmp -s kernel/json/utf8.c "$work/utf8.tail.c"; then
  echo 'SETUP: the tail-term cut changed nothing' >&2
  exit 3
fi

"$cc" "${cflags[@]}" -I kernel/json -c "$work/utf8.tail.c" -o "$work/kernel.tail.o" \
  2>"$work/kernel.tail.err" || {
  echo 'FAIL: the defect object did not compile' >&2
  cat "$work/kernel.tail.err" >&2
  exit 1
}
"$cc" -O2 -I kernel/json -I probes/json -o "$work/driver_tail" \
  probes/json/utf8_driver.c "$work/kernel.tail.o" 2>"$work/driver_tail.err" || {
  echo 'FAIL: the defect driver did not link' >&2
  cat "$work/driver_tail.err" >&2
  exit 1
}

for gate in g u; do
  flag=0
  [ "$gate" = u ] && flag=1
  run_actor "$work/defect.$gate" "$work/driver_tail" --corpus "$corpus_rel" --arms --ungated "$flag"
  run_actor "$work/defect.$gate.2" "$work/driver_tail" --corpus "$corpus_rel" --arms --ungated "$flag"
  if ! cmp -s "$work/defect.$gate" "$work/defect.$gate.2"; then
    fail "the defect object is not deterministic across two runs at gate $gate"
  fi
done

if ! awk -F '\t' '
  function fail(msg) { printf "FAIL: %s\n", msg > "/dev/stderr"; bad = 1 }
  NR == FNR { split($0, e, "\t"); ex[FNR] = $0; total = FNR; next }
  FILENAME == ARGV[2] { ctl[FNR] = $6; next }
  FILENAME == ARGV[3] { def[FNR] = $6; next }
  END {
    named = 0; movedrows = 0; first = 0
    for (i = 1; i <= total; i++) {
      split(ex[i], e, "\t")
      lastb = e[9] + 0
      tailhit = (e[8] == 0 && lastb >= 0 &&
                 (lastb == 192 || lastb == 193 || lastb >= 245))
      moved = (ctl[i] != def[i])
      if (tailhit) named++
      if (moved) { movedrows++; if (!first) first = i }
      if (tailhit && !moved)
        fail("the defect did not move row " i " (" e[1] "/" e[2] "), which the tail rule names")
      if (!tailhit && moved)
        fail("the defect moved row " i " (" e[1] "/" e[2] "), which the tail rule does not name")
      if (moved && ctl[i] != "1")
        fail("the defect moved row " i " (" e[1] "/" e[2] ") from " ctl[i] ", not from a rejection")
    }
    if (named == 0) fail("the tail rule names no row, so the cut has nothing to bite")
    if (movedrows != named) fail("the defect moved " movedrows " row(s), " named " named")
    if (bad) exit 1
    print first
  }
' "$work/expected.tsv" "$work/object.g" "$work/defect.g" > "$work/defect.first.g" 2>"$work/defect.g.err"; then
  cat "$work/defect.g.err" >&2
  exit 1
fi
if ! awk -F '\t' '
  function fail(msg) { printf "FAIL: %s\n", msg > "/dev/stderr"; bad = 1 }
  NR == FNR { split($0, e, "\t"); ex[FNR] = $0; total = FNR; next }
  FILENAME == ARGV[2] { ctl[FNR] = $6; next }
  FILENAME == ARGV[3] { def[FNR] = $6; next }
  END {
    named = 0; movedrows = 0; first = 0
    for (i = 1; i <= total; i++) {
      split(ex[i], e, "\t")
      lastb = e[9] + 0
      tailhit = (e[8] == 0 && lastb >= 0 &&
                 (lastb == 192 || lastb == 193 || lastb >= 245))
      moved = (ctl[i] != def[i])
      if (tailhit) named++
      if (moved) { movedrows++; if (!first) first = i }
      if (tailhit && !moved) fail("the defect did not move row " i " at the ungated gate")
      if (!tailhit && moved) fail("the defect moved row " i " at the ungated gate, which the tail rule does not name")
    }
    if (movedrows != named) fail("the ungated defect moved " movedrows " row(s), " named " named")
    if (bad) exit 1
    print first
  }
' "$work/expected.tsv" "$work/object.u" "$work/defect.u" > "$work/defect.first.u" 2>"$work/defect.u.err"; then
  cat "$work/defect.u.err" >&2
  exit 1
fi

defect_rows=$(awk -F '\t' '{ split($0, e, "\t"); lastb = e[9] + 0;
  if (e[8] == 0 && lastb >= 0 && (lastb == 192 || lastb == 193 || lastb >= 245)) n++ }
  END { print n + 0 }' "$work/expected.tsv")
first_g=$(cat "$work/defect.first.g")
first_u=$(cat "$work/defect.first.u")
if [ "$first_g" != "$first_u" ]; then
  fail "the defect's first differing row is $first_g gated and $first_u ungated"
fi
first_line=$(awk -F '\t' -v n="$first_g" 'NR == n { print $1 "/" $2 }' "$work/expected.tsv")

# ======================================================================
# Report
# ======================================================================
printf 'ok: the fixture is %s emission at the pinned flags\n' "kernel/json/utf8.c"
printf 'ok: %s is the vendored header'"'"'s %s bytes, table for table, and a changed byte is reported at its row and lane\n' \
  "${runner#"$repo"/}" "$bytes"
printf 'ok: %s row(s) per gate value = %s corpus + %s arm, each row the enumeration'"'"'s\n' \
  "$expected_rows" "$corpus_rows" "$arm_total"
printf 'ok: the object, the Lean body and the measured statements agree row for row at both gate values\n'
printf 'ok: every row'"'"'s word is the reference'"'"'s window form, and the corpus'"'"'s expectation column is the same verdict\n'
printf 'ok: the document form disagrees with the window form %s / %s / %s times on the one-, two-byte and tail arms and never elsewhere\n' \
  "$(awk '$1 == "splits" { print $2 }' "$work/facts")" \
  "$(awk '$1 == "splits" { print $3 }' "$work/facts")" \
  "$(awk '$1 == "splits" { print $4 }' "$work/facts")"
printf 'ok: the per-lead rejection counts are the RFC 3629 range restrictions over 486 + 5,103 rows\n'
printf 'ok: both gate values return the same word on %s documents, and the gate and path columns are each transcript'"'"'s gate letter\n' \
  "$gate_coverage"
printf 'ok: the three prefix values move exactly %s document verdict(s), and ascii:200-c3a9 skips 3 of 4 blocks gated and 0 ungated\n' "$moved"
printf 'ok: the tail boundary is rejected, accepted, rejected at 63, 64 and 65 bytes\n'
printf 'ok: the corpus'"'"'s %s document rows are the committed files'"'"' bytes\n' "$derived_rows"
printf 'ok: the defect object moves exactly the %s rows whose length is a multiple of 64 and whose last byte is C0, C1 or at least F5, at both gate values; first is %s\n' \
  "$defect_rows" "$first_line"
printf 'ok: a tampered expectation is a mismatch naming its row\n'
