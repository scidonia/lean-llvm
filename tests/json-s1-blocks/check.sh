#!/usr/bin/env bash
# Route check for the contracted stage-1 block unit.
#
#   nix develop -c lake build leanllvm-json-s1-blocks
#   nix develop -c bash tests/json-s1-blocks/check.sh
#
# Two actors must agree, row for row, on the same rows:
#
#   * the Lean body — `s1BlocksFunction`, the AST
#     `LeanLLVM/Refinement/JsonS1BlocksIR.lean` pins to
#     `probes/install/ir/json-s1-blocks.candidate.ll` — run by
#     `leanllvm-json-s1-blocks` under the repository's semantics, with the
#     classifier's intrinsics from `s1Calls` and `leanllvm_json_escape_list`
#     resolved to its own pinned body at `Γ_escape_positions`'s budget;
#   * the installed object — `kernel/json/s1_blocks.c` with
#     `kernel/json/escape.c` for the escape list, both compiled at the measured
#     compiler line and called through `probes/json/s1_blocks_driver.c`.
#
# Every document is padded with zeroes to a whole number of 64-byte blocks and
# staged at **offset 4** of a buffer — a misaligned pointer with the three bytes
# before it zero, the UTF-8 DFA's load-form carry.  `ent` is pre-filled with
# `0xA5`; `xp` is 64 sentinel bytes; the eight-byte count is staged at zero (the
# cursor the first escape-list call reads) and the two carry words at zero (the
# all-false carry).  A row is
#
#   <source>\t<label>\t<arm>\t<blocks>\t<touched>\t<ent words…>
#   \t<nxp>\t<xp bytes>\t<xcarry lo>\t<xcarry hi>\t<ret>
#
# with `arm` in {0, 2, 4, 6} (bit 1 the escape list, bit 2 the ungated UTF-8
# gate), one `0x`-and-sixteen-hex-digit `ent` word per block, the count, carry
# and return words the same way, the first 64 `xp` bytes as 128 lowercase hex
# digits, `touched` set when `xp`, `nxp` and `xcarry` are still the staged
# bytes, and `ret` the unit's two-bit word: bit 0 the ASCII probe (`1` when
# every document byte is below `0x80`), bit 1 the UTF-8 stage's error word (`1`
# when the staged window is not a valid prefix).  The label carries the
# document's length as `len<n>`, which is what makes a moved row's block
# boundary checkable from the row itself.  `ret` is last so the `ent` words
# stay the first `0x` fields of the row.
#
# The object is compiled from the kernel source rather than from the fixture,
# as in `tests/json-s1-masks/check.sh`: the fixture's loads carry no alignment
# operand, so an object built from it would inherit the type's ABI alignment
# and the offset-1 staging would not be reachable.  In the same run the fixture
# — and the three inventories the capture writes beside it — is regenerated
# from that same source at the pinned flags and compared with the committed
# bytes; a difference is a setup failure (exit 3), not an assertion failure.
#
# What this scenario asserts, in order:
#
#   0. Both actors' `--emit-block` output is the same 64 bytes, so the mixed
#      block the two row streams share is one block and not two copies.
#   1. The Lean body classifies every row and the row count is exactly the
#      computed count: (1 mixed + corpus files + 64*256 byte + 65 short +
#      8^4 alphabet + 512 random) documents, each once per arm.  Every row's
#      field count, block count and `len<n>` label agree; the four arms are
#      `0, 2, 4, 6` in that order for one document; the three boundary corpus
#      files are asserted by name (63 → 1, 64 → 1, 65 → 2 blocks).  Every
#      list-free row (arms 0 and 4) is `touched = 1`, and the mixed list rows
#      (arms 2 and 6) are `touched = 0` with a nonzero count, so the sentinel
#      detector has an affirmative control in the same run.  Every row's `ret`
#      word is in `0…3`.
#   1b. The ASCII probe is the document's own high bits, not a rehearsal: the
#      driver's `--ascii-expected` mode recomputes `all b < 0x80` from the
#      staged bytes of the same documents, and every row's bit 0 must agree
#      with that computed value on all four arms.  The expectation stream must
#      carry both answers, so the comparison has an affirmative control;
#      `escapes.json` (control bytes, still ASCII) is asserted `1` and
#      `utf8.json` (UTF-8 bytes) `0`, each computed from the file's bytes by a
#      separate `od` reader, not from a list.
#   1c. The UTF-8 error bit is the window's own validity, read by a scalar
#      reference validator that shares no code with the object: the driver's
#      `--utf8-expected` mode walks the three zero bytes, the document and the
#      zero padding with a scalar UTF-8 prefix reader, and every row's bit 1
#      must agree on all four arms.  The gate's two modes have the same verdict
#      by construction, so the four arms are also a gate-invariance check.
#   2. The object's rows equal the Lean body's rows line for line, in order,
#      on all four arms — the `ret` column included, so the two actors' ASCII
#      probes and UTF-8 verdicts are the same columns.
#   3. The detector bites: a defect object built from a copy of the kernel
#      whose peeled-tail clamp also sets lane `rem` — the one lane past the
#      document's end — disagrees with the control on exactly the rows whose
#      document does not end on a block boundary (`64 * blocks != length`),
#      and on no other row; the report names the first differing row and two
#      runs of the defect name the same row.  The recommended flip to
#      `~(1ULL << rem)` is not used: on a document that ends inside a string,
#      or whose last scalar run reaches the padding, both masks clear every
#      lane the body set, so that flip leaves rows unmoved and cannot be
#      asserted as "all partial documents".  Setting lane `rem` is the same
#      clamp defect (the out-of-document lane survives) and is visible on every
#      partial document, whatever the body set below `rem`.
#   4. The tampered expectation: one `ent` word of the Lean stream changed by
#      hand, fed back to the runner as its expectation, exits nonzero, says
#      `mismatch:` on stderr, names the row, and prints the same rows as the
#      control, so the disagreement is the expectation's and not the body's.
#
# The runner is the artifact `lake build leanllvm-json-s1-blocks` produces;
# this script does not invoke `lake`.  `clang` compiles committed sources into a
# private temporary directory; `CC` is not consulted because the dev shell's
# `CC` is gcc.  The corpus, the fixture, the capture script and the driver
# source are only read — the fixture and the three inventories are replaced and
# restored around the regeneration comparison, and the script's exit trap puts
# the committed bytes back whatever happens.
#
# Exit status: 0 when the assertions hold, 1 when one fails, 3 when the route is
# not usable (an absent corpus, fixture, capture script, driver or kernel
# source, an absent runner binary, no `clang` on PATH, or a capture that does
# not reproduce the committed artefacts), so a setup fault is never read as an
# assertion result.
set -uo pipefail

repo=$(cd "$(dirname "$0")/../.." && pwd)
corpus=$repo/tests/json-s1-blocks/corpus
fixture=$repo/probes/install/ir/json-s1-blocks.candidate.ll
strip=$repo/probes/install/ir/json-s1-blocks.strip.tsv
rewrites=$repo/probes/install/ir/json-s1-blocks.rewrites.tsv
inventory=$repo/probes/install/ir/json-s1-blocks.inventory
capture=$repo/probes/install/ir/capture-s1-blocks.sh
driver_src=$repo/probes/json/s1_blocks_driver.c
kernel_src=$repo/kernel/json/s1_blocks.c
escape_src=$repo/kernel/json/escape.c
runner=$repo/.lake/build/bin/leanllvm-json-s1-blocks
build_hint='nix develop -c lake build leanllvm-json-s1-blocks'
cc=clang

# The measured compiler line (`build49.sh:17`).
cflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)

for path in "$corpus" "$fixture" "$strip" "$rewrites" "$inventory" "$capture" \
            "$driver_src" "$kernel_src" "$escape_src"; do
  [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done

if [ ! -x "$runner" ]; then
  printf 'SETUP: absent runner: %s\n' "$runner" >&2
  printf 'SETUP: build it with: %s\n' "$build_hint" >&2
  exit 3
fi

if ! command -v "$cc" >/dev/null 2>&1; then
  printf 'SETUP: no %s on PATH, and the kernel is C\n' "$cc" >&2
  exit 3
fi

work=$(mktemp -d) || { echo "SETUP: cannot create a temporary directory" >&2; exit 3; }
restore_capture() {
  for name in candidate.ll strip.tsv rewrites.tsv inventory; do
    if [ -f "$work/json-s1-blocks.$name" ]; then
      cp "$work/json-s1-blocks.$name" "$repo/probes/install/ir/json-s1-blocks.$name"
    fi
  done
}
trap 'restore_capture; rm -rf "$work"' EXIT

cd "$repo" || exit 3

mapfile -t corpus_files < <(find "$corpus" -mindepth 1 -maxdepth 1 -type f | LC_ALL=C sort)
if [ "${#corpus_files[@]}" -eq 0 ]; then
  printf 'SETUP: no corpus files under %s\n' "$corpus" >&2
  exit 3
fi

corpus_args=()
for f in "${corpus_files[@]}"; do
  corpus_args+=(--corpus "$f")
done

# --- The object, compiled once with the measured line. ---

if ! "$cc" "${cflags[@]}" -I "$repo/kernel/json" -c "$kernel_src" \
    -o "$work/s1_blocks.o" 2>"$work/cc.err"; then
  printf 'FAIL: the block unit did not compile with the measured flags\n' >&2
  cat "$work/cc.err" >&2
  exit 1
fi

if ! "$cc" "${cflags[@]}" -I "$repo/kernel/json" -c "$escape_src" \
    -o "$work/escape.o" 2>"$work/cc.err"; then
  printf 'FAIL: the escape list did not compile with the measured flags\n' >&2
  cat "$work/cc.err" >&2
  exit 1
fi

if ! "$cc" -O2 -o "$work/driver" "$driver_src" "$work/s1_blocks.o" "$work/escape.o" \
    2>"$work/link.err"; then
  printf 'FAIL: the driver did not link against the kernel objects\n' >&2
  cat "$work/link.err" >&2
  exit 1
fi

# --- The fixture is the kernel source's emission at the same flags. ---
#
# The capture writes the fixture and its three inventories in place, so the
# committed bytes are copied aside, the files are removed, and the exit trap
# restores the copies whatever the outcome.  A capture that writes nothing, or
# writes different bytes, is a setup fault: the theorem's subject would not be
# the code the object arm ran.

for name in candidate.ll strip.tsv rewrites.tsv inventory; do
  cp "$repo/probes/install/ir/json-s1-blocks.$name" "$work/json-s1-blocks.$name"
  rm -f "$repo/probes/install/ir/json-s1-blocks.$name"
done

if ! bash "$capture" >"$work/capture.out" 2>"$work/capture.err"; then
  printf 'SETUP: %s exited nonzero; the fixture did not regenerate\n' "$capture" >&2
  cat "$work/capture.err" >&2
  exit 3
fi

for path in "$fixture" "$strip" "$rewrites" "$inventory"; do
  if [ ! -f "$path" ]; then
    printf 'SETUP: %s wrote no fixture at %s\n' "$capture" "$path" >&2
    exit 3
  fi
done

for name in candidate.ll strip.tsv rewrites.tsv inventory; do
  if ! cmp -s "$work/json-s1-blocks.$name" \
      "$repo/probes/install/ir/json-s1-blocks.$name"; then
    printf 'SETUP: the committed json-s1-blocks.%s is not the kernel source emission at the pinned flags\n' \
      "$name" >&2
    diff -u "$work/json-s1-blocks.$name" \
      "$repo/probes/install/ir/json-s1-blocks.$name" | awk 'NR <= 40' >&2
    exit 3
  fi
done

# --- 0. The mixed block is one block: both actors emit the same 64 bytes. ---

if ! "$runner" --emit-block >"$work/runner.block" 2>"$work/runner.err"; then
  printf 'FAIL: the runner could not emit the mixed block\n' >&2
  cat "$work/runner.err" >&2
  exit 1
fi

if ! "$work/driver" --emit-block >"$work/driver.block" 2>"$work/driver.err"; then
  printf 'FAIL: the driver could not emit the mixed block\n' >&2
  cat "$work/driver.err" >&2
  exit 1
fi

if ! cmp -s "$work/runner.block" "$work/driver.block"; then
  printf 'FAIL: the two actors stage different mixed blocks\n' >&2
  exit 1
fi

mixed_size=$(wc -c < "$work/runner.block")
if [ "$mixed_size" -ne 64 ]; then
  printf 'FAIL: the mixed block is %s bytes, not 64\n' "$mixed_size" >&2
  exit 1
fi

# --- 1. The Lean body classifies every row, and the count is computed. ---

if ! "$runner" "${corpus_args[@]}" --arms >"$work/lean.out" 2>"$work/lean.err"; then
  printf 'FAIL: the Lean body did not classify every row\n' >&2
  cat "$work/lean.err" >&2
  exit 1
fi

byte_docs=$((64 * 256))
short_docs=65
alphabet_docs=$((8 * 8 * 8 * 8))
random_docs=512
docs=$((1 + ${#corpus_files[@]} + byte_docs + short_docs + alphabet_docs + random_docs))
computed=$((4 * docs))

rows=$(wc -l < "$work/lean.out")
if [ "$rows" -ne "$computed" ]; then
  printf 'FAIL: %s row(s) printed, %s computed\n' "$rows" "$computed" >&2
  exit 1
fi

# Every row: its label names a length, its block count and field count follow
# from it, its arm is one of the two, and its words have the documented shape.
if ! awk -F '\t' '
  function len_of(s,   m) {
    if (match(s, /len[0-9]+/) == 0) return -1
    return substr(s, RSTART + 3, RLENGTH - 3) + 0
  }
  function word(x) { return length(x) == 18 && x ~ /^0x[0-9a-f]+$/ }
  function hexbytes(x) { return length(x) == 128 && x ~ /^[0-9a-f]+$/ }
  {
    len = len_of($2)
    if (len < 0) { printf "FAIL: no len<n> in label %s on row %d\n", $2, NR > "/dev/stderr"; bad = 1; exit }
    blocks = int((len + 63) / 64)
    if (blocks < 1) { printf "FAIL: row %d has no block\n", NR > "/dev/stderr"; bad = 1; exit }
    if ($4 + 0 != blocks) { printf "FAIL: row %d says %s block(s), len%d needs %d\n", NR, $4, len, blocks > "/dev/stderr"; bad = 1; exit }
    if (NF != 10 + blocks) { printf "FAIL: row %d has %d field(s), len%d needs %d\n", NR, NF, len, 10 + blocks > "/dev/stderr"; bad = 1; exit }
    if ($3 != 0 && $3 != 2 && $3 != 4 && $3 != 6) {
      printf "FAIL: row %d has arm %s\n", NR, $3 > "/dev/stderr"; bad = 1; exit
    }
    if ($5 != 0 && $5 != 1) { printf "FAIL: row %d has touched %s\n", NR, $5 > "/dev/stderr"; bad = 1; exit }
    for (i = 6; i <= 5 + blocks; i++)
      if (!word($i)) { printf "FAIL: row %d ent word %s\n", NR, $i > "/dev/stderr"; bad = 1; exit }
    if (!word($(6 + blocks))) { printf "FAIL: row %d nxp word %s\n", NR, $(6 + blocks) > "/dev/stderr"; bad = 1; exit }
    if (!hexbytes($(7 + blocks))) { printf "FAIL: row %d xp bytes are not 64 bytes of hex\n", NR > "/dev/stderr"; bad = 1; exit }
    if (!word($(8 + blocks)) || !word($(9 + blocks))) {
      printf "FAIL: row %d carry words\n", NR > "/dev/stderr"; bad = 1; exit
    }
    if (!word($(10 + blocks)) || ($(10 + blocks) != "0x0000000000000000" && \
        $(10 + blocks) != "0x0000000000000001" && \
        $(10 + blocks) != "0x0000000000000002" && \
        $(10 + blocks) != "0x0000000000000003")) {
      printf "FAIL: row %d ret word %s\n", NR, $(10 + blocks) > "/dev/stderr"; bad = 1; exit
    }
    if (NR % 4 == 1) {
      if ($3 != 0) { printf "FAIL: row %d is not the gated list-free arm\n", NR > "/dev/stderr"; bad = 1; exit }
      prev_source = $1; prev_label = $2
    } else {
      want = (NR % 4 == 2) ? 2 : ((NR % 4 == 3) ? 4 : 6)
      if ($3 != want) { printf "FAIL: row %d has arm %s, want %s\n", NR, $3, want > "/dev/stderr"; bad = 1; exit }
      if ($1 != prev_source || $2 != prev_label) {
        printf "FAIL: row %d does not group with row %d\n", NR, NR - (NR % 4) + 1 > "/dev/stderr"; bad = 1; exit
      }
    }
  }
  END { exit bad }
' "$work/lean.out"; then
  exit 1
fi

# The three boundary files, read against their names as a second, independent
# reading of the same arithmetic.
for spec in boundary-63.json:1 boundary-64.json:1 boundary-65.json:2; do
  name=${spec%%:*}
  want=${spec##*:}
  size=$(wc -c < "$corpus/$name") || { printf 'SETUP: absent %s\n' "$name" >&2; exit 3; }
  got=$(((size + 63) / 64))
  if [ "$got" -ne "$want" ]; then
    printf 'FAIL: %s is %s bytes, giving %s block(s), not %s\n' \
      "$name" "$size" "$got" "$want" >&2
    exit 1
  fi
done

# The list-free arms must leave the staged regions untouched; the mixed list
# rows are the affirmative control, so `touched` is not a column that reads 1
# forever.
gateoff_rows=$(awk -F '\t' '$3 == 0 || $3 == 4' "$work/lean.out" | wc -l)
if [ "$gateoff_rows" -ne "$((rows / 2))" ]; then
  printf 'FAIL: %s list-free row(s) among %s\n' "$gateoff_rows" "$rows" >&2
  exit 1
fi

if ! awk -F '\t' '
  ($3 == 0 || $3 == 4) && $5 != 1 { printf "FAIL: a list-free row moved: %s\n", $2 > "/dev/stderr"; bad = 1 }
  ($3 == 2 || $3 == 6) && $5 == 0 { moved++ }
  (NR == 2 || NR == 4) {
    if ($5 != 0) { printf "FAIL: the mixed list row %d is untouched\n", NR > "/dev/stderr"; bad = 1 }
    if ($(6 + $4) == "0x0000000000000000") {
      printf "FAIL: the mixed list row %d reports no position\n", NR > "/dev/stderr"; bad = 1
    }
  }
  END {
    if (moved <= 0) { printf "FAIL: no list row moved\n" > "/dev/stderr"; bad = 1 }
    exit bad
  }
' "$work/lean.out"; then
  exit 1
fi
gateon_moved=$(awk -F '\t' '($3 == 2 || $3 == 6) && $5 == 0' "$work/lean.out" | wc -l)

# --- 1b. The return word is the document's own ASCII probe. ---
#
# The expectation is recomputed from the staged document bytes, not read off a
# list: `--ascii-expected` prints `all b < 0x80` for the same documents in the
# same order.  Both answers must occur, or the comparison says nothing.

if ! "$work/driver" "${corpus_args[@]}" --arms --ascii-expected \
    >"$work/ascii.out" 2>"$work/ascii.err"; then
  printf 'FAIL: the driver could not compute the expected ASCII probe\n' >&2
  cat "$work/ascii.err" >&2
  exit 1
fi

ascii_docs=$(wc -l < "$work/ascii.out")
if [ "$ascii_docs" -ne "$docs" ]; then
  printf 'FAIL: %s expected-ASCII row(s), %s document(s)\n' "$ascii_docs" "$docs" >&2
  exit 1
fi

if ! awk -F '\t' '
  NR == FNR {
    key = $1 "\t" $2
    if (key in expectv) { printf "FAIL: duplicate expectation for %s\n", key > "/dev/stderr"; bad = 1 }
    if ($3 != 0 && $3 != 1) { printf "FAIL: expectation %s is %s\n", key, $3 > "/dev/stderr"; bad = 1 }
    expectv[key] = $3
    n++
    ones += $3
    zeros += (1 - $3)
    next
  }
  {
    key = $1 "\t" $2
    if (!(key in expectv)) { printf "FAIL: no expectation for %s\n", key > "/dev/stderr"; bad = 1; next }
    ret = $(10 + $4)
    if (expectv[key] == 1) {
      if (ret != "0x0000000000000001") {
        printf "FAIL: row %d (%s) returns %s, the document is all-ASCII\n", FNR, key, ret > "/dev/stderr"
        bad = 1
      }
    } else if (ret != "0x0000000000000000" && ret != "0x0000000000000002") {
      printf "FAIL: row %d (%s) returns %s, the document is not all-ASCII\n", FNR, key, ret > "/dev/stderr"
      bad = 1
    }
  }
  END {
    if (ones <= 0) { printf "FAIL: no document is all-ASCII, so return 1 is unexercised\n" > "/dev/stderr"; bad = 1 }
    if (zeros <= 0) { printf "FAIL: no document has a high byte, so return 0 is unexercised\n" > "/dev/stderr"; bad = 1 }
    exit bad
  }
' "$work/ascii.out" "$work/lean.out"; then
  exit 1
fi

# The two named corpus documents, read by a separate `od` byte reader: the
# escape/control file is still ASCII, the UTF-8 file is not.
ascii_of() {
  od -An -tu1 "$1" | awk '{ for (i = 1; i <= NF; i++) if ($i >= 128) high = 1 } END { print high ? 0 : 1 }'
}
escapes_ascii=$(ascii_of "$corpus/escapes.json")
utf8_ascii=$(ascii_of "$corpus/utf8.json")
if [ "$escapes_ascii" -ne 1 ] || [ "$utf8_ascii" -ne 0 ]; then
  printf 'SETUP: corpus ASCII readings are %s and %s; expected 1 and 0\n' \
    "$escapes_ascii" "$utf8_ascii" >&2
  exit 3
fi

if ! awk -v e="$escapes_ascii" -v u="$utf8_ascii" -F '\t' '
  $1 ~ /escapes\.json$/ { se++; if ($3 + 0 != e) { printf "FAIL: escapes.json probe %s\n", $3 > "/dev/stderr"; bad = 1 } }
  $1 ~ /utf8\.json$/ { su++; if ($3 + 0 != u) { printf "FAIL: utf8.json probe %s\n", $3 > "/dev/stderr"; bad = 1 } }
  END {
    if (se != 1 || su != 1) { printf "FAIL: named corpus rows %d and %d\n", se, su > "/dev/stderr"; bad = 1 }
    exit bad
  }
' "$work/ascii.out"; then
  exit 1
fi

# --- 1c. The UTF-8 error bit is the window's own validity. ---
#
# The expectation is a scalar reference reader of the staged window — three
# zero bytes, the document, zero padding — that shares no code with the object.
# `--utf8-expected` prints `1` when that reader rejects the window.  An invalid
# window is never all-ASCII, so its row's word must be exactly `2`; a valid one
# is `0` or `1`.

if ! "$work/driver" "${corpus_args[@]}" --arms --utf8-expected \
    >"$work/utf8.out" 2>"$work/utf8.err"; then
  printf 'FAIL: the driver could not compute the expected UTF-8 word\n' >&2
  cat "$work/utf8.err" >&2
  exit 1
fi

utf8_docs=$(wc -l < "$work/utf8.out")
if [ "$utf8_docs" -ne "$docs" ]; then
  printf 'FAIL: %s expected-UTF-8 row(s), %s document(s)\n' "$utf8_docs" "$docs" >&2
  exit 1
fi

if ! awk -F '\t' '
  NR == FNR {
    key = $1 "\t" $2
    if (key in expectv) { printf "FAIL: duplicate UTF-8 expectation for %s\n", key > "/dev/stderr"; bad = 1 }
    if ($3 != 0 && $3 != 1) { printf "FAIL: UTF-8 expectation %s is %s\n", key, $3 > "/dev/stderr"; bad = 1 }
    expectv[key] = $3
    ones += $3
    zeros += (1 - $3)
    next
  }
  {
    key = $1 "\t" $2
    if (!(key in expectv)) { printf "FAIL: no UTF-8 expectation for %s\n", key > "/dev/stderr"; bad = 1; next }
    ret = $(10 + $4)
    if (expectv[key] == 1) {
      if (ret != "0x0000000000000002") {
        printf "FAIL: row %d (%s) returns %s, the window is not a valid prefix\n", FNR, key, ret > "/dev/stderr"
        bad = 1
      }
    } else if (ret != "0x0000000000000000" && ret != "0x0000000000000001") {
      printf "FAIL: row %d (%s) returns %s, the window is a valid prefix\n", FNR, key, ret > "/dev/stderr"
      bad = 1
    }
  }
  END {
    if (ones <= 0) { printf "FAIL: no invalid UTF-8 window, so error bit 1 is unexercised\n" > "/dev/stderr"; bad = 1 }
    if (zeros <= 0) { printf "FAIL: no valid UTF-8 window, so error bit 0 is unexercised\n" > "/dev/stderr"; bad = 1 }
    exit bad
  }
' "$work/utf8.out" "$work/lean.out"; then
  exit 1
fi

# The two gate modes must answer the same word: a group of four rows differs
# only in arm bits 1 and 2, and the verdict is not either of them.
if ! awk -F '\t' '
  NR % 4 == 1 { want = $(10 + $4); key = $1 "\t" $2; next }
  $(10 + $4) != want {
    printf "FAIL: the gate changed the word for %s: %s against %s\n", key, $(10 + $4), want > "/dev/stderr"
    bad = 1
  }
  END { exit bad }
' "$work/lean.out"; then
  exit 1
fi

# The named corpus documents, read by the reference stream's own rows: the
# UTF-8 file holds valid multi-byte sequences and the escape/control file is
# ASCII, so both windows are valid prefixes.  The invalid case is exercised by
# the generated stream, whose `ones > 0` above requires it.
if ! awk -F '\t' '
  $1 ~ /utf8\.json$/ { u++; if ($3 + 0 != 0) { printf "FAIL: utf8.json expected word %s\n", $3 > "/dev/stderr"; bad = 1 } }
  $1 ~ /escapes\.json$/ { e++; if ($3 + 0 != 0) { printf "FAIL: escapes.json expected word %s\n", $3 > "/dev/stderr"; bad = 1 } }
  END {
    if (u != 1 || e != 1) { printf "FAIL: named UTF-8 corpus rows %d and %d\n", u, e > "/dev/stderr"; bad = 1 }
    exit bad
  }
' "$work/utf8.out"; then
  exit 1
fi

# --- 2. The object's rows equal the Lean body's rows. ---

if ! "$work/driver" "${corpus_args[@]}" --arms >"$work/object.out" 2>"$work/object.err"; then
  printf 'FAIL: the object did not produce every row\n' >&2
  cat "$work/object.err" >&2
  exit 1
fi

if ! cmp -s "$work/lean.out" "$work/object.out"; then
  printf 'FAIL: the object and the Lean body disagree\n' >&2
  diff -u "$work/lean.out" "$work/object.out" | awk 'NR <= 40' >&2
  exit 1
fi

kernel_sha=$(sha256sum "$work/s1_blocks.o" | cut -d' ' -f1)

# --- 3. The detector bites: the peeled-tail clamp also sets lane `rem`. ---
#
# The substitution is textual because the kernel source owns the clamp's
# spelling; a source without that statement is a failed mutation, not a silent
# pass.  The number of substitutions that land is counted and must be one, so
# "changed nothing" and "changed more than the tail" both fail here.
needle='ent[nfull] = e & ((1ULL << rem) - 1ULL);'
repl='ent[nfull] = (e & ((1ULL << rem) - 1ULL)) | (1ULL << rem);'
if ! awk -v needle="$needle" -v repl="$repl" '
  { line = $0; out = ""
    while ((p = index(line, needle)) > 0) {
      out = out substr(line, 1, p - 1) repl
      line = substr(line, p + length(needle))
      n++
    }
    print out line }
  END { if (n != 1) { printf "the clamp substitution landed %d time(s)\n", n > "/dev/stderr"; exit 3 } }
' "$kernel_src" > "$work/s1_blocks.defect.c"; then
  printf 'SETUP: the clamp mutation did not apply\n' >&2
  exit 3
fi

if cmp -s "$kernel_src" "$work/s1_blocks.defect.c"; then
  printf 'SETUP: the clamp mutation changed nothing\n' >&2
  exit 3
fi

if ! "$cc" "${cflags[@]}" -I "$repo/kernel/json" -c "$work/s1_blocks.defect.c" \
    -o "$work/s1_blocks.defect.o" 2>"$work/cc.err"; then
  printf 'FAIL: the defect kernel did not compile\n' >&2
  cat "$work/cc.err" >&2
  exit 1
fi

if ! "$cc" -O2 -o "$work/driver_defect" "$driver_src" \
    "$work/s1_blocks.defect.o" "$work/escape.o" 2>"$work/link.err"; then
  printf 'FAIL: the defect driver did not link\n' >&2
  cat "$work/link.err" >&2
  exit 1
fi

if ! "$work/driver_defect" "${corpus_args[@]}" --arms >"$work/defect.out" \
    2>"$work/defect.err"; then
  printf 'FAIL: the defect object did not produce every row\n' >&2
  cat "$work/defect.err" >&2
  exit 1
fi

defect_rows=$(wc -l < "$work/defect.out")
if [ "$defect_rows" -ne "$rows" ]; then
  printf 'FAIL: the defect printed %s row(s), the control %s\n' "$defect_rows" "$rows" >&2
  exit 1
fi

# The disagreement set must be exactly the rows whose document does not end on
# a block boundary: a partial row that did not move means the mutation did not
# bite where the clamp says it should, and a block-aligned row that moved means
# the mutation reached the full-block loop, which the claim says it is not.
if ! awk -F '\t' '
  function partial(label,   m, s) {
    if (match(label, /len[0-9]+/) == 0) return -1
    s = substr(label, RSTART + 3, RLENGTH - 3) + 0
    return (s % 64 != 0) ? 1 : 0
  }
  NR == FNR { line[FNR] = $0; p[FNR] = partial($2); part += p[FNR]; next }
  {
    moved = ($0 != line[FNR])
    if (p[FNR] != 1 && moved) {
      printf "FAIL: a block-aligned row moved: %s\n", line[FNR] > "/dev/stderr"; bad = 1
    }
    if (p[FNR] == 1 && !moved) {
      printf "FAIL: a partial row did not move: %s\n", line[FNR] > "/dev/stderr"; bad = 1
    }
    if (moved) { count++; if (first == 0) first = FNR }
  }
  END {
    if (part <= 0) { printf "FAIL: no partial document, so the detector has nothing to bite\n" > "/dev/stderr"; bad = 1 }
    printf "%d %d %d\n", count + 0, part + 0, first + 0
    exit bad
  }
' "$work/lean.out" "$work/defect.out" > "$work/moved.txt"; then
  exit 1
fi

read -r moved_rows partial_rows first_row < "$work/moved.txt"
if [ "$moved_rows" -ne "$partial_rows" ]; then
  printf 'FAIL: %s row(s) moved, %s are partial\n' "$moved_rows" "$partial_rows" >&2
  exit 1
fi

if [ "$first_row" -eq 0 ]; then
  printf 'FAIL: the defect differs but no differing row was found\n' >&2
  exit 1
fi

first_line=$(awk -v n="$first_row" 'NR == n' "$work/lean.out")

if ! "$work/driver_defect" "${corpus_args[@]}" --arms >"$work/defect2.out" \
    2>/dev/null; then
  printf 'FAIL: the second defect run failed\n' >&2
  exit 1
fi

if ! cmp -s "$work/defect.out" "$work/defect2.out"; then
  printf 'FAIL: the defect is not deterministic across two runs\n' >&2
  exit 1
fi

# --- 4. A tampered expectation is a mismatch naming its row. ---

awk 'NR == 1 { sub(/\t0x[0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]/, "\t0x0000000000000000") } { print }' \
  "$work/lean.out" > "$work/tampered.tsv"

if cmp -s "$work/lean.out" "$work/tampered.tsv"; then
  printf 'SETUP: the tamper changed nothing\n' >&2
  exit 3
fi

"$runner" "${corpus_args[@]}" --arms --expect "$work/tampered.tsv" \
  >"$work/tampered.out" 2>"$work/tampered.err"
status=$?

if [ "$status" -eq 0 ]; then
  printf 'FAIL: a tampered expectation exited 0\n' >&2
  exit 1
fi

if ! grep -q '^mismatch:' "$work/tampered.err"; then
  printf 'FAIL: the tampered run did not report a mismatch\n' >&2
  cat "$work/tampered.err" >&2
  exit 1
fi

if ! grep -q $'mismatch: mixed\tlen64:' "$work/tampered.err"; then
  printf 'FAIL: the mismatch does not name the tampered row\n' >&2
  cat "$work/tampered.err" >&2
  exit 1
fi

if ! cmp -s "$work/lean.out" "$work/tampered.out"; then
  printf 'FAIL: the tampered run printed different rows\n' >&2
  exit 1
fi

# --- Report ---

ascii_ones=$(awk -F '\t' '$3 == 1' "$work/ascii.out" | wc -l)
ascii_zeros=$(awk -F '\t' '$3 == 0' "$work/ascii.out" | wc -l)
utf8_ones=$(awk -F '\t' '$3 == 1' "$work/utf8.out" | wc -l)
utf8_zeros=$(awk -F '\t' '$3 == 0' "$work/utf8.out" | wc -l)
fixture_sha=$(sha256sum "$work/json-s1-blocks.candidate.ll" | cut -d' ' -f1)

printf 'ok: the fixture is the kernel source emission at the pinned flags (sha256 %s)\n' \
  "$fixture_sha"
printf 'ok: both actors stage the same mixed block (64 bytes)\n'
printf 'ok: %s row(s) produced by the Lean body: %s document(s) x 4 arms, %s corpus file(s), %s byte, %s short, %s alphabet, %s random\n' \
  "$rows" "$docs" "${#corpus_files[@]}" "$byte_docs" "$short_docs" "$alphabet_docs" "$random_docs"
printf 'ok: the list-free arms left every staged region untouched on %s row(s); the list arms moved %s\n' \
  "$gateoff_rows" "$gateon_moved"
printf 'ok: the ASCII probe agrees with the staged documents on %s document(s): %s all-ASCII, %s with a high byte; escapes.json 1, utf8.json 0\n' \
  "$ascii_docs" "$ascii_ones" "$ascii_zeros"
printf 'ok: the UTF-8 error bit agrees with the scalar reference on %s document(s): %s invalid, %s valid; the gate does not move the word\n' \
  "$utf8_docs" "$utf8_ones" "$utf8_zeros"
printf 'ok: the object (s1_blocks.o sha256 %s) agrees with the Lean body on %s row(s), ret included\n' \
  "$kernel_sha" "$rows"
printf 'ok: the detector bites: %s of %s row(s) moved, exactly the partial-tail documents; first is %s\n' \
  "$moved_rows" "$rows" "$first_line"
printf 'ok: a tampered expectation is a mismatch naming its row\n'
