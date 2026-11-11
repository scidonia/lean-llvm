#!/usr/bin/env bash
# Route check for the stage-1 classification masks.
#
#   nix develop -c bash tests/json-s1-masks/check.sh
#
# Two actors must agree, row for row, on the same rows:
#
#   * the Lean body — `s1MasksFunction`, the AST
#     `LeanLLVM/Refinement/JsonS1MasksIR.lean` pins to
#     `probes/install/ir/json-s1-masks.candidate.ll` — run by
#     `leanllvm-json-s1-masks` under the repository's semantics;
#   * the installed object — `kernel/json/s1_block.c` compiled with the measured
#     compiler line and called through `probes/json/s1_masks_driver.c`.
#
# Every window is staged at offset 1 of a 96-byte buffer, so the object is
# called on a misaligned pointer, and the output slot is pre-filled with `0xA5`,
# so a store the body does not make shows as a sentinel word.  A row is
#
#   <source>\t<label>\t<open>\t<ppar>\t<inside>\t<comma>\t<quote>\t<delim>
#   \t<in_string>\t<ws>\t<backslash>\t<ctl>\t<esc_open>\t<esc_ppar>\t<im_carry>
#
# with `comma` set when any lane of the block is `0x2C`.
#
# The object is compiled from the kernel source rather than from the fixture:
# the fixture's loads carry no alignment operand (the capture drops `align 1`
# and the parser's `load` has no alignment field), so an object built from it
# inherits the type's ABI alignment and the offset-1 staging is not reachable.
# In the same run the fixture is regenerated from that same source at those
# same flags and compared with the committed bytes; a difference is a setup
# failure (exit 3), not an assertion failure.  The fixture is the theorem's
# subject; the source is the object's.
#
# What this scenario asserts, in order:
#
#   0. Both actors' `--emit-block` output is the same 64 bytes, so the mixed
#      block the two row streams share is one block and not two copies.
#   1. The Lean body classifies every row and the row count is exactly the
#      computed count: 8 mixed rows, 8 per corpus window, and 131072 + 524288 +
#      32768 rows for the byte, alphabet and random arms.  The three boundary
#      corpus files are also asserted by name (63 → 0, 64 → 1, 65 → 2 windows).
#   2. The object's rows equal the Lean body's rows line for line, in order.
#   3. The detector bites: a defect object built from a copy of the kernel with
#      bit 0 of both `s1f_lo_tab` entries for the low nibble of `,` — offsets 12
#      and 28, the sixteen-entry table being duplicated for pshufb's lane-local
#      addressing — flipped disagrees with the control on exactly the rows whose
#      `comma` column is 1, and on no other row; the report names the first
#      differing row and two runs of the defect name the same row.
#   4. The tampered expectation: one word of the Lean stream changed by hand, fed
#      back to the runner as its expectation, exits nonzero, says `mismatch:` on
#      stderr, names the row, and prints the same rows as the control, so the
#      disagreement is the expectation's and not the classification's.
#
# The runner is the artifact `lake build leanllvm-json-s1-masks` produces; this
# script does not invoke `lake`.  `clang` compiles committed sources into a
# private temporary directory; `CC` is not consulted because the dev shell's
# `CC` is gcc.  The corpus, the fixture, the capture script and the driver
# source are only read — the fixture is replaced and restored around the
# regeneration comparison, and the script's exit trap puts the committed bytes
# back whatever happens.
#
# Exit status: 0 when the assertions hold, 1 when one fails, 3 when the route is
# not usable (an absent corpus, fixture, capture script, driver or kernel
# source, an absent runner binary, no `clang` on PATH, a capture that does not
# reproduce the fixture, or a capture that writes nothing), so a setup fault is
# never read as an assertion result.
set -uo pipefail

repo=$(cd "$(dirname "$0")/../.." && pwd)
corpus=$repo/tests/json-s1-masks/corpus
fixture=$repo/probes/install/ir/json-s1-masks.candidate.ll
capture=$repo/probes/install/ir/capture-s1-masks.sh
driver_src=$repo/probes/json/s1_masks_driver.c
kernel_src=$repo/kernel/json/s1_block.c
runner=$repo/.lake/build/bin/leanllvm-json-s1-masks
build_hint='nix develop -c lake build leanllvm-json-s1-masks'
cc=clang

# The measured compiler line (`build49.sh:17`).
cflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)

for path in "$corpus" "$fixture" "$capture" "$driver_src" "$kernel_src"; do
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
restore_fixture() {
  if [ -f "$work/fixture.committed" ]; then
    cp "$work/fixture.committed" "$fixture"
  fi
}
trap 'restore_fixture; rm -rf "$work"' EXIT

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
    -o "$work/kernel.o" 2>"$work/cc.err"; then
  printf 'FAIL: the kernel did not compile with the measured flags\n' >&2
  cat "$work/cc.err" >&2
  exit 1
fi

if ! "$cc" -O2 -o "$work/driver" "$driver_src" "$work/kernel.o" 2>"$work/link.err"; then
  printf 'FAIL: the driver did not link against the kernel object\n' >&2
  cat "$work/link.err" >&2
  exit 1
fi

# --- The fixture is the kernel source's emission at the same flags. ---
#
# The capture writes the fixture in place, so the committed bytes are copied
# aside, the file is removed, and the exit trap restores the copy whatever the
# outcome.  A capture that writes nothing, or writes different bytes, is a
# setup fault: the theorem's subject would not be the code the object arm ran.

cp "$fixture" "$work/fixture.committed"
rm -f "$fixture"

if ! bash "$capture" >"$work/capture.out" 2>"$work/capture.err"; then
  printf 'SETUP: %s exited nonzero; the fixture did not regenerate\n' "$capture" >&2
  cat "$work/capture.err" >&2
  exit 3
fi

if [ ! -f "$fixture" ]; then
  printf 'SETUP: %s wrote no fixture at %s\n' "$capture" "$fixture" >&2
  exit 3
fi

if ! cmp -s "$work/fixture.committed" "$fixture"; then
  printf 'SETUP: the committed fixture is not the kernel source emission at the pinned flags\n' >&2
  diff -u "$work/fixture.committed" "$fixture" | awk 'NR <= 40' >&2
  exit 3
fi

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

corpus_windows=0
for f in "${corpus_files[@]}"; do
  size=$(wc -c < "$f")
  if [ "$size" -ge 64 ]; then
    corpus_windows=$((corpus_windows + size - 63))
  fi
done

byte_rows=131072      # 8 states * 64 positions * 256 values
alphabet_rows=524288  # 8 states * 16^4 sequences
random_rows=32768     # 8 states * 4096 blocks
computed=$((8 + 8 * corpus_windows + byte_rows + alphabet_rows + random_rows))

rows=$(wc -l < "$work/lean.out")
if [ "$rows" -ne "$computed" ]; then
  printf 'FAIL: %s row(s) printed, %s computed\n' "$rows" "$computed" >&2
  exit 1
fi

# The three boundary files, read against their names as a second, independent
# reading of the same arithmetic.
for spec in boundary-63.json:0 boundary-64.json:1 boundary-65.json:2; do
  name=${spec%%:*}
  want=${spec##*:}
  size=$(wc -c < "$corpus/$name") || { printf 'SETUP: absent %s\n' "$name" >&2; exit 3; }
  if [ "$size" -lt 64 ]; then got=0; else got=$((size - 63)); fi
  if [ "$got" -ne "$want" ]; then
    printf 'FAIL: %s is %s bytes, giving %s window(s), not %s\n' \
      "$name" "$size" "$got" "$want" >&2
    exit 1
  fi
done

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

kernel_sha=$(sha256sum "$work/kernel.o" | cut -d' ' -f1)

# The comma column is derived, not trusted: the two arms whose label carries
# the block's bytes must agree with it; the mixed block must read 1.
awk -F '\t' '
  $1 == "arm:byte"     { split($2, p, "/"); want = (p[2] == "val2c") ? 1 : 0 }
  $1 == "arm:alphabet" { want = (index(substr($2,1,8), "2c") > 0) ? 1 : 0 }
  $1 == "mixed"        { want = 1 }
  $1 ~ /^(arm:(byte|alphabet)|mixed)$/ {
    if ($6 != want) { printf "FAIL: comma column %s on %s\n", $6, $2 > "/dev/stderr"; bad = 1 }
  }
  END { exit bad }
' "$work/lean.out" || exit 1

# --- 3. The detector bites: bit 0 of both copies of the comma class's table
# entry — offsets 12 and 28, the sixteen-entry table being duplicated for
# `pshufb`'s lane-local addressing — is flipped. ---

# The table is the sixteen-entry pattern duplicated, because pshufb addresses
# lanes locally, so the comma class's bit lives at both offsets 12 and 28.  Both
# are flipped: mutating only the first leaves comma lanes 16-31 and 48-63
# untouched and the comma-row set would not move as one.
#
# `(& ^ 0x01)` is exactly a bit-0 flip of the entry, whatever its written value,
# and it is a constant expression the compiler folds.  The substitution is
# textual because the kernel source owns the table's spelling; a source without
# `s1f_lo_tab`, or one whose initialiser is shorter than the twenty-nine entries
# the modulo rule needs, is a failed mutation and not a silent pass.  The number
# of mutations that land is counted and must equal the number of offsets
# congruent to `idx` in the initialiser, so "changed one of two" fails here.
if ! awk -v idx=12 '
  { buf = buf $0 "\n" }
  END {
    p = index(buf, "s1f_lo_tab")
    if (p == 0) {
      print "SETUP: s1f_lo_tab not found in the kernel source" > "/dev/stderr"
      exit 4
    }
    rest = substr(buf, p)
    b = index(rest, "{")
    if (b == 0) {
      print "SETUP: s1f_lo_tab has no initialiser" > "/dev/stderr"
      exit 4
    }
    pre = substr(buf, 1, p + b - 1)
    after = substr(rest, b + 1)
    c = index(after, "}")
    if (c == 0) {
      print "SETUP: s1f_lo_tab initialiser is not terminated" > "/dev/stderr"
      exit 4
    }
    inner = substr(after, 1, c - 1)
    post = substr(after, c)
    n = split(inner, items, ",")
    if (n < idx + 17) {
      print "SETUP: s1f_lo_tab has " n " entries; the modulo rule needs " (idx + 17) > "/dev/stderr"
      exit 4
    }
    expected = 0
    for (k = idx; k < n; k += 16) expected++
    out = ""
    for (i = 1; i <= n; i++) {
      item = items[i]
      if ((i - 1) % 16 == idx) sub(/[^ \t\n][^,]*/, "(& ^ 0x01)", item)
      out = out item
      if (i < n) out = out ","
    }
    # Count the mutations that actually landed in the emitted text, not the
    # ones the loop meant to apply: a `sub` that matched nothing, or a template
    # that never reached the output, is exactly the "changed one of two" case.
    # The emitted form is `(<entry> ^ 0x01)` — the `&` in the template expands
    # to the entry — so the marker counted is the tail every mutation shares.
    mutated = 0
    rest = out
    while ((q = index(rest, " ^ 0x01)")) > 0) {
      mutated++
      rest = substr(rest, q + 8)
    }
    if (mutated != expected) {
      print "SETUP: the mutation flipped " mutated " of " expected " table entries" > "/dev/stderr"
      exit 3
    }
    printf "%s%s%s", pre, out, post
  }
' "$kernel_src" > "$work/s1_block.defect.c"; then
  printf 'SETUP: the table mutation did not apply\n' >&2
  exit 3
fi

if cmp -s "$kernel_src" "$work/s1_block.defect.c"; then
  printf 'SETUP: the table mutation changed nothing\n' >&2
  exit 3
fi

if ! "$cc" "${cflags[@]}" -I "$repo/kernel/json" -c "$work/s1_block.defect.c" \
    -o "$work/kernel.defect.o" 2>"$work/cc.err"; then
  printf 'FAIL: the defect kernel did not compile\n' >&2
  cat "$work/cc.err" >&2
  exit 1
fi

if ! "$cc" -O2 -o "$work/driver_defect" "$driver_src" "$work/kernel.defect.o" \
    2>"$work/link.err"; then
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

# The disagreement set must be exactly the rows whose block carries a comma:
# a comma row that did not move means the mutation did not bite where the
# classification says it should, and a comma-free row that moved means the
# table entry is shared with a class the claim says it is not.
comma_rows=$(awk -F '\t' '$6 == 1' "$work/lean.out" | wc -l)
if [ "$comma_rows" -le 0 ]; then
  printf 'FAIL: no row carries a comma, so the detector has nothing to bite\n' >&2
  exit 1
fi

moved_rows=$(awk -F '\t' '
  NR == FNR { line[FNR] = $0; comma[FNR] = $6; next }
  {
    moved = ($0 != line[FNR])
    if (comma[FNR] == 1 && !moved) {
      printf "FAIL: a comma row did not move: %s\n", line[FNR] > "/dev/stderr"
      bad = 1
    }
    if (comma[FNR] == 0 && moved) {
      printf "FAIL: a comma-free row moved: %s\n", line[FNR] > "/dev/stderr"
      bad = 1
    }
    if (moved) count++
  }
  END { print count + 0; exit bad }
' "$work/lean.out" "$work/defect.out") || exit 1

if [ "$moved_rows" -ne "$comma_rows" ]; then
  printf 'FAIL: %s row(s) moved, %s carry a comma\n' "$moved_rows" "$comma_rows" >&2
  exit 1
fi

first_row=$(awk 'NR == FNR { a[FNR] = $0; next } $0 != a[FNR] { print FNR; exit }' \
  "$work/lean.out" "$work/defect.out")
if [ -z "$first_row" ]; then
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

if ! grep -q "mismatch: mixed	0:" "$work/tampered.err"; then
  printf 'FAIL: the mismatch does not name the tampered row\n' >&2
  cat "$work/tampered.err" >&2
  exit 1
fi

if ! cmp -s "$work/lean.out" "$work/tampered.out"; then
  printf 'FAIL: the tampered run printed different rows\n' >&2
  exit 1
fi

# --- Report ---

printf 'ok: the fixture is the kernel source emission at the pinned flags\n'
printf 'ok: both actors stage the same mixed block (64 bytes)\n'
printf 'ok: %s row(s) classified by the Lean body: %s corpus window(s) over %s file(s), %s byte rows, %s alphabet rows, %s random rows\n' \
  "$rows" "$corpus_windows" "${#corpus_files[@]}" "$byte_rows" "$alphabet_rows" "$random_rows"
printf 'ok: the object (kernel sha256 %s) agrees with the Lean body on %s row(s)\n' \
  "$kernel_sha" "$rows"
printf 'ok: the detector bites: %s of %s row(s) moved, all comma-carrying; first is %s\n' \
  "$moved_rows" "$rows" "$first_line"
printf 'ok: a tampered expectation is a mismatch naming its row\n'
