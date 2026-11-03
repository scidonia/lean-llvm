#!/usr/bin/env bash
# Corpus check for the JSON block classifier.
#
#   nix develop -c bash tests/json-classify/check.sh
#
# The route has two arms that must agree, window for window, on the same 32-byte
# blocks:
#
#   * the certified Lean body — `classify32Function`, the AST
#     `LeanLLVM/Vellum/JsonClassifyIR.lean` pins to
#     `probes/install/ir/json-classify.candidate.ll` and proves equal to the
#     block layer's mask on every readable block — run by
#     `leanllvm-json-classify` under the repository's semantics;
#   * the installed object — the committed fixture compiled as it stands and
#     called through `probes/json/classify_driver.c`.
#
# What the object arm establishes is agreement on **aligned** 32-byte windows:
# the fixture's load carries no alignment operand (the capture drops clang's
# `align 1` because the parser's `load` has no alignment field), and for this
# build — `clang -c` on the fixture, without `-mavx2` — the load lowers to two
# 16-byte `movdqa`s, so the object requires **16-byte** alignment, not the
# type's 32: a 16-byte-aligned, non-32-byte-aligned pointer returns
# `0x7bd6f7b7` and exits 0, while `pad33`'s offset-1 window exited 139 before
# the driver staged its windows.  The driver copies each window into a
# 32-byte-aligned scratch buffer, which is conservative for a 16-byte
# requirement and equal to the load's type alignment.  The object's behaviour
# on an unaligned pointer is not covered by this route, and that gap is a real
# difference between the text LeanLLVM refines and the object built from it;
# `probes/json/classify_driver.c` states it where the staging is defined.
#
# What this scenario asserts, in order:
#
#   0. `tests/json-classify/mixed.block` is the executable's own 32-byte block:
#      `leanllvm-json-classify --emit-block` writes it and the committed file
#      must match byte for byte, so the fixture cannot drift from the
#      definition whose classification the route reports.
#   1. Every row of `tests/json-classify/manifest.tsv` is classified by the Lean
#      body and agrees with its hand-written mask.  Every byte of every pad
#      window is `[`, `]` or space, so every bit is set and the mask is
#      `0xffffffff`; `tests/json-classify/mixed.block` interleaves structural
#      bytes, JSON whitespace and ordinary content, its byte 0 is `[` (bit 0
#      set) and its byte 31 is `q` (bit 31 clear), and its mask is
#      `0x7bd6f7b7`.  That row is why a body returning a constant all-ones mask
#      cannot pass.
#   2. Every 32-byte window of every file in `tests/json/corpus` is classified.
#      The window count per file is computed from the file's size with `wc -c`,
#      not from its name, and the five boundary-named files' counts are
#      asserted explicitly: pad31 0, pad32 1, pad33 2, pad64 33, pad65 34 —
#      70 windows.  The corpus windows are a no-regression set: they are all
#      `0xffffffff`, and what discriminates a constant body is the mixed block
#      in step 1.
#   3. The installed object agrees with the Lean body on the corpus windows and
#      on the mixed block (71 rows), line for line.  The object is rebuilt from
#      the committed fixture here, and the fixture's and the object's sha256 are
#      recorded.
#   4. The detector bites.  A defect object built from the same fixture with
#      the comma comparison changed (`splat (i8 44)` → `splat (i8 45)`) must
#      disagree at the mixed block's offset 0, where the removed class is
#      present (bytes 4 and 17 are `,`), and nowhere else; the mismatch is
#      printed naming the window.
#   5. A tampered expectation — one manifest row's mask changed by hand — must
#      exit nonzero, say `mismatch:` on stderr, name the row it disagrees with,
#      and print the same windows and masks as the control, so the
#      disagreement is the expectation's and not the classification's.
#
# The binary is the artifact `probes/install/lake-locked.sh build
# leanllvm-json-classify` builds; this scenario does not invoke `lake`, so a
# corpus check does not build or contest the certificate lock.  `clang` is used
# only to build the two objects and the driver from committed sources into a
# private temporary directory; `CC` is not consulted because the dev shell's
# `CC` is gcc, which does not compile LLVM IR.  The corpus, the manifest, the
# mixed block, the fixture and the driver source are only read.
#
# Exit status: 0 when the assertions hold, 1 when one fails, 3 when the fixture
# is not usable (an absent corpus, manifest, mixed block, fixture or driver
# source, a manifest whose last line has no newline, a mixed block that is not
# 32 bytes, an absent runner binary, or no `clang` on PATH), so a setup fault
# is never read as an assertion result.
set -uo pipefail

repo=$(cd "$(dirname "$0")/../.." && pwd)
corpus=$repo/tests/json/corpus
manifest=$repo/tests/json-classify/manifest.tsv
mixed=$repo/tests/json-classify/mixed.block
fixture=$repo/probes/install/ir/json-classify.candidate.ll
driver_src=$repo/probes/json/classify_driver.c
runner=$repo/.lake/build/bin/leanllvm-json-classify
build_hint='nix develop -c bash probes/install/lake-locked.sh build leanllvm-json-classify'
# The fixture is LLVM IR, so the compiler must be an LLVM one; the dev shell's
# `CC` is gcc, which does not compile `.ll`.
cc=clang

for path in "$corpus" "$manifest" "$mixed" "$fixture" "$driver_src"; do
  [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done

if [ ! -x "$runner" ]; then
  printf 'SETUP: absent: %s\n  build it with: %s\n' "$runner" "$build_hint" >&2
  exit 3
fi

if ! command -v "$cc" >/dev/null 2>&1; then
  printf 'SETUP: no LLVM compiler: %s is not on PATH\n' "$cc" >&2
  printf '  run this scenario through the dev shell: nix develop -c bash tests/json-classify/check.sh\n' >&2
  exit 3
fi

if [ -s "$manifest" ] && [ -n "$(tail -c 1 "$manifest")" ]; then
  echo "SETUP: the manifest's last line has no newline" >&2
  exit 3
fi

mixed_size=$(wc -c < "$mixed")
if [ "$mixed_size" -ne 32 ]; then
  printf 'SETUP: %s is %s bytes, expected a 32-byte block\n' "$mixed" "$mixed_size" >&2
  exit 3
fi

work=$(mktemp -d) || { echo "SETUP: cannot create a temporary directory" >&2; exit 3; }
trap 'rm -rf "$work"' EXIT

cd "$repo" || exit 3

manifest_rows=$(awk 'NF && $0 !~ /^#/' "$manifest" | wc -l)

# --- 0. The committed mixed block is the executable's own block, byte for
# byte, so the fixture cannot drift from the definition the route classifies
# without this failing. ---

"$runner" --emit-block >"$work/emitted.block" 2>"$work/emitted.err"
status=$?
if [ "$status" -ne 0 ]; then
  printf 'FAIL: --emit-block exited %s\n' "$status" >&2
  cat "$work/emitted.err" >&2
  exit 1
fi

if ! cmp -s "$work/emitted.block" "$mixed"; then
  printf 'FAIL: %s differs from the block leanllvm-json-classify --emit-block writes\n' \
    "${mixed#"$repo"/}" >&2
  od -An -v -tx1 "$work/emitted.block" >&2
  exit 1
fi

# --- 1. Control: every manifest row is classified by the Lean body and agrees
# with its hand-written expectation. ---

"$runner" --manifest "$manifest" >"$work/control.out" 2>"$work/control.err"
status=$?
if [ "$status" -ne 0 ]; then
  printf 'FAIL: the unchanged manifest exited %s\n' "$status" >&2
  cat "$work/control.out" "$work/control.err" >&2
  exit 1
fi

out_rows=$(wc -l < "$work/control.out")
if [ "$out_rows" -ne "$manifest_rows" ]; then
  printf 'FAIL: the runner printed %s lines for %s manifest rows\n' \
    "$out_rows" "$manifest_rows" >&2
  cat "$work/control.out" >&2
  exit 1
fi

# The runner prints the window it classified and the mask its run returned; the
# manifest holds the same two columns as written.  Compare them separately, so
# a row that reported a different window cannot pass on a matching mask and a
# row that classified the right window cannot pass on a substituted
# expectation.
if ! diff -u <(awk 'NF && $0 !~ /^#/' "$manifest" | cut -f1,2) <(cut -f1,2 "$work/control.out") >&2; then
  echo 'FAIL: the reported windows differ from the manifest rows' >&2
  exit 1
fi

if ! diff -u <(awk 'NF && $0 !~ /^#/' "$manifest" | cut -f3) <(cut -f3 "$work/control.out") >&2; then
  echo 'FAIL: the classified masks differ from the manifest expectations' >&2
  exit 1
fi

# The mixed block's row holds the mask no constant all-ones body can produce;
# assert it by name rather than relying on the projection above.
mixed_row='tests/json-classify/mixed.block'
if ! awk -F '\t' -v p="$mixed_row" '
    $1 == p && $2 == "0" && $3 == "0x7bd6f7b7" { found = 1 }
    END { exit !found }
  ' "$work/control.out"; then
  echo 'FAIL: the mixed block was not classified as 0x7bd6f7b7' >&2
  cat "$work/control.out" >&2
  exit 1
fi

# --- 2. Every 32-byte window of the corpus, with the count derived from each
# file's size. ---

"$runner" --windows "$corpus" >"$work/windows.out" 2>"$work/windows.err"
status=$?
if [ "$status" -ne 0 ]; then
  printf 'FAIL: the window run exited %s\n' "$status" >&2
  cat "$work/windows.err" >&2
  exit 1
fi

total=$(wc -l < "$work/windows.out")
if [ "$total" -le 0 ]; then
  echo 'FAIL: the corpus run classified no window' >&2
  exit 1
fi

if grep -vqE $'^[^\t]+\t[0-9]+\t0x[0-9a-f]{8}$' "$work/windows.out"; then
  echo 'FAIL: a window line is not <path>\t<offset>\t<eight hex digits>' >&2
  grep -vE $'^[^\t]+\t[0-9]+\t0x[0-9a-f]{8}$' "$work/windows.out" >&2
  exit 1
fi

for file in "$corpus"/*; do
  name=${file#"$corpus"/}
  size=$(wc -c < "$file")
  if [ "$size" -ge 32 ]; then want=$((size - 31)); else want=0; fi
  got=$(awk -F '\t' -v p="$corpus/$name" '$1 == p' "$work/windows.out" | wc -l)
  if [ "$got" -ne "$want" ]; then
    printf 'FAIL: %s is %s bytes but the run classified %s windows, expected %s\n' \
      "$name" "$size" "$got" "$want" >&2
    exit 1
  fi
done

# The five boundary-named files, asserted against their names as a second,
# independent reading of the same arithmetic.
for spec in pad31.json:0 pad32.json:1 pad33.json:2 pad64.json:33 pad65.json:34; do
  name=${spec%%:*}
  want=${spec##*:}
  got=$(awk -F '\t' -v p="$corpus/$name" '$1 == p' "$work/windows.out" | wc -l)
  if [ "$got" -ne "$want" ]; then
    printf 'FAIL: %s yielded %s window(s), expected %s\n' "$name" "$got" "$want" >&2
    exit 1
  fi
done

files=$(find "$corpus" -mindepth 1 -maxdepth 1 -type f | wc -l)

# --- 3. The installed object: the committed fixture compiled as it stands,
# through the C driver, over the same windows and the mixed block. ---

if ! "$cc" -c "$fixture" -o "$work/candidate.o" 2>"$work/cc.err"; then
  echo 'FAIL: the committed fixture does not compile' >&2
  cat "$work/cc.err" >&2
  exit 1
fi

if ! "$cc" -O2 -o "$work/classify_driver" "$driver_src" "$work/candidate.o" 2>"$work/link.err"; then
  echo 'FAIL: the driver does not link against the candidate object' >&2
  cat "$work/link.err" >&2
  exit 1
fi

mapfile -t corpus_files < <(find "$corpus" -mindepth 1 -maxdepth 1 -type f | LC_ALL=C sort)

if ! "$work/classify_driver" "${corpus_files[@]}" "$mixed" >"$work/object.out" 2>"$work/object.err"; then
  echo 'FAIL: the driver failed over the corpus and the mixed block' >&2
  cat "$work/object.err" >&2
  exit 1
fi

"$runner" --windows "$corpus" --windows "$mixed" >"$work/lean.out" 2>"$work/lean.err"
status=$?
if [ "$status" -ne 0 ]; then
  printf 'FAIL: the Lean body exited %s over the corpus and the mixed block\n' "$status" >&2
  cat "$work/lean.err" >&2
  exit 1
fi

LC_ALL=C sort "$work/object.out" >"$work/object.sorted"
LC_ALL=C sort "$work/lean.out" >"$work/lean.sorted"

if ! cmp -s "$work/object.sorted" "$work/lean.sorted"; then
  echo 'FAIL: the installed object and the Lean body disagree' >&2
  diff -u "$work/lean.sorted" "$work/object.sorted" >&2
  exit 1
fi

windows_compared=$(wc -l < "$work/object.sorted")
corpus_windows=$((total + 1))

if [ "$windows_compared" -ne "$corpus_windows" ]; then
  printf 'FAIL: compared %s window(s), expected the corpus windows plus the mixed block (%s)\n' \
    "$windows_compared" "$corpus_windows" >&2
  exit 1
fi

fixture_sha=$(sha256sum "$fixture" | cut -d' ' -f1)
object_sha=$(sha256sum "$work/candidate.o" | cut -d' ' -f1)

# --- 4. The detector bites: the comma comparison changed, nothing else. ---

sed 's/splat (i8 44)/splat (i8 45)/' "$fixture" > "$work/candidate.defect.ll"

if cmp -s "$fixture" "$work/candidate.defect.ll"; then
  echo 'SETUP: the fixture has no comma comparison to mutate' >&2
  exit 3
fi

if ! "$cc" -c "$work/candidate.defect.ll" -o "$work/candidate.defect.o" 2>"$work/cc.err"; then
  echo 'FAIL: the mutated fixture does not compile' >&2
  cat "$work/cc.err" >&2
  exit 1
fi

if ! "$cc" -O2 -o "$work/classify_driver_defect" "$driver_src" "$work/candidate.defect.o" \
    2>"$work/link.err"; then
  echo 'FAIL: the driver does not link against the defect object' >&2
  cat "$work/link.err" >&2
  exit 1
fi

if ! "$work/classify_driver_defect" "${corpus_files[@]}" "$mixed" >"$work/defect.out" \
    2>"$work/defect.err"; then
  echo 'FAIL: the driver failed over the defect object' >&2
  cat "$work/defect.err" >&2
  exit 1
fi

LC_ALL=C sort "$work/defect.out" >"$work/defect.sorted"

# The defect must differ from the certified route in exactly one window.  The
# removed comma class occurs only in the mixed block (bytes 4 and 17), so every
# corpus row is identical — a defect that also moved a corpus window fails
# here — and the one differing line is the mixed block at offset 0:
# 0x7bd6f7b7 from the route, 0x7bd4f7a7 from the defect.
diff_output=$(diff "$work/lean.sorted" "$work/defect.sorted")
status=$?

if [ "$status" -ne 1 ]; then
  printf 'FAIL: diff between the Lean body and the defect object exited %s, expected exactly one difference\n' \
    "$status" >&2
  printf '%s\n' "$diff_output" >&2
  exit 1
fi

removed=$(printf '%s\n' "$diff_output" | grep -c '^< ')
added=$(printf '%s\n' "$diff_output" | grep -c '^> ')

if [ "$removed" -ne 1 ] || [ "$added" -ne 1 ]; then
  printf 'FAIL: the defect object differs in %s line(s) and %s line(s), expected exactly one window\n' \
    "$removed" "$added" >&2
  printf '%s\n' "$diff_output" >&2
  exit 1
fi

if ! printf '%s\n' "$diff_output" | grep -qxF "< $mixed"$'\t'"0"$'\t'"0x7bd6f7b7"; then
  echo "FAIL: the differing line is not the route's mixed block at offset 0" >&2
  printf '%s\n' "$diff_output" >&2
  exit 1
fi

if ! printf '%s\n' "$diff_output" | grep -qxF "> $mixed"$'\t'"0"$'\t'"0x7bd4f7a7"; then
  echo 'FAIL: the defect line is not the mixed block at offset 0 with the comma class removed' >&2
  printf '%s\n' "$diff_output" >&2
  exit 1
fi

# --- 5. Tamper: change one expected mask, and nothing else. ---

awk -F '\t' -v OFS='\t' '
  !done && $1 == "tests/json-classify/mixed.block" { $3 = "0x7bd6f7b6"; done = 1 }
  { print }
' "$manifest" > "$work/tampered.tsv"

if cmp -s "$manifest" "$work/tampered.tsv"; then
  echo 'SETUP: the manifest has no mixed-block row to tamper' >&2
  exit 3
fi

"$runner" --manifest "$work/tampered.tsv" >"$work/tampered.out" 2>"$work/tampered.err"
status=$?

if [ "$status" -eq 0 ]; then
  echo 'FAIL: the tampered manifest exited 0' >&2
  cat "$work/tampered.out" >&2
  exit 1
fi

expected_line='mismatch: tests/json-classify/mixed.block: offset 0: expected mask 0x7bd6f7b6, got 0x7bd6f7b7'
if ! grep -qxF "$expected_line" "$work/tampered.err"; then
  printf 'FAIL: the tampered run exited %s without naming the row it disagreed with\n' \
    "$status" >&2
  cat "$work/tampered.err" >&2
  exit 1
fi

# The tampered run printed the same windows and masks as the control: the
# mismatch came from the expectation, not from a different classification.
if ! cmp -s "$work/control.out" "$work/tampered.out"; then
  echo 'FAIL: the tampered run classified different windows or masks' >&2
  diff -u "$work/control.out" "$work/tampered.out" >&2
  exit 1
fi

# --- Report ---

printf 'ok: mixed.block is the emitted block (sha256 %s)\n' \
  "$(sha256sum "$mixed" | cut -d' ' -f1)"
printf 'ok: %s manifest row(s) agree with their hand-written masks\n' "$manifest_rows"
printf 'ok: %s corpus window(s) over %s file(s); boundary counts 0/1/2/33/34\n' \
  "$total" "$files"
printf 'ok: the installed object (sha256 %s, from fixture sha256 %s) agrees with the Lean body on %s window(s)\n' \
  "$object_sha" "$fixture_sha" "$windows_compared"
printf 'ok: the detector bites: %s: offset 0: 0x7bd6f7b7 -> 0x7bd4f7a7\n' "$mixed"
printf 'ok: a tampered expectation is a mismatch\n'
