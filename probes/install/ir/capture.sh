#!/usr/bin/env bash
# Regenerate the emitted-IR fixtures in probes/install/ir/.
#
# Run through the flake, from the repository root:
#
#   nix develop -c bash probes/install/ir/capture.sh
#
# Inputs
#   probes/install/build/Baseline.c   Lean's own C emission of probes/install/Baseline.lean
#   probes/install/build/Candidate.c  Lean's own C emission of probes/install/Candidate.lean
#   probes/install/ir/candidate_lanes.c
#                                     the candidate's eight-lane fold, lane by
#                                     lane, without the boxed `Nat` counter
#
# Outputs (all under probes/install/ir/)
#   baseline.raw.ll    -O0 emission of @leanllvm_comma_mask8 from Baseline.c, verbatim
#   candidate.raw.ll   -O0 emission of @leanllvm_comma_mask8 and @l_commaMask8_go
#                      from Candidate.c, verbatim
#   baseline.o1.ll     -O1 emission of @leanllvm_comma_mask8, for the record
#   baseline.ll        parseable fixture
#   candidate.ll       parseable fixture
#
# --- Why the parseable fixtures are -O0 plus two passes --------------------
#
# `lean.h` defines every `UInt64` primitive the emitted C calls as a
# `static inline` function (`static inline uint64_t lean_uint64_xor(uint64_t a,
# uint64_t b) { return a ^ b; }`, "UInt64" section), and the emitted C also
# carries forward declarations of them.  At -O0 clang does not inline, so the
# raw emission calls them; `LeanLLVM.Semantics` has no `call`.
#
# For baseline.ll the branch entry defines those five primitives itself, with
# `__attribute__((always_inline))`, so clang inlines them at -O0 and the body
# comes out as the source expression's operations in source order, with the
# generated function body copied verbatim.  -O0 still keeps every temporary in
# an alloca, so two standard passes follow:
#
#   opt -passes='function(mem2reg),instnamer'
#
# `mem2reg` promotes the allocas to SSA registers (it is refused while the
# functions carry clang's `optnone`, hence `-Xclang -disable-O0-optnone`), and
# `instnamer` names every value and block, which also labels the entry block --
# `LeanLLVM.Parser` requires a label on every block, and textual IR leaves the
# entry block unlabelled.  Neither pass changes the operations.
#
# Noise-reducing rewrites are avoided on purpose: `-O1` (or `instcombine`) would
# turn `and`/`xor` against `0x2C..` into different masks, and the resulting
# fixture's equality with `CommaMask.swar` would then be a bit-level fact rather
# than the source expression.  The -O1 emission is kept in baseline.o1.ll so
# that the difference is on record.
#
# For candidate.ll the loop of the probe's source is written out lane by lane in
# candidate_lanes.c, because the emission of the boxed-`Nat` loop is outside the
# modelled fragment (see candidate.raw.ll).  At -O0 a `?:` becomes a diamond of
# basic blocks closed by `phi`, which `LeanLLVM.Parser` refuses, so
# `simplifycfg` runs alongside `mem2reg`:
#
#   opt -passes='function(mem2reg,simplifycfg),instnamer'
#
# It folds each lane's diamond back into the `select` the source wrote, and
# merges the blocks.
#
# --- Text removed before the parser sees the fixture ----------------------
#
# The parser refuses anything outside the modelled subset, so the emission is
# reduced to the function it analyses plus the instruction text.  Removed, and
# why it is irrelevant to the value computed:
#
#   `noundef`        parameter attribute; a promise about the argument, not
#                    part of the computation
#   `local_unnamed_addr`, `#N`
#                    linkage and attribute-group references; the groups
#                    (`attributes #0 = { ... }`) are removed with them
#   `, align N`      alignment of a load or store; the memory model is byte
#                    addressed with no alignment
#   `, !tbaa !7`     per-instruction metadata
#   `target datalayout`, `target triple`, `source_filename`,
#   `attributes #N = ...`, `!llvm.*`, `!N = ...`
#                    module-level lines outside the function
#   other `define` blocks, `@` globals
#                    the fixture is one function; the Lean initializer and the
#                    boxed wrappers are not part of the pure seam
#
# Nothing inside the retained instruction list is rewritten.  Both fixtures are
# checked with `opt -passes=verify`, so they remain valid LLVM IR.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)

lean_prefix=$(cd "$repo" && lake env lean --print-prefix)
inc="$lean_prefix/include"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# The `define` block of @<symbol>, verbatim, from a clang emission.
extract_fn() {
  awk -v sym="$2" '
    !d && $0 ~ ("^define .*@" sym "\\(") { d = 1; print; depth += gsub(/\{/, "{"); next }
    d { print; depth += gsub(/\{/, "{"); depth -= gsub(/\}/, "}"); if (depth <= 0) exit }
  ' "$1"
}

# The exported function as C, from Lean's emission: the definition only, with
# `LEAN_EXPORT` dropped.
extract_fn_c() {
  awk -v sym="$2" '
    !d && $0 ~ ("^LEAN_EXPORT uint64_t " sym "\\(") && /\{$/ { d = 1 }
    d { print; depth += gsub(/\{/, "{"); depth -= gsub(/\}/, "}"); if (depth <= 0) exit }
  ' "$1" | sed 's/^LEAN_EXPORT //'
}

# Text the parser does not model; see the header comment.
strip_ir() {
  sed -E \
    -e 's/, *align [0-9]+//g' \
    -e 's/, *![a-zA-Z0-9_.]+ ![-a-zA-Z0-9_.]+//g' \
    -e 's/, *![a-zA-Z0-9_.]+ [0-9]+//g' \
    -e 's/ noundef//g' \
    -e 's/ local_unnamed_addr//g' \
    -e 's/ #[0-9]+//g'
}

# One block, one `ret`.
check_shape() {
  local file=$1
  if [ "$(grep -cE '^[^ ;{}]+:$' "$file")" -ne 1 ]; then
    echo "capture: $file is not single-block" >&2; exit 1
  fi
  if [ "$(grep -cE '^  ret ' "$file")" -ne 1 ]; then
    echo "capture: $file does not end in a single ret" >&2; exit 1
  fi
}

emit() { # emit <out> <provenance-comment> <body-file>
  { printf '%s\n' "$2"; cat "$3"; } > "$1"
}

# --- the raw emissions ----------------------------------------------------

clang -S -emit-llvm -O0 -I"$inc" -Wno-#warnings \
  "$repo/probes/install/build/Baseline.c" -o "$work/baseline.O0.ll"
clang -S -emit-llvm -O0 -I"$inc" -Wno-#warnings \
  "$repo/probes/install/build/Candidate.c" -o "$work/candidate.O0.ll"
clang -S -emit-llvm -O1 -I"$inc" -Wno-#warnings \
  "$repo/probes/install/build/Baseline.c" -o "$work/baseline.O1.ll"

extract_fn "$work/baseline.O0.ll" leanllvm_comma_mask8 > "$work/baseline.raw.body.ll"
{ extract_fn "$work/candidate.O0.ll" leanllvm_comma_mask8
  echo
  extract_fn "$work/candidate.O0.ll" l_commaMask8_go; } > "$work/candidate.raw.body.ll"

emit "$here/baseline.raw.ll" '; probes/install/build/Baseline.c, emitted with
;
;   clang -S -emit-llvm -O0 -I"$(lake env lean --print-prefix)/include" \
;     probes/install/build/Baseline.c
;
; and reduced to the verbatim `define` block of @leanllvm_comma_mask8.
; Nothing inside the block is changed.  The calls are to the `UInt64`
; primitives that `lean.h` defines `static inline`; `LeanLLVM.Semantics` has no
; `call`, so this emission is not parseable.  baseline.ll is the same function
; emitted with those primitives inlined, which is what a production build does.' \
  "$work/baseline.raw.body.ll"

emit "$here/candidate.raw.ll" '; probes/install/build/Candidate.c, emitted with
;
;   clang -S -emit-llvm -O0 -I"$(lake env lean --print-prefix)/include" \
;     probes/install/build/Candidate.c
;
; and reduced to the verbatim `define` blocks of @leanllvm_comma_mask8 and
; @l_commaMask8_go.  Nothing inside the blocks is changed.  The exported
; function only calls @l_commaMask8_go, and the loop runs on a boxed `Nat`
; counter: `lean_nat_dec_lt`, `lean_nat_mul`, `lean_nat_add`, `lean_dec`,
; `lean_unsigned_to_nat`, closed by `phi` over a `lean_object*`.  That is
; outside the fragment `LeanLLVM.Semantics` models on three counts (calls,
; heap objects, `phi`), so this emission is not parseable and candidate.ll is
; the lane-by-lane transcription in candidate_lanes.c instead.' \
  "$work/candidate.raw.body.ll"

extract_fn "$work/baseline.O1.ll" leanllvm_comma_mask8 > "$work/baseline.o1.body.ll"

emit "$here/baseline.o1.ll" '; probes/install/build/Baseline.c emitted at -O1, for the record:
;
;   clang -S -emit-llvm -O1 -I"$(lake env lean --print-prefix)/include" \
;     probes/install/build/Baseline.c
;
; verbatim `define` block of @leanllvm_comma_mask8.  InstCombine has rewritten
; the mask and the final complement here (`x &&& 0x7F..` for `m &&& 0x7F..`,
; `^^^ 0x80..` for `~~~ _ &&& 0x80..`), so relating this body to
; `CommaMask.swar` is a bit-level fact rather than the source expression.  It is
; kept as evidence of that difference; baseline.ll is the fixture used.' \
  "$work/baseline.o1.body.ll"

# --- the parseable fixtures ----------------------------------------------

# The baseline body: the generated function, verbatim, behind the header's own
# definitions of the five primitives, forced inline.
cat > "$work/baseline_inline.c" <<'C'
#include <stdint.h>
static inline __attribute__((always_inline)) uint64_t lean_uint64_xor(uint64_t a, uint64_t b) { return a ^ b; }
static inline __attribute__((always_inline)) uint64_t lean_uint64_land(uint64_t a, uint64_t b) { return a & b; }
static inline __attribute__((always_inline)) uint64_t lean_uint64_lor(uint64_t a, uint64_t b) { return a | b; }
static inline __attribute__((always_inline)) uint64_t lean_uint64_add(uint64_t a, uint64_t b) { return a + b; }
static inline __attribute__((always_inline)) uint64_t lean_uint64_complement(uint64_t a) { return ~a; }
C
extract_fn_c "$repo/probes/install/build/Baseline.c" leanllvm_comma_mask8 \
  >> "$work/baseline_inline.c"

clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone -Wno-#warnings \
  "$work/baseline_inline.c" -o "$work/baseline.inline.ll"
opt -passes='function(mem2reg),instnamer' -S "$work/baseline.inline.ll" \
  -o "$work/baseline.promoted.ll"

clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone -Wno-#warnings \
  "$repo/probes/install/ir/candidate_lanes.c" -o "$work/candidate.lanes.ll"
opt -passes='function(mem2reg,simplifycfg),instnamer' -S "$work/candidate.lanes.ll" \
  -o "$work/candidate.promoted.ll"

extract_fn "$work/baseline.promoted.ll" leanllvm_comma_mask8 | strip_ir \
  > "$work/baseline.body.ll"
extract_fn "$work/candidate.promoted.ll" leanllvm_comma_mask8 | strip_ir \
  > "$work/candidate.body.ll"

check_shape "$work/baseline.body.ll"
check_shape "$work/candidate.body.ll"

emit "$here/baseline.ll" '; The baseline seam as emitted, in the fragment `LeanLLVM.Semantics` models.
;
;   clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone \
;     -I"$(lake env lean --print-prefix)/include" <Baseline.c body behind the
;     header'"'"'s own static-inline UInt64 primitives>
;   opt -passes='"'"'function(mem2reg),instnamer'"'"'
;
; then the verbatim `define` block of @leanllvm_comma_mask8, with the textual
; syntax listed in capture.sh removed.  The body is the source expression
; operation for operation: the parameter is XORed with the comma pattern, masked
; against 0x7F.., given the 0x7F.. bias, OR-ed with the XOR word, complemented
; and masked against 0x80...
; LeanLLVM/Vellum/CommaMaskIR.lean proves this body returns `swar x` for every
; `x`, by rewriting it to `CommaMask.swar` (no bit-blasting).' \
  "$work/baseline.body.ll"

emit "$here/candidate.ll" '; The candidate seam as emitted, in the fragment `LeanLLVM.Semantics` models.
;
;   clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone candidate_lanes.c
;   opt -passes='"'"'function(mem2reg,simplifycfg),instnamer'"'"'
;
; candidate_lanes.c is probes/install/Candidate.lean'"'"'s eight-lane fold with
; the boxed-`Nat` counter written out lane by lane; the emission of the boxed
; loop itself (candidate.raw.ll) is outside the modelled fragment.  Same
; textual stripping as baseline.ll; `simplifycfg` folded each lane'"'"'s diamond
; back into the `select` the source wrote.
; LeanLLVM/Vellum/CommaMaskIR.lean proves this body returns `byteLoop x` for
; every `x`, by rewriting it to the fold in `CommaMask.byteLoop` (no
; bit-blasting).' "$work/candidate.body.ll"

# --- both fixtures are still valid LLVM IR --------------------------------

for f in baseline.ll candidate.ll; do
  opt -passes=verify -disable-output "$here/$f"
  echo "capture: $f verifies"
done

echo "capture: wrote probes/install/ir/{baseline,candidate}{,.raw}.ll and baseline.o1.ll"
