/-
`num_d8_el1`'s emitted body, pinned, and the eight-digit test it computes.

`JsonNumFastAssumed` states the conversion's callee half as one value,
`NumFastCalleesAnswered`: the walk's `Calls` selection answers `num_d8_el1`,
`num_el_el1` and `stk_mul_u64` with their measured model, and the content that
the compiled bodies behave as that model is the trust statement the value names.
`JsonStage2NumFastCalls` supplies the model — `numD8Answer` for the eight-digit
reader — but no `define` for any of the three existed under `probes/` or
`kernel/`, so nothing in the tree said what the emitted text *is*.

This module is the first of the three.  `probes/install/ir/capture-stage2-callees.sh`
captures the three bodies from `kernel/json/stage2.c` at the measured compiler
line (the helper capture's transform, its strip and its compiler line, with
`stk_mul_u64` marked `noinline` as the twelve helpers already are), and
`stage2.callees.tsv` records each one's shape: `num_d8_el1` is three blocks and
sixteen instructions (nineteen instruction lines), `stk_mul_u64` eight blocks and
eighty-eight lines, and `num_el_el1` six blocks and forty-one lines that call
`el_exact`/`el_pack` out of line and index the module-level `EPOW` table.

**What this module establishes.**  The pin — `numD8Src` is the fixture,
`firstFunction` of it is `numD8Body`, block by block and instruction by
instruction, with a mutated-text control so the equality is about the file rather
than a search — and the pieces of the body's *test*, in the model's vocabulary:

* `numD8_natToBytes_byte` / `numD8_bitcast_lane` — the eight bytes `numD8Answer`
  reads, the eight `i64` bytes the body loads, and the sixteen lanes the two
  `madd` calls consume are one list: lane `k` below eight is byte `k`, and the
  upper eight are zero;
* `numD8_lanesToNat_mask` — the mask `%2 &&& 0xFF` is all ones exactly when the
  first eight lane bits are, which is the fragment's own `lanesToNat_testBit`;
* `numD8_lane_test` — the emitted per-lane test `(b - '0') < 10` as `i8`
  arithmetic is the byte's being in `'0' … '9'`; `numD8_asciiDigit_iff` — the
  model's `asciiDigit` succeeds on exactly those bytes.

**What it is not.**  It is not the agreement theorem, and it is not yet the
composite test.  The branch's condition is
`numD8Test v = 1 ↔ ∀ k < 8, asciiDigit (numD8Byte v k) ≠ none`, which is the three
pieces above assembled through `d8Value`'s fold; and `numD8Answer`'s answer at the
entry state — the refusal branch's `0`, and the success branch's value, which is
the two `madd` calls as the decimal value of eight digit lanes — is not stated
here.  The emitted body's *run* (three blocks, the `if.end` arm's `madd` calls and
store, the `cleanup` phi) is not stated either.  What is here is everything the
branch step and the value step read, each proved of the pinned text.

**Why the fixture's lanes are the model's.**  The emission writes three literal
vectors with `poison` in trailing lanes — the `insertelement`'s overwritten lane
and the two `madd` constants' upper lanes — and the fragment's `Const.vector`
carries lane values, so the capture substitutes the defined lane 0 exactly as
`capture-escape.sh` does for the hex reader's two constants.  Each substitution
is sound where it is made: the overwritten lane is the one `insertelement` writes,
and the `madd` constants' upper lanes feed result lanes the body never reads — the
observable is lanes 0 and 1 of the `pmadd.wd` result, which read lanes 0-3 of its
input and so lanes 0-7 of the `pmadd.ub.sw` result.  `stage2.callees.rewrites.tsv`
records every substitution.
-/
import LeanLLVM.Refinement.JsonStage2HelperIR
import LeanLLVM.Refinement.JsonStage2NumFastCalls
import LeanLLVM.Refinement.JsonEscapeIntrinsics

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonEscapeIntrinsics

/-! ### The fixture and the body -/

/-- The captured body, as `capture-stage2-callees.sh` writes it. -/
def numD8Src : String :=
  include_str "../../probes/install/ir/stage2.callee.num_d8_el1.ll"

/-- `@num_d8_el1`, as the fixture parses.  Generated from the parse by
`capture-stage2-callees.sh --emit-pins`; the `#guard` below holds it to the
fixture. -/
def numD8EntryInstrs : List Instr :=
  [
    Instr.load "%0" (Ty.int 64) (Operand.reg "%p"),
    Instr.insertelement "%vecinit1.i" 2 64 (Operand.imm (Const.vector 64 [0x0000000000000000#64, 0x0000000000000000#64])) (Operand.reg "%0") (Operand.imm (Const.int 64 0x0000000000000000#64)),
    Instr.vecBitcast "%1" 2 64 16 8 (Operand.reg "%vecinit1.i"),
    Instr.binopVec "%sub.i" (BinOp.add) 16 8 (Operand.reg "%1") (Operand.imm (Const.splat 16 8 0xd0#8)),
    Instr.icmpVec "%cmp.i" (IPred.ult) 16 8 (Operand.reg "%sub.i") (Operand.imm (Const.splat 16 8 0x0a#8)),
    Instr.bitcastMask "%2" 16 (Operand.reg "%cmp.i"),
    Instr.binop "%3" (BinOp.and) 16 (Operand.reg "%2") (Operand.imm (Const.int 16 0x00ff#16)),
    Instr.icmp "%cmp.not" (IPred.eq) 16 (Operand.reg "%3") (Operand.imm (Const.int 16 0x00ff#16))]

/-- The refusal arm's call block: the two `madd` calls, the two lane reads, the
`* 10000 +` and the store. -/
def numD8IfEndInstrs : List Instr :=
  [
    Instr.call "%4" (Ty.vec 8 (Ty.int 16)) "llvm.x86.ssse3.pmadd.ub.sw.128" [((Ty.vec 16 (Ty.int 8)), (Operand.reg "%sub.i")),
                             ((Ty.vec 16 (Ty.int 8)), (Operand.imm (Const.vector 8 [0x0a#8, 0x01#8, 0x0a#8, 0x01#8, 0x0a#8, 0x01#8, 0x0a#8, 0x01#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8])))],
    Instr.call "%5" (Ty.vec 4 (Ty.int 32)) "llvm.x86.sse2.pmadd.wd" [((Ty.vec 8 (Ty.int 16)), (Operand.reg "%4")),
                             ((Ty.vec 8 (Ty.int 16)), (Operand.imm (Const.vector 16 [0x0064#16, 0x0001#16, 0x0064#16, 0x0001#16, 0x0000#16, 0x0000#16, 0x0000#16, 0x0000#16])))],
    Instr.extractelement "%vecext.i" 4 32 (Operand.reg "%5") (Operand.imm (Const.int 64 0x0000000000000000#64)),
    Instr.binop "%mul" (BinOp.mul) 32 (Operand.reg "%vecext.i") (Operand.imm (Const.int 32 0x00002710#32)),
    Instr.extractelement "%6" 4 32 (Operand.reg "%5") (Operand.imm (Const.int 64 0x0000000000000001#64)),
    Instr.binop "%add" (BinOp.add) 32 (Operand.reg "%mul") (Operand.reg "%6"),
    Instr.store (Ty.int 32) (Operand.reg "%add") (Operand.reg "%val")]

/-- The merge block: the returned word. -/
def numD8CleanupInstrs : List Instr :=
  [
    Instr.phi "%retval.0" (Ty.int 32) [("if.end", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("entry", (Operand.imm (Const.int 32 0x00000000#32)))]]

/-- `@num_d8_el1`, as `probes/install/ir/stage2.callee.num_d8_el1.ll` parses. -/
def numD8Body : Function :=
  { name := "num_d8_el1",
    retTy := (Ty.int 32),
    params := [("%p", Ty.ptr),
               ("%val", Ty.ptr)],
    blocks := [
      { name := "entry", instrs := numD8EntryInstrs,
        term := Term.condbr (Operand.reg "%cmp.not") "if.end" "cleanup" },
      { name := "if.end", instrs := numD8IfEndInstrs, term := Term.br "cleanup" },
      { name := "cleanup", instrs := numD8CleanupInstrs,
        term := Term.ret (Ty.int 32) (some (Operand.reg "%retval.0")) }] }

/- The pin: the fixture parses to the literal above. -/
#guard decide (firstFunction numD8Src = some numD8Body)

/- The control: the same fixture with the tier-1 multiplier changed parses, and
it is not the pinned body, so the equality above is about the text rather than
about a search that would accept anything. -/
def numD8SrcMutated : String := numD8Src.replace ", 10000" ", 10001"

#guard parses numD8SrcMutated
#guard decide (firstFunction numD8SrcMutated ≠ some numD8Body)

/- The shape `stage2.callees.tsv` records, in the inventory's own vocabulary.
`stage2.callees.tsv` counts instruction *lines* (19); the pin's own count is the
parsed instructions, which is what the body literal states. -/
#guard decide
  ((numD8Body.name, numD8Body.blocks.length,
      (numD8Body.blocks.flatMap (·.instrs)).length, numD8Body.params.length) =
    ("num_d8_el1", 3, 16, 2))

/- The two `madd` spellings are the fixture's own symbols.  The two constants'
trailing lanes are the capture's substituted zeros, and the control is that the
body records no `poison` at all. -/
#guard hasSubstr numD8Src "@llvm.x86.ssse3.pmadd.ub.sw.128"
#guard hasSubstr numD8Src "@llvm.x86.sse2.pmadd.wd"
#guard !hasSubstr numD8Src "i8 poison"
#guard hasSubstr numD8Src "i8 0, i8 0, i8 0, i8 0, i8 0>"

/-! ### The block pins

Each block's run, read from the literal rather than from a re-reading of the
fixture's text: the three equations are what the branch proofs below consume. -/

theorem numD8_findBlock_entry :
    numD8Body.findBlock "entry" =
      some ⟨"entry", numD8EntryInstrs,
        Term.condbr (Operand.reg "%cmp.not") "if.end" "cleanup"⟩ := by decide

theorem numD8_findBlock_ifEnd :
    numD8Body.findBlock "if.end" =
      some ⟨"if.end", numD8IfEndInstrs, Term.br "cleanup"⟩ := by decide

theorem numD8_findBlock_cleanup :
    numD8Body.findBlock "cleanup" =
      some ⟨"cleanup", numD8CleanupInstrs,
        Term.ret (Ty.int 32) (some (Operand.reg "%retval.0"))⟩ := by decide

/-! ### The call environment

The body calls the two `madd` spellings and nothing else.  `escapeCalls` already
answers them at the arities and lane widths the fixture uses, with the models
`BitLanes` proves against the instructions, so the callee's environment is that
one rather than a second copy of it. -/

/-- The callee's `Calls`: the escape unit's environment, which answers the two
`madd` spellings the body calls. -/
def numD8Calls : Calls := escapeCalls

/-! ### The eight bytes and their lanes

The body reads eight bytes as one `i64`, inserts the word into a two-lane vector
and reinterprets it as sixteen bytes.  Lane `k` below eight is byte `k` of the
little-endian word; the upper eight are zero, which is why the mask's high bits
are unaffected.  `numD8Byte` is that byte, and the lemmas below are the two ways
the proof reaches it: through `natToBytes` (the model's own encoding of the
loaded word) and through the bitcast's lane list. -/

/-- Byte `k` of the little-endian word, as a natural below 256. -/
def numD8ByteNat (v : BitVec 64) (k : Nat) : Nat := v.toNat / 256 ^ k % 256

/-- Byte `k` of the little-endian word. -/
def numD8Byte (v : BitVec 64) (k : Nat) : UInt8 := UInt8.ofNat (numD8ByteNat v k)

/-- The byte's natural reading is the definition's: `UInt8.ofNat` truncates and
`numD8ByteNat` is already below 256. -/
theorem numD8Byte_toNat (v : BitVec 64) (k : Nat) :
    (numD8Byte v k).toNat = numD8ByteNat v k := by
  simp [numD8Byte, numD8ByteNat, Nat.mod_mod]

/-- The model's encoding of the loaded word holds, at `k`, the byte the word's
`k`-th little-endian position spells.  The right-hand side is written modulo 256
so the step never needs `UInt8.ofNat`'s invariance under its own reduction. -/
theorem numD8_natToBytes_getElem? (v n k : Nat) (hk : k < n) :
    (natToBytes v n)[k]? = some (UInt8.ofNat (v / 256 ^ k % 256)) := by
  induction n generalizing v k with
  | zero => omega
  | succ m ih =>
      cases k with
      | zero =>
          cases m with
          | zero => simp [natToBytes, Nat.div_one, Nat.mod_mod]
          | succ _ => simp [natToBytes, Nat.div_one, Nat.mod_mod]
      | succ j =>
          simp only [natToBytes, List.getElem?_cons_succ]
          rw [ih (v / 256) j (by omega)]
          congr 3
          rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.pow_succ]

/-- The model's encoding holds the body's bytes: `numD8Answer` reads the same
eight-byte list the body loaded. -/
theorem numD8_natToBytes_byte {v : BitVec 64} {k : Nat} (hk : k < 8) :
    (natToBytes v.toNat 8)[k]? = some (numD8Byte v k) := by
  rw [numD8_natToBytes_getElem? v.toNat 8 k hk]
  rfl

/-- `2 ^ (k * 8)` is `256 ^ k`: the byte width's own power. -/
theorem numD8_pow (k : Nat) : 2 ^ (k * 8) = 256 ^ k := by
  rw [Nat.mul_comm, Nat.pow_mul, show (2 : Nat) ^ 8 = 256 from by decide]

/-- The bitcast's lane `k`, below eight, is byte `k`: `unpackLanes` reads the
word's bit `k * 8` and the byte's own value is its low eight bits. -/
theorem numD8_lane {v : BitVec 64} {k : Nat} (hk : k < 8) :
    (unpackLanes 8 16 v.toNat)[k]? = some (BitVec.ofNat 8 (numD8ByteNat v k)) := by
  have hlt : k < 16 := by omega
  simp only [unpackLanes, List.getElem?_map, List.getElem?_range, hlt, if_pos]
  apply congrArg some
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, numD8ByteNat, Nat.mod_mod, numD8_pow]

/-- The lane a `bitcast <2 x i64> … to <16 x i8>` of the loaded word produces:
lane `k` below eight is the body's byte `k`. -/
theorem numD8_bitcast_lane {v : BitVec 64} {k : Nat} (hk : k < 8) :
    (bitcastVecLanes 8 16 [v, 0])[k]? = some (BitVec.ofNat 8 (numD8ByteNat v k)) := by
  have hp : packLanes ([v, 0] : List (BitVec 64)) = v.toNat := by simp [packLanes]
  rw [bitcastVecLanes, hp]
  exact numD8_lane hk

/-! ### The mask and the test

`%2` is `bitcastMask`'s packing of the sixteen lane bits, `%3` its low byte, and
`%cmp.not` the equality of that byte with `0xFF`.  The bit-level statement — the
low byte is all ones exactly when lanes 0-7 are — is the fragment's
`lanesToNat_testBit`, and the byte-level one is exhausted over the sixteen-bit
word. -/

/-- A sixteen-bit word's low byte is `0xFF` exactly when its eight low bits are
set.  Exhausted over the word; the statement is the `and`'s mask in the bit
reading `getLsbD` gives. -/
theorem numD8_mask255 (w : BitVec 16) :
    (w &&& 0x00ff#16 = 0x00ff#16) ↔ ∀ k : Fin 8, w.getLsbD k = true := by
  revert w
  decide

/-- The packed lanes' low byte is `0xFF` exactly when lanes 0-7 are set.  The
list's length is not a hypothesis: a longer list's extra bits are masked off by
the `and`, and a shorter one's absent lanes are clear in both readings. -/
theorem numD8_lanesToNat_mask (l : List (BitVec 1)) :
    ((BitVec.ofNat 16 (lanesToNat l)) &&& 0x00ff#16 = 0x00ff#16) ↔
      ∀ k : Nat, k < 8 → l[k]? = some (1 : BitVec 1) := by
  rw [numD8_mask255]
  constructor
  · intro h k hk
    have hk16 : k < 16 := by omega
    have hbit := h ⟨k, hk⟩
    rw [BitVec.getLsbD_ofNat] at hbit
    simp only [hk16, decide_true, Bool.true_and] at hbit
    rw [lanesToNat_testBit] at hbit
    simpa using hbit
  · intro h k
    have hk16 : (k : Nat) < 16 := by omega
    rw [BitVec.getLsbD_ofNat]
    simp only [hk16, decide_true, Bool.true_and]
    rw [lanesToNat_testBit, h k k.isLt]

/-! ### The refusal test, in the model's vocabulary

`d8Value` succeeds exactly when every byte is an ASCII digit; the body's branch
takes `if.end` exactly then.  The two lane-level facts below are what the
equivalence consumes: the model's `asciiDigit` at a byte, and the body's
`(b - '0') < 10` at a byte lane. -/

/-- One byte is a digit, in the model's reading: `asciiDigit` succeeds exactly
for `'0' … '9'`. -/
theorem numD8_asciiDigit_iff (b : UInt8) :
    asciiDigit b ≠ none ↔ 0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39 := by
  unfold asciiDigit
  by_cases h : 0x30 ≤ b ∧ b ≤ 0x39
  · rw [if_pos h]
    have h1 : 0x30 ≤ b.toNat := UInt8.le_iff_toNat_le.mp h.1
    have h2 : b.toNat ≤ 0x39 := UInt8.le_iff_toNat_le.mp h.2
    simp [h1, h2]
  · rw [if_neg h]
    simp only [ne_eq, not_true_eq_false]
    constructor
    · intro hf
      exact hf.elim
    · intro hc
      exact h ⟨UInt8.le_iff_toNat_le.mpr hc.1, UInt8.le_iff_toNat_le.mpr hc.2⟩

/-- The body's per-lane test at a byte: `(b - '0') < 10` as `i8` arithmetic is the
byte's being an ASCII digit.  The byte is the lane's `toNat`, so the two sides
meet at `natToBytes`'s byte. -/
theorem numD8_lane_test (b : BitVec 8) :
    evalICmp .ult (b + 0xd0#8) 0x0a#8 = (1 : BitVec 1) ↔
      0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39 := by
  revert b
  decide

/-! ### Axiom footprints

Pinned with `#guard_msgs` so the build checks the footprints rather than printing
them.  The instrument is `#print axioms`; a declaration proved with `sorry`
prints `sorryAx` under the same command, which is the control the tree records. -/

/-- info: 'LeanLLVM.Refinement.numD8Byte_toNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms numD8Byte_toNat

/-- info: 'LeanLLVM.Refinement.numD8_natToBytes_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numD8_natToBytes_byte

/-- info: 'LeanLLVM.Refinement.numD8_bitcast_lane' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numD8_bitcast_lane

/-- info: 'LeanLLVM.Refinement.numD8_lanesToNat_mask' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numD8_lanesToNat_mask

/-- info: 'LeanLLVM.Refinement.numD8_asciiDigit_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms numD8_asciiDigit_iff

/-- info: 'LeanLLVM.Refinement.numD8_lane_test' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numD8_lane_test

end LeanLLVM.Refinement
