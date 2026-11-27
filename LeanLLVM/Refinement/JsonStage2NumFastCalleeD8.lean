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

**What the module now establishes.**  Everything the *arm* needs is proved of
the pinned text, not assumed:

* the branch's condition is `d8Value`'s own test — `numD8Test_iff` states
  `numD8Test v = 1 ↔ d8Value (natToBytes v.toNat 8) ≠ none`, the three lane pieces
  assembled through `d8Value`'s fold (`numD8_bits_range`, `numD8_asciiDigit_bn`,
  and `d8Value_eq_none_of_digit_none` for the converse);
* the `if.end` arm's value is the fold's value — `numD8UbSw_eq`/`numD8Wd_eq` read
  the two `madd` calls lane by lane, and `numD8_d8Value_of_digits` composes them
  with `d8Value`, giving `d8Value (natToBytes v.toNat 8) = some (numD8Product v)`
  on a digit word, with `numD8Product_lt` bounding it below `2 ^ 32` so the store
  is the model's four bytes;
* the body's run is stated — `numD8_run_success` and `numD8_run_refusal` are the
  three- and two-step `runFuel` runs of `numD8Body` from the selection's entry
  state, at `numD8Calls` (the escape unit's environment, which answers the two
  `madd` spellings), reaching the model's return and memory;
* the arm is the model — `numD8BodyCalls_num_d8` states that the environment whose
  `num_d8_el1` is this body's run answers exactly `numD8Answer` at the two pointer
  arguments, so the site's `ub` (`s2HelperCalls_num_d8_el1`) can be replaced by
  the model, which is what `NumFastCalleesAnswered` records.

What is *not* here is the other two callees (`num_el_el1`, `stk_mul_u64`) and the
agreement of the whole walk; this module is one of the three bodies the callee
half's discharge path names.

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
import LeanLLVM.Refinement.BlockEvalVector
import LeanLLVM.Refinement.JsonEntrySteps

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonEscapeIntrinsics
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BlockEvalVector
open LeanLLVM.Refinement.BitLanes

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

/-! ### Stage 1 -/

def numD8LaneNat (v : BitVec 64) (k : Nat) : Nat := v.toNat / 2 ^ (k * 8)

def numD8Lanes (v : BitVec 64) : List (BitVec 8) :=
  (List.range 16).map fun k => BitVec.ofNat 8 (numD8LaneNat v k)

def numD8SubLane (v : BitVec 64) (k : Nat) : BitVec 8 :=
  BitVec.ofNat 8 (numD8LaneNat v k) + 0xd0

def numD8Sub (v : BitVec 64) : List (BitVec 8) :=
  (List.range 16).map (numD8SubLane v)

def numD8BitLane (v : BitVec 64) (k : Nat) : BitVec 1 :=
  evalICmp .ult (numD8SubLane v k) 0x0a#8

def numD8Bits (v : BitVec 64) : List (BitVec 1) :=
  (List.range 16).map (numD8BitLane v)

def numD8Mask (v : BitVec 64) : BitVec 16 :=
  BitVec.ofNat 16 (lanesToNat (numD8Bits v))

def numD8Masked (v : BitVec 64) : BitVec 16 := numD8Mask v &&& 0x00ff#16

def numD8Test (v : BitVec 64) : BitVec 1 :=
  evalICmp .eq (numD8Masked v) 0x00ff#16

def numD8C8 : List (BitVec 8) :=
  [0x0a#8, 0x01#8, 0x0a#8, 0x01#8, 0x0a#8, 0x01#8, 0x0a#8, 0x01#8,
   0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8]

def numD8C16 : List (BitVec 16) :=
  [0x0064#16, 0x0001#16, 0x0064#16, 0x0001#16,
   0x0000#16, 0x0000#16, 0x0000#16, 0x0000#16]

def numD8UbSw (v : BitVec 64) : List (BitVec 16) := pmaddUbSw (numD8Sub v) numD8C8

def numD8Wd (v : BitVec 64) : List (BitVec 32) := pmaddWd (numD8UbSw v) numD8C16

def numD8Dec (v : BitVec 64) : Nat :=
  (numD8ByteNat v 0 - 0x30) * 10000000 + (numD8ByteNat v 1 - 0x30) * 1000000 +
  (numD8ByteNat v 2 - 0x30) * 100000 + (numD8ByteNat v 3 - 0x30) * 10000 +
  (numD8ByteNat v 4 - 0x30) * 1000 + (numD8ByteNat v 5 - 0x30) * 100 +
  (numD8ByteNat v 6 - 0x30) * 10 + (numD8ByteNat v 7 - 0x30)

def numD8Product (v : BitVec 64) : Nat :=
  ((numD8Wd v).getD 0 0).toNat * 10000 + ((numD8Wd v).getD 1 0).toNat

theorem numD8Lanes_bitcast (v : BitVec 64) :
    bitcastVecLanes 8 16 [v, 0] = numD8Lanes v := by
  unfold bitcastVecLanes numD8Lanes numD8LaneNat unpackLanes
  rw [show packLanes [v, 0] = v.toNat from by simp [packLanes]]

theorem numD8Lanes_length (v : BitVec 64) : (numD8Lanes v).length = 16 := by
  simp [numD8Lanes]

theorem numD8Lanes_getElem? (v : BitVec 64) {k : Nat} (hk : k < 16) :
    (numD8Lanes v)[k]? = some (BitVec.ofNat 8 (numD8LaneNat v k)) := by
  simp only [numD8Lanes, List.getElem?_map, List.getElem?_range, hk, if_pos, Option.map_some]

theorem numD8Sub_getElem? (v : BitVec 64) {k : Nat} (hk : k < 16) :
    (numD8Sub v)[k]? = some (numD8SubLane v k) := by
  simp only [numD8Sub, List.getElem?_map, List.getElem?_range, hk, if_pos, Option.map_some]

theorem numD8Bits_getElem? (v : BitVec 64) {k : Nat} (hk : k < 16) :
    (numD8Bits v)[k]? = some (numD8BitLane v k) := by
  simp only [numD8Bits, List.getElem?_map, List.getElem?_range, hk, if_pos, Option.map_some]

theorem numD8LaneNat_high (v : BitVec 64) {k : Nat} (hk : 8 ≤ k) :
    numD8LaneNat v k = 0 := by
  unfold numD8LaneNat
  apply Nat.div_eq_of_lt
  have h1 : (2 : Nat) ^ 64 ≤ 2 ^ (k * 8) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : v.toNat < 2 ^ 64 := v.isLt
  omega

theorem ofNat8_mod (x : Nat) : BitVec.ofNat 8 x = BitVec.ofNat 8 (x % 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (2 : Nat) ^ 8 = 256 from by decide, Nat.mod_mod]

theorem numD8SubLane_byte (v : BitVec 64) {k : Nat} (hk : k < 8) :
    numD8SubLane v k = BitVec.ofNat 8 (numD8ByteNat v k) + 0xd0 := by
  unfold numD8SubLane numD8LaneNat
  rw [numD8_pow, ofNat8_mod]
  rfl

theorem numD8SubLane_zero (v : BitVec 64) {k : Nat} (hk : 8 ≤ k) :
    numD8SubLane v k = 0xd0 := by
  unfold numD8SubLane
  rw [numD8LaneNat_high v hk]
  simp

theorem numD8Sub_literal (v : BitVec 64) :
    numD8Sub v =
      [numD8SubLane v 0, numD8SubLane v 1, numD8SubLane v 2, numD8SubLane v 3,
       numD8SubLane v 4, numD8SubLane v 5, numD8SubLane v 6, numD8SubLane v 7,
       numD8SubLane v 8, numD8SubLane v 9, numD8SubLane v 10, numD8SubLane v 11,
       numD8SubLane v 12, numD8SubLane v 13, numD8SubLane v 14, numD8SubLane v 15] :=
  rfl

theorem numD8Sub_literal_byte (v : BitVec 64) :
    numD8Sub v =
      [BitVec.ofNat 8 (numD8ByteNat v 0) + 0xd0, BitVec.ofNat 8 (numD8ByteNat v 1) + 0xd0,
       BitVec.ofNat 8 (numD8ByteNat v 2) + 0xd0, BitVec.ofNat 8 (numD8ByteNat v 3) + 0xd0,
       BitVec.ofNat 8 (numD8ByteNat v 4) + 0xd0, BitVec.ofNat 8 (numD8ByteNat v 5) + 0xd0,
       BitVec.ofNat 8 (numD8ByteNat v 6) + 0xd0, BitVec.ofNat 8 (numD8ByteNat v 7) + 0xd0,
       0xd0, 0xd0, 0xd0, 0xd0, 0xd0, 0xd0, 0xd0, 0xd0] := by
  rw [numD8Sub_literal]
  rw [numD8SubLane_byte v (k := 0) (by decide), numD8SubLane_byte v (k := 1) (by decide),
    numD8SubLane_byte v (k := 2) (by decide), numD8SubLane_byte v (k := 3) (by decide),
    numD8SubLane_byte v (k := 4) (by decide), numD8SubLane_byte v (k := 5) (by decide),
    numD8SubLane_byte v (k := 6) (by decide), numD8SubLane_byte v (k := 7) (by decide),
    numD8SubLane_zero v (k := 8) (by decide), numD8SubLane_zero v (k := 9) (by decide),
    numD8SubLane_zero v (k := 10) (by decide), numD8SubLane_zero v (k := 11) (by decide),
    numD8SubLane_zero v (k := 12) (by decide), numD8SubLane_zero v (k := 13) (by decide),
    numD8SubLane_zero v (k := 14) (by decide), numD8SubLane_zero v (k := 15) (by decide)]

theorem numD8Sub_of_lanes (v : BitVec 64) :
    (numD8Lanes v).map (fun x => x + 0xd0) = numD8Sub v := by
  simp only [numD8Lanes, numD8Sub, numD8SubLane, List.map_map]
  rfl

theorem numD8BitLane_byte (v : BitVec 64) {k : Nat} (hk : k < 8) :
    numD8BitLane v k =
      evalICmp .ult (BitVec.ofNat 8 (numD8ByteNat v k) + 0xd0) 0x0a#8 := by
  simp only [numD8BitLane, numD8SubLane_byte v hk]

theorem numD8Bits_of_lanes (v : BitVec 64) :
    (numD8Sub v).map (fun x => evalICmp .ult x 0x0a#8) = numD8Bits v := by
  simp only [numD8Sub, numD8Bits, numD8BitLane, List.map_map]
  rfl

theorem numD8Test_iff_lanes (v : BitVec 64) :
    numD8Test v = 1 ↔ ∀ k, k < 8 → (numD8Bits v)[k]? = some (1 : BitVec 1) := by
  unfold numD8Test numD8Masked numD8Mask
  rw [evalICmp_eq_one_iff]
  exact numD8_lanesToNat_mask (numD8Bits v)

/-- The body's per-lane test, at a byte's own natural. -/
theorem numD8_lane_test_bn (bn : Nat) (hbn : bn < 256) :
    evalICmp .ult (BitVec.ofNat 8 bn + (0xd0 : BitVec 8)) 0x0a#8 = (1 : BitVec 1) ↔
      0x30 ≤ bn ∧ bn ≤ 0x39 := by
  have h : (BitVec.ofNat 8 bn).toNat = bn := by
    rw [BitVec.toNat_ofNat, show (2 : Nat) ^ 8 = 256 from by decide, Nat.mod_eq_of_lt hbn]
  rw [show (BitVec.ofNat 8 bn + (0xd0 : BitVec 8)) = (BitVec.ofNat 8 bn + 0xd0#8) from rfl,
    numD8_lane_test, h]

/-- A lane's test is the byte's range, at `%cmp.i`. -/
theorem numD8_bits_range (v : BitVec 64) {k : Nat} (hk : k < 8) :
    (numD8Bits v)[k]? = some (1 : BitVec 1) ↔
      0x30 ≤ numD8ByteNat v k ∧ numD8ByteNat v k ≤ 0x39 := by
  rw [numD8Bits_getElem? v (by omega), numD8BitLane_byte v hk]
  simp only [Option.some.injEq]
  exact numD8_lane_test_bn _ (Nat.mod_lt _ (by decide))

/-- The model's digit test at a byte, in the byte's natural. -/
theorem numD8_asciiDigit_bn (v : BitVec 64) (k : Nat) :
    asciiDigit (numD8Byte v k) ≠ none ↔
      0x30 ≤ numD8ByteNat v k ∧ numD8ByteNat v k ≤ 0x39 := by
  rw [numD8_asciiDigit_iff, numD8Byte_toNat]

theorem numD8_digits_of_test (v : BitVec 64) (h : numD8Test v = 1) :
    ∀ k, k < 8 → 0x30 ≤ numD8ByteNat v k ∧ numD8ByteNat v k ≤ 0x39 := by
  have hb := (numD8Test_iff_lanes v).mp h
  intro k hk
  exact (numD8_bits_range v hk).mp (hb k hk)

theorem d8Value_eq_none_of_digit_none (bs : List UInt8) {k : Nat} {b : UInt8}
    (hk : bs[k]? = some b) (h : asciiDigit b = none) : d8Value bs = none := by
  induction bs generalizing k with
  | nil => simp at hk
  | cons b' rest ih =>
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          cases hb' : asciiDigit b'
          · simp only [d8Value, hb']
          · rw [h] at hb'
            exact absurd hb' (by simp)
      | succ j =>
          have hk' : rest[j]? = some b := by simpa using hk
          have hrs : d8Value rest = none := ih hk'
          cases hb' : asciiDigit b'
          · simp only [d8Value, hb', hrs]
          · simp only [d8Value, hb', hrs]

theorem d8Value_digit_ne_none (bs : List UInt8) {k : Nat} {b : UInt8}
    (h : d8Value bs ≠ none) (hk : bs[k]? = some b) : asciiDigit b ≠ none := by
  intro hb
  exact h (d8Value_eq_none_of_digit_none bs hk hb)

theorem numD8_bytes_getD (v : BitVec 64) {k : Nat} (hk : k < 8) :
    (natToBytes v.toNat 8).getD k 0 = numD8Byte v k := by
  rw [List.getD_eq_getElem?_getD, numD8_natToBytes_byte hk]
  rfl

theorem list_of_length_eight {α : Type} (l : List α) (h : l.length = 8) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7, l = [a0, a1, a2, a3, a4, a5, a6, a7] := by
  match l, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7], _ =>
      exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩
  | [], h => exact absurd h (by simp)
  | [_], h => exact absurd h (by simp)
  | [_, _], h => exact absurd h (by simp)
  | [_, _, _], h => exact absurd h (by simp)
  | [_, _, _, _], h => exact absurd h (by simp)
  | [_, _, _, _, _], h => exact absurd h (by simp)
  | [_, _, _, _, _, _], h => exact absurd h (by simp)
  | [_, _, _, _, _, _, _], h => exact absurd h (by simp)
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => exact absurd h (by simp)

theorem asciiDigit_eq_sub (b : UInt8) (h0 : 0x30 ≤ b.toNat) (h1 : b.toNat ≤ 0x39) :
    asciiDigit b = some (b.toNat - 0x30) := by
  unfold asciiDigit
  rw [if_pos]
  exact ⟨UInt8.le_iff_toNat_le.mpr h0, UInt8.le_iff_toNat_le.mpr h1⟩

/-- A digit lane's `toNat`, at a byte lane of the bitcast. -/
theorem numD8ByteLane_toNat (v : BitVec 64) {k : Nat} (hk : k < 8)
    (h0 : 0x30 ≤ numD8ByteNat v k) (h1 : numD8ByteNat v k ≤ 0x39) :
    (BitVec.ofNat 8 (numD8ByteNat v k) + (0xd0 : BitVec 8)).toNat =
      numD8ByteNat v k - 0x30 := by
  have hbn : numD8ByteNat v k % 256 = numD8ByteNat v k :=
    Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    show (0xd0 : BitVec 8).toNat = 208 from by decide,
    show (2 : Nat) ^ 8 = 256 from by decide, hbn]
  rw [show numD8ByteNat v k + 208 = (numD8ByteNat v k - 0x30) + 256 * 1 from by omega,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-! #### The multiply-adds' values -/

private theorem ofInt_toNat_of_range {w : Nat} {k : Int} (h0 : 0 ≤ k)
    (h1 : k < (2 ^ w : Int)) : (BitVec.ofInt w k).toNat = k.toNat := by
  rw [BitVec.toNat_ofInt]
  exact congrArg Int.toNat (Int.emod_eq_of_lt h0 h1)

private theorem ofInt_eq_ofNat_of_range {w : Nat} {k : Int} (h0 : 0 ≤ k)
    (h1 : k < (2 ^ w : Int)) : BitVec.ofInt w k = BitVec.ofNat w k.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [ofInt_toNat_of_range h0 h1, BitVec.toNat_ofNat]
  have hk : k.toNat < 2 ^ w := by
    have hk' : (k.toNat : Int) < ((2 ^ w : Nat) : Int) := by
      rw [Int.toNat_of_nonneg h0]; exact h1
    omega
  exact (Nat.mod_eq_of_lt hk).symm

theorem numD8_ubsw_lane (x0 x1 : BitVec 8) (h0 : x0.toNat < 10) (h1 : x1.toNat < 10) :
    pmaddUbSwLane x0 x1 0x0a#8 0x01#8 = BitVec.ofNat 16 (10 * x0.toNat + x1.toNat) := by
  unfold pmaddUbSwLane
  rw [show (0x0a#8).toInt = 10 from by decide, show (0x01#8).toInt = 1 from by decide,
    satI16_of_range (by omega) (by omega), ofInt_eq_ofNat_of_range (by omega) (by omega)]
  rw [show (((x0.toNat : Int) * 10 + (x1.toNat : Int) * 1).toNat) = 10 * x0.toNat + x1.toNat
    from by omega]

theorem numD8_wd_lane (w0 w1 : BitVec 16) (h0 : w0.toNat < 100) (h1 : w1.toNat < 100) :
    pmaddWdLane w0 w1 0x0064#16 0x0001#16 =
      BitVec.ofNat 32 (100 * w0.toNat + w1.toNat) := by
  unfold pmaddWdLane
  rw [show (0x0064#16).toInt = 100 from by decide, show (0x0001#16).toInt = 1 from by decide]
  have i0 : w0.toInt = (w0.toNat : Int) := by rw [BitVec.toInt_eq_toNat_of_lt]; omega
  have i1 : w1.toInt = (w1.toNat : Int) := by rw [BitVec.toInt_eq_toNat_of_lt]; omega
  rw [i0, i1, ofInt_eq_ofNat_of_range (by omega) (by omega)]
  rw [show (((w0.toNat : Int) * 100 + (w1.toNat : Int) * 1).toNat) = 100 * w0.toNat + w1.toNat
    from by omega]

theorem numD8C8_eq : numD8C8 =
    [0x0a#8, 0x01#8, 0x0a#8, 0x01#8, 0x0a#8, 0x01#8, 0x0a#8, 0x01#8,
     0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8] := rfl

theorem numD8C16_eq : numD8C16 =
    [0x0064#16, 0x0001#16, 0x0064#16, 0x0001#16,
     0x0000#16, 0x0000#16, 0x0000#16, 0x0000#16] := rfl

theorem numD8UbSw_eq (v : BitVec 64)
    (hd : ∀ k, k < 8 → 0x30 ≤ numD8ByteNat v k ∧ numD8ByteNat v k ≤ 0x39) :
    numD8UbSw v =
      [BitVec.ofNat 16 (10 * (numD8ByteNat v 0 - 0x30) + (numD8ByteNat v 1 - 0x30)),
       BitVec.ofNat 16 (10 * (numD8ByteNat v 2 - 0x30) + (numD8ByteNat v 3 - 0x30)),
       BitVec.ofNat 16 (10 * (numD8ByteNat v 4 - 0x30) + (numD8ByteNat v 5 - 0x30)),
       BitVec.ofNat 16 (10 * (numD8ByteNat v 6 - 0x30) + (numD8ByteNat v 7 - 0x30)),
       0, 0, 0, 0] := by
  have f0 : numD8ByteNat v 0 ≤ 0x39 := (hd 0 (by decide)).2
  have f1 : numD8ByteNat v 1 ≤ 0x39 := (hd 1 (by decide)).2
  have f2 : numD8ByteNat v 2 ≤ 0x39 := (hd 2 (by decide)).2
  have f3 : numD8ByteNat v 3 ≤ 0x39 := (hd 3 (by decide)).2
  have f4 : numD8ByteNat v 4 ≤ 0x39 := (hd 4 (by decide)).2
  have f5 : numD8ByteNat v 5 ≤ 0x39 := (hd 5 (by decide)).2
  have f6 : numD8ByteNat v 6 ≤ 0x39 := (hd 6 (by decide)).2
  have f7 : numD8ByteNat v 7 ≤ 0x39 := (hd 7 (by decide)).2
  have d0 := numD8ByteLane_toNat v (k := 0) (by decide) (hd 0 (by decide)).1 (hd 0 (by decide)).2
  have d1 := numD8ByteLane_toNat v (k := 1) (by decide) (hd 1 (by decide)).1 (hd 1 (by decide)).2
  have d2 := numD8ByteLane_toNat v (k := 2) (by decide) (hd 2 (by decide)).1 (hd 2 (by decide)).2
  have d3 := numD8ByteLane_toNat v (k := 3) (by decide) (hd 3 (by decide)).1 (hd 3 (by decide)).2
  have d4 := numD8ByteLane_toNat v (k := 4) (by decide) (hd 4 (by decide)).1 (hd 4 (by decide)).2
  have d5 := numD8ByteLane_toNat v (k := 5) (by decide) (hd 5 (by decide)).1 (hd 5 (by decide)).2
  have d6 := numD8ByteLane_toNat v (k := 6) (by decide) (hd 6 (by decide)).1 (hd 6 (by decide)).2
  have d7 := numD8ByteLane_toNat v (k := 7) (by decide) (hd 7 (by decide)).1 (hd 7 (by decide)).2
  have l0 : pmaddUbSwLane (BitVec.ofNat 8 (numD8ByteNat v 0) + (0xd0 : BitVec 8))
      (BitVec.ofNat 8 (numD8ByteNat v 1) + (0xd0 : BitVec 8)) 0x0a#8 0x01#8 =
      BitVec.ofNat 16 (10 * (numD8ByteNat v 0 - 0x30) + (numD8ByteNat v 1 - 0x30)) := by
    rw [numD8_ubsw_lane _ _ (by rw [d0]; omega) (by rw [d1]; omega), d0, d1]
  have l1 : pmaddUbSwLane (BitVec.ofNat 8 (numD8ByteNat v 2) + (0xd0 : BitVec 8))
      (BitVec.ofNat 8 (numD8ByteNat v 3) + (0xd0 : BitVec 8)) 0x0a#8 0x01#8 =
      BitVec.ofNat 16 (10 * (numD8ByteNat v 2 - 0x30) + (numD8ByteNat v 3 - 0x30)) := by
    rw [numD8_ubsw_lane _ _ (by rw [d2]; omega) (by rw [d3]; omega), d2, d3]
  have l2 : pmaddUbSwLane (BitVec.ofNat 8 (numD8ByteNat v 4) + (0xd0 : BitVec 8))
      (BitVec.ofNat 8 (numD8ByteNat v 5) + (0xd0 : BitVec 8)) 0x0a#8 0x01#8 =
      BitVec.ofNat 16 (10 * (numD8ByteNat v 4 - 0x30) + (numD8ByteNat v 5 - 0x30)) := by
    rw [numD8_ubsw_lane _ _ (by rw [d4]; omega) (by rw [d5]; omega), d4, d5]
  have l3 : pmaddUbSwLane (BitVec.ofNat 8 (numD8ByteNat v 6) + (0xd0 : BitVec 8))
      (BitVec.ofNat 8 (numD8ByteNat v 7) + (0xd0 : BitVec 8)) 0x0a#8 0x01#8 =
      BitVec.ofNat 16 (10 * (numD8ByteNat v 6 - 0x30) + (numD8ByteNat v 7 - 0x30)) := by
    rw [numD8_ubsw_lane _ _ (by rw [d6]; omega) (by rw [d7]; omega), d6, d7]
  show pmaddUbSw (numD8Sub v) numD8C8 = _
  rw [numD8Sub_literal_byte v, numD8C8_eq]
  rw [pmaddUbSw_cons, pmaddUbSw_cons, pmaddUbSw_cons, pmaddUbSw_cons]
  have hz : pmaddUbSw [0xd0, 0xd0, 0xd0, 0xd0, 0xd0, 0xd0, 0xd0, 0xd0]
      [0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8] = [0, 0, 0, 0] := by
    decide
  rw [hz, l0, l1, l2, l3]

theorem numD8Wd_eq (v : BitVec 64)
    (hd : ∀ k, k < 8 → 0x30 ≤ numD8ByteNat v k ∧ numD8ByteNat v k ≤ 0x39) :
    numD8Wd v =
      [BitVec.ofNat 32 (100 * (10 * (numD8ByteNat v 0 - 0x30) + (numD8ByteNat v 1 - 0x30)) +
          (10 * (numD8ByteNat v 2 - 0x30) + (numD8ByteNat v 3 - 0x30))),
       BitVec.ofNat 32 (100 * (10 * (numD8ByteNat v 4 - 0x30) + (numD8ByteNat v 5 - 0x30)) +
          (10 * (numD8ByteNat v 6 - 0x30) + (numD8ByteNat v 7 - 0x30))),
       0, 0] := by
  have e0 : numD8ByteNat v 0 - 0x30 ≤ 9 := by have := (hd 0 (by decide)).2; omega
  have e1 : numD8ByteNat v 1 - 0x30 ≤ 9 := by have := (hd 1 (by decide)).2; omega
  have e2 : numD8ByteNat v 2 - 0x30 ≤ 9 := by have := (hd 2 (by decide)).2; omega
  have e3 : numD8ByteNat v 3 - 0x30 ≤ 9 := by have := (hd 3 (by decide)).2; omega
  have e4 : numD8ByteNat v 4 - 0x30 ≤ 9 := by have := (hd 4 (by decide)).2; omega
  have e5 : numD8ByteNat v 5 - 0x30 ≤ 9 := by have := (hd 5 (by decide)).2; omega
  have e6 : numD8ByteNat v 6 - 0x30 ≤ 9 := by have := (hd 6 (by decide)).2; omega
  have e7 : numD8ByteNat v 7 - 0x30 ≤ 9 := by have := (hd 7 (by decide)).2; omega
  have s0 : (BitVec.ofNat 16 (10 * (numD8ByteNat v 0 - 0x30) + (numD8ByteNat v 1 - 0x30))).toNat
      = 10 * (numD8ByteNat v 0 - 0x30) + (numD8ByteNat v 1 - 0x30) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have s1 : (BitVec.ofNat 16 (10 * (numD8ByteNat v 2 - 0x30) + (numD8ByteNat v 3 - 0x30))).toNat
      = 10 * (numD8ByteNat v 2 - 0x30) + (numD8ByteNat v 3 - 0x30) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have s2 : (BitVec.ofNat 16 (10 * (numD8ByteNat v 4 - 0x30) + (numD8ByteNat v 5 - 0x30))).toNat
      = 10 * (numD8ByteNat v 4 - 0x30) + (numD8ByteNat v 5 - 0x30) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have s3 : (BitVec.ofNat 16 (10 * (numD8ByteNat v 6 - 0x30) + (numD8ByteNat v 7 - 0x30))).toNat
      = 10 * (numD8ByteNat v 6 - 0x30) + (numD8ByteNat v 7 - 0x30) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have l0 : pmaddWdLane (BitVec.ofNat 16 (10 * (numD8ByteNat v 0 - 0x30) + (numD8ByteNat v 1 - 0x30)))
      (BitVec.ofNat 16 (10 * (numD8ByteNat v 2 - 0x30) + (numD8ByteNat v 3 - 0x30)))
      0x0064#16 0x0001#16 =
      BitVec.ofNat 32 (100 * (10 * (numD8ByteNat v 0 - 0x30) + (numD8ByteNat v 1 - 0x30)) +
        (10 * (numD8ByteNat v 2 - 0x30) + (numD8ByteNat v 3 - 0x30))) := by
    rw [numD8_wd_lane _ _ (by rw [s0]; omega) (by rw [s1]; omega), s0, s1]
  have l1 : pmaddWdLane (BitVec.ofNat 16 (10 * (numD8ByteNat v 4 - 0x30) + (numD8ByteNat v 5 - 0x30)))
      (BitVec.ofNat 16 (10 * (numD8ByteNat v 6 - 0x30) + (numD8ByteNat v 7 - 0x30)))
      0x0064#16 0x0001#16 =
      BitVec.ofNat 32 (100 * (10 * (numD8ByteNat v 4 - 0x30) + (numD8ByteNat v 5 - 0x30)) +
        (10 * (numD8ByteNat v 6 - 0x30) + (numD8ByteNat v 7 - 0x30))) := by
    rw [numD8_wd_lane _ _ (by rw [s2]; omega) (by rw [s3]; omega), s2, s3]
  have u := numD8UbSw_eq v hd
  show pmaddWd (numD8UbSw v) numD8C16 = _
  rw [u, numD8C16_eq]
  rw [pmaddWd_cons, pmaddWd_cons]
  have hz : pmaddWd [0, 0, 0, 0] [0x0000#16, 0x0000#16, 0x0000#16, 0x0000#16] = [0, 0] := by
    decide
  rw [hz, l0, l1]

theorem numD8Product_eq (v : BitVec 64)
    (hd : ∀ k, k < 8 → 0x30 ≤ numD8ByteNat v k ∧ numD8ByteNat v k ≤ 0x39) :
    numD8Product v = numD8Dec v := by
  have e0 : numD8ByteNat v 0 - 0x30 ≤ 9 := by have := (hd 0 (by decide)).2; omega
  have e1 : numD8ByteNat v 1 - 0x30 ≤ 9 := by have := (hd 1 (by decide)).2; omega
  have e2 : numD8ByteNat v 2 - 0x30 ≤ 9 := by have := (hd 2 (by decide)).2; omega
  have e3 : numD8ByteNat v 3 - 0x30 ≤ 9 := by have := (hd 3 (by decide)).2; omega
  have e4 : numD8ByteNat v 4 - 0x30 ≤ 9 := by have := (hd 4 (by decide)).2; omega
  have e5 : numD8ByteNat v 5 - 0x30 ≤ 9 := by have := (hd 5 (by decide)).2; omega
  have e6 : numD8ByteNat v 6 - 0x30 ≤ 9 := by have := (hd 6 (by decide)).2; omega
  have e7 : numD8ByteNat v 7 - 0x30 ≤ 9 := by have := (hd 7 (by decide)).2; omega
  have hwd := numD8Wd_eq v hd
  have hx : ((numD8Wd v).getD 0 0).toNat =
      100 * (10 * (numD8ByteNat v 0 - 0x30) + (numD8ByteNat v 1 - 0x30)) +
        (10 * (numD8ByteNat v 2 - 0x30) + (numD8ByteNat v 3 - 0x30)) := by
    rw [hwd]
    show (BitVec.ofNat 32 (100 * (10 * (numD8ByteNat v 0 - 0x30) + (numD8ByteNat v 1 - 0x30)) +
      (10 * (numD8ByteNat v 2 - 0x30) + (numD8ByteNat v 3 - 0x30)))).toNat = _
    rw [BitVec.toNat_ofNat, show (2 : Nat) ^ 32 = 4294967296 from by decide]
    exact Nat.mod_eq_of_lt (by omega)
  have hy : ((numD8Wd v).getD 1 0).toNat =
      100 * (10 * (numD8ByteNat v 4 - 0x30) + (numD8ByteNat v 5 - 0x30)) +
        (10 * (numD8ByteNat v 6 - 0x30) + (numD8ByteNat v 7 - 0x30)) := by
    rw [hwd]
    show (BitVec.ofNat 32 (100 * (10 * (numD8ByteNat v 4 - 0x30) + (numD8ByteNat v 5 - 0x30)) +
      (10 * (numD8ByteNat v 6 - 0x30) + (numD8ByteNat v 7 - 0x30)))).toNat = _
    rw [BitVec.toNat_ofNat, show (2 : Nat) ^ 32 = 4294967296 from by decide]
    exact Nat.mod_eq_of_lt (by omega)
  show ((numD8Wd v).getD 0 0).toNat * 10000 + ((numD8Wd v).getD 1 0).toNat = numD8Dec v
  rw [hx, hy]
  unfold numD8Dec
  omega

theorem numD8Product_lt (v : BitVec 64)
    (hd : ∀ k, k < 8 → 0x30 ≤ numD8ByteNat v k ∧ numD8ByteNat v k ≤ 0x39) :
    numD8Product v < 2 ^ 32 := by
  rw [numD8Product_eq v hd]
  unfold numD8Dec
  rw [show (2 : Nat) ^ 32 = 4294967296 from by decide]
  have e0 : numD8ByteNat v 0 - 0x30 ≤ 9 := by have := (hd 0 (by decide)).2; omega
  have e1 : numD8ByteNat v 1 - 0x30 ≤ 9 := by have := (hd 1 (by decide)).2; omega
  have e2 : numD8ByteNat v 2 - 0x30 ≤ 9 := by have := (hd 2 (by decide)).2; omega
  have e3 : numD8ByteNat v 3 - 0x30 ≤ 9 := by have := (hd 3 (by decide)).2; omega
  have e4 : numD8ByteNat v 4 - 0x30 ≤ 9 := by have := (hd 4 (by decide)).2; omega
  have e5 : numD8ByteNat v 5 - 0x30 ≤ 9 := by have := (hd 5 (by decide)).2; omega
  have e6 : numD8ByteNat v 6 - 0x30 ≤ 9 := by have := (hd 6 (by decide)).2; omega
  have e7 : numD8ByteNat v 7 - 0x30 ≤ 9 := by have := (hd 7 (by decide)).2; omega
  omega

theorem numD8_d8Value_of_digits (v : BitVec 64)
    (hd : ∀ k, k < 8 → 0x30 ≤ numD8ByteNat v k ∧ numD8ByteNat v k ≤ 0x39) :
    d8Value (natToBytes v.toNat 8) = some (numD8Product v) := by
  have hlen : (natToBytes v.toNat 8).length = 8 := natToBytes_length _ _
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hbs⟩ := list_of_length_eight _ hlen
  have hb0 : b0 = numD8Byte v 0 := by
    have h := numD8_natToBytes_byte (v := v) (k := 0) (by decide)
    rw [hbs] at h
    simpa using h
  have hb1 : b1 = numD8Byte v 1 := by
    have h := numD8_natToBytes_byte (v := v) (k := 1) (by decide)
    rw [hbs] at h
    simpa using h
  have hb2 : b2 = numD8Byte v 2 := by
    have h := numD8_natToBytes_byte (v := v) (k := 2) (by decide)
    rw [hbs] at h
    simpa using h
  have hb3 : b3 = numD8Byte v 3 := by
    have h := numD8_natToBytes_byte (v := v) (k := 3) (by decide)
    rw [hbs] at h
    simpa using h
  have hb4 : b4 = numD8Byte v 4 := by
    have h := numD8_natToBytes_byte (v := v) (k := 4) (by decide)
    rw [hbs] at h
    simpa using h
  have hb5 : b5 = numD8Byte v 5 := by
    have h := numD8_natToBytes_byte (v := v) (k := 5) (by decide)
    rw [hbs] at h
    simpa using h
  have hb6 : b6 = numD8Byte v 6 := by
    have h := numD8_natToBytes_byte (v := v) (k := 6) (by decide)
    rw [hbs] at h
    simpa using h
  have hb7 : b7 = numD8Byte v 7 := by
    have h := numD8_natToBytes_byte (v := v) (k := 7) (by decide)
    rw [hbs] at h
    simpa using h
  have ha0 : asciiDigit b0 = some (numD8ByteNat v 0 - 0x30) := by
    rw [hb0]
    have h := asciiDigit_eq_sub (numD8Byte v 0)
      (by rw [numD8Byte_toNat]; exact (hd 0 (by decide)).1)
      (by rw [numD8Byte_toNat]; exact (hd 0 (by decide)).2)
    simpa [numD8Byte_toNat] using h
  have ha1 : asciiDigit b1 = some (numD8ByteNat v 1 - 0x30) := by
    rw [hb1]
    have h := asciiDigit_eq_sub (numD8Byte v 1)
      (by rw [numD8Byte_toNat]; exact (hd 1 (by decide)).1)
      (by rw [numD8Byte_toNat]; exact (hd 1 (by decide)).2)
    simpa [numD8Byte_toNat] using h
  have ha2 : asciiDigit b2 = some (numD8ByteNat v 2 - 0x30) := by
    rw [hb2]
    have h := asciiDigit_eq_sub (numD8Byte v 2)
      (by rw [numD8Byte_toNat]; exact (hd 2 (by decide)).1)
      (by rw [numD8Byte_toNat]; exact (hd 2 (by decide)).2)
    simpa [numD8Byte_toNat] using h
  have ha3 : asciiDigit b3 = some (numD8ByteNat v 3 - 0x30) := by
    rw [hb3]
    have h := asciiDigit_eq_sub (numD8Byte v 3)
      (by rw [numD8Byte_toNat]; exact (hd 3 (by decide)).1)
      (by rw [numD8Byte_toNat]; exact (hd 3 (by decide)).2)
    simpa [numD8Byte_toNat] using h
  have ha4 : asciiDigit b4 = some (numD8ByteNat v 4 - 0x30) := by
    rw [hb4]
    have h := asciiDigit_eq_sub (numD8Byte v 4)
      (by rw [numD8Byte_toNat]; exact (hd 4 (by decide)).1)
      (by rw [numD8Byte_toNat]; exact (hd 4 (by decide)).2)
    simpa [numD8Byte_toNat] using h
  have ha5 : asciiDigit b5 = some (numD8ByteNat v 5 - 0x30) := by
    rw [hb5]
    have h := asciiDigit_eq_sub (numD8Byte v 5)
      (by rw [numD8Byte_toNat]; exact (hd 5 (by decide)).1)
      (by rw [numD8Byte_toNat]; exact (hd 5 (by decide)).2)
    simpa [numD8Byte_toNat] using h
  have ha6 : asciiDigit b6 = some (numD8ByteNat v 6 - 0x30) := by
    rw [hb6]
    have h := asciiDigit_eq_sub (numD8Byte v 6)
      (by rw [numD8Byte_toNat]; exact (hd 6 (by decide)).1)
      (by rw [numD8Byte_toNat]; exact (hd 6 (by decide)).2)
    simpa [numD8Byte_toNat] using h
  have ha7 : asciiDigit b7 = some (numD8ByteNat v 7 - 0x30) := by
    rw [hb7]
    have h := asciiDigit_eq_sub (numD8Byte v 7)
      (by rw [numD8Byte_toNat]; exact (hd 7 (by decide)).1)
      (by rw [numD8Byte_toNat]; exact (hd 7 (by decide)).2)
    simpa [numD8Byte_toNat] using h
  have hval : d8Value [b0, b1, b2, b3, b4, b5, b6, b7] = some (numD8Dec v) := by
    simp only [d8Value, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7,
      List.length_cons, List.length_nil, Nat.pow_zero, Nat.mul_one, Nat.add_zero]
    rw [Option.some.injEq]
    rw [show (10 : Nat) ^ 7 = 10000000 from by decide,
      show (10 : Nat) ^ 6 = 1000000 from by decide,
      show (10 : Nat) ^ 5 = 100000 from by decide,
      show (10 : Nat) ^ 4 = 10000 from by decide,
      show (10 : Nat) ^ 3 = 1000 from by decide,
      show (10 : Nat) ^ 2 = 100 from by decide,
      show (10 : Nat) ^ 1 = 10 from by decide]
    unfold numD8Dec
    omega
  rw [hbs, hval, numD8Product_eq v hd]


/-- The branch's condition is exactly the model's digit test on the loaded word. -/
theorem numD8Test_iff (v : BitVec 64) :
    numD8Test v = 1 ↔ d8Value (natToBytes v.toNat 8) ≠ none := by
  constructor
  · intro h
    have hd := numD8_digits_of_test v h
    rw [numD8_d8Value_of_digits v hd]
    exact Option.some_ne_none _
  · intro h
    refine (numD8Test_iff_lanes v).mpr ?_
    intro k hk
    have hb : (natToBytes v.toNat 8)[k]? = some (numD8Byte v k) :=
      numD8_natToBytes_byte hk
    have hd := d8Value_digit_ne_none _ h hb
    exact (numD8_bits_range v hk).mpr ((numD8_asciiDigit_bn v k).mp hd)


def numD8EntryEnv (p val : Nat) : Env := [("%p", .ptr p), ("%val", .ptr val)]

def numD8EntryState (p val : Nat) (mem : Mem) (next : Nat) : State :=
  { env := numD8EntryEnv p val, mem := mem, next := next, pc := "entry", pre := none }

def numD8AfterEntryEnv (p val : Nat) (v : BitVec 64) : Env :=
  ("%cmp.not", .int 1 (numD8Test v)) ::
  ("%3", .int 16 (numD8Masked v)) ::
  ("%2", .int 16 (numD8Mask v)) ::
  ("%cmp.i", .vec 16 1 (numD8Bits v)) ::
  ("%sub.i", .vec 16 8 (numD8Sub v)) ::
  ("%1", .vec 16 8 (numD8Lanes v)) ::
  ("%vecinit1.i", .vec 2 64 [v, 0#64]) ::
  ("%0", .int 64 v) ::
  numD8EntryEnv p val

def numD8AfterIfEndEnv (p val : Nat) (v : BitVec 64) : Env :=
  ("%add", .int 32 (BitVec.ofNat 32 (numD8Product v))) ::
  ("%6", .int 32 ((numD8Wd v).getD 1 0)) ::
  ("%mul", .int 32 (BitVec.ofNat 32 (((numD8Wd v).getD 0 0).toNat * 10000))) ::
  ("%vecext.i", .int 32 ((numD8Wd v).getD 0 0)) ::
  ("%5", .vec 4 32 (numD8Wd v)) ::
  ("%4", .vec 8 16 (numD8UbSw v)) ::
  numD8AfterEntryEnv p val v

/-! #### The step shapes -/

theorem numD8_step_insert (env : Env) (s : State) (d a : String) (v : BitVec 64)
    (ha : lookupName env a = some (.int 64 v)) :
    evalInstr numD8Calls (stateAt env s)
        (.insertelement d 2 64 (.imm (.vector 64 [0#64, 0#64])) (.reg a)
          (.imm (.int 64 0#64))) =
      some (stateAt ((d, .vec 2 64 [v, 0#64]) :: env) s) := by
  have hx : Value.intToNat 64 (.int 64 v) = some v.toNat := by simp [Value.intToNat]
  have hk : (0#64).toNat < ([0#64, 0#64] : List (BitVec 64)).length := by decide
  rw [step_insertelement numD8Calls env s d 2 64 (.imm (.vector 64 [0#64, 0#64]))
      (.reg a) (.imm (.int 64 0#64)) (vv := .vec 2 64 [0#64, 0#64])
      (lanes := [0#64, 0#64]) (ev := .int 64 v) (x := v.toNat) (wi := 64)
      (k := 0#64) (by rfl) (JsonS1MasksIR.vecLanes_self rfl)
      (BlockEval.evalOperand_reg_of env s a (.int 64 v) ha) hx (by rfl) hk]
  simp only [stateAt, State.bind]
  congr 1
  simp [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem numD8_step_bitcast (env : Env) (s : State) (d a : String) (v : BitVec 64)
    (ha : lookupName env a = some (.vec 2 64 [v, 0#64])) :
    evalInstr numD8Calls (stateAt env s) (.vecBitcast d 2 64 16 8 (.reg a)) =
      some (stateAt ((d, .vec 16 8 (numD8Lanes v)) :: env) s) := by
  have hb : bitcastVecLanes 8 16 [v, 0#64] = numD8Lanes v := by
    simpa using numD8Lanes_bitcast v
  rw [step_vecBitcast numD8Calls env s d 2 64 16 8 (.reg a)
    (vv := .vec 2 64 [v, 0#64]) (lanes := [v, 0#64])
    (BlockEval.evalOperand_reg_of env s a (.vec 2 64 [v, 0#64]) ha)
    (JsonS1MasksIR.vecLanes_self rfl) (by decide), hb]

theorem numD8_icmpLanes (l : List (BitVec 8)) (hlen : l.length = 16) :
    icmpLanes .ult l (List.replicate 16 (0x0a#8)) =
      l.map (fun x => evalICmp .ult x 0x0a#8) := by
  show (l.zip (List.replicate 16 (0x0a#8))).map
    (fun (x, y) => evalICmp .ult x y) = l.map (fun x => evalICmp .ult x 0x0a#8)
  rw [← hlen]
  exact JsonS1MasksIR.zipReplicate_map l 0x0a#8 (fun x y => evalICmp .ult x y)

theorem numD8_step_add (env : Env) (s : State) (d a : String) (l : List (BitVec 8))
    (hlen : l.length = 16) (ha : lookupName env a = some (.vec 16 8 l)) :
    evalInstr numD8Calls (stateAt env s)
        (.binopVec d .add 16 8 (.reg a) (.imm (.splat 16 8 0xd0#8))) =
      some (stateAt ((d, .vec 16 8 (l.map (fun x => x + 0xd0#8))) :: env) s) := by
  have hm : (l.zip (List.replicate 16 (0xd0#8))).mapM
      (fun (x, y) => evalBinop .add x y) = some (l.map (fun x => x + 0xd0#8)) := by
    rw [← hlen]
    exact JsonS1MasksIR.zipReplicate_mapM l 0xd0#8 (fun x y => evalBinop .add x y)
      (fun x => x + 0xd0#8) (fun x => rfl)
  exact step_binopVec numD8Calls env s d .add 16 8 (.reg a)
    (.imm (.splat 16 8 0xd0#8)) (ha := BlockEval.evalOperand_reg_of env s a (.vec 16 8 l) ha)
    (hb := by rfl) (h1 := JsonS1MasksIR.vecLanes_self hlen)
    (h2 := JsonS1MasksIR.vecLanes_self (by simp)) (hm := hm)

theorem numD8_step_icmp (env : Env) (s : State) (d a : String) (l : List (BitVec 8))
    (hlen : l.length = 16) (ha : lookupName env a = some (.vec 16 8 l)) :
    evalInstr numD8Calls (stateAt env s)
        (.icmpVec d .ult 16 8 (.reg a) (.imm (.splat 16 8 0x0a#8))) =
      some (stateAt ((d, .vec 16 1 (l.map (fun x => evalICmp .ult x 0x0a#8))) :: env) s) := by
  rw [← numD8_icmpLanes l hlen]
  exact step_icmpVec numD8Calls env s d .ult 16 8 (.reg a) (.imm (.splat 16 8 0x0a#8))
    (ha := BlockEval.evalOperand_reg_of env s a (.vec 16 8 l) ha) (hb := by rfl)
    (h1 := JsonS1MasksIR.vecLanes_self hlen)
    (h2 := JsonS1MasksIR.vecLanes_self (by simp))

theorem numD8_step_mask (env : Env) (s : State) (d a : String) (l : List (BitVec 1))
    (hlen : l.length = 16) (ha : lookupName env a = some (.vec 16 1 l)) :
    evalInstr numD8Calls (stateAt env s) (.bitcastMask d 16 (.reg a)) =
      some (stateAt ((d, .int 16 (BitVec.ofNat 16 (lanesToNat l))) :: env) s) :=
  step_bitcastMask numD8Calls env s d 16 (.reg a)
    (BlockEval.evalOperand_reg_of env s a (.vec 16 1 l) ha) hlen

theorem numD8_evalBinopNat_and16 (x c : BitVec 16) :
    evalBinopNat .and 16 x.toNat c.toNat = some (x.toNat &&& c.toNat) := by
  simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat, BitVec.toNat_and]

theorem numD8_step_and16 (env : Env) (s : State) (d a : String) (x c : BitVec 16)
    (ha : lookupName env a = some (.int 16 x)) :
    evalInstr numD8Calls (stateAt env s) (.binop d .and 16 (.reg a) (.imm (.int 16 c))) =
      some (stateAt ((d, .int 16 (x &&& c)) :: env) s) := by
  have h := JsonS1MasksIR.evalInstr_binop (calls := numD8Calls)
    (s := stateAt env s) (d := d) (op := .and) (w := 16) (a := .reg a)
    (b := .imm (.int 16 c)) (x := x) (y := c) (r := x.toNat &&& c.toNat)
    (BlockEval.evalOperand_reg_of env s a (.int 16 x) ha)
    (BlockEval.evalOperand_lit_of (stateAt env s) 16 c) (numD8_evalBinopNat_and16 x c)
  rw [h]
  simp only [stateAt, State.bind]
  rw [show BitVec.ofNat 16 (x.toNat &&& c.toNat) = x &&& c from by
    rw [← BitVec.toNat_and x c, BitVec.ofNat_toNat, BitVec.setWidth_eq]]

theorem numD8_step_icmp16 (env : Env) (s : State) (d a : String) (x c : BitVec 16)
    (ha : lookupName env a = some (.int 16 x)) :
    evalInstr numD8Calls (stateAt env s) (.icmp d .eq 16 (.reg a) (.imm (.int 16 c))) =
      some (stateAt ((d, .int 1 (evalICmp .eq x c)) :: env) s) :=
  JsonS1MasksIR.evalInstr_icmp (calls := numD8Calls) (s := stateAt env s) (d := d)
    (pred := .eq) (w := 16) (a := .reg a) (b := .imm (.int 16 c)) (x := x) (y := c)
    (BlockEval.evalOperand_reg_of env s a (.int 16 x) ha)
    (BlockEval.evalOperand_lit_of (stateAt env s) 16 c)

theorem numD8_step_call2 (env : Env) (s : State) (d callee : String) (ty : Ty)
    (t1 t2 : Ty) (o1 o2 : Operand) {v1 v2 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (hc : numD8Calls callee [v1, v2] s.mem s.next = some r) :
    evalInstr numD8Calls (stateAt env s) (.call d ty callee [(t1, o1), (t2, o2)]) =
      some (stateAt ((d, r.ret) :: env) { s with mem := r.mem, next := r.next }) := by
  have hargs : evalOperands (stateAt env s) [(t1, o1), (t2, o2)] = some [v1, v2] := by
    simp only [evalOperands, h1, h2]
  rw [JsonS1MasksIR.evalInstr_call (ha := hargs) (hc := hc)]
  simp only [stateAt, State.bind]

theorem numD8_step_extract32 (env : Env) (s : State) (d a : String) (n : Nat)
    (l : List (BitVec 32)) (k : Nat) (x : BitVec 32)
    (ha : lookupName env a = some (.vec n 32 l)) (hln : l.length = n)
    (hk64 : k < 2 ^ 64) (hx : l[k]? = some x) :
    evalInstr numD8Calls (stateAt env s)
        (.extractelement d n 32 (.reg a) (.imm (.int 64 (BitVec.ofNat 64 k)))) =
      some (stateAt ((d, .int 32 x) :: env) s) := by
  have hk' : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hk64
  exact step_extractelement numD8Calls env s d n 32 (.reg a)
    (.imm (.int 64 (BitVec.ofNat 64 k))) (vv := .vec n 32 l) (lanes := l) (wi := 64)
    (k := BitVec.ofNat 64 k) (x := x)
    (BlockEval.evalOperand_reg_of env s a (.vec n 32 l) ha)
    (JsonS1MasksIR.vecLanes_self hln) (by rfl) (by rw [hk']; exact hx)

theorem numD8_evalBinopNat_mul (w a b : Nat) :
    evalBinopNat .mul w a b = some ((a * b) % 2 ^ w) := by
  simp [evalBinopNat, evalBinop, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod]

theorem numD8_evalBinopNat_add (w a b : Nat) :
    evalBinopNat .add w a b = some ((a + b) % 2 ^ w) := by
  simp [evalBinopNat, evalBinop, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]

theorem ofNat32_mod (x : Nat) : BitVec.ofNat 32 (x % 2 ^ 32) = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod]

theorem numD8_step_mul (env : Env) (s : State) (d a : String) (x : BitVec 32) (c : BitVec 32)
    (ha : lookupName env a = some (.int 32 x)) :
    evalInstr numD8Calls (stateAt env s) (.binop d .mul 32 (.reg a) (.imm (.int 32 c))) =
      some (stateAt ((d, .int 32 (BitVec.ofNat 32 (x.toNat * c.toNat))) :: env) s) := by
  have h := JsonS1MasksIR.evalInstr_binop (calls := numD8Calls) (s := stateAt env s)
    (d := d) (op := .mul) (w := 32) (a := .reg a) (b := .imm (.int 32 c))
    (x := x) (y := c) (r := (x.toNat * c.toNat) % 2 ^ 32)
    (BlockEval.evalOperand_reg_of env s a (.int 32 x) ha)
    (BlockEval.evalOperand_lit_of (stateAt env s) 32 c)
    (numD8_evalBinopNat_mul 32 x.toNat c.toNat)
  rw [h]
  simp only [stateAt, State.bind, ofNat32_mod]

theorem numD8_step_addv (env : Env) (s : State) (d a b : String) (x y : BitVec 32)
    (ha : lookupName env a = some (.int 32 x)) (hb : lookupName env b = some (.int 32 y)) :
    evalInstr numD8Calls (stateAt env s) (.binop d .add 32 (.reg a) (.reg b)) =
      some (stateAt ((d, .int 32 (BitVec.ofNat 32 (x.toNat + y.toNat))) :: env) s) := by
  have h := JsonS1MasksIR.evalInstr_binop (calls := numD8Calls) (s := stateAt env s)
    (d := d) (op := .add) (w := 32) (a := .reg a) (b := .reg b)
    (x := x) (y := y) (r := (x.toNat + y.toNat) % 2 ^ 32)
    (BlockEval.evalOperand_reg_of env s a (.int 32 x) ha)
    (BlockEval.evalOperand_reg_of env s b (.int 32 y) hb)
    (numD8_evalBinopNat_add 32 x.toNat y.toNat)
  rw [h]
  simp only [stateAt, State.bind, ofNat32_mod]

theorem numD8_step_store32 (env : Env) (s : State) (v p : String) {x : BitVec 32} {a : Nat}
    (hv : lookupName env v = some (.int 32 x)) (hp : lookupName env p = some (.ptr a)) :
    evalInstr numD8Calls (stateAt env s) (.store (.int 32) (.reg v) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
  have hs : storeValue (stateAt env s) (.int 32) (.int 32 x) a =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
    simp [storeValue, stateAt, show ((32 + 7) / 8) = 4 from by decide]
  exact JsonS1MasksIR.evalInstr_store (s := stateAt env s) (ty := .int 32)
    (v := .reg v) (p := .reg p) (vv := .int 32 x) (a := a)
    (BlockEval.evalOperand_reg_of env s v (.int 32 x) hv)
    (BlockEval.evalOperand_reg_of env s p (.ptr a) hp) hs

theorem numD8Calls_pmaddUbSw (x y : List (BitVec 8)) (mem : Mem) (next : Nat) :
    numD8Calls "llvm.x86.ssse3.pmadd.ub.sw.128" [.vec 16 8 x, .vec 16 8 y] mem next =
      some { ret := .vec 8 16 (pmaddUbSw x y), mem := mem, next := next } :=
  escapeCalls_pmaddUbSw x y mem next

theorem numD8Calls_pmaddWd (x y : List (BitVec 16)) (mem : Mem) (next : Nat) :
    numD8Calls "llvm.x86.sse2.pmadd.wd" [.vec 8 16 x, .vec 8 16 y] mem next =
      some { ret := .vec 4 32 (pmaddWd x y), mem := mem, next := next } :=
  escapeCalls_pmaddWd x y mem next

/-! #### The entry block -/

theorem numD8Sub_length (v : BitVec 64) : (numD8Sub v).length = 16 := by
  simp [numD8Sub]

theorem numD8Bits_length (v : BitVec 64) : (numD8Bits v).length = 16 := by
  simp [numD8Bits]

theorem numD8Sub_of_lanes_bv (v : BitVec 64) :
    (numD8Lanes v).map (fun x => x + 0xd0#8) = numD8Sub v := by
  simpa using numD8Sub_of_lanes v

theorem numD8_entry_denote (v : BitVec 64) (p val : Nat) (s : State)
    (hread : readBytes s.mem p 8 = some (natToBytes v.toNat 8)) :
    denoteCode numD8Calls numD8EntryInstrs (stateAt (numD8EntryEnv p val) s) =
      some (stateAt (numD8AfterEntryEnv p val v) s) := by
  rw [numD8EntryInstrs]
  rw [denoteCode_cons_of _ _ _ _ _ (BlockEval.step_load64 (calls := numD8Calls)
    (env := numD8EntryEnv p val) (s := s) (d := "%0") (p := "%p") (a := p) (v := v)
    (by block_lk) hread)]
  rw [denoteCode_cons_of _ _ _ _ _ (numD8_step_insert (s := s)
    (env := ("%0", .int 64 v) :: numD8EntryEnv p val) (d := "%vecinit1.i") (a := "%0")
    (v := v) (by block_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (numD8_step_bitcast (s := s)
    (env := ("%vecinit1.i", .vec 2 64 [v, 0#64]) :: ("%0", .int 64 v) :: numD8EntryEnv p val)
    (d := "%1") (a := "%vecinit1.i") (v := v) (by block_lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (numD8_step_add (s := s)
    (env := ("%1", .vec 16 8 (numD8Lanes v)) ::
      ("%vecinit1.i", .vec 2 64 [v, 0#64]) :: ("%0", .int 64 v) :: numD8EntryEnv p val)
    (d := "%sub.i") (a := "%1") (l := numD8Lanes v) (numD8Lanes_length v) (by block_lk))]
  rw [numD8Sub_of_lanes_bv v]
  rw [denoteCode_cons_of _ _ _ _ _ (numD8_step_icmp (s := s)
    (env := ("%sub.i", .vec 16 8 (numD8Sub v)) ::
      ("%1", .vec 16 8 (numD8Lanes v)) ::
      ("%vecinit1.i", .vec 2 64 [v, 0#64]) :: ("%0", .int 64 v) :: numD8EntryEnv p val)
    (d := "%cmp.i") (a := "%sub.i") (l := numD8Sub v) (numD8Sub_length v) (by block_lk))]
  rw [numD8Bits_of_lanes v]
  rw [denoteCode_cons_of _ _ _ _ _ (numD8_step_mask (s := s)
    (env := ("%cmp.i", .vec 16 1 (numD8Bits v)) ::
      ("%sub.i", .vec 16 8 (numD8Sub v)) ::
      ("%1", .vec 16 8 (numD8Lanes v)) ::
      ("%vecinit1.i", .vec 2 64 [v, 0#64]) :: ("%0", .int 64 v) :: numD8EntryEnv p val)
    (d := "%2") (a := "%cmp.i") (l := numD8Bits v) (numD8Bits_length v) (by block_lk))]
  rw [show BitVec.ofNat 16 (lanesToNat (numD8Bits v)) = numD8Mask v from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (numD8_step_and16 (s := s)
    (env := ("%2", .int 16 (numD8Mask v)) ::
      ("%cmp.i", .vec 16 1 (numD8Bits v)) ::
      ("%sub.i", .vec 16 8 (numD8Sub v)) ::
      ("%1", .vec 16 8 (numD8Lanes v)) ::
      ("%vecinit1.i", .vec 2 64 [v, 0#64]) :: ("%0", .int 64 v) :: numD8EntryEnv p val)
    (d := "%3") (a := "%2") (x := numD8Mask v) (c := 0x00ff#16) (by block_lk))]
  rw [show numD8Mask v &&& 0x00ff#16 = numD8Masked v from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (numD8_step_icmp16 (s := s)
    (env := ("%3", .int 16 (numD8Masked v)) ::
      ("%2", .int 16 (numD8Mask v)) ::
      ("%cmp.i", .vec 16 1 (numD8Bits v)) ::
      ("%sub.i", .vec 16 8 (numD8Sub v)) ::
      ("%1", .vec 16 8 (numD8Lanes v)) ::
      ("%vecinit1.i", .vec 2 64 [v, 0#64]) :: ("%0", .int 64 v) :: numD8EntryEnv p val)
    (d := "%cmp.not") (a := "%3") (x := numD8Masked v) (c := 0x00ff#16) (by block_lk))]
  rw [show evalICmp .eq (numD8Masked v) 0x00ff#16 = numD8Test v from rfl]
  rfl

theorem numD8_entry_step_success (v : BitVec 64) (p val : Nat) (s : State)
    (hpc : s.pc = "entry") (hread : readBytes s.mem p 8 = some (natToBytes v.toNat 8))
    (htest : numD8Test v = 1) :
    step numD8Calls numD8Body (stateAt (numD8EntryEnv p val) s) =
      .jump (stateAt (numD8AfterEntryEnv p val v)
        { s with pc := "if.end", pre := some s.pc }) := by
  have hcode := numD8_entry_denote v p val s hread
  have hnot : lookupName (numD8AfterEntryEnv p val v) "%cmp.not" =
      some (.int 1 (numD8Test v)) := by block_lk
  have hop : evalOperand (stateAt (numD8AfterEntryEnv p val v) s) (.reg "%cmp.not") =
      some (.int 1 (numD8Test v)) := BlockEval.evalOperand_reg_of _ _ _ _ hnot
  unfold step execTerm
  rw [show (stateAt (numD8EntryEnv p val) s).pc = "entry" from hpc, numD8_findBlock_entry]
  simp only [hcode, hop, htest]
  rfl

theorem numD8_entry_step_refusal (v : BitVec 64) (p val : Nat) (s : State)
    (hpc : s.pc = "entry") (hread : readBytes s.mem p 8 = some (natToBytes v.toNat 8))
    (htest : numD8Test v = 0) :
    step numD8Calls numD8Body (stateAt (numD8EntryEnv p val) s) =
      .jump (stateAt (numD8AfterEntryEnv p val v)
        { s with pc := "cleanup", pre := some s.pc }) := by
  have hcode := numD8_entry_denote v p val s hread
  have hnot : lookupName (numD8AfterEntryEnv p val v) "%cmp.not" =
      some (.int 1 (numD8Test v)) := by block_lk
  have hop : evalOperand (stateAt (numD8AfterEntryEnv p val v) s) (.reg "%cmp.not") =
      some (.int 1 (numD8Test v)) := BlockEval.evalOperand_reg_of _ _ _ _ hnot
  unfold step execTerm
  rw [show (stateAt (numD8EntryEnv p val) s).pc = "entry" from hpc, numD8_findBlock_entry]
  simp only [hcode, hop, htest]
  rfl

/-! #### The `if.end` block -/

theorem numD8_ifEnd_denote (v : BitVec 64) (p val : Nat) (s : State)
    (hd : ∀ k, k < 8 → 0x30 ≤ numD8ByteNat v k ∧ numD8ByteNat v k ≤ 0x39)
    (hprod : numD8Product v < 2 ^ 32) :
    denoteCode numD8Calls numD8IfEndInstrs (stateAt (numD8AfterEntryEnv p val v) s) =
      some (stateAt (numD8AfterIfEndEnv p val v)
        { s with mem := writeBytes s.mem val (natToBytes (numD8Product v) 4) }) := by
  have hsub : lookupName (numD8AfterEntryEnv p val v) "%sub.i" =
      some (.vec 16 8 (numD8Sub v)) := by block_lk
  have hl0 : (numD8Wd v)[0]? = some ((numD8Wd v).getD 0 0) := by
    rw [numD8Wd_eq v hd]
    rfl
  have hl1 : (numD8Wd v)[1]? = some ((numD8Wd v).getD 1 0) := by
    rw [numD8Wd_eq v hd]
    rfl
  have hlen : (numD8Wd v).length = 4 := by
    rw [numD8Wd_eq v hd]
    rfl
  have hprod' : ((numD8Wd v).getD 0 0).toNat * 10000 + ((numD8Wd v).getD 1 0).toNat <
      2 ^ 32 := hprod
  have hadd : BitVec.ofNat 32 (((BitVec.ofNat 32 (((numD8Wd v).getD 0 0).toNat * 10000)).toNat +
      ((numD8Wd v).getD 1 0).toNat)) = BitVec.ofNat 32 (numD8Product v) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (2 : Nat) ^ 32 = 4294967296 from by decide]
    rw [show numD8Product v = ((numD8Wd v).getD 0 0).toNat * 10000 +
      ((numD8Wd v).getD 1 0).toNat from rfl]
    have hY : ((numD8Wd v).getD 1 0).toNat % 4294967296 = ((numD8Wd v).getD 1 0).toNat :=
      Nat.mod_eq_of_lt (BitVec.isLt _)
    have hXY : ((numD8Wd v).getD 0 0).toNat * 10000 + ((numD8Wd v).getD 1 0).toNat <
        4294967296 := hprod
    rw [← hY, ← Nat.add_mod, hY, Nat.mod_eq_of_lt hXY]
  rw [numD8IfEndInstrs]
  rw [denoteCode_cons_of _ _ _ _ _ (numD8_step_call2 (s := s)
    (env := numD8AfterEntryEnv p val v) (d := "%4")
    (callee := "llvm.x86.ssse3.pmadd.ub.sw.128") (ty := .vec 8 (.int 16))
    (t1 := .vec 16 (.int 8)) (t2 := .vec 16 (.int 8))
    (o1 := .reg "%sub.i")
    (o2 := .imm (.vector 8 [0x0a#8, 0x01#8, 0x0a#8, 0x01#8, 0x0a#8, 0x01#8, 0x0a#8,
      0x01#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8]))
    (v1 := .vec 16 8 (numD8Sub v)) (v2 := .vec 16 8 numD8C8)
    (r := { ret := .vec 8 16 (numD8UbSw v), mem := s.mem, next := s.next })
    (BlockEval.evalOperand_reg_of _ _ _ _ hsub) (by rfl)
    (numD8Calls_pmaddUbSw (numD8Sub v) numD8C8 s.mem s.next))]
  rw [denoteCode_cons_of _ _ _ _ _ (numD8_step_call2 (s := s)
    (env := ("%4", .vec 8 16 (numD8UbSw v)) :: numD8AfterEntryEnv p val v) (d := "%5")
    (callee := "llvm.x86.sse2.pmadd.wd") (ty := .vec 4 (.int 32))
    (t1 := .vec 8 (.int 16)) (t2 := .vec 8 (.int 16))
    (o1 := .reg "%4")
    (o2 := .imm (.vector 16 [0x0064#16, 0x0001#16, 0x0064#16, 0x0001#16,
      0x0000#16, 0x0000#16, 0x0000#16, 0x0000#16]))
    (v1 := .vec 8 16 (numD8UbSw v)) (v2 := .vec 8 16 numD8C16)
    (r := { ret := .vec 4 32 (numD8Wd v), mem := s.mem, next := s.next })
    (by block_lk) (by rfl)
    (numD8Calls_pmaddWd (numD8UbSw v) numD8C16 s.mem s.next))]
  rw [denoteCode_cons_of _ _ _ _ _ (numD8_step_extract32 (s := s)
    (env := ("%5", .vec 4 32 (numD8Wd v)) ::
      ("%4", .vec 8 16 (numD8UbSw v)) :: numD8AfterEntryEnv p val v)
    (d := "%vecext.i") (a := "%5") (n := 4) (l := numD8Wd v) (k := 0)
    (x := (numD8Wd v).getD 0 0) (by block_lk) hlen (by decide) hl0)]
  rw [denoteCode_cons_of _ _ _ _ _ (numD8_step_mul (s := s)
    (env := ("%vecext.i", .int 32 ((numD8Wd v).getD 0 0)) ::
      ("%5", .vec 4 32 (numD8Wd v)) ::
      ("%4", .vec 8 16 (numD8UbSw v)) :: numD8AfterEntryEnv p val v)
    (d := "%mul") (a := "%vecext.i") (x := (numD8Wd v).getD 0 0)
    (c := 0x00002710#32) (by block_lk))]
  rw [show (0x00002710#32).toNat = 10000 from by decide]
  rw [denoteCode_cons_of _ _ _ _ _ (numD8_step_extract32 (s := s)
    (env := ("%mul", .int 32 (BitVec.ofNat 32 (((numD8Wd v).getD 0 0).toNat * 10000))) ::
      ("%vecext.i", .int 32 ((numD8Wd v).getD 0 0)) ::
      ("%5", .vec 4 32 (numD8Wd v)) ::
      ("%4", .vec 8 16 (numD8UbSw v)) :: numD8AfterEntryEnv p val v)
    (d := "%6") (a := "%5") (n := 4) (l := numD8Wd v) (k := 1)
    (x := (numD8Wd v).getD 1 0) (by block_lk) hlen (by decide) hl1)]
  rw [denoteCode_cons_of _ _ _ _ _ (numD8_step_addv (s := s)
    (env := ("%6", .int 32 ((numD8Wd v).getD 1 0)) ::
      ("%mul", .int 32 (BitVec.ofNat 32 (((numD8Wd v).getD 0 0).toNat * 10000))) ::
      ("%vecext.i", .int 32 ((numD8Wd v).getD 0 0)) ::
      ("%5", .vec 4 32 (numD8Wd v)) ::
      ("%4", .vec 8 16 (numD8UbSw v)) :: numD8AfterEntryEnv p val v)
    (d := "%add") (a := "%mul") (b := "%6")
    (x := BitVec.ofNat 32 (((numD8Wd v).getD 0 0).toNat * 10000))
    (y := (numD8Wd v).getD 1 0) (by block_lk) (by block_lk))]
  rw [hadd]
  rw [denoteCode_cons_of _ _ _ _ _ (numD8_step_store32 (s := s)
    (env := ("%add", .int 32 (BitVec.ofNat 32 (numD8Product v))) ::
      ("%6", .int 32 ((numD8Wd v).getD 1 0)) ::
      ("%mul", .int 32 (BitVec.ofNat 32 (((numD8Wd v).getD 0 0).toNat * 10000))) ::
      ("%vecext.i", .int 32 ((numD8Wd v).getD 0 0)) ::
      ("%5", .vec 4 32 (numD8Wd v)) ::
      ("%4", .vec 8 16 (numD8UbSw v)) :: numD8AfterEntryEnv p val v)
    (v := "%add") (p := "%val") (x := BitVec.ofNat 32 (numD8Product v)) (a := val)
    (by block_lk) (by block_lk))]
  rw [show (BitVec.ofNat 32 (numD8Product v)).toNat = numD8Product v from by
    rw [BitVec.toNat_ofNat, show (2 : Nat) ^ 32 = 4294967296 from by decide]
    exact Nat.mod_eq_of_lt hprod]
  rfl

theorem numD8_ifEnd_step (v : BitVec 64) (p val : Nat) (s : State)
    (hpc : s.pc = "if.end")
    (hd : ∀ k, k < 8 → 0x30 ≤ numD8ByteNat v k ∧ numD8ByteNat v k ≤ 0x39)
    (hprod : numD8Product v < 2 ^ 32) :
    step numD8Calls numD8Body (stateAt (numD8AfterEntryEnv p val v) s) =
      .jump (stateAt (numD8AfterIfEndEnv p val v)
        { s with
          mem := writeBytes s.mem val (natToBytes (numD8Product v) 4),
          pc := "cleanup", pre := some s.pc }) := by
  have hcode := numD8_ifEnd_denote v p val s hd hprod
  unfold step execTerm
  rw [show (stateAt (numD8AfterEntryEnv p val v) s).pc = "if.end" from hpc, numD8_findBlock_ifEnd]
  simp only [hcode, execTerm]
  rfl

/-! #### The `cleanup` block -/

theorem numD8_cleanup_denote_ifEnd (env : Env) (s : State) (hpre : s.pre = some "if.end") :
    denoteCode numD8Calls numD8CleanupInstrs (stateAt env s) =
      some (stateAt (("%retval.0", .int 32 1) :: env) s) := by
  have hinc : phiIncoming "if.end"
      [("if.end", Operand.imm (Const.int 32 0x00000001#32)),
       ("entry", Operand.imm (Const.int 32 0x00000000#32))] =
      some (Operand.imm (Const.int 32 0x00000001#32)) := by simp [phiIncoming]
  have hop : evalOperand (stateAt env s) (.imm (.int 32 0x00000001#32)) = some (.int 32 1) := rfl
  rw [numD8CleanupInstrs]
  rw [BlockEval.denoteCode_phi numD8Calls env s "%retval.0" (.int 32)
    [("if.end", Operand.imm (Const.int 32 0x00000001#32)),
     ("entry", Operand.imm (Const.int 32 0x00000000#32))] hpre hinc hop [] rfl]
  rfl

theorem numD8_cleanup_denote_entry (env : Env) (s : State) (hpre : s.pre = some "entry") :
    denoteCode numD8Calls numD8CleanupInstrs (stateAt env s) =
      some (stateAt (("%retval.0", .int 32 0) :: env) s) := by
  have hinc : phiIncoming "entry"
      [("if.end", Operand.imm (Const.int 32 0x00000001#32)),
       ("entry", Operand.imm (Const.int 32 0x00000000#32))] =
      some (Operand.imm (Const.int 32 0x00000000#32)) := by simp [phiIncoming]
  have hop : evalOperand (stateAt env s) (.imm (.int 32 0x00000000#32)) = some (.int 32 0) := rfl
  rw [numD8CleanupInstrs]
  rw [BlockEval.denoteCode_phi numD8Calls env s "%retval.0" (.int 32)
    [("if.end", Operand.imm (Const.int 32 0x00000001#32)),
     ("entry", Operand.imm (Const.int 32 0x00000000#32))] hpre hinc hop [] rfl]
  rfl

theorem numD8_cleanup_step_ifEnd (env : Env) (s : State) (hpc : s.pc = "cleanup")
    (hpre : s.pre = some "if.end") :
    step numD8Calls numD8Body (stateAt env s) =
      .ret (some (.int 32 1)) (stateAt (("%retval.0", .int 32 1) :: env) s) := by
  have hcode := numD8_cleanup_denote_ifEnd env s hpre
  have hret : lookupName (("%retval.0", .int 32 1) :: env) "%retval.0" =
      some (.int 32 1) := by block_lk
  have hop : evalOperand (stateAt (("%retval.0", .int 32 1) :: env) s) (.reg "%retval.0") =
      some (.int 32 1) := BlockEval.evalOperand_reg_of _ _ _ _ hret
  unfold step execTerm
  rw [show (stateAt env s).pc = "cleanup" from hpc, numD8_findBlock_cleanup]
  simp only [hcode, hop]

theorem numD8_cleanup_step_entry (env : Env) (s : State) (hpc : s.pc = "cleanup")
    (hpre : s.pre = some "entry") :
    step numD8Calls numD8Body (stateAt env s) =
      .ret (some (.int 32 0)) (stateAt (("%retval.0", .int 32 0) :: env) s) := by
  have hcode := numD8_cleanup_denote_entry env s hpre
  have hret : lookupName (("%retval.0", .int 32 0) :: env) "%retval.0" =
      some (.int 32 0) := by block_lk
  have hop : evalOperand (stateAt (("%retval.0", .int 32 0) :: env) s) (.reg "%retval.0") =
      some (.int 32 0) := BlockEval.evalOperand_reg_of _ _ _ _ hret
  unfold step execTerm
  rw [show (stateAt env s).pc = "cleanup" from hpc, numD8_findBlock_cleanup]
  simp only [hcode, hop]

/-! #### The runs -/

theorem numD8_runFuel_jump {calls : Calls} {f : Function} {s t : State}
    (h : step calls f s = .jump t) : ∀ k, runFuel calls (1 + k) f s = runFuel calls k f t := by
  intro k
  rw [show 1 + k = k + 1 from Nat.add_comm 1 k, runFuel.eq_2, h]

theorem numD8_runFuel_ret {calls : Calls} {f : Function} {s s' : State} {v : Option Value}
    (h : step calls f s = .ret v s') : runFuel calls 1 f s = some (.ret v s'.mem) := by
  rw [show (1 : Nat) = 0 + 1 from rfl, runFuel.eq_2, h]

def numD8Raw (mem : Mem) (next : Nat) : State :=
  { env := [], mem := mem, next := next, pc := "entry", pre := none }

theorem numD8_run_success (v : BitVec 64) (p val : Nat) (mem : Mem) (next : Nat)
    (hd : ∀ k, k < 8 → 0x30 ≤ numD8ByteNat v k ∧ numD8ByteNat v k ≤ 0x39)
    (hprod : numD8Product v < 2 ^ 32)
    (hread : readBytes mem p 8 = some (natToBytes v.toNat 8)) (htest : numD8Test v = 1) :
    runFuel numD8Calls 3 numD8Body (numD8EntryState p val mem next) =
      some (.ret (some (.int 32 1)) (writeBytes mem val (natToBytes (numD8Product v) 4))) := by
  have h1 : step numD8Calls numD8Body (numD8EntryState p val mem next) =
      .jump (stateAt (numD8AfterEntryEnv p val v)
        { numD8Raw mem next with pc := "if.end", pre := some "entry" }) := by
    rw [show numD8EntryState p val mem next =
        stateAt (numD8EntryEnv p val) (numD8Raw mem next) from rfl]
    exact numD8_entry_step_success v p val (numD8Raw mem next) rfl hread htest
  have h2 : step numD8Calls numD8Body
      (stateAt (numD8AfterEntryEnv p val v)
        { numD8Raw mem next with pc := "if.end", pre := some "entry" }) =
      .jump (stateAt (numD8AfterIfEndEnv p val v)
        { numD8Raw mem next with
          mem := writeBytes mem val (natToBytes (numD8Product v) 4),
          pc := "cleanup", pre := some "if.end" }) :=
    numD8_ifEnd_step v p val _ rfl hd hprod
  have h3 : step numD8Calls numD8Body
      (stateAt (numD8AfterIfEndEnv p val v)
        { numD8Raw mem next with
          mem := writeBytes mem val (natToBytes (numD8Product v) 4),
          pc := "cleanup", pre := some "if.end" }) =
      .ret (some (.int 32 1))
        (stateAt (("%retval.0", .int 32 1) :: numD8AfterIfEndEnv p val v)
          { numD8Raw mem next with
            mem := writeBytes mem val (natToBytes (numD8Product v) 4),
            pc := "cleanup", pre := some "if.end" }) :=
    numD8_cleanup_step_ifEnd _ _ rfl rfl
  exact runFuel_prefix_some
    (runFuel_prefix_trans (numD8_runFuel_jump h1) (numD8_runFuel_jump h2))
    (numD8_runFuel_ret h3)

theorem numD8_run_refusal (v : BitVec 64) (p val : Nat) (mem : Mem) (next : Nat)
    (hread : readBytes mem p 8 = some (natToBytes v.toNat 8)) (htest : numD8Test v = 0) :
    runFuel numD8Calls 3 numD8Body (numD8EntryState p val mem next) =
      some (.ret (some (.int 32 0)) mem) := by
  have h1 : step numD8Calls numD8Body (numD8EntryState p val mem next) =
      .jump (stateAt (numD8AfterEntryEnv p val v)
        { numD8Raw mem next with pc := "cleanup", pre := some "entry" }) := by
    rw [show numD8EntryState p val mem next =
        stateAt (numD8EntryEnv p val) (numD8Raw mem next) from rfl]
    exact numD8_entry_step_refusal v p val (numD8Raw mem next) rfl hread htest
  have h2 : step numD8Calls numD8Body
      (stateAt (numD8AfterEntryEnv p val v)
        { numD8Raw mem next with pc := "cleanup", pre := some "entry" }) =
      .ret (some (.int 32 0))
        (stateAt (("%retval.0", .int 32 0) :: numD8AfterEntryEnv p val v)
          { numD8Raw mem next with pc := "cleanup", pre := some "entry" }) :=
    numD8_cleanup_step_entry _ _ rfl rfl
  rw [show (3 : Nat) = 1 + 2 from rfl, numD8_runFuel_jump h1 2]
  rw [show (2 : Nat) = 1 + 1 from rfl, runFuel.eq_2, h2]
  rfl

/-! #### The selection's reader arm -/

theorem bytesToNat_lt_eight (bs : List UInt8) : bytesToNat bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [bytesToNat]
  | cons b rest ih =>
      show b.toNat + 256 * bytesToNat rest < 256 ^ (rest.length + 1)
      rw [Nat.pow_succ]
      have hb : b.toNat < 256 := UInt8.toNat_lt b
      calc b.toNat + 256 * bytesToNat rest < 256 + 256 * bytesToNat rest := by omega
        _ = 256 * (bytesToNat rest + 1) := by omega
        _ ≤ 256 * 256 ^ rest.length := Nat.mul_le_mul_left 256 (by omega)
        _ = 256 ^ rest.length * 256 := Nat.mul_comm _ _

theorem natToBytes_ofNat64_bytesToNat (bs : List UInt8) (hlen : bs.length = 8) :
    natToBytes (BitVec.ofNat 64 (bytesToNat bs)).toNat 8 = bs := by
  have hlt : bytesToNat bs < 2 ^ 64 := by
    have h := bytesToNat_lt_eight bs
    rw [hlen] at h
    have h256 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, ← hlen]
  have h := natToBytes_bytesToNat bs bs.length (le_refl _)
  rw [List.take_of_length_le (by rw [natToBytes_length])] at h
  exact h

/-- A run's outcome as the call's answer. -/
def numD8OptionOutcome : Option Outcome → Nat → Option CallOutcome
  | some (.ret (some v) m), next => some { ret := v, mem := m, next := next }
  | _, _ => none

/-- The body's answer, run from the selection's entry state. -/
def numD8RunAnswer (p val : Nat) (mem : Mem) (next : Nat) : Option CallOutcome :=
  numD8OptionOutcome (runFuel numD8Calls 3 numD8Body (numD8EntryState p val mem next)) next

theorem numD8RunAnswer_success (v : BitVec 64) (p val : Nat) (mem : Mem) (next : Nat)
    (hd : ∀ k, k < 8 → 0x30 ≤ numD8ByteNat v k ∧ numD8ByteNat v k ≤ 0x39)
    (hprod : numD8Product v < 2 ^ 32)
    (hread : readBytes mem p 8 = some (natToBytes v.toNat 8)) (htest : numD8Test v = 1) :
    numD8RunAnswer p val mem next =
      some { ret := .int 32 1, mem := writeBytes mem val (natToBytes (numD8Product v) 4),
             next := next } := by
  exact congrArg (fun o => numD8OptionOutcome o next)
    (numD8_run_success v p val mem next hd hprod hread htest)

theorem numD8RunAnswer_refusal (v : BitVec 64) (p val : Nat) (mem : Mem) (next : Nat)
    (hread : readBytes mem p 8 = some (natToBytes v.toNat 8)) (htest : numD8Test v = 0) :
    numD8RunAnswer p val mem next =
      some { ret := .int 32 0, mem := mem, next := next } := by
  exact congrArg (fun o => numD8OptionOutcome o next)
    (numD8_run_refusal v p val mem next hread htest)

theorem numD8RunAnswer_eq (p val : Nat) (mem : Mem) (next : Nat) {bs : List UInt8}
    (hread : readBytes mem p 8 = some bs) :
    numD8RunAnswer p val mem next = numD8Answer [.ptr p, .ptr val] mem next := by
  have hlen : bs.length = 8 := JsonEntrySteps.readBytes_length mem p 8 hread
  have hbytes := natToBytes_ofNat64_bytesToNat bs hlen
  have hread' : readBytes mem p 8 =
      some (natToBytes (BitVec.ofNat 64 (bytesToNat bs)).toNat 8) := by
    rw [hbytes]; exact hread
  cases hd8 : d8Value bs with
  | some w =>
      have htest : numD8Test (BitVec.ofNat 64 (bytesToNat bs)) = 1 := by
        refine (numD8Test_iff _).mpr ?_
        rw [hbytes, hd8]
        exact Option.some_ne_none w
      have hdig := numD8_digits_of_test _ htest
      have hprod := numD8Product_lt _ hdig
      have hval := numD8_d8Value_of_digits _ hdig
      have hs : d8Value (natToBytes (BitVec.ofNat 64 (bytesToNat bs)).toNat 8) = some w := by
        rw [hbytes]
        exact hd8
      have hw : w = numD8Product (BitVec.ofNat 64 (bytesToNat bs)) :=
        (Option.some.inj (hval.symm.trans hs)).symm
      rw [numD8RunAnswer_success _ p val mem next hdig hprod hread' htest,
        numD8Answer_read hread hd8, hw]
  | none =>
      have htest : numD8Test (BitVec.ofNat 64 (bytesToNat bs)) = 0 := by
        rcases BlockEval.bitVec1_eq_zero_or_one
          (numD8Test (BitVec.ofNat 64 (bytesToNat bs))) with h | h
        · exact h
        · exfalso
          have hne : d8Value (natToBytes (BitVec.ofNat 64 (bytesToNat bs)).toNat 8) ≠ none :=
            (numD8Test_iff _).mp h
          rw [hbytes, hd8] at hne
          exact hne (by simp)
      rw [numD8RunAnswer_refusal _ p val mem next hread' htest,
        numD8Answer_refuse hread hd8]

/-- The walk's environment with the reader answered by its pinned body. -/
def numD8BodyCalls (base : Calls) : Calls :=
  fun callee args mem next =>
    if callee = "num_d8_el1" then
      match args with
      | [.ptr p, .ptr val] => numD8RunAnswer p val mem next
      | _ => none
    else base callee args mem next

/-- **The reader's arm is the model.**  At the two pointer arguments the selection
passes, the environment whose `num_d8_el1` is the pinned body's run answers exactly
`numD8Answer`: the compiled three blocks answer with the model rather than `ub`. -/
theorem numD8BodyCalls_num_d8 (base : Calls) (p val : Nat) (mem : Mem) (next : Nat)
    {bs : List UInt8} (hread : readBytes mem p 8 = some bs) :
    numD8BodyCalls base "num_d8_el1" [.ptr p, .ptr val] mem next =
      numD8Answer [.ptr p, .ptr val] mem next := by
  simp only [numD8BodyCalls, if_true]
  exact numD8RunAnswer_eq p val mem next hread


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

/-- info: 'LeanLLVM.Refinement.numD8Test_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numD8Test_iff

/-- info: 'LeanLLVM.Refinement.numD8_d8Value_of_digits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numD8_d8Value_of_digits

/-- info: 'LeanLLVM.Refinement.numD8Product_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numD8Product_lt

/-- info: 'LeanLLVM.Refinement.numD8_run_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numD8_run_success

/-- info: 'LeanLLVM.Refinement.numD8_run_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numD8_run_refusal

/-- info: 'LeanLLVM.Refinement.numD8RunAnswer_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numD8RunAnswer_eq

/-- info: 'LeanLLVM.Refinement.numD8BodyCalls_num_d8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numD8BodyCalls_num_d8


end LeanLLVM.Refinement