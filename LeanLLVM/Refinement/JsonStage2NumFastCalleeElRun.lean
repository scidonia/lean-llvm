/-
`num_el_el1`'s run: the emitted body, block by block, to its answer on every arm.

`JsonStage2NumFastCalleeEl` pins the body and states what each instruction
computes — the address, the guard slice, the window test, the staging and the
window arm's counter write — and `JsonStage2NumFastCalleeElFacts` supplies the
two arithmetic bridges the model needs (`ctlz` against `Nat.size`, and the
`i128` product's `toNat` readings).  What neither states is the body's *run*: the
denotation of the five blocks that reach `return`, and the answer they give at
the `Calls` boundary.  This module is that run.

**The words.**  Each register the guard computes is named once (`eSub`, `eRow`,
`e0`, `eCast`, `eShl`, `eConv`, `eMul`, `eShr`, `eConv6`, `eShr7`, `eConv8`,
`eShl9`, `eOr`, `eAnd`, `eShl11`, `eConv12`, `eReass`, `eSub14`, `eCmp15`, and
`eAdd19`, `eShr21`, `eCmp22`, `eConv23` for the fast arm), with the expression the
pinned instruction's step produces, so a block's denotation is a computation over
the body's own terms.  The model's words — `elW`, `elAhi`, `elUb`, `elHp`, `elHh`,
`elM`, `elUp`, `elWindow` — are the same arithmetic in `Nat`, and the two sets are
proved equal where the run reads them (`eConv6_toNat`, `eAnd_toNat`,
`eCmp15_eq_one_iff`, `eShr21_toNat`, …).

**The run.**  `numElRunAnswer epow w q out mem next` is the body's answer at the
environment that answers `llvm.ctlz.i64`, `el_exact` and `el_pack`
(`numElCalls epow`, from `JsonStage2NumFastCalleeEl`): fuel four — the entry, the
guard, one arm and the return.  Each arm's answer is stated with the write it
makes:

* `numEl_run_zero` — `%w = 0`: `*out = 0.0`, return one;
* `numEl_run_window_some` / `_none` — the window arm: the counter's word is read,
  incremented and stored back, then `el_exact` writes `out` and its answer is
  returned;
* `numEl_run_fast_some` / `_none` — the fast arm: `el_pack` writes `out` and its
  answer is returned, and nothing else moves.

**The arm, at the model.**  `numElAnswer` is `numElAnswerAt numElWindowAddr`:
`numElWindow` names the window arm, `numElCounterMem` writes the counter's next
word there, and `numElWindowMem` is the caller's memory on the other arms.  So the
body's answer and the model's are the *same* `CallOutcome` on every arm the kernel
decides: `numElBodyCalls_eq` is the equality for a nonzero mantissa, with the two
memories identified through `numEl_ifThen18_counter_write`
(the emitted store's word is `numElCounterMem`'s), and `numElBodyCalls_eq_zero` is
the zero mantissa's.  The selection `numElBodyCalls base epow` answers
`num_el_el1` with this run, so the equality is exactly the value
`NumFastCalleesAnswered` names for the callee, at every staged row and counter.
The release path's site that reads the equality — `if.end268` at
`stage2NumFastCalls guardTable`, with the emitted table's exponent bound
discharged by the table's own sweep — is
`JsonStage2NumFastCalleeElSeam`.
-/
import LeanLLVM.Refinement.JsonStage2NumFastCalleeEl
import LeanLLVM.Refinement.JsonStage2NumFastCalleeElFacts
import LeanLLVM.Refinement.JsonStage2NumFastCalleeMul

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval

/-! ### The emitted words

Each is the expression its instruction's step produces from the previous ones, so
the block's denotation is checked against the body rather than against a second
arithmetic. -/

/-- `%sub = %q + 45`: the table index. -/
def eSub (q : BitVec 64) : BitVec 64 := q + 0x000000000000002d#64

/-- `%arrayidx`: the row's address, `@EPOW + 24 * %sub`. -/
def eRow (q : BitVec 64) : Nat := 0x100000 + (eSub q).toNat * 24

/-- `%0`: `llvm.ctlz.i64 %w`. -/
def e0 (w : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (BitLanes.ctlz w)

/-- `%cast = trunc i64 %0 to i32`. -/
def eCast (w : BitVec 64) : BitVec 32 := BitVec.ofNat 32 ((e0 w).toNat % 2 ^ 32)

/-- `%shl = %w << %0`: the normalised mantissa. -/
def eShl (w : BitVec 64) : BitVec 64 := w <<< (e0 w).toNat

/-- `%conv = zext i64 %shl to i128`. -/
def eConv (w : BitVec 64) : BitVec 128 := BitVec.ofNat 128 (eShl w).toNat

/-- `%1`, the row's `hi` word, as the load binds it. -/
def eHi (hi : Nat) : BitVec 64 := BitVec.ofNat 64 hi

/-- `%conv5 = zext i64 %1 to i128`. -/
def eConv5 (hi : Nat) : BitVec 128 := BitVec.ofNat 128 (eHi hi).toNat

/-- `%mul = mul i128 %conv5, %conv`. -/
def eMul (w : BitVec 64) (hi : Nat) : BitVec 128 := eConv5 hi * eConv w

/-- `%shr = lshr i128 %mul, 64`. -/
def eShr (w : BitVec 64) (hi : Nat) : BitVec 128 :=
  eMul w hi >>> (0x00000000000000000000000000000040#128).toNat

/-- `%conv6 = trunc i128 %shr to i64`: the product's high word. -/
def eConv6 (w : BitVec 64) (hi : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((eShr w hi).toNat % 2 ^ 64)

/-- `%shr7 = %conv6 >>> 63`: the slice's top bit. -/
def eShr7 (w : BitVec 64) (hi : Nat) : BitVec 64 :=
  eConv6 w hi >>> (0x000000000000003f#64).toNat

/-- `%conv8 = trunc i64 %shr7 to i32`. -/
def eConv8 (w : BitVec 64) (hi : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((eShr7 w hi).toNat % 2 ^ 32)

/-- `%shl9 = %shr7 << 10`. -/
def eShl9 (w : BitVec 64) (hi : Nat) : BitVec 64 :=
  eShr7 w hi <<< (0x000000000000000a#64).toNat

/-- `%or = %shl9 | 1023`: the mask `2 ^ (10 + ub) - 1`. -/
def eOr (w : BitVec 64) (hi : Nat) : BitVec 64 := eShl9 w hi ||| 0x00000000000003ff#64

/-- `%and = %or & %conv6`: the guard slice. -/
def eAnd (w : BitVec 64) (hi : Nat) : BitVec 64 := eOr w hi &&& eConv6 w hi

/-- `%shl11 = 512 << %conv8`: half the slice. -/
def eShl11 (w : BitVec 64) (hi : Nat) : BitVec 32 :=
  (0x00000200#32) <<< (eConv8 w hi).toNat

/-- `%conv12 = zext i32 %shl11 to i64`. -/
def eConv12 (w : BitVec 64) (hi : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (eShl11 w hi).toNat

/-- `%reass.sub = %and - %conv12`. -/
def eReass (w : BitVec 64) (hi : Nat) : BitVec 64 := eAnd w hi - eConv12 w hi

/-- `%sub14 = %reass.sub + 2`. -/
def eSub14 (w : BitVec 64) (hi : Nat) : BitVec 64 := eReass w hi + 0x0000000000000002#64

/-- `%cmp15 = icmp ult %sub14, 3`: the window test. -/
def eCmp15 (w : BitVec 64) (hi : Nat) : BitVec 1 :=
  evalICmp .ult (eSub14 w hi) 0x0000000000000003#64

/-- `%add = %shr7 | 10`: the fast arm's shift count. -/
def eAdd19 (w : BitVec 64) (hi : Nat) : BitVec 64 := eShr7 w hi ||| 0x000000000000000a#64

/-- `%shr21 = %conv6 >>> %add`: the significand's quotient. -/
def eShr21 (w : BitVec 64) (hi : Nat) : BitVec 64 := eConv6 w hi >>> (eAdd19 w hi).toNat

/-- `%cmp22 = icmp ugt %and, %conv12`: the round-up test. -/
def eCmp22 (w : BitVec 64) (hi : Nat) : BitVec 1 :=
  evalICmp .ugt (eAnd w hi) (eConv12 w hi)

/-- `%conv23 = zext i1 %cmp22 to i32`. -/
def eConv23 (w : BitVec 64) (hi : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (eCmp22 w hi).toNat

/-- `%arrayidx.val`, the row's exponent word, as the load binds it. -/
def eE (t : EPow) : BitVec 32 := BitVec.ofNat 32 (epowEWord t.e)

/-! ### The model's words

The same arithmetic in `Nat`, spelled as `numElEl1` spells it. -/

/-- The model's normalised mantissa `w * 2 ^ (64 - size w)`. -/
def elW (n : Nat) : Nat := n * 2 ^ (64 - Nat.size n)

/-- The product's high word: the model's `Ahi`. -/
def elAhi (n hi : Nat) : Nat := elW n * hi / 2 ^ 64

/-- The slice's top bit. -/
def elUb (n hi : Nat) : Nat := elAhi n hi / 2 ^ 63

/-- The guard slice. -/
def elHp (n hi : Nat) : Nat := elAhi n hi % 2 ^ (10 + elUb n hi)

/-- Half the slice. -/
def elHh (n hi : Nat) : Nat := 2 ^ (9 + elUb n hi)

/-- The fast arm's quotient. -/
def elM (n hi : Nat) : Nat := elAhi n hi / 2 ^ (10 + elUb n hi)

/-- The fast arm's round-up bit. -/
def elUp (n hi : Nat) : Nat := if elHp n hi > elHh n hi then 1 else 0

/-- The three-value window, as `numElEl1` tests it. -/
abbrev elWindow (n hi : Nat) : Prop := elHh n hi ≤ elHp n hi + 2 ∧ elHp n hi ≤ elHh n hi

/-! ### The comparisons' one-bit readings

The two tests the arm branches on are `evalICmp`'s `i1`, read at the `Nat` order
the same way every other block in this tree reads one. -/

/-- `icmp ult` at one is the `Nat` order. -/
theorem numEl_evalICmp_ult_one {w : Nat} (x y : BitVec w) :
    evalICmp .ult x y = (1 : BitVec 1) ↔ x.toNat < y.toNat := by
  unfold evalICmp
  cases hb : BitVec.ult x y
  · have h : ¬ x.toNat < y.toNat := by
      intro hlt
      have htrue : BitVec.ult x y = true := (BitVec.ult_iff_toNat_lt).2 hlt
      rw [htrue] at hb
      exact Bool.noConfusion hb
    simp [h]
  · have h : x.toNat < y.toNat := by
      rw [← BitVec.ult_iff_toNat_lt]
      exact hb
    simp [h]

/-- `icmp ugt` at one is the `Nat` order on the operands. -/
theorem numEl_evalICmp_ugt_one {w : Nat} (x y : BitVec w) :
    evalICmp .ugt x y = (1 : BitVec 1) ↔ y.toNat < x.toNat := by
  unfold evalICmp
  cases hb : BitVec.ult y x
  · have h : ¬ y.toNat < x.toNat := by
      intro hlt
      have htrue : BitVec.ult y x = true := (BitVec.ult_iff_toNat_lt).2 hlt
      rw [htrue] at hb
      exact Bool.noConfusion hb
    simp [h]
  · have h : y.toNat < x.toNat := by
      rw [← BitVec.ult_iff_toNat_lt]
      exact hb
    simp [h]

/-! ### The bounds the arithmetic runs at -/

/-- A nonzero sixty-four-bit word normalises inside `2 ^ 64`. -/
theorem elW_lt (n : Nat) (hn : n < 2 ^ 64) (hn0 : n ≠ 0) : elW n < 2 ^ 64 :=
  wnorm_lt n hn hn0

/-- Two sixty-four-bit words' product fits `i128`. -/
theorem elProd_lt (n hi : Nat) (hn : n < 2 ^ 64) (hn0 : n ≠ 0) (hhi : hi < 2 ^ 64) :
    hi * elW n < 2 ^ 128 := by
  have hW := elW_lt n hn hn0
  have hhi' : hi ≤ 2 ^ 64 - 1 := by omega
  calc hi * elW n ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
        Nat.mul_le_mul hhi' (by omega)
    _ < 2 ^ 128 := by decide

/-- The product's high word is a sixty-four-bit word. -/
theorem elAhi_lt (n hi : Nat) (hn : n < 2 ^ 64) (hn0 : n ≠ 0) (hhi : hi < 2 ^ 64) :
    elAhi n hi < 2 ^ 64 := by
  unfold elAhi
  rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 64)]
  rw [show (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 from by decide]
  rw [Nat.mul_comm (elW n) hi]
  exact elProd_lt n hi hn hn0 hhi

/-- The slice's top bit is at most one. -/
theorem elUb_le (n hi : Nat) (hn : n < 2 ^ 64) (hn0 : n ≠ 0) (hhi : hi < 2 ^ 64) :
    elUb n hi ≤ 1 := by
  unfold elUb
  have h : elAhi n hi / 2 ^ 63 < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 63)]
    rw [show (2 : Nat) * 2 ^ 63 = 2 ^ 64 from by decide]
    exact elAhi_lt n hi hn hn0 hhi
  omega

/-- The slice is below `2 ^ 64`. -/
theorem elHp_lt (n hi : Nat) (hn : n < 2 ^ 64) (hn0 : n ≠ 0) (hhi : hi < 2 ^ 64) :
    elHp n hi < 2 ^ 64 := by
  unfold elHp
  have hle : 10 + elUb n hi ≤ 64 := by
    have := elUb_le n hi hn hn0 hhi
    omega
  calc elAhi n hi % 2 ^ (10 + elUb n hi) < 2 ^ (10 + elUb n hi) :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hle

/-- Half the slice is in the window's range. -/
theorem elHh_two (n hi : Nat) (hn : n < 2 ^ 64) (hn0 : n ≠ 0) (hhi : hi < 2 ^ 64) :
    2 ≤ elHh n hi ∧ elHh n hi ≤ 2 ^ 11 := by
  have hle := elUb_le n hi hn hn0 hhi
  unfold elHh
  constructor
  · calc 2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ (9 + elUb n hi) := Nat.pow_le_pow_right (by decide) (by omega)
  · calc 2 ^ (9 + elUb n hi) ≤ 2 ^ (9 + 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by omega)

/-- Half the slice is below `2 ^ 64`. -/
theorem elHh_lt (n hi : Nat) (hn : n < 2 ^ 64) (hn0 : n ≠ 0) (hhi : hi < 2 ^ 64) :
    elHh n hi ≤ 2 ^ 64 := by
  have := (elHh_two n hi hn hn0 hhi).2
  omega

/-- A `ofNat` of a value already inside the width is that value's `toNat`. -/
theorem bvOfNat_toNat_of_lt {w n : Nat} (h : n < 2 ^ w) :
    (BitVec.ofNat w n).toNat = n :=
  ofNat_ofNat_of_lt h

/-! ### The words against the model's -/

/-- The counted zeroes are `64 - size`. -/
theorem e0_toNat (w : BitVec 64) (hw : w ≠ 0) : (e0 w).toNat = BitLanes.ctlz w := by
  rw [e0, bvOfNat_toNat_of_lt]
  rw [ctlz_eq_size w hw]
  have := Nat.size_le.mpr w.isLt
  omega

/-- `%cast`'s word is the model's shift count. -/
theorem eCast_toNat (w : BitVec 64) (hw : w ≠ 0) :
    (eCast w).toNat = 64 - Nat.size w.toNat := by
  have hb : (e0 w).toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [eCast, bvOfNat_toNat_of_lt hb, e0_toNat w hw, ctlz_eq_size w hw]
  exact Nat.mod_eq_of_lt (by
    have := Nat.size_le.mpr w.isLt
    rw [show (2 : Nat) ^ 32 = 4294967296 from by decide]
    omega)

/-- The row's `hi` word, as a `toNat`. -/
theorem eHi_toNat (hi : Nat) (hhi : hi < 2 ^ 64) : (eHi hi).toNat = hi :=
  bvOfNat_toNat_of_lt hhi

/-- The widened `hi` word keeps its value. -/
theorem eConv5_toNat (hi : Nat) (hhi : hi < 2 ^ 64) : (eConv5 hi).toNat = hi := by
  rw [eConv5, bvOfNat_toNat_of_lt]
  · exact eHi_toNat hi hhi
  · rw [eHi_toNat hi hhi]
    rw [show (2 : Nat) ^ 128 = 340282366920938463463374607431768211456 from by decide]
    omega

/-- **The normalised mantissa is the model's.** -/
theorem eShl_toNat (w : BitVec 64) (hw : w ≠ 0) : (eShl w).toNat = elW w.toNat := by
  rw [eShl, e0_toNat w hw, ctlz_eq_size w hw]
  have hw0 : w.toNat ≠ 0 := by
    intro h0; exact hw (BitVec.toNat_inj.mp (by simpa using h0))
  unfold elW
  exact toNat_shiftLeft_of_mul_lt w _
    (elW_lt w.toNat w.isLt hw0)

/-- The widened mantissa keeps its value. -/
theorem eConv_toNat (w : BitVec 64) (hw : w ≠ 0) : (eConv w).toNat = elW w.toNat := by
  rw [eConv, bvOfNat_toNat_of_lt]
  · exact eShl_toNat w hw
  · rw [eShl_toNat w hw]
    have hw0 : w.toNat ≠ 0 := by
      intro h0; exact hw (BitVec.toNat_inj.mp (by simpa using h0))
    rw [show (2 : Nat) ^ 128 = 340282366920938463463374607431768211456 from by decide]
    have := elW_lt w.toNat w.isLt hw0
    omega

/-- The `i128` product's `toNat` is the doubled value, at two sixty-four-bit
factors. -/
theorem eMul_toNat (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    (eMul w hi).toNat = hi * elW w.toNat := by
  rw [eMul, toNat_mul_mod, eConv5_toNat hi hhi, eConv_toNat w hw]
  have hw0 : w.toNat ≠ 0 := by
    intro h0; exact hw (BitVec.toNat_inj.mp (by simpa using h0))
  exact Nat.mod_eq_of_lt (elProd_lt w.toNat hi w.isLt hw0 hhi)

/-- The high word is the model's `Ahi`. -/
theorem eConv6_toNat (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    (eConv6 w hi).toNat = elAhi w.toNat hi := by
  have hb : (eShr w hi).toNat % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hw0 : w.toNat ≠ 0 := by
    intro h0; exact hw (BitVec.toNat_inj.mp (by simpa using h0))
  rw [eConv6, bvOfNat_toNat_of_lt hb, eShr, toNat_ushiftRight_div,
    show (0x00000000000000000000000000000040#128).toNat = 64 from by decide,
    eMul_toNat w hi hw hhi]
  unfold elAhi
  rw [Nat.mul_comm (elW w.toNat) hi]
  rw [Nat.mod_eq_of_lt (by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 64)]
    rw [show (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 from by decide]
    exact elProd_lt w.toNat hi w.isLt hw0 hhi)]

/-- The high word as a `BitVec`. -/
theorem eConv6_eq_ofNat (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    eConv6 w hi = BitVec.ofNat 64 (elAhi w.toNat hi) := by
  have hw0 : w.toNat ≠ 0 := by
    intro h0; exact hw (BitVec.toNat_inj.mp (by simpa using h0))
  apply BitVec.toNat_inj.mp
  rw [eConv6_toNat w hi hw hhi]
  exact (bvOfNat_toNat_of_lt (elAhi_lt w.toNat hi w.isLt hw0 hhi)).symm

/-- The slice's top bit is `Ahi`'s. -/
theorem eShr7_toNat (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    (eShr7 w hi).toNat = elUb w.toNat hi := by
  rw [eShr7, toNat_ushiftRight_div,
    show (0x000000000000003f#64).toNat = 63 from by decide,
    eConv6_toNat w hi hw hhi]
  rfl

/-- The slice's top bit as a word. -/
theorem eShr7_eq_ofNat (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    eShr7 w hi = BitVec.ofNat 64 (elUb w.toNat hi) := by
  have hw0 : w.toNat ≠ 0 := by
    intro h0; exact hw (BitVec.toNat_inj.mp (by simpa using h0))
  apply BitVec.toNat_inj.mp
  rw [eShr7_toNat w hi hw hhi]
  exact (bvOfNat_toNat_of_lt (by
    have := elUb_le w.toNat hi w.isLt hw0 hhi
    omega)).symm

/-- The truncated slice bit is the model's `ub`. -/
theorem eConv8_toNat (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    (eConv8 w hi).toNat = elUb w.toNat hi := by
  have hb : (eShr7 w hi).toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hw0 : w.toNat ≠ 0 := by
    intro h0; exact hw (BitVec.toNat_inj.mp (by simpa using h0))
  rw [eConv8, bvOfNat_toNat_of_lt hb, eShr7_toNat w hi hw hhi]
  exact Nat.mod_eq_of_lt (by
    have := elUb_le w.toNat hi w.isLt hw0 hhi
    rw [show (2 : Nat) ^ 32 = 4294967296 from by decide]
    omega)

/-- The truncated slice bit as a word. -/
theorem eConv8_eq_ofNat (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    eConv8 w hi = BitVec.ofNat 32 (elUb w.toNat hi) := by
  have hw0 : w.toNat ≠ 0 := by
    intro h0; exact hw (BitVec.toNat_inj.mp (by simpa using h0))
  apply BitVec.toNat_inj.mp
  rw [eConv8_toNat w hi hw hhi]
  exact (bvOfNat_toNat_of_lt (by
    have := elUb_le w.toNat hi w.isLt hw0 hhi
    omega)).symm

/-- The mask word's `BitVec` is the slice bit's shift. -/
theorem eOr_eq (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    eOr w hi = ((BitVec.ofNat 64 (elUb w.toNat hi)) <<< 10) ||| 1023 := by
  rw [eOr, eShl9, eShr7_eq_ofNat w hi hw hhi,
    show (0x000000000000000a#64).toNat = 10 from by decide]
  rfl

/-- `%or`'s `toNat` is the mask's. -/
theorem eOr_toNat (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    (eOr w hi).toNat = 2 ^ (10 + elUb w.toNat hi) - 1 := by
  have hw0 : w.toNat ≠ 0 := by
    intro h0; exact hw (BitVec.toNat_inj.mp (by simpa using h0))
  rw [eOr_eq w hi hw hhi]
  exact numEl_mask (elUb w.toNat hi) (elUb_le w.toNat hi w.isLt hw0 hhi)

/-- The guard slice is the model's `hp`. -/
theorem eAnd_toNat (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    (eAnd w hi).toNat = elHp w.toNat hi := by
  rw [eAnd, BitVec.toNat_and, eOr_toNat w hi hw hhi,
    eConv6_toNat w hi hw hhi, Nat.and_comm]
  exact land_two_pow_sub_one _ _

/-- Half the slice's `toNat`. -/
theorem eConv12_toNat (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    (eConv12 w hi).toNat = elHh w.toNat hi := by
  have hw0 : w.toNat ≠ 0 := by
    intro h0; exact hw (BitVec.toNat_inj.mp (by simpa using h0))
  have hb : (eShl11 w hi).toNat < 2 ^ 64 := by
    have := (eShl11 w hi).isLt
    omega
  rw [eConv12, bvOfNat_toNat_of_lt hb, eShl11, eConv8_toNat w hi hw hhi]
  exact numEl_half (elUb w.toNat hi) (elUb_le w.toNat hi w.isLt hw0 hhi)

/-- The wrapped difference's `toNat`. -/
theorem eReass_toNat (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    (eReass w hi).toNat
      = (elHp w.toNat hi + 2 ^ 64 - elHh w.toNat hi) % 2 ^ 64 := by
  have hw0 : w.toNat ≠ 0 := by
    intro h0; exact hw (BitVec.toNat_inj.mp (by simpa using h0))
  have hhle := elHh_lt w.toNat hi w.isLt hw0 hhi
  rw [eReass, BitVec.toNat_sub, eAnd_toNat w hi hw hhi, eConv12_toNat w hi hw hhi]
  rw [show (2 ^ 64 - elHh w.toNat hi + elHp w.toNat hi)
      = elHp w.toNat hi + (2 ^ 64 - elHh w.toNat hi) from by omega,
    Nat.add_sub_assoc hhle]

/-- `%sub14`'s `toNat` is the wrapped sum the model's window reads. -/
theorem eSub14_toNat (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    (eSub14 w hi).toNat
      = ((elHp w.toNat hi + 2 ^ 64 - elHh w.toNat hi) % 2 ^ 64 + 2) % 2 ^ 64 := by
  rw [eSub14, BitVec.toNat_add, eReass_toNat w hi hw hhi,
    show (0x0000000000000002#64).toNat = 2 from by decide]

/-- The model's window at the body's `%cmp15`. -/
theorem eCmp15_eq_one_iff (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    eCmp15 w hi = 1 ↔ elWindow w.toNat hi := by
  have hn0 : w.toNat ≠ 0 := by
    intro h0; exact hw (BitVec.toNat_inj.mp (by simpa using h0))
  have hh := elHh_two w.toNat hi w.isLt hn0 hhi
  have hp_lt := elHp_lt w.toNat hi w.isLt hn0 hhi
  have hwin := numEl_window (elHp w.toNat hi) (elHh w.toNat hi) hh.1 hh.2 hp_lt
  have hin : elWindow w.toNat hi ↔
      LeanLLVM.ElGuardRefine.inWindow (elHp w.toNat hi) (elHh w.toNat hi) = true := by
    rw [LeanLLVM.ElGuardRefine.inWindow_iff hh.1 hh.2 hp_lt]
    unfold elWindow
    constructor <;> intro h' <;> omega
  have hsub := eSub14_toNat w hi hw hhi
  rw [eCmp15, numEl_evalICmp_ult_one, hsub,
    show (0x0000000000000003#64).toNat = 3 from by decide]
  constructor
  · intro h'
    exact hin.mpr (hwin.mp (by omega))
  · intro h'
    have hle : ((elHp w.toNat hi + 2 ^ 64 - elHh w.toNat hi) % 2 ^ 64 + 2) % 2 ^ 64 ≤ 2 :=
      hwin.mpr (hin.mp h')
    omega

/-- The model's window false, at `%cmp15 = 0`. -/
theorem eCmp15_eq_zero_iff (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    eCmp15 w hi = 0 ↔ ¬ elWindow w.toNat hi := by
  constructor
  · intro h hw'
    have hone := (eCmp15_eq_one_iff w hi hw hhi).mpr hw'
    rw [hone] at h
    exact absurd h (by decide)
  · intro h
    rcases BlockEval.bitVec1_eq_zero_or_one (eCmp15 w hi) with h0 | h0
    · exact h0
    · exact absurd ((eCmp15_eq_one_iff w hi hw hhi).mp h0) h

/-- `%add`'s `toNat` is `10 + ub`. -/
theorem eAdd19_toNat (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    (eAdd19 w hi).toNat = 10 + elUb w.toNat hi := by
  have hw0 : w.toNat ≠ 0 := by
    intro h0; exact hw (BitVec.toNat_inj.mp (by simpa using h0))
  rw [eAdd19, BitVec.toNat_or, eShr7_toNat w hi hw hhi,
    show (0x000000000000000a#64).toNat = 10 from by decide, Nat.or_comm]
  exact numEl_shift (elUb w.toNat hi) (elUb_le w.toNat hi w.isLt hw0 hhi)

/-- `%shr21` is the model's quotient. -/
theorem eShr21_toNat (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    (eShr21 w hi).toNat = elM w.toNat hi := by
  rw [eShr21, toNat_ushiftRight_div, eAdd19_toNat w hi hw hhi,
    eConv6_toNat w hi hw hhi]
  rfl

/-- `%cmp22`'s bit is the model's round-up test. -/
theorem eCmp22_eq_one_iff (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    eCmp22 w hi = 1 ↔ elHp w.toNat hi > elHh w.toNat hi := by
  rw [eCmp22, numEl_evalICmp_ugt_one, eConv12_toNat w hi hw hhi,
    eAnd_toNat w hi hw hhi]

/-- `%conv23`'s `toNat` is the model's round-up bit. -/
theorem eConv23_toNat (w : BitVec 64) (hi : Nat) (hw : w ≠ 0) (hhi : hi < 2 ^ 64) :
    (eConv23 w hi).toNat = elUp w.toNat hi := by
  have hb : (eCmp22 w hi).toNat < 2 ^ 32 := by
    rcases BlockEval.bitVec1_eq_zero_or_one (eCmp22 w hi) with h0 | h0
    · rw [h0]; decide
    · rw [h0]; decide
  rw [eConv23, bvOfNat_toNat_of_lt hb]
  unfold elUp
  by_cases h : elHp w.toNat hi > elHh w.toNat hi
  · rw [if_pos h]
    have h1 : eCmp22 w hi = 1 := (eCmp22_eq_one_iff w hi hw hhi).mpr h
    rw [h1]
    rfl
  · rw [if_neg h]
    have h0 : eCmp22 w hi = 0 := by
      rcases BlockEval.bitVec1_eq_zero_or_one (eCmp22 w hi) with h0 | h0
      · exact h0
      · exact absurd ((eCmp22_eq_one_iff w hi hw hhi).mp h0) h
    rw [h0]
    rfl

/-! ### The staged bytes at the body's words -/

/-- The row's `hi` bytes are the load's. -/
theorem natToBytes_eHi (hi : Nat) (hhi : hi < 2 ^ 64) :
    natToBytes (eHi hi).toNat 8 = natToBytes hi 8 := by
  rw [eHi_toNat hi hhi]

/-- The exponent's word bytes are the `i32` load's. -/
theorem natToBytes_eE (t : EPow) :
    natToBytes (eE t).toNat 4 = natToBytes (epowEWord t.e) 4 := by
  rw [eE, bvOfNat_toNat_of_lt (epowEWord_lt t.e)]

/-! ### The block vocabulary this body needs

`BlockEval`'s and `JsonStage2NumFastCalleeMul`'s steps cover most of the guard;
the additions are the `i32` literal shift, the `getelementptr` at a resolved
struct, the `double` zero store, and the three calls the body makes at its own
argument lists. -/

/-- `%d = op iW <c>, %b`: the literal-first binary operation. -/
theorem step_binop_lit_w (calls : Calls) (env : Env) (s : State) (d b : String)
    (op : BinOp) (w : Nat) {c y z : BitVec w}
    (hb : lookupName env b = some (.int w y)) (hz : evalBinop op c y = some z) :
    evalInstr calls (stateAt env s) (.binop d op w (.imm (.int w c)) (.reg b)) =
      some (stateAt ((d, .int w z) :: env) s) := by
  have hr : evalBinopNat op w c.toNat y.toNat = some z.toNat := by
    simp only [evalBinopNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, hz, Option.map_some]
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using JsonS1MasksIR.evalInstr_binop (calls := calls) (s := stateAt env s)
      (d := d) (op := op) (w := w)
      (ha := evalOperand_lit_of _ w c)
      (hb := evalOperand_reg_of env s b (.int w y) hb) (hr := hr)

theorem denoteCode_binop_lit_w (calls : Calls) (env : Env) (s : State) (d b : String)
    (op : BinOp) (w : Nat) {c y z : BitVec w}
    (hb : lookupName env b = some (.int w y)) (hz : evalBinop op c y = some z)
    (is : List Instr) :
    denoteCode calls (.binop d op w (.imm (.int w c)) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w z) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_binop_lit_w calls env s d b op w hb hz)]

/-- `%d = getelementptr [91 x %struct.EPow], ptr @EPOW, i64 0, i64 %sub` in its
reduced one-index form: `24` bytes per row. -/
theorem step_gep_EPow (calls : Calls) (env : Env) (s : State) (d : String)
    {a : Nat} {idx : BitVec 64}
    (hb : lookupName env "@EPOW" = some (.ptr a))
    (ho : lookupName env "%sub" = some (.int 64 idx))
    (hpos : idx.toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s)
        (.gep d (.struct "EPow" 24) (.global "@EPOW") (.reg "%sub")) =
      some (stateAt ((d, .ptr (a + idx.toNat * 24)) :: env) s) := by
  have hb' : evalOperand (stateAt env s) (.global "@EPOW") = some (.ptr a) := by
    simp only [evalOperand, stateAt, hb]
  have ho' : evalOperand (stateAt env s) (.reg "%sub") = some (.int 64 idx) :=
    evalOperand_reg_of env s "%sub" (.int 64 idx) ho
  have hse : (idx.signExtend 64).toNat = idx.toNat := by rw [BitVec.signExtend_eq]
  rw [evalInstr_gep (s := stateAt env s) (elemTy := .struct "EPow" 24)
    (hb := hb') (ho := ho') (hpos := by rw [hse]; exact hpos)]
  simp only [show Ty.sizeBytes (.struct "EPow" 24) = 24 from by decide, hse,
    stateAt, State.bind]

theorem denoteCode_gep_EPow (calls : Calls) (env : Env) (s : State) (d : String)
    {a : Nat} {idx : BitVec 64}
    (hb : lookupName env "@EPOW" = some (.ptr a))
    (ho : lookupName env "%sub" = some (.int 64 idx))
    (hpos : idx.toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.struct "EPow" 24) (.global "@EPOW") (.reg "%sub") :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a + idx.toNat * 24)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_gep_EPow calls env s d hb ho hpos)]

/-- `store double 0.0, ptr %p` writes the eight zero bytes. -/
theorem step_store_zero_double (calls : Calls) (env : Env) (s : State) (p : String)
    {a : Nat} (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s)
        (.store .double (.imm (.float (0x0000000000000000#64))) (.reg p)) =
      some (stateAt env ({ s with mem := writeBytes s.mem a (natToBytes 0 8) })) := by
  rw [JsonS1MasksIR.evalInstr_store (s := stateAt env s)
    (vv := .float (0x0000000000000000#64)) (a := a)
    (s' := stateAt env ({ s with mem := writeBytes s.mem a (natToBytes 0 8) }))
    (hv := rfl)
    (hp := evalOperand_reg_of env s p (.ptr a) hp)]
  simp [storeValue, stateAt]

theorem denoteCode_store_zero_double (calls : Calls) (env : Env) (s : State) (p : String)
    {a : Nat} (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls
        (.store .double (.imm (.float (0x0000000000000000#64))) (.reg p) :: is)
        (stateAt env s) =
      denoteCode calls is
        (stateAt env ({ s with mem := writeBytes s.mem a (natToBytes 0 8) })) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_store_zero_double calls env s p hp)]

/-- The `ctlz` call at the body's argument list. -/
theorem denoteCode_call_ctlz (epow : Int → Option EPow) (env : Env) (s : State)
    (w : BitVec 64) (is : List Instr)
    (hw : lookupName env "%w" = some (.int 64 w)) :
    denoteCode (numElCalls epow)
        (.call "%0" (.int 64) "llvm.ctlz.i64"
          [((Ty.int 64), (.reg "%w")), ((Ty.int 1), (.imm (.int 1 0x0#1)))] :: is)
        (stateAt env s) =
      denoteCode (numElCalls epow) is (stateAt (("%0", .int 64 (e0 w)) :: env) s) := by
  refine denoteCode_cons_of _ _ _ _ _ ?_
  rw [JsonS1MasksIR.evalInstr_call (s := stateAt env s)
    (vs := [.int 64 w, .int 1 0x0#1])
    (r := { ret := .int 64 (e0 w), mem := s.mem, next := s.next })
    (ha := ?_) (hc := ?_)]
  · rfl
  · simp [evalOperands, evalOperand, Const.toValue, stateAt, hw]
  · exact numElCalls_ctlz epow w 0x0#1 s.mem s.next

/-- The `el_pack` call at the body's argument list. -/
theorem denoteCode_call_elPack (epow : Int → Option EPow) (env : Env) (s : State)
    (is : List Instr) {m : BitVec 64} {up ub e lz : BitVec 32} {out : Nat}
    {r : CallOutcome}
    (hm : lookupName env "%shr21" = some (.int 64 m))
    (hup : lookupName env "%conv23" = some (.int 32 up))
    (hub : lookupName env "%conv8" = some (.int 32 ub))
    (he : lookupName env "%arrayidx.val" = some (.int 32 e))
    (hlz : lookupName env "%cast" = some (.int 32 lz))
    (hout : lookupName env "%out" = some (.ptr out))
    (hcalls : numElCalls epow "el_pack"
      [.int 64 m, .int 32 up, .int 32 ub, .int 32 e, .int 32 lz, .ptr out]
      s.mem s.next = some r) :
    denoteCode (numElCalls epow)
        (.call "%call24" (.int 32) "el_pack"
          [((Ty.int 64), (.reg "%shr21")), ((Ty.int 32), (.reg "%conv23")),
           ((Ty.int 32), (.reg "%conv8")), ((Ty.int 32), (.reg "%arrayidx.val")),
           ((Ty.int 32), (.reg "%cast")), (Ty.ptr, (.reg "%out"))] :: is)
        (stateAt env s) =
      denoteCode (numElCalls epow) is
        (stateAt (("%call24", r.ret) :: env)
          ({ s with mem := r.mem, next := r.next })) := by
  refine denoteCode_cons_of _ _ _ _ _ ?_
  rw [JsonS1MasksIR.evalInstr_call (s := stateAt env s)
    (vs := [.int 64 m, .int 32 up, .int 32 ub, .int 32 e, .int 32 lz, .ptr out])
    (r := { ret := r.ret, mem := r.mem, next := r.next })
    (ha := ?_) (hc := ?_)]
  · rfl
  · simp [evalOperands, evalOperand, stateAt, hm, hup, hub, he, hlz, hout]
  · exact hcalls

/-- The window arm's `el_exact` call, in the block's own environment, at a
refusal: the counter has already moved and `out` is untouched. -/
theorem numEl_ifThen18_denote_refuse (epow : Int → Option EPow) (env : Env) (s : State)
    {W : BitVec 64} {lz : BitVec 32} {row out k : Nat} {q : BitVec 64} {t : EPow}
    (hW : lookupName env "%shl" = some (.int 64 W))
    (hlz : lookupName env "%cast" = some (.int 32 lz))
    (hrow : lookupName env "%arrayidx" = some (.ptr row))
    (hq : lookupName env "%q" = some (.int 64 q))
    (hout : lookupName env "%out" = some (.ptr out))
    (hglob : lookupName env "@g_el_window" = some (.ptr 0x200000))
    (hread : readBytes s.mem 0x200000 8 = some (natToBytes k 8))
    (hk : k < 2 ^ 64)
    (hep : epow q.toInt = some t)
    (he : elExact W.toNat lz.toNat t q.toInt = none) :
    denoteCode (numElCalls epow) numElIfThen18Instrs (stateAt env s) =
      some (stateAt
        (("%call", .int 32 0) ::
          ("%inc", .int 64 ((BitVec.ofNat 64 k) + 1#64)) ::
          ("%2", .int 64 (BitVec.ofNat 64 k)) :: env)
        ({ s with
          mem := writeBytes s.mem 0x200000
            (natToBytes (((BitVec.ofNat 64 k) + 1#64).toNat) 8) })) := by
  unfold numElIfThen18Instrs
  let s1 : State :=
    { s with mem := (writeBytes s.mem 0x200000
        (natToBytes (((BitVec.ofNat 64 k) + 1#64).toNat) 8)) }
  have hread' : readBytes s.mem 0x200000 8 =
      some (natToBytes (BitVec.ofNat 64 k).toNat 8) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
    exact hread
  rw [BlockEval.denoteCode_cons_of _ _ _ _ _
    (numEl_step_load64_global (numElCalls epow) env s "%2" "@g_el_window" hglob hread')]
  rw [BlockEval.denoteCode_cons_of _ _ _ _ _
    (BlockEval.step_add_imm (calls := numElCalls epow)
      (env := ("%2", .int 64 (BitVec.ofNat 64 k)) :: env) (s := s) (d := "%inc")
      (a := "%2") (x := BitVec.ofNat 64 k) (c := 0x0000000000000001#64) (by block_lk))]
  rw [BlockEval.denoteCode_cons_of _ _ _ _ _
    (numEl_step_store64_global (numElCalls epow)
      (("%inc", .int 64 ((BitVec.ofNat 64 k) + 1#64)) ::
        ("%2", .int 64 (BitVec.ofNat 64 k)) :: env) s "%inc" "@g_el_window"
      (by block_lk) hglob)]
  rw [denoteCode_call_some (numElCalls epow)
    (("%inc", .int 64 ((BitVec.ofNat 64 k) + 1#64)) ::
      ("%2", .int 64 (BitVec.ofNat 64 k)) :: env) s1
    "%call" (Ty.int 32) "el_exact"
    [((Ty.int 64), (Operand.reg "%shl")), ((Ty.int 32), (Operand.reg "%cast")),
     (Ty.ptr, (Operand.reg "%arrayidx")), ((Ty.int 64), (Operand.reg "%q")),
     (Ty.ptr, (Operand.reg "%out"))]
    [.int 64 W, .int 32 lz, .ptr row, .int 64 q, .ptr out]
    ({ ret := .int 32 0, mem := s1.mem, next := s1.next } : CallOutcome)
    (by simp only [evalOperands,
        BlockEval.evalOperand_reg_of
          (("%inc", .int 64 ((BitVec.ofNat 64 k) + 1#64)) ::
            ("%2", .int 64 (BitVec.ofNat 64 k)) :: env) s1 "%shl" (.int 64 W) (by block_lk),
        BlockEval.evalOperand_reg_of
          (("%inc", .int 64 ((BitVec.ofNat 64 k) + 1#64)) ::
            ("%2", .int 64 (BitVec.ofNat 64 k)) :: env) s1 "%cast" (.int 32 lz) (by block_lk),
        BlockEval.evalOperand_reg_of
          (("%inc", .int 64 ((BitVec.ofNat 64 k) + 1#64)) ::
            ("%2", .int 64 (BitVec.ofNat 64 k)) :: env) s1 "%arrayidx" (.ptr row) (by block_lk),
        BlockEval.evalOperand_reg_of
          (("%inc", .int 64 ((BitVec.ofNat 64 k) + 1#64)) ::
            ("%2", .int 64 (BitVec.ofNat 64 k)) :: env) s1 "%q" (.int 64 q) (by block_lk),
        BlockEval.evalOperand_reg_of
          (("%inc", .int 64 ((BitVec.ofNat 64 k) + 1#64)) ::
            ("%2", .int 64 (BitVec.ofNat 64 k)) :: env) s1 "%out" (.ptr out) (by block_lk)])
    (numElCalls_elExact_refuse epow hep he _ _) []]
  rfl

/-! ### The chain -/

/-- One instruction of this body. -/
macro "el_block_step" : tactic => `(tactic|
  (first
   | block_step
   | rw [denoteCode_binop_reg_w _ _ _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_binop_imm_w _ _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_binop_lit_w _ _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_icmp_reg_w _ _ _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_icmp_imm_w _ _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_gep8_imm _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_load32 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_gep_EPow _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_store_zero_double _ _ _ _ ?_ _]
   | rw [denoteCode_call_ctlz _ _ _ _ _ ?_]
   | rw [denoteCode_call_elPack _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_]))

macro "el_block_eval" : tactic => `(tactic|
  (repeat el_block_step
   block_close
   all_goals (try decide)
   all_goals (try (rw [lookupName_cons_self]))))

/-- A `lookupName` past a run of cells whose names differ. -/
macro "el_lk_cons" : tactic => `(tactic|
  (repeat rw [lookupName_cons_ne _ _ (by decide)]
   first
    | rw [lookupName_cons_self]
    | assumption
   try rfl))

/-! ### The environments

The entry's environment is the three parameters and the two staged globals; each
block's is the previous one with the cells the block writes. -/

/-- The entry environment. -/
def numElEntryEnv (w q : BitVec 64) (out : Nat) : Env :=
  [("%w", .int 64 w), ("%q", .int 64 q), ("%out", .ptr out),
   ("@EPOW", .ptr 0x100000), ("@g_el_window", .ptr 0x200000)]

/-- The entry's test, as the entry block binds it. -/
def numElAfterEntryEnv (w q : BitVec 64) (out : Nat) : Env :=
  ("%cmp2", .int 1 (evalICmp .eq w 0)) :: numElEntryEnv w q out

/-- The guard's environment: the twenty-one cells `if.end4` writes. -/
def numElIfEnd4Env (env : Env) (w q : BitVec 64) (hi : Nat) : Env :=
  cells
    [("%cmp15", .int 1 (eCmp15 w hi)),
     ("%sub14", .int 64 (eSub14 w hi)),
     ("%reass.sub", .int 64 (eReass w hi)),
     ("%conv12", .int 64 (eConv12 w hi)),
     ("%shl11", .int 32 (eShl11 w hi)),
     ("%and", .int 64 (eAnd w hi)),
     ("%or", .int 64 (eOr w hi)),
     ("%shl9", .int 64 (eShl9 w hi)),
     ("%conv8", .int 32 (eConv8 w hi)),
     ("%shr7", .int 64 (eShr7 w hi)),
     ("%conv6", .int 64 (eConv6 w hi)),
     ("%shr", .int 128 (eShr w hi)),
     ("%mul", .int 128 (eMul w hi)),
     ("%conv5", .int 128 (eConv5 hi)),
     ("%1", .int 64 (eHi hi)),
     ("%conv", .int 128 (eConv w)),
     ("%shl", .int 64 (eShl w)),
     ("%cast", .int 32 (eCast w)),
     ("%0", .int 64 (e0 w)),
     ("%arrayidx", .ptr (eRow q)),
     ("%sub", .int 64 (eSub q))] env

/-- The fast arm's environment. -/
def numElIfEnd19Env (env : Env) (w q : BitVec 64) (hi : Nat) (ev : BitVec 32)
    (r : CallOutcome) : Env :=
  cells
    [("%call24", r.ret),
     ("%arrayidx.val", .int 32 ev),
     ("%3", .ptr (eRow q + 16)),
     ("%conv23", .int 32 (eConv23 w hi)),
     ("%cmp22", .int 1 (eCmp22 w hi)),
     ("%shr21", .int 64 (eShr21 w hi)),
     ("%add", .int 64 (eAdd19 w hi))] env

/-! ### The reads the steps and the calls make

Each is one `lookupName` into a block's environment, unfolded. -/

theorem lookupNumElEntryEnv_w (w q : BitVec 64) (out : Nat) :
    lookupName (numElEntryEnv w q out) "%w" = some (.int 64 w) := by
  simp only [numElEntryEnv]
  el_lk_cons

theorem lookupNumElEntryEnv_q (w q : BitVec 64) (out : Nat) :
    lookupName (numElEntryEnv w q out) "%q" = some (.int 64 q) := by
  simp only [numElEntryEnv]
  el_lk_cons

theorem lookupNumElEntryEnv_out (w q : BitVec 64) (out : Nat) :
    lookupName (numElEntryEnv w q out) "%out" = some (.ptr out) := by
  simp only [numElEntryEnv]
  el_lk_cons

theorem lookupNumElEntryEnv_EPOW (w q : BitVec 64) (out : Nat) :
    lookupName (numElEntryEnv w q out) "@EPOW" = some (.ptr 0x100000) := by
  simp only [numElEntryEnv]
  el_lk_cons

theorem lookupNumElEntryEnv_glob (w q : BitVec 64) (out : Nat) :
    lookupName (numElEntryEnv w q out) "@g_el_window" = some (.ptr 0x200000) := by
  simp only [numElEntryEnv]
  el_lk_cons

theorem lookupNumElAfterEntryEnv_w (w q : BitVec 64) (out : Nat) :
    lookupName (numElAfterEntryEnv w q out) "%w" = some (.int 64 w) := by
  simp only [numElAfterEntryEnv, numElEntryEnv]
  el_lk_cons

theorem lookupNumElAfterEntryEnv_q (w q : BitVec 64) (out : Nat) :
    lookupName (numElAfterEntryEnv w q out) "%q" = some (.int 64 q) := by
  simp only [numElAfterEntryEnv, numElEntryEnv]
  el_lk_cons

theorem lookupNumElAfterEntryEnv_out (w q : BitVec 64) (out : Nat) :
    lookupName (numElAfterEntryEnv w q out) "%out" = some (.ptr out) := by
  simp only [numElAfterEntryEnv, numElEntryEnv]
  el_lk_cons

theorem lookupNumElAfterEntryEnv_EPOW (w q : BitVec 64) (out : Nat) :
    lookupName (numElAfterEntryEnv w q out) "@EPOW" = some (.ptr 0x100000) := by
  simp only [numElAfterEntryEnv, numElEntryEnv]
  el_lk_cons

theorem lookupNumElAfterEntryEnv_glob (w q : BitVec 64) (out : Nat) :
    lookupName (numElAfterEntryEnv w q out) "@g_el_window" = some (.ptr 0x200000) := by
  simp only [numElAfterEntryEnv, numElEntryEnv]
  el_lk_cons

theorem lookupNumElIfEnd4Env_cmp15 (env : Env) (w q : BitVec 64) (hi : Nat) :
    lookupName (numElIfEnd4Env env w q hi) "%cmp15" = some (.int 1 (eCmp15 w hi)) := by
  simp only [numElIfEnd4Env, cells, lookupName_cons_self]

theorem lookupNumElIfEnd4Env_cmp15_neg (env : Env) (w q : BitVec 64) (hi : Nat)
    (h : eCmp15 w hi = 0) :
    lookupName (numElIfEnd4Env env w q hi) "%cmp15" = some (.int 1 (0 : BitVec 1)) := by
  rw [lookupNumElIfEnd4Env_cmp15, h]

theorem lookupNumElIfEnd4Env_shl (env : Env) (w q : BitVec 64) (hi : Nat) :
    lookupName (numElIfEnd4Env env w q hi) "%shl" = some (.int 64 (eShl w)) := by
  simp only [numElIfEnd4Env, cells]
  el_lk_cons

theorem lookupNumElIfEnd4Env_cast (env : Env) (w q : BitVec 64) (hi : Nat) :
    lookupName (numElIfEnd4Env env w q hi) "%cast" = some (.int 32 (eCast w)) := by
  simp only [numElIfEnd4Env, cells]
  el_lk_cons

theorem lookupNumElIfEnd4Env_conv8 (env : Env) (w q : BitVec 64) (hi : Nat) :
    lookupName (numElIfEnd4Env env w q hi) "%conv8" = some (.int 32 (eConv8 w hi)) := by
  simp only [numElIfEnd4Env, cells]
  el_lk_cons

theorem lookupNumElIfEnd4Env_arrayidx (env : Env) (w q : BitVec 64) (hi : Nat) :
    lookupName (numElIfEnd4Env env w q hi) "%arrayidx" = some (.ptr (eRow q)) := by
  simp only [numElIfEnd4Env, cells]
  el_lk_cons

theorem lookupNumElIfEnd4Env_shr7 (env : Env) (w q : BitVec 64) (hi : Nat) :
    lookupName (numElIfEnd4Env env w q hi) "%shr7" = some (.int 64 (eShr7 w hi)) := by
  simp only [numElIfEnd4Env, cells]
  el_lk_cons

theorem lookupNumElIfEnd4Env_conv6 (env : Env) (w q : BitVec 64) (hi : Nat) :
    lookupName (numElIfEnd4Env env w q hi) "%conv6" = some (.int 64 (eConv6 w hi)) := by
  simp only [numElIfEnd4Env, cells]
  el_lk_cons

theorem lookupNumElIfEnd4Env_and (env : Env) (w q : BitVec 64) (hi : Nat) :
    lookupName (numElIfEnd4Env env w q hi) "%and" = some (.int 64 (eAnd w hi)) := by
  simp only [numElIfEnd4Env, cells]
  el_lk_cons

theorem lookupNumElIfEnd4Env_conv12 (env : Env) (w q : BitVec 64) (hi : Nat) :
    lookupName (numElIfEnd4Env env w q hi) "%conv12" = some (.int 64 (eConv12 w hi)) := by
  simp only [numElIfEnd4Env, cells]
  el_lk_cons

theorem lookupNumElIfEnd4Env_glob (w q : BitVec 64) (hi : Nat) (out : Nat) :
    lookupName (numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi) "@g_el_window" =
      some (.ptr 0x200000) := by
  simp only [numElIfEnd4Env, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupNumElAfterEntryEnv_glob w q out

theorem liftQ (w q : BitVec 64) (hi : Nat) (out : Nat) :
    lookupName (numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi) "%q" =
      some (.int 64 q) := by
  simp only [numElIfEnd4Env, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupNumElAfterEntryEnv_q w q out

theorem liftW (w q : BitVec 64) (hi : Nat) (out : Nat) :
    lookupName (numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi) "%w" =
      some (.int 64 w) := by
  simp only [numElIfEnd4Env, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupNumElAfterEntryEnv_w w q out

theorem liftOut (w q : BitVec 64) (hi : Nat) (out : Nat) :
    lookupName (numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi) "%out" =
      some (.ptr out) := by
  simp only [numElIfEnd4Env, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupNumElAfterEntryEnv_out w q out

theorem liftEPOW (w q : BitVec 64) (hi : Nat) (out : Nat) :
    lookupName (numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi) "@EPOW" =
      some (.ptr 0x100000) := by
  simp only [numElIfEnd4Env, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupNumElAfterEntryEnv_EPOW w q out

/-! ### The blocks -/

/-- The entry block. -/
theorem numEl_entry_denote (epow : Int → Option EPow) (env : Env) (s : State)
    (w : BitVec 64) (hw : lookupName env "%w" = some (.int 64 w)) :
    denoteCode (numElCalls epow) numElEntryInstrs (stateAt env s) =
      some (stateAt (("%cmp2", .int 1 (evalICmp .eq w 0)) :: env) s) := by
  unfold numElEntryInstrs
  el_block_eval

/-- The zero arm's store. -/
theorem numEl_ifThen3_denote (epow : Int → Option EPow) (env : Env) (s : State)
    (out : Nat) (hout : lookupName env "%out" = some (.ptr out)) :
    denoteCode (numElCalls epow) numElIfThen3Instrs (stateAt env s) =
      some (stateAt env ({ s with mem := writeBytes s.mem out (natToBytes 0 8) })) := by
  unfold numElIfThen3Instrs
  el_block_eval

/-- The guard's twenty-one instructions. -/
theorem numEl_ifEnd4_denote (epow : Int → Option EPow) (env : Env) (s : State)
    (w q : BitVec 64) (hi : Nat)
    (hw : lookupName env "%w" = some (.int 64 w))
    (hq : lookupName env "%q" = some (.int 64 q))
    (hEPOW : lookupName env "@EPOW" = some (.ptr 0x100000))
    (hhi : hi < 2 ^ 64) (hsub : (eSub q).toNat < 2 ^ 63)
    (hread : readBytes s.mem (eRow q) 8 = some (natToBytes (eHi hi).toNat 8)) :
    denoteCode (numElCalls epow) numElIfEnd4Instrs (stateAt env s) =
      some (stateAt (numElIfEnd4Env env w q hi) s) := by
  unfold numElIfEnd4Instrs numElIfEnd4Env
  el_block_eval

/-- The fast arm's seven instructions and its call. -/
theorem numEl_ifEnd19_denote (epow : Int → Option EPow) (env : Env) (s : State)
    (w q : BitVec 64) (hi : Nat) (out : Nat) (ev : BitVec 32) (r : CallOutcome)
    (hshr7 : lookupName env "%shr7" = some (.int 64 (eShr7 w hi)))
    (hconv6 : lookupName env "%conv6" = some (.int 64 (eConv6 w hi)))
    (hand : lookupName env "%and" = some (.int 64 (eAnd w hi)))
    (hconv12 : lookupName env "%conv12" = some (.int 64 (eConv12 w hi)))
    (hcast : lookupName env "%cast" = some (.int 32 (eCast w)))
    (hconv8 : lookupName env "%conv8" = some (.int 32 (eConv8 w hi)))
    (hout : lookupName env "%out" = some (.ptr out))
    (hrow : lookupName env "%arrayidx" = some (.ptr (eRow q)))
    (he : readBytes s.mem (eRow q + 16) 4 = some (natToBytes ev.toNat 4))
    (hcalls : numElCalls epow "el_pack"
      [.int 64 (eShr21 w hi), .int 32 (eConv23 w hi), .int 32 (eConv8 w hi),
       .int 32 ev, .int 32 (eCast w), .ptr out] s.mem s.next = some r) :
    denoteCode (numElCalls epow) numElIfEnd19Instrs (stateAt env s) =
      some (stateAt (numElIfEnd19Env env w q hi ev r)
        ({ s with mem := r.mem, next := r.next })) := by
  unfold numElIfEnd19Instrs numElIfEnd19Env
  rw [denoteCode_binop_imm_w (calls := numElCalls epow) (s := s)
    (d := "%add") (a := "%shr7") (op := .or) (w := 64)
    (x := eShr7 w hi) (c := 0x000000000000000a#64) (z := eAdd19 w hi)
    (ha := hshr7) (hz := rfl)]
  rw [denoteCode_binop_reg_w (calls := numElCalls epow) (s := s)
    (d := "%shr21") (a := "%conv6") (b := "%add") (op := .lshr) (w := 64)
    (x := eConv6 w hi) (y := eAdd19 w hi) (z := eShr21 w hi)
    (ha := by el_lk_cons) (hb := by el_lk_cons) (hz := rfl)]
  rw [denoteCode_icmp_reg_w (calls := numElCalls epow) (s := s)
    (d := "%cmp22") (a := "%and") (b := "%conv12") (pred := .ugt) (w := 64)
    (x := eAnd w hi) (y := eConv12 w hi)
    (ha := by el_lk_cons) (hb := by el_lk_cons)]
  rw [denoteCode_zext (calls := numElCalls epow) (s := s)
    (d := "%conv23") (v := "%cmp22") (wIn := 1) (wOut := 32)
    (x := eCmp22 w hi) (hv := by el_lk_cons)]
  rw [denoteCode_gep8_imm (calls := numElCalls epow) (s := s)
    (d := "%3") (base := "%arrayidx") (a := eRow q) (c := 0x0000000000000010#64)
    (hb := by el_lk_cons) (hc := by decide)]
  rw [denoteCode_load32_word (calls := numElCalls epow) (s := s)
    (d := "%arrayidx.val") (p := "%3") (a := eRow q + 16) (v := ev)
    (hp := by el_lk_cons) (hv := he)]
  rw [denoteCode_call_elPack (epow := epow) (s := s) (is := [])
    (m := eShr21 w hi) (up := eConv23 w hi) (ub := eConv8 w hi) (e := ev)
    (lz := eCast w) (out := out) (r := r)
    (hm := by el_lk_cons) (hup := by el_lk_cons) (hub := by el_lk_cons)
    (he := by el_lk_cons) (hlz := by el_lk_cons) (hout := by el_lk_cons)
    (hcalls := hcalls)]
  rfl

/-- The return block, from the zero arm. -/
theorem numEl_return_denote_ifThen3 (epow : Int → Option EPow) (env : Env) (s : State)
    (hpre : s.pre = some "if.then3") :
    denoteCode (numElCalls epow) numElReturnInstrs (stateAt env s) =
      some (stateAt (("%retval.1", .int 32 1) :: env) s) := by
  have hinc : phiIncoming "if.then3"
      [("if.then3", Operand.imm (Const.int 32 0x00000001#32)),
       ("if.then18", Operand.reg "%call"),
       ("if.end19", Operand.reg "%call24")] =
      some (Operand.imm (Const.int 32 0x00000001#32)) := by simp [phiIncoming]
  have hop : evalOperand (stateAt env s) (.imm (.int 32 0x00000001#32)) =
      some (.int 32 1) := rfl
  unfold numElReturnInstrs
  rw [denoteCode_phi _ env s "%retval.1" (.int 32)
    [("if.then3", Operand.imm (Const.int 32 0x00000001#32)),
     ("if.then18", Operand.reg "%call"),
     ("if.end19", Operand.reg "%call24")] hpre hinc hop [] (by rfl)]
  rfl

/-- The return block, from the window arm. -/
theorem numEl_return_denote_ifThen18 (epow : Int → Option EPow) (env : Env) (s : State)
    {v : BitVec 32} (hpre : s.pre = some "if.then18")
    (hcall : lookupName env "%call" = some (.int 32 v)) :
    denoteCode (numElCalls epow) numElReturnInstrs (stateAt env s) =
      some (stateAt (("%retval.1", .int 32 v) :: env) s) := by
  have hinc : phiIncoming "if.then18"
      [("if.then3", Operand.imm (Const.int 32 0x00000001#32)),
       ("if.then18", Operand.reg "%call"),
       ("if.end19", Operand.reg "%call24")] =
      some (Operand.reg "%call") := by simp [phiIncoming]
  have hop : evalOperand (stateAt env s) (.reg "%call") = some (.int 32 v) :=
    evalOperand_reg_of env s "%call" (.int 32 v) hcall
  unfold numElReturnInstrs
  rw [denoteCode_phi _ env s "%retval.1" (.int 32)
    [("if.then3", Operand.imm (Const.int 32 0x00000001#32)),
     ("if.then18", Operand.reg "%call"),
     ("if.end19", Operand.reg "%call24")] hpre hinc hop [] (by rfl)]
  rfl

/-- The return block, from the fast arm. -/
theorem numEl_return_denote_ifEnd19 (epow : Int → Option EPow) (env : Env) (s : State)
    {v : BitVec 32} (hpre : s.pre = some "if.end19")
    (hcall : lookupName env "%call24" = some (.int 32 v)) :
    denoteCode (numElCalls epow) numElReturnInstrs (stateAt env s) =
      some (stateAt (("%retval.1", .int 32 v) :: env) s) := by
  have hinc : phiIncoming "if.end19"
      [("if.then3", Operand.imm (Const.int 32 0x00000001#32)),
       ("if.then18", Operand.reg "%call"),
       ("if.end19", Operand.reg "%call24")] =
      some (Operand.reg "%call24") := by simp [phiIncoming]
  have hop : evalOperand (stateAt env s) (.reg "%call24") = some (.int 32 v) :=
    evalOperand_reg_of env s "%call24" (.int 32 v) hcall
  unfold numElReturnInstrs
  rw [denoteCode_phi _ env s "%retval.1" (.int 32)
    [("if.then3", Operand.imm (Const.int 32 0x00000001#32)),
     ("if.then18", Operand.reg "%call"),
     ("if.end19", Operand.reg "%call24")] hpre hinc hop [] (by rfl)]
  rfl

/-- The entry's pin, at the state's own program counter. -/
theorem numEl_findBlock_entry_at (env : Env) (s : State) (hpc : s.pc = "entry") :
    numElBody.findBlock (stateAt env s).pc =
      some ⟨(stateAt env s).pc, numElEntryInstrs,
        Term.condbr (Operand.reg "%cmp2") "if.then3" "if.end4"⟩ := by
  rw [show (stateAt env s).pc = "entry" from hpc]
  exact numEl_findBlock_entry

/-- `if.then3`'s pin, at the state's own program counter. -/
theorem numEl_findBlock_ifThen3_at (env : Env) (s : State) (hpc : s.pc = "if.then3") :
    numElBody.findBlock (stateAt env s).pc =
      some ⟨(stateAt env s).pc, numElIfThen3Instrs, Term.br "return"⟩ := by
  rw [show (stateAt env s).pc = "if.then3" from hpc]
  exact numEl_findBlock_ifThen3

/-- `if.end4`'s pin, at the state's own program counter. -/
theorem numEl_findBlock_ifEnd4_at (env : Env) (s : State) (hpc : s.pc = "if.end4") :
    numElBody.findBlock (stateAt env s).pc =
      some ⟨(stateAt env s).pc, numElIfEnd4Instrs,
        Term.condbr (Operand.reg "%cmp15") "if.then18" "if.end19"⟩ := by
  rw [show (stateAt env s).pc = "if.end4" from hpc]
  exact numEl_findBlock_ifEnd4

/-- `if.then18`'s pin, at the state's own program counter. -/
theorem numEl_findBlock_ifThen18_at (env : Env) (s : State) (hpc : s.pc = "if.then18") :
    numElBody.findBlock (stateAt env s).pc =
      some ⟨(stateAt env s).pc, numElIfThen18Instrs, Term.br "return"⟩ := by
  rw [show (stateAt env s).pc = "if.then18" from hpc]
  exact numEl_findBlock_ifThen18

/-- `if.end19`'s pin, at the state's own program counter. -/
theorem numEl_findBlock_ifEnd19_at (env : Env) (s : State) (hpc : s.pc = "if.end19") :
    numElBody.findBlock (stateAt env s).pc =
      some ⟨(stateAt env s).pc, numElIfEnd19Instrs, Term.br "return"⟩ := by
  rw [show (stateAt env s).pc = "if.end19" from hpc]
  exact numEl_findBlock_ifEnd19

/-- `return`'s pin, at the state's own program counter. -/
theorem numEl_findBlock_return_at (env : Env) (s : State) (hpc : s.pc = "return") :
    numElBody.findBlock (stateAt env s).pc =
      some ⟨(stateAt env s).pc, numElReturnInstrs,
        Term.ret (.int 32) (some (Operand.reg "%retval.1"))⟩ := by
  rw [show (stateAt env s).pc = "return" from hpc]
  exact numEl_findBlock_return

/-! ### The steps at the pinned blocks

Each reads the block off `s.pc`: the caller supplies the pin at its own block
name, so the state's predecessor and program counter are the ones the block's
own step produces. -/

/-- A block ending in `br`: one jump to its target. -/
theorem numEl_step_br {calls : Calls} {env env' : Env} {s t : State}
    {instrs : List Instr} {dest : String}
    (hfind : numElBody.findBlock (stateAt env s).pc =
      some ⟨(stateAt env s).pc, instrs, Term.br dest⟩)
    (hden : denoteCode calls instrs (stateAt env s) = some (stateAt env' t)) :
    step calls numElBody (stateAt env s) =
      .jump (stateAt env' { t with pc := dest, pre := some t.pc }) := by
  unfold step execTerm
  rw [hfind]
  simp only [hden]
  rfl

/-- A block ending in a branch whose bit is one: the true edge. -/
theorem numEl_step_condbr_true {calls : Calls} {env env' : Env} {s t : State}
    {instrs : List Instr} {destT destF c : String}
    (hfind : numElBody.findBlock (stateAt env s).pc =
      some ⟨(stateAt env s).pc, instrs, Term.condbr (Operand.reg c) destT destF⟩)
    (hden : denoteCode calls instrs (stateAt env s) = some (stateAt env' t))
    (hbit : lookupName env' c = some (.int 1 (1 : BitVec 1))) :
    step calls numElBody (stateAt env s) =
      .jump (stateAt env' { t with pc := destT, pre := some t.pc }) := by
  have hop : evalOperand (stateAt env' t) (.reg c) = some (.int 1 (1 : BitVec 1)) :=
    evalOperand_reg_of env' t c (.int 1 (1 : BitVec 1)) hbit
  unfold step execTerm
  rw [hfind]
  simp only [hden, hop]
  rfl

/-- A block ending in a branch whose bit is zero: the false edge. -/
theorem numEl_step_condbr_false {calls : Calls} {env env' : Env} {s t : State}
    {instrs : List Instr} {destT destF c : String}
    (hfind : numElBody.findBlock (stateAt env s).pc =
      some ⟨(stateAt env s).pc, instrs, Term.condbr (Operand.reg c) destT destF⟩)
    (hden : denoteCode calls instrs (stateAt env s) = some (stateAt env' t))
    (hbit : lookupName env' c = some (.int 1 (0 : BitVec 1))) :
    step calls numElBody (stateAt env s) =
      .jump (stateAt env' { t with pc := destF, pre := some t.pc }) := by
  have hop : evalOperand (stateAt env' t) (.reg c) = some (.int 1 (0 : BitVec 1)) :=
    evalOperand_reg_of env' t c (.int 1 (0 : BitVec 1)) hbit
  unfold step execTerm
  rw [hfind]
  simp only [hden, hop]
  rfl

/-- A block ending in `ret`: the value is read and the run completes. -/
theorem numEl_step_ret {calls : Calls} {env env' : Env} {s t : State}
    {instrs : List Instr} {v : Value}
    (hfind : numElBody.findBlock (stateAt env s).pc =
      some ⟨(stateAt env s).pc, instrs,
        Term.ret (.int 32) (some (Operand.reg "%retval.1"))⟩)
    (hden : denoteCode calls instrs (stateAt env s) = some (stateAt env' t))
    (hval : lookupName env' "%retval.1" = some v) (hv : v ≠ .poison := by intro hh; cases hh) :
    step calls numElBody (stateAt env s) = .ret (some v) (stateAt env' t) := by
  have hop : evalOperand (stateAt env' t) (.reg "%retval.1") = some v :=
    evalOperand_reg_of env' t "%retval.1" v hval hv
  unfold step execTerm
  rw [hfind]
  simp only [hden, hop]

/-! ### The run -/

theorem numEl_runFuel_jump {calls : Calls} {s t : State}
    (h : step calls numElBody s = .jump t) :
    ∀ k, runFuel calls (1 + k) numElBody s = runFuel calls k numElBody t := by
  intro k
  rw [show 1 + k = k + 1 from Nat.add_comm 1 k, runFuel.eq_2, h]

theorem numEl_runFuel_ret {calls : Calls} {s s' : State} {v : Option Value}
    (h : step calls numElBody s = .ret v s') :
    runFuel calls 1 numElBody s = some (.ret v s'.mem) := by
  rw [show (1 : Nat) = 0 + 1 from rfl, runFuel.eq_2, h]

/-- The raw state at the body's entry. -/
def numElRaw (mem : Mem) (next : Nat) : State :=
  { env := [], mem := mem, next := next, pc := "entry", pre := none }

/-- The body's entry state. -/
def numElEntryState (w q : BitVec 64) (out : Nat) (mem : Mem) (next : Nat) : State :=
  stateAt (numElEntryEnv w q out) (numElRaw mem next)

/-- The entry's step at a nonzero word. -/
theorem numEl_entry_step_nonzero (epow : Int → Option EPow) (w q : BitVec 64) (out : Nat)
    (s : State) (hpc : s.pc = "entry") (hw : w ≠ 0) :
    step (numElCalls epow) numElBody (stateAt (numElEntryEnv w q out) s) =
      .jump (stateAt (numElAfterEntryEnv w q out)
        ({ s with pc := "if.end4", pre := some s.pc })) := by
  refine numEl_step_condbr_false (calls := numElCalls epow)
    (env := numElEntryEnv w q out) (s := s) (t := s)
    (hfind := numEl_findBlock_entry_at (numElEntryEnv w q out) s hpc) ?_ ?_
  · rw [numEl_entry_denote (epow := epow) (env := numElEntryEnv w q out) (s := s)
      (w := w) (hw := lookupNumElEntryEnv_w w q out)]
    rfl
  · rw [numElAfterEntryEnv, lookupName_cons_self, numEl_test_nonzero hw]

/-- The entry's step at the zero word. -/
theorem numEl_entry_step_zero (epow : Int → Option EPow) (w q : BitVec 64) (out : Nat)
    (s : State) (hpc : s.pc = "entry") (hw : w = 0) :
    step (numElCalls epow) numElBody (stateAt (numElEntryEnv w q out) s) =
      .jump (stateAt (numElAfterEntryEnv w q out)
        ({ s with pc := "if.then3", pre := some s.pc })) := by
  refine numEl_step_condbr_true (calls := numElCalls epow)
    (env := numElEntryEnv w q out) (s := s) (t := s)
    (hfind := numEl_findBlock_entry_at (numElEntryEnv w q out) s hpc) ?_ ?_
  · rw [numEl_entry_denote (epow := epow) (env := numElEntryEnv w q out) (s := s)
      (w := w) (hw := lookupNumElEntryEnv_w w q out)]
    rfl
  · subst hw
    rw [numElAfterEntryEnv, lookupName_cons_self, numEl_test_zero]

/-- The zero arm's step. -/
theorem numEl_ifThen3_step (epow : Int → Option EPow) (env : Env) (s : State)
    (out : Nat) (hpc : s.pc = "if.then3")
    (hout : lookupName env "%out" = some (.ptr out)) :
    step (numElCalls epow) numElBody (stateAt env s) =
      .jump (stateAt env
        ({ s with
          mem := writeBytes s.mem out (natToBytes 0 8),
          pc := "return", pre := some s.pc })) := by
  refine numEl_step_br (calls := numElCalls epow) (env := env) (env' := env) (s := s)
    (t := { s with mem := writeBytes s.mem out (natToBytes 0 8) })
    (hfind := numEl_findBlock_ifThen3_at env s hpc) ?_
  rw [numEl_ifThen3_denote epow env s out hout]

/-- The guard's step on the window arm. -/
theorem numEl_ifEnd4_step_window (epow : Int → Option EPow) (env : Env) (s : State)
    (w q : BitVec 64) (hi : Nat)
    (hpc : s.pc = "if.end4")
    (hw : lookupName env "%w" = some (.int 64 w))
    (hq : lookupName env "%q" = some (.int 64 q))
    (hEPOW : lookupName env "@EPOW" = some (.ptr 0x100000))
    (hhi : hi < 2 ^ 64) (hsub : (eSub q).toNat < 2 ^ 63)
    (hread : readBytes s.mem (eRow q) 8 = some (natToBytes (eHi hi).toNat 8))
    (hbit : eCmp15 w hi = 1) :
    step (numElCalls epow) numElBody (stateAt env s) =
      .jump (stateAt (numElIfEnd4Env env w q hi)
        ({ s with pc := "if.then18", pre := some s.pc })) := by
  refine numEl_step_condbr_true (calls := numElCalls epow) (env := env)
    (env' := numElIfEnd4Env env w q hi) (s := s) (t := s)
    (hfind := numEl_findBlock_ifEnd4_at env s hpc) ?_ ?_
  · rw [numEl_ifEnd4_denote epow env s w q hi hw hq hEPOW hhi hsub hread]
  · rw [lookupNumElIfEnd4Env_cmp15, hbit]

/-- The guard's step on the fast arm. -/
theorem numEl_ifEnd4_step_fast (epow : Int → Option EPow) (env : Env) (s : State)
    (w q : BitVec 64) (hi : Nat)
    (hpc : s.pc = "if.end4")
    (hw : lookupName env "%w" = some (.int 64 w))
    (hq : lookupName env "%q" = some (.int 64 q))
    (hEPOW : lookupName env "@EPOW" = some (.ptr 0x100000))
    (hhi : hi < 2 ^ 64) (hsub : (eSub q).toNat < 2 ^ 63)
    (hread : readBytes s.mem (eRow q) 8 = some (natToBytes (eHi hi).toNat 8))
    (hbit : eCmp15 w hi = 0) :
    step (numElCalls epow) numElBody (stateAt env s) =
      .jump (stateAt (numElIfEnd4Env env w q hi)
        ({ s with pc := "if.end19", pre := some s.pc })) := by
  refine numEl_step_condbr_false (calls := numElCalls epow) (env := env)
    (env' := numElIfEnd4Env env w q hi) (s := s) (t := s)
    (hfind := numEl_findBlock_ifEnd4_at env s hpc) ?_ ?_
  · rw [numEl_ifEnd4_denote epow env s w q hi hw hq hEPOW hhi hsub hread]
  · exact lookupNumElIfEnd4Env_cmp15_neg env w q hi hbit

/-- The window arm's step, accepted. -/
theorem numEl_ifThen18_step (epow : Int → Option EPow) (env : Env) (s : State)
    {W : BitVec 64} {lz : BitVec 32} {row out k : Nat} {q : BitVec 64} {t : EPow}
    {bits : Nat}
    (hpc : s.pc = "if.then18")
    (hW : lookupName env "%shl" = some (.int 64 W))
    (hlz : lookupName env "%cast" = some (.int 32 lz))
    (hrow : lookupName env "%arrayidx" = some (.ptr row))
    (hq : lookupName env "%q" = some (.int 64 q))
    (hout : lookupName env "%out" = some (.ptr out))
    (hglob : lookupName env "@g_el_window" = some (.ptr 0x200000))
    (hread : readBytes s.mem 0x200000 8 = some (natToBytes k 8))
    (hk : k < 2 ^ 64) (hep : epow q.toInt = some t)
    (he : elExact W.toNat lz.toNat t q.toInt = some bits) :
    step (numElCalls epow) numElBody (stateAt env s) =
      .jump (stateAt
        (("%call", .int 32 1) ::
          ("%inc", .int 64 ((BitVec.ofNat 64 k) + 1#64)) ::
          ("%2", .int 64 (BitVec.ofNat 64 k)) :: env)
        ({ s with
          mem := writeBytes
            (writeBytes s.mem 0x200000
              (natToBytes (((BitVec.ofNat 64 k) + 1#64).toNat) 8))
            out (natToBytes bits 8),
          pc := "return", pre := some s.pc })) := by
  refine numEl_step_br (calls := numElCalls epow) (env := env) (s := s)
    (t := { s with
            mem := writeBytes
              (writeBytes s.mem 0x200000
                (natToBytes (((BitVec.ofNat 64 k) + 1#64).toNat) 8))
              out (natToBytes bits 8) })
    (hfind := numEl_findBlock_ifThen18_at env s hpc) ?_
  rw [numEl_ifThen18_denote epow env s hW hlz hrow hq hout hglob hread hk hep he]

/-- The window arm's step, refused. -/
theorem numEl_ifThen18_step_none (epow : Int → Option EPow) (env : Env) (s : State)
    {W : BitVec 64} {lz : BitVec 32} {row out k : Nat} {q : BitVec 64} {t : EPow}
    (hpc : s.pc = "if.then18")
    (hW : lookupName env "%shl" = some (.int 64 W))
    (hlz : lookupName env "%cast" = some (.int 32 lz))
    (hrow : lookupName env "%arrayidx" = some (.ptr row))
    (hq : lookupName env "%q" = some (.int 64 q))
    (hout : lookupName env "%out" = some (.ptr out))
    (hglob : lookupName env "@g_el_window" = some (.ptr 0x200000))
    (hread : readBytes s.mem 0x200000 8 = some (natToBytes k 8))
    (hk : k < 2 ^ 64) (hep : epow q.toInt = some t)
    (he : elExact W.toNat lz.toNat t q.toInt = none) :
    step (numElCalls epow) numElBody (stateAt env s) =
      .jump (stateAt
        (("%call", .int 32 0) ::
          ("%inc", .int 64 ((BitVec.ofNat 64 k) + 1#64)) ::
          ("%2", .int 64 (BitVec.ofNat 64 k)) :: env)
        ({ s with
          mem := writeBytes s.mem 0x200000
            (natToBytes (((BitVec.ofNat 64 k) + 1#64).toNat) 8),
          pc := "return", pre := some s.pc })) := by
  refine numEl_step_br (calls := numElCalls epow) (env := env) (s := s)
    (t := { s with
            mem := writeBytes s.mem 0x200000
              (natToBytes (((BitVec.ofNat 64 k) + 1#64).toNat) 8) })
    (hfind := numEl_findBlock_ifThen18_at env s hpc) ?_
  rw [numEl_ifThen18_denote_refuse epow env s hW hlz hrow hq hout hglob hread hk hep he]

/-- The fast arm's step. -/
theorem numEl_ifEnd19_step (epow : Int → Option EPow) (env : Env) (s : State)
    (w q : BitVec 64) (hi : Nat) (out : Nat) (ev : BitVec 32) (r : CallOutcome)
    (hpc : s.pc = "if.end19")
    (hshr7 : lookupName env "%shr7" = some (.int 64 (eShr7 w hi)))
    (hconv6 : lookupName env "%conv6" = some (.int 64 (eConv6 w hi)))
    (hand : lookupName env "%and" = some (.int 64 (eAnd w hi)))
    (hconv12 : lookupName env "%conv12" = some (.int 64 (eConv12 w hi)))
    (hcast : lookupName env "%cast" = some (.int 32 (eCast w)))
    (hconv8 : lookupName env "%conv8" = some (.int 32 (eConv8 w hi)))
    (hout : lookupName env "%out" = some (.ptr out))
    (hrow : lookupName env "%arrayidx" = some (.ptr (eRow q)))
    (he : readBytes s.mem (eRow q + 16) 4 = some (natToBytes ev.toNat 4))
    (hcalls : numElCalls epow "el_pack"
      [.int 64 (eShr21 w hi), .int 32 (eConv23 w hi), .int 32 (eConv8 w hi),
       .int 32 ev, .int 32 (eCast w), .ptr out] s.mem s.next = some r) :
    step (numElCalls epow) numElBody (stateAt env s) =
      .jump (stateAt (numElIfEnd19Env env w q hi ev r)
        ({ s with
          mem := r.mem, next := r.next,
          pc := "return", pre := some s.pc })) := by
  refine numEl_step_br (calls := numElCalls epow) (env := env) (s := s)
    (t := { s with mem := r.mem, next := r.next })
    (hfind := numEl_findBlock_ifEnd19_at env s hpc) ?_
  rw [numEl_ifEnd19_denote epow env s w q hi out ev r hshr7 hconv6 hand hconv12
    hcast hconv8 hout hrow he hcalls]

/-- The return's step from the zero arm. -/
theorem numEl_return_step_zero (epow : Int → Option EPow) (env : Env) (s : State)
    (hpc : s.pc = "return") (hpre : s.pre = some "if.then3") :
    step (numElCalls epow) numElBody (stateAt env s) =
      .ret (some (.int 32 1)) (stateAt (("%retval.1", .int 32 1) :: env) s) := by
  refine numEl_step_ret (calls := numElCalls epow) (env := env)
    (env' := ("%retval.1", .int 32 1) :: env) (s := s)
    (hfind := numEl_findBlock_return_at env s hpc) ?_ ?_
  · rw [numEl_return_denote_ifThen3 epow env s hpre]
  · rfl

/-- The return's step from the window arm. -/
theorem numEl_return_step_window (epow : Int → Option EPow) (env : Env) (s : State)
    {v : BitVec 32} (hpc : s.pc = "return") (hpre : s.pre = some "if.then18")
    (hcall : lookupName env "%call" = some (.int 32 v)) :
    step (numElCalls epow) numElBody (stateAt env s) =
      .ret (some (.int 32 v)) (stateAt (("%retval.1", .int 32 v) :: env) s) := by
  refine numEl_step_ret (calls := numElCalls epow) (env := env)
    (env' := ("%retval.1", .int 32 v) :: env) (s := s)
    (hfind := numEl_findBlock_return_at env s hpc) ?_ ?_
  · rw [numEl_return_denote_ifThen18 epow env s hpre hcall]
  · rfl

/-- The return's step from the fast arm. -/
theorem numEl_return_step_fast (epow : Int → Option EPow) (env : Env) (s : State)
    {v : BitVec 32} (hpc : s.pc = "return") (hpre : s.pre = some "if.end19")
    (hcall : lookupName env "%call24" = some (.int 32 v)) :
    step (numElCalls epow) numElBody (stateAt env s) =
      .ret (some (.int 32 v)) (stateAt (("%retval.1", .int 32 v) :: env) s) := by
  refine numEl_step_ret (calls := numElCalls epow) (env := env)
    (env' := ("%retval.1", .int 32 v) :: env) (s := s)
    (hfind := numEl_findBlock_return_at env s hpc) ?_ ?_
  · rw [numEl_return_denote_ifEnd19 epow env s hpre hcall]
  · rfl

/-! ### The per-arm runs

Each states the whole body's answer at the environment that answers the body's
three callees.  Fuel four is the entry, the guard, one arm and the return; the
zero arm's third step is its last, so the same fuel covers it. -/

/-- The zero mantissa: `*out = 0.0`, return one. -/
theorem numEl_run_zero (epow : Int → Option EPow) (q : BitVec 64) (out : Nat)
    (mem : Mem) (next : Nat) :
    runFuel (numElCalls epow) 4 numElBody (numElEntryState 0#64 q out mem next) =
      some (.ret (some (.int 32 1)) (writeBytes mem out (natToBytes 0 8))) := by
  have h1 : step (numElCalls epow) numElBody (numElEntryState 0#64 q out mem next) =
      .jump (stateAt (numElAfterEntryEnv 0#64 q out)
        (({ numElRaw mem next with pc := "if.then3", pre := some "entry" }) : State)) := by
    rw [show numElEntryState 0#64 q out mem next
        = stateAt (numElEntryEnv 0#64 q out) (numElRaw mem next) from rfl]
    exact numEl_entry_step_zero epow 0#64 q out (numElRaw mem next) rfl rfl
  have h2 : step (numElCalls epow) numElBody
      (stateAt (numElAfterEntryEnv 0#64 q out)
        (({ numElRaw mem next with pc := "if.then3", pre := some "entry" }) : State)) =
      .jump (stateAt (numElAfterEntryEnv 0#64 q out)
        ({ numElRaw mem next with
          mem := writeBytes mem out (natToBytes 0 8),
          pc := "return", pre := some "if.then3" })) :=
    numEl_ifThen3_step epow _ ((({ numElRaw mem next with pc := "if.then3", pre := some "entry" }) : State)) out rfl (lookupNumElAfterEntryEnv_out 0#64 q out)
  have h3 : runFuel (numElCalls epow) 2 numElBody
      (stateAt (numElAfterEntryEnv 0#64 q out)
        ({ numElRaw mem next with
          mem := writeBytes mem out (natToBytes 0 8),
          pc := "return", pre := some "if.then3" })) =
      some (.ret (some (.int 32 1)) (writeBytes mem out (natToBytes 0 8))) := by
    rw [show (2 : Nat) = 1 + 1 from rfl, runFuel.eq_2,
      numEl_return_step_zero epow _ _ rfl rfl]
    rfl
  exact runFuel_prefix_some
    (runFuel_prefix_trans (numEl_runFuel_jump (calls := numElCalls epow) h1)
      (numEl_runFuel_jump (calls := numElCalls epow) h2)) h3

/-- The window arm, accepted: the counter advances, `el_exact` writes `out`, and
the call's one is returned. -/
theorem numEl_run_window_some (epow : Int → Option EPow) (w q : BitVec 64) (hi : Nat)
    (out : Nat) (mem : Mem) (next : Nat) {t : EPow} {k bits : Nat}
    (hhi : hi < 2 ^ 64) (hw : w ≠ 0) (hsub : (eSub q).toNat < 2 ^ 63)
    (hreadHi : readBytes mem (eRow q) 8 = some (natToBytes hi 8))
    (hreadE : readBytes mem (eRow q + 16) 4 = some (natToBytes (epowEWord t.e) 4))
    (hcount : readBytes mem 0x200000 8 = some (natToBytes k 8)) (hk : k < 2 ^ 64)
    (hbit : eCmp15 w hi = 1) (hep : epow q.toInt = some t)
    (hex : elExact (eShl w).toNat (eCast w).toNat t q.toInt = some bits) :
    runFuel (numElCalls epow) 4 numElBody (numElEntryState w q out mem next) =
      some (.ret (some (.int 32 1))
        (writeBytes (writeBytes mem 0x200000
          (natToBytes (((BitVec.ofNat 64 k) + 1#64).toNat) 8)) out (natToBytes bits 8))) := by
  have hreadHi' : readBytes mem (eRow q) 8 = some (natToBytes (eHi hi).toNat 8) := by
    rw [natToBytes_eHi hi hhi]; exact hreadHi
  have h1 : step (numElCalls epow) numElBody (numElEntryState w q out mem next) =
      .jump (stateAt (numElAfterEntryEnv w q out)
        (({ numElRaw mem next with pc := "if.end4", pre := some "entry" }) : State)) := by
    rw [show numElEntryState w q out mem next
        = stateAt (numElEntryEnv w q out) (numElRaw mem next) from rfl]
    exact numEl_entry_step_nonzero epow w q out (numElRaw mem next) rfl hw
  have h2 : step (numElCalls epow) numElBody
      (stateAt (numElAfterEntryEnv w q out)
        (({ numElRaw mem next with pc := "if.end4", pre := some "entry" }) : State)) =
      .jump (stateAt (numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi)
        (({ numElRaw mem next with pc := "if.then18", pre := some "if.end4" }) : State)) := by
    exact numEl_ifEnd4_step_window epow _ _ w q hi rfl
      (lookupNumElAfterEntryEnv_w w q out) (lookupNumElAfterEntryEnv_q w q out)
      (lookupNumElAfterEntryEnv_EPOW w q out) hhi hsub hreadHi' hbit
  have h3 : step (numElCalls epow) numElBody
      (stateAt (numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi)
        (({ numElRaw mem next with pc := "if.then18", pre := some "if.end4" }) : State)) =
      .jump (stateAt
        (("%call", .int 32 1) ::
          ("%inc", .int 64 ((BitVec.ofNat 64 k) + 1#64)) ::
          ("%2", .int 64 (BitVec.ofNat 64 k)) ::
          numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi)
        ({ numElRaw mem next with
          mem := writeBytes
            (writeBytes mem 0x200000
              (natToBytes (((BitVec.ofNat 64 k) + 1#64).toNat) 8))
            out (natToBytes bits 8),
          pc := "return", pre := some "if.then18" })) := by
    exact numEl_ifThen18_step epow _ ((({ numElRaw mem next with pc := "if.then18", pre := some "if.end4" }) : State)) rfl
      (lookupNumElIfEnd4Env_shl _ w q hi) (lookupNumElIfEnd4Env_cast _ w q hi)
      (lookupNumElIfEnd4Env_arrayidx _ w q hi) (liftQ w q hi out) (liftOut w q hi out)
      (lookupNumElIfEnd4Env_glob w q hi out) hcount hk hep hex
  have h4 : runFuel (numElCalls epow) 1 numElBody
      (stateAt
        (("%call", .int 32 1) ::
          ("%inc", .int 64 ((BitVec.ofNat 64 k) + 1#64)) ::
          ("%2", .int 64 (BitVec.ofNat 64 k)) ::
          numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi)
        ({ numElRaw mem next with
          mem := writeBytes
            (writeBytes mem 0x200000
              (natToBytes (((BitVec.ofNat 64 k) + 1#64).toNat) 8))
            out (natToBytes bits 8),
          pc := "return", pre := some "if.then18" })) =
      some (.ret (some (.int 32 1))
        (writeBytes (writeBytes mem 0x200000
          (natToBytes (((BitVec.ofNat 64 k) + 1#64).toNat) 8)) out (natToBytes bits 8))) := by
    rw [show (1 : Nat) = 0 + 1 from rfl, runFuel.eq_2,
      numEl_return_step_window (v := 1) epow _ _ rfl rfl (by
        simp only [lookupName_cons_self])]
    rfl
  exact runFuel_prefix_some
    (runFuel_prefix_trans
      (runFuel_prefix_trans (numEl_runFuel_jump (calls := numElCalls epow) h1)
        (numEl_runFuel_jump (calls := numElCalls epow) h2))
      (numEl_runFuel_jump (calls := numElCalls epow) h3)) h4

/-- The window arm, refused: the counter advances before `el_exact` declines, so
the memory carries the next word and no `out` write. -/
theorem numEl_run_window_none (epow : Int → Option EPow) (w q : BitVec 64) (hi : Nat)
    (out : Nat) (mem : Mem) (next : Nat) {t : EPow} {k : Nat}
    (hhi : hi < 2 ^ 64) (hw : w ≠ 0) (hsub : (eSub q).toNat < 2 ^ 63)
    (hreadHi : readBytes mem (eRow q) 8 = some (natToBytes hi 8))
    (hreadE : readBytes mem (eRow q + 16) 4 = some (natToBytes (epowEWord t.e) 4))
    (hcount : readBytes mem 0x200000 8 = some (natToBytes k 8)) (hk : k < 2 ^ 64)
    (hbit : eCmp15 w hi = 1) (hep : epow q.toInt = some t)
    (hex : elExact (eShl w).toNat (eCast w).toNat t q.toInt = none) :
    runFuel (numElCalls epow) 4 numElBody (numElEntryState w q out mem next) =
      some (.ret (some (.int 32 0))
        (writeBytes mem 0x200000
          (natToBytes (((BitVec.ofNat 64 k) + 1#64).toNat) 8))) := by
  have hreadHi' : readBytes mem (eRow q) 8 = some (natToBytes (eHi hi).toNat 8) := by
    rw [natToBytes_eHi hi hhi]; exact hreadHi
  have h1 : step (numElCalls epow) numElBody (numElEntryState w q out mem next) =
      .jump (stateAt (numElAfterEntryEnv w q out)
        (({ numElRaw mem next with pc := "if.end4", pre := some "entry" }) : State)) := by
    rw [show numElEntryState w q out mem next
        = stateAt (numElEntryEnv w q out) (numElRaw mem next) from rfl]
    exact numEl_entry_step_nonzero epow w q out (numElRaw mem next) rfl hw
  have h2 : step (numElCalls epow) numElBody
      (stateAt (numElAfterEntryEnv w q out)
        (({ numElRaw mem next with pc := "if.end4", pre := some "entry" }) : State)) =
      .jump (stateAt (numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi)
        (({ numElRaw mem next with pc := "if.then18", pre := some "if.end4" }) : State)) := by
    exact numEl_ifEnd4_step_window epow _ _ w q hi rfl
      (lookupNumElAfterEntryEnv_w w q out) (lookupNumElAfterEntryEnv_q w q out)
      (lookupNumElAfterEntryEnv_EPOW w q out) hhi hsub hreadHi' hbit
  have h3 : step (numElCalls epow) numElBody
      (stateAt (numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi)
        (({ numElRaw mem next with pc := "if.then18", pre := some "if.end4" }) : State)) =
      .jump (stateAt
        (("%call", .int 32 0) ::
          ("%inc", .int 64 ((BitVec.ofNat 64 k) + 1#64)) ::
          ("%2", .int 64 (BitVec.ofNat 64 k)) ::
          numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi)
        ({ numElRaw mem next with
          mem := writeBytes mem 0x200000
            (natToBytes (((BitVec.ofNat 64 k) + 1#64).toNat) 8),
          pc := "return", pre := some "if.then18" })) := by
    exact numEl_ifThen18_step_none epow _ ((({ numElRaw mem next with pc := "if.then18", pre := some "if.end4" }) : State)) rfl
      (lookupNumElIfEnd4Env_shl _ w q hi) (lookupNumElIfEnd4Env_cast _ w q hi)
      (lookupNumElIfEnd4Env_arrayidx _ w q hi) (liftQ w q hi out) (liftOut w q hi out)
      (lookupNumElIfEnd4Env_glob w q hi out) hcount hk hep hex
  have h4 : runFuel (numElCalls epow) 1 numElBody
      (stateAt
        (("%call", .int 32 0) ::
          ("%inc", .int 64 ((BitVec.ofNat 64 k) + 1#64)) ::
          ("%2", .int 64 (BitVec.ofNat 64 k)) ::
          numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi)
        ({ numElRaw mem next with
          mem := writeBytes mem 0x200000
            (natToBytes (((BitVec.ofNat 64 k) + 1#64).toNat) 8),
          pc := "return", pre := some "if.then18" })) =
      some (.ret (some (.int 32 0))
        (writeBytes mem 0x200000
          (natToBytes (((BitVec.ofNat 64 k) + 1#64).toNat) 8))) := by
    rw [show (1 : Nat) = 0 + 1 from rfl, runFuel.eq_2,
      numEl_return_step_window (v := 0) epow _ _ rfl rfl (by
        simp only [lookupName_cons_self])]
    rfl
  exact runFuel_prefix_some
    (runFuel_prefix_trans
      (runFuel_prefix_trans (numEl_runFuel_jump (calls := numElCalls epow) h1)
        (numEl_runFuel_jump (calls := numElCalls epow) h2))
      (numEl_runFuel_jump (calls := numElCalls epow) h3)) h4

/-- The fast arm, accepted: `el_pack` writes `out`, nothing else moves. -/
theorem numEl_run_fast_some (epow : Int → Option EPow) (w q : BitVec 64) (hi : Nat)
    (out : Nat) (mem : Mem) (next : Nat) {t : EPow} {bits : Nat}
    (hhi : hi < 2 ^ 64) (hw : w ≠ 0) (hsub : (eSub q).toNat < 2 ^ 63)
    (hreadHi : readBytes mem (eRow q) 8 = some (natToBytes hi 8))
    (hreadE : readBytes mem (eRow q + 16) 4 = some (natToBytes (epowEWord t.e) 4))
    (hbit : eCmp15 w hi = 0)
    (hpack : elPack (eShr21 w hi).toNat (eConv23 w hi).toNat (eConv8 w hi).toNat
      ⟨0, 0, numElI32ToInt (eE t)⟩ (eCast w).toNat = some bits) :
    runFuel (numElCalls epow) 4 numElBody (numElEntryState w q out mem next) =
      some (.ret (some (.int 32 1)) (writeBytes mem out (natToBytes bits 8))) := by
  have hreadHi' : readBytes mem (eRow q) 8 = some (natToBytes (eHi hi).toNat 8) := by
    rw [natToBytes_eHi hi hhi]; exact hreadHi
  have hreadE' : readBytes mem (eRow q + 16) 4 = some (natToBytes (eE t).toNat 4) := by
    rw [natToBytes_eE]; exact hreadE
  have h1 : step (numElCalls epow) numElBody (numElEntryState w q out mem next) =
      .jump (stateAt (numElAfterEntryEnv w q out)
        (({ numElRaw mem next with pc := "if.end4", pre := some "entry" }) : State)) := by
    rw [show numElEntryState w q out mem next
        = stateAt (numElEntryEnv w q out) (numElRaw mem next) from rfl]
    exact numEl_entry_step_nonzero epow w q out (numElRaw mem next) rfl hw
  have h2 : step (numElCalls epow) numElBody
      (stateAt (numElAfterEntryEnv w q out)
        (({ numElRaw mem next with pc := "if.end4", pre := some "entry" }) : State)) =
      .jump (stateAt (numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi)
        (({ numElRaw mem next with pc := "if.end19", pre := some "if.end4" }) : State)) := by
    exact numEl_ifEnd4_step_fast epow _ _ w q hi rfl
      (lookupNumElAfterEntryEnv_w w q out) (lookupNumElAfterEntryEnv_q w q out)
      (lookupNumElAfterEntryEnv_EPOW w q out) hhi hsub hreadHi' hbit
  have h3 : step (numElCalls epow) numElBody
      (stateAt (numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi)
        (({ numElRaw mem next with pc := "if.end19", pre := some "if.end4" }) : State)) =
      .jump (stateAt
        (numElIfEnd19Env (numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi) w q hi
          (eE t) { ret := .int 32 1, mem := writeBytes mem out (natToBytes bits 8),
                   next := next })
        ({ numElRaw mem next with
          mem := writeBytes mem out (natToBytes bits 8), next := next,
          pc := "return", pre := some "if.end19" })) := by
    exact numEl_ifEnd19_step epow _ ((({ numElRaw mem next with pc := "if.end19", pre := some "if.end4" }) : State)) w q hi out (eE t) _ rfl
      (lookupNumElIfEnd4Env_shr7 _ w q hi) (lookupNumElIfEnd4Env_conv6 _ w q hi)
      (lookupNumElIfEnd4Env_and _ w q hi) (lookupNumElIfEnd4Env_conv12 _ w q hi)
      (lookupNumElIfEnd4Env_cast _ w q hi) (lookupNumElIfEnd4Env_conv8 _ w q hi)
      (liftOut w q hi out)
      (lookupNumElIfEnd4Env_arrayidx _ w q hi) hreadE'
      (numElCalls_elPack epow hpack mem next)
  have h4 : runFuel (numElCalls epow) 1 numElBody
      (stateAt
        (numElIfEnd19Env (numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi) w q hi
          (eE t) { ret := .int 32 1, mem := writeBytes mem out (natToBytes bits 8),
                   next := next })
        ({ numElRaw mem next with
          mem := writeBytes mem out (natToBytes bits 8), next := next,
          pc := "return", pre := some "if.end19" })) =
      some (.ret (some (.int 32 1)) (writeBytes mem out (natToBytes bits 8))) := by
    rw [show (1 : Nat) = 0 + 1 from rfl, runFuel.eq_2,
      numEl_return_step_fast (v := 1) epow _ _ rfl rfl (by
        simp only [numElIfEnd19Env, cells, lookupName_cons_self])]
    rfl
  exact runFuel_prefix_some
    (runFuel_prefix_trans
      (runFuel_prefix_trans (numEl_runFuel_jump (calls := numElCalls epow) h1)
        (numEl_runFuel_jump (calls := numElCalls epow) h2))
      (numEl_runFuel_jump (calls := numElCalls epow) h3)) h4

/-- The fast arm, refused: `el_pack` declines, nothing is written. -/
theorem numEl_run_fast_none (epow : Int → Option EPow) (w q : BitVec 64) (hi : Nat)
    (out : Nat) (mem : Mem) (next : Nat) {t : EPow}
    (hhi : hi < 2 ^ 64) (hw : w ≠ 0) (hsub : (eSub q).toNat < 2 ^ 63)
    (hreadHi : readBytes mem (eRow q) 8 = some (natToBytes hi 8))
    (hreadE : readBytes mem (eRow q + 16) 4 = some (natToBytes (epowEWord t.e) 4))
    (hbit : eCmp15 w hi = 0)
    (hpack : elPack (eShr21 w hi).toNat (eConv23 w hi).toNat (eConv8 w hi).toNat
      ⟨0, 0, numElI32ToInt (eE t)⟩ (eCast w).toNat = none) :
    runFuel (numElCalls epow) 4 numElBody (numElEntryState w q out mem next) =
      some (.ret (some (.int 32 0)) mem) := by
  have hreadHi' : readBytes mem (eRow q) 8 = some (natToBytes (eHi hi).toNat 8) := by
    rw [natToBytes_eHi hi hhi]; exact hreadHi
  have hreadE' : readBytes mem (eRow q + 16) 4 = some (natToBytes (eE t).toNat 4) := by
    rw [natToBytes_eE]; exact hreadE
  have h1 : step (numElCalls epow) numElBody (numElEntryState w q out mem next) =
      .jump (stateAt (numElAfterEntryEnv w q out)
        (({ numElRaw mem next with pc := "if.end4", pre := some "entry" }) : State)) := by
    rw [show numElEntryState w q out mem next
        = stateAt (numElEntryEnv w q out) (numElRaw mem next) from rfl]
    exact numEl_entry_step_nonzero epow w q out (numElRaw mem next) rfl hw
  have h2 : step (numElCalls epow) numElBody
      (stateAt (numElAfterEntryEnv w q out)
        (({ numElRaw mem next with pc := "if.end4", pre := some "entry" }) : State)) =
      .jump (stateAt (numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi)
        (({ numElRaw mem next with pc := "if.end19", pre := some "if.end4" }) : State)) := by
    exact numEl_ifEnd4_step_fast epow _ _ w q hi rfl
      (lookupNumElAfterEntryEnv_w w q out) (lookupNumElAfterEntryEnv_q w q out)
      (lookupNumElAfterEntryEnv_EPOW w q out) hhi hsub hreadHi' hbit
  have h3 : step (numElCalls epow) numElBody
      (stateAt (numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi)
        (({ numElRaw mem next with pc := "if.end19", pre := some "if.end4" }) : State)) =
      .jump (stateAt
        (numElIfEnd19Env (numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi) w q hi
          (eE t) { ret := .int 32 0, mem := mem, next := next })
        ({ numElRaw mem next with
          mem := mem, next := next,
          pc := "return", pre := some "if.end19" })) := by
    exact numEl_ifEnd19_step epow _ ((({ numElRaw mem next with pc := "if.end19", pre := some "if.end4" }) : State)) w q hi out (eE t) _ rfl
      (lookupNumElIfEnd4Env_shr7 _ w q hi) (lookupNumElIfEnd4Env_conv6 _ w q hi)
      (lookupNumElIfEnd4Env_and _ w q hi) (lookupNumElIfEnd4Env_conv12 _ w q hi)
      (lookupNumElIfEnd4Env_cast _ w q hi) (lookupNumElIfEnd4Env_conv8 _ w q hi)
      (liftOut w q hi out)
      (lookupNumElIfEnd4Env_arrayidx _ w q hi) hreadE'
      (numElCalls_elPack_refuse epow hpack mem next)
  have h4 : runFuel (numElCalls epow) 1 numElBody
      (stateAt
        (numElIfEnd19Env (numElIfEnd4Env (numElAfterEntryEnv w q out) w q hi) w q hi
          (eE t) { ret := .int 32 0, mem := mem, next := next })
        ({ numElRaw mem next with
          mem := mem, next := next,
          pc := "return", pre := some "if.end19" })) =
      some (.ret (some (.int 32 0)) mem) := by
    rw [show (1 : Nat) = 0 + 1 from rfl, runFuel.eq_2,
      numEl_return_step_fast (v := 0) epow _ _ rfl rfl (by
        simp only [numElIfEnd19Env, cells, lookupName_cons_self])]
    rfl
  exact runFuel_prefix_some
    (runFuel_prefix_trans
      (runFuel_prefix_trans (numEl_runFuel_jump (calls := numElCalls epow) h1)
        (numEl_runFuel_jump (calls := numElCalls epow) h2))
      (numEl_runFuel_jump (calls := numElCalls epow) h3)) h4

/-! ### The body's answer, and the selection that uses it -/

/-- A run's outcome as the call's answer. -/
def numElOptionOutcome : Option Outcome → Nat → Option CallOutcome
  | some (.ret (some v) m), next => some { ret := v, mem := m, next := next }
  | _, _ => none

/-- The body's answer, run from the entry state at the environment that answers
its three callees. -/
def numElRunAnswer (epow : Int → Option EPow) (w q : BitVec 64) (out : Nat)
    (mem : Mem) (next : Nat) : Option CallOutcome :=
  numElOptionOutcome
    (runFuel (numElCalls epow) 4 numElBody (numElEntryState w q out mem next)) next

theorem numElRunAnswer_zero (epow : Int → Option EPow) (q : BitVec 64) (out : Nat)
    (mem : Mem) (next : Nat) :
    numElRunAnswer epow 0#64 q out mem next =
      some { ret := .int 32 1, mem := writeBytes mem out (natToBytes 0 8), next := next } := by
  unfold numElRunAnswer
  rw [numEl_run_zero]
  rfl

theorem numElRunAnswer_window_some (epow : Int → Option EPow) (w q : BitVec 64)
    (hi : Nat) (out : Nat) (mem : Mem) (next : Nat) {t : EPow} {k bits : Nat}
    (hhi : hi < 2 ^ 64) (hw : w ≠ 0) (hsub : (eSub q).toNat < 2 ^ 63)
    (hreadHi : readBytes mem (eRow q) 8 = some (natToBytes hi 8))
    (hreadE : readBytes mem (eRow q + 16) 4 = some (natToBytes (epowEWord t.e) 4))
    (hcount : readBytes mem 0x200000 8 = some (natToBytes k 8)) (hk : k < 2 ^ 64)
    (hbit : eCmp15 w hi = 1) (hep : epow q.toInt = some t)
    (hex : elExact (eShl w).toNat (eCast w).toNat t q.toInt = some bits) :
    numElRunAnswer epow w q out mem next =
      some { ret := .int 32 1,
             mem := writeBytes (writeBytes mem 0x200000
               (natToBytes (((BitVec.ofNat 64 k) + 1#64).toNat) 8)) out
               (natToBytes bits 8),
             next := next } := by
  unfold numElRunAnswer
  rw [numEl_run_window_some epow w q hi out mem next hhi hw hsub hreadHi hreadE hcount hk
    hbit hep hex]
  rfl

theorem numElRunAnswer_window_none (epow : Int → Option EPow) (w q : BitVec 64)
    (hi : Nat) (out : Nat) (mem : Mem) (next : Nat) {t : EPow} {k : Nat}
    (hhi : hi < 2 ^ 64) (hw : w ≠ 0) (hsub : (eSub q).toNat < 2 ^ 63)
    (hreadHi : readBytes mem (eRow q) 8 = some (natToBytes hi 8))
    (hreadE : readBytes mem (eRow q + 16) 4 = some (natToBytes (epowEWord t.e) 4))
    (hcount : readBytes mem 0x200000 8 = some (natToBytes k 8)) (hk : k < 2 ^ 64)
    (hbit : eCmp15 w hi = 1) (hep : epow q.toInt = some t)
    (hex : elExact (eShl w).toNat (eCast w).toNat t q.toInt = none) :
    numElRunAnswer epow w q out mem next =
      some { ret := .int 32 0,
             mem := writeBytes mem 0x200000
               (natToBytes (((BitVec.ofNat 64 k) + 1#64).toNat) 8),
             next := next } := by
  unfold numElRunAnswer
  rw [numEl_run_window_none epow w q hi out mem next hhi hw hsub hreadHi hreadE hcount hk
    hbit hep hex]
  rfl

theorem numElRunAnswer_fast_some (epow : Int → Option EPow) (w q : BitVec 64)
    (hi : Nat) (out : Nat) (mem : Mem) (next : Nat) {t : EPow} {bits : Nat}
    (hhi : hi < 2 ^ 64) (hw : w ≠ 0) (hsub : (eSub q).toNat < 2 ^ 63)
    (hreadHi : readBytes mem (eRow q) 8 = some (natToBytes hi 8))
    (hreadE : readBytes mem (eRow q + 16) 4 = some (natToBytes (epowEWord t.e) 4))
    (hbit : eCmp15 w hi = 0)
    (hpack : elPack (eShr21 w hi).toNat (eConv23 w hi).toNat (eConv8 w hi).toNat
      ⟨0, 0, numElI32ToInt (eE t)⟩ (eCast w).toNat = some bits) :
    numElRunAnswer epow w q out mem next =
      some { ret := .int 32 1, mem := writeBytes mem out (natToBytes bits 8),
             next := next } := by
  unfold numElRunAnswer
  rw [numEl_run_fast_some epow w q hi out mem next hhi hw hsub hreadHi hreadE hbit hpack]
  rfl

theorem numElRunAnswer_fast_none (epow : Int → Option EPow) (w q : BitVec 64)
    (hi : Nat) (out : Nat) (mem : Mem) (next : Nat) {t : EPow}
    (hhi : hi < 2 ^ 64) (hw : w ≠ 0) (hsub : (eSub q).toNat < 2 ^ 63)
    (hreadHi : readBytes mem (eRow q) 8 = some (natToBytes hi 8))
    (hreadE : readBytes mem (eRow q + 16) 4 = some (natToBytes (epowEWord t.e) 4))
    (hbit : eCmp15 w hi = 0)
    (hpack : elPack (eShr21 w hi).toNat (eConv23 w hi).toNat (eConv8 w hi).toNat
      ⟨0, 0, numElI32ToInt (eE t)⟩ (eCast w).toNat = none) :
    numElRunAnswer epow w q out mem next =
      some { ret := .int 32 0, mem := mem, next := next } := by
  unfold numElRunAnswer
  rw [numEl_run_fast_none epow w q hi out mem next hhi hw hsub hreadHi hreadE hbit hpack]
  rfl

/-- The walk's environment with `num_el_el1` answered by its pinned body's run. -/
def numElBodyCalls (base : Calls) (epow : Int → Option EPow) : Calls :=
  fun callee args mem next =>
    if callee = "num_el_el1" then
      match args with
      | [.int 64 w, .int 64 q, .ptr out] => numElRunAnswer epow w q out mem next
      | _ => none
    else base callee args mem next

/-- The selection's answer at the body's arguments is the run's. -/
theorem numElBodyCalls_num_el (base : Calls) (epow : Int → Option EPow)
    (w q : BitVec 64) (out : Nat) (mem : Mem) (next : Nat) :
    numElBodyCalls base epow "num_el_el1" [.int 64 w, .int 64 q, .ptr out] mem next =
      numElRunAnswer epow w q out mem next := by
  simp only [numElBodyCalls, if_true]

/-! ### The model's window branch at the body's words -/

/-- **The model takes the window arm at `%cmp15 = 1`.**  `numElWindow` is
`numElEl1`'s branch written out, so its arm at the staged row is exactly the
emitted test's: the normalised word and the row are the model's. -/
theorem numElWindow_eq_some (epow : Int → Option EPow) (w q : BitVec 64) (t : EPow)
    (hw : w ≠ 0) (hhi : t.hi < 2 ^ 64)
    (hrange : ¬ (q.toInt < -45 ∨ 45 < q.toInt)) (hep : epow q.toInt = some t)
    (hbit : eCmp15 w t.hi = 1) :
    numElWindow epow w.toNat q.toInt =
      some (elW w.toNat, 64 - Nat.size w.toNat, t) := by
  have hw0 : w.toNat ≠ 0 := by
    intro h0; exact hw (BitVec.toNat_inj.mp (by simpa using h0))
  have hwin : elWindow w.toNat t.hi := (eCmp15_eq_one_iff w t.hi hw hhi).mp hbit
  have hwin' : elHalf (elAhi w.toNat t.hi / 2 ^ 63) ≤
        elAhi w.toNat t.hi % 2 ^ (10 + elAhi w.toNat t.hi / 2 ^ 63) + 2 ∧
      elAhi w.toNat t.hi % 2 ^ (10 + elAhi w.toNat t.hi / 2 ^ 63) ≤
        elHalf (elAhi w.toNat t.hi / 2 ^ 63) := by
    simpa [elWindow, elHh, elHp, elUb, elHalf] using hwin
  unfold numElWindow
  rw [if_neg hrange, if_neg hw0, hep]
  dsimp only
  rw [if_pos (by simpa [elW, elAhi, elUb, elHp, elHh, elHalf] using hwin')]
  simp only [elW]

/-- **The model leaves the window arm at `%cmp15 = 0`.** -/
theorem numElWindow_eq_none (epow : Int → Option EPow) (w q : BitVec 64) (t : EPow)
    (hw : w ≠ 0) (hhi : t.hi < 2 ^ 64)
    (hrange : ¬ (q.toInt < -45 ∨ 45 < q.toInt)) (hep : epow q.toInt = some t)
    (hbit : eCmp15 w t.hi = 0) : numElWindow epow w.toNat q.toInt = none := by
  have hw0 : w.toNat ≠ 0 := by
    intro h0; exact hw (BitVec.toNat_inj.mp (by simpa using h0))
  have hnwin : ¬ elWindow w.toNat t.hi := (eCmp15_eq_zero_iff w t.hi hw hhi).mp hbit
  have hnwin' : ¬ (elHalf (elAhi w.toNat t.hi / 2 ^ 63) ≤
        elAhi w.toNat t.hi % 2 ^ (10 + elAhi w.toNat t.hi / 2 ^ 63) + 2 ∧
      elAhi w.toNat t.hi % 2 ^ (10 + elAhi w.toNat t.hi / 2 ^ 63) ≤
        elHalf (elAhi w.toNat t.hi / 2 ^ 63)) := by
    simpa [elWindow, elHh, elHp, elUb, elHalf] using hnwin
  unfold numElWindow
  rw [if_neg hrange, if_neg hw0, hep]
  dsimp only
  rw [if_neg (by simpa [elW, elAhi, elUb, elHp, elHh, elHalf] using hnwin')]

/-- **The model, unfolded at the body's words.** -/
theorem numElEl1_unfold (epow : Int → Option EPow) (w q : BitVec 64) (t : EPow)
    (hw0 : w.toNat ≠ 0) (hrange : ¬ (q.toInt < -45 ∨ 45 < q.toInt))
    (hep : epow q.toInt = some t) :
    numElEl1 epow w.toNat q.toInt =
      (if elWindow w.toNat t.hi then
         elExact (elW w.toNat) (64 - Nat.size w.toNat) t q.toInt
       else
         elPack (elM w.toNat t.hi) (elUp w.toNat t.hi) (elUb w.toNat t.hi) t
           (64 - Nat.size w.toNat)) := by
  unfold numElEl1 elWindow elHh elHp elUb elAhi elM elUp elW
  rw [if_neg hrange, if_neg hw0, hep]
  dsimp only
  rfl

/-- The model's answer on the window arm, accepted. -/
theorem numElAnswer_window_some (epow : Int → Option EPow) (w q : BitVec 64)
    (out : Nat) (mem : Mem) (next : Nat) {t : EPow} {bits : Nat}
    (hwin : numElWindow epow w.toNat q.toInt =
      some (elW w.toNat, 64 - Nat.size w.toNat, t))
    (hex : elExact (elW w.toNat) (64 - Nat.size w.toNat) t q.toInt = some bits) :
    numElAnswer epow [.int 64 w, .int 64 q, .ptr out] mem next =
      some { ret := .int 32 1,
             mem := writeBytes (numElCounterMem mem numElWindowAddr) out
               (natToBytes bits 8),
             next := next } := by
  simp only [numElAnswer, numElAnswerAt, numElWindowAddr]
  rw [hwin, numElEl1_window hwin, hex]
  rfl

/-- The model's answer on the window arm, refused. -/
theorem numElAnswer_window_none (epow : Int → Option EPow) (w q : BitVec 64)
    (out : Nat) (mem : Mem) (next : Nat) {t : EPow}
    (hwin : numElWindow epow w.toNat q.toInt =
      some (elW w.toNat, 64 - Nat.size w.toNat, t))
    (hex : elExact (elW w.toNat) (64 - Nat.size w.toNat) t q.toInt = none) :
    numElAnswer epow [.int 64 w, .int 64 q, .ptr out] mem next =
      some { ret := .int 32 0, mem := numElCounterMem mem numElWindowAddr,
             next := next } := by
  simp only [numElAnswer, numElAnswerAt, numElWindowAddr]
  rw [hwin, numElEl1_window hwin, hex]
  rfl

/-- The model's answer on the fast arm, accepted. -/
theorem numElAnswer_fast_some (epow : Int → Option EPow) (w q : BitVec 64)
    (out : Nat) (mem : Mem) (next : Nat) {t : EPow} {bits : Nat}
    (hw0 : w.toNat ≠ 0) (hrange : ¬ (q.toInt < -45 ∨ 45 < q.toInt))
    (hep : epow q.toInt = some t)
    (hwin : numElWindow epow w.toNat q.toInt = none)
    (hnwin : ¬ elWindow w.toNat t.hi)
    (hpack : elPack (elM w.toNat t.hi) (elUp w.toNat t.hi) (elUb w.toNat t.hi) t
      (64 - Nat.size w.toNat) = some bits) :
    numElAnswer epow [.int 64 w, .int 64 q, .ptr out] mem next =
      some { ret := .int 32 1, mem := writeBytes mem out (natToBytes bits 8),
             next := next } := by
  simp only [numElAnswer, numElAnswerAt, numElWindowAddr]
  rw [hwin, numElEl1_unfold epow w q t hw0 hrange hep, if_neg hnwin, hpack]
  rfl

/-- The model's answer on the fast arm, refused. -/
theorem numElAnswer_fast_none (epow : Int → Option EPow) (w q : BitVec 64)
    (out : Nat) (mem : Mem) (next : Nat) {t : EPow}
    (hw0 : w.toNat ≠ 0) (hrange : ¬ (q.toInt < -45 ∨ 45 < q.toInt))
    (hep : epow q.toInt = some t)
    (hwin : numElWindow epow w.toNat q.toInt = none)
    (hnwin : ¬ elWindow w.toNat t.hi)
    (hpack : elPack (elM w.toNat t.hi) (elUp w.toNat t.hi) (elUb w.toNat t.hi) t
      (64 - Nat.size w.toNat) = none) :
    numElAnswer epow [.int 64 w, .int 64 q, .ptr out] mem next =
      some { ret := .int 32 0, mem := mem, next := next } := by
  simp only [numElAnswer, numElAnswerAt, numElWindowAddr]
  rw [hwin, numElEl1_unfold epow w q t hw0 hrange hep, if_neg hnwin, hpack]
  rfl

/-- The `el_pack` argument list the body passes is the model's, at the staged
exponent's word. -/
theorem ePack_model (w : BitVec 64) (hi : Nat) (t : EPow) (hw : w ≠ 0)
    (hhi : hi < 2 ^ 64) (hlo : -(2 ^ 31 : Int) ≤ t.e) (heHi : t.e < 2 ^ 31) :
    elPack (eShr21 w hi).toNat (eConv23 w hi).toNat (eConv8 w hi).toNat
        ⟨0, 0, numElI32ToInt (eE t)⟩ (eCast w).toNat =
      elPack (elM w.toNat hi) (elUp w.toNat hi) (elUb w.toNat hi) t
        (64 - Nat.size w.toNat) := by
  rw [eShr21_toNat w hi hw hhi, eConv23_toNat w hi hw hhi, eConv8_toNat w hi hw hhi,
    eCast_toNat w hw, eE, numElI32ToInt_epowEWord hlo heHi]
  rfl

/-! ### The arm

The body's answer *is* the model's answer at the selection's arguments, on every
arm the kernel decides: the outcomes agree because the branch and its two calls
are the model's, and the memories agree because the window arm's counter write is
`numElCounterMem`'s (`numEl_ifThen18_counter_write`) and the fast arm moves
nothing but `out`. -/

/-- **The body's answer is the model's**, at a nonzero mantissa. -/
theorem numElBodyCalls_eq (base : Calls) (epow : Int → Option EPow)
    (w q : BitVec 64) (out : Nat) (mem : Mem) (next : Nat) (t : EPow) (row k : Nat)
    (hrow : NumElRow mem row t) (hrowAddr : eRow q = row) (hhi : t.hi < 2 ^ 64)
    (hw : w ≠ 0) (hep : epow q.toInt = some t)
    (hrange : -45 ≤ q.toInt ∧ q.toInt ≤ 45)
    (heLo : -(2 ^ 31 : Int) ≤ t.e) (heHi : t.e < 2 ^ 31)
    (hcount : readBytes mem 0x200000 8 = some (natToBytes k 8)) (hk : k < 2 ^ 64)
    (hsub : (eSub q).toNat < 2 ^ 63) :
    numElBodyCalls base epow "num_el_el1" [.int 64 w, .int 64 q, .ptr out] mem next =
      numElAnswer epow [.int 64 w, .int 64 q, .ptr out] mem next := by
  rw [numElBodyCalls_num_el]
  have hw0 : w.toNat ≠ 0 := by
    intro h0; exact hw (BitVec.toNat_inj.mp (by simpa using h0))
  have hrange' : ¬ (q.toInt < -45 ∨ 45 < q.toInt) := by omega
  have hreadHi : readBytes mem (eRow q) 8 = some (natToBytes t.hi 8) := by
    rw [hrowAddr]; exact hrow.hi
  have hreadE : readBytes mem (eRow q + 16) 4 = some (natToBytes (epowEWord t.e) 4) := by
    rw [hrowAddr]; exact hrow.e
  have hcounter := numEl_ifThen18_counter_write hcount hk
  rcases BlockEval.bitVec1_eq_zero_or_one (eCmp15 w t.hi) with hbit | hbit
  · -- the fast arm
    have hnwin : ¬ elWindow w.toNat t.hi := (eCmp15_eq_zero_iff w t.hi hw hhi).mp hbit
    have hwinNone := numElWindow_eq_none epow w q t hw hhi hrange' hep hbit
    cases hpack : elPack (elM w.toNat t.hi) (elUp w.toNat t.hi) (elUb w.toNat t.hi) t
        (64 - Nat.size w.toNat) with
    | some bits =>
        rw [numElRunAnswer_fast_some epow w q t.hi out mem next hhi hw hsub
          hreadHi hreadE hbit (by
            rw [ePack_model w t.hi t hw hhi heLo heHi]; exact hpack)]
        rw [numElAnswer_fast_some epow w q out mem next hw0 hrange' hep hwinNone hnwin
          hpack]
    | none =>
        rw [numElRunAnswer_fast_none epow w q t.hi out mem next hhi hw hsub
          hreadHi hreadE hbit (by
            rw [ePack_model w t.hi t hw hhi heLo heHi]; exact hpack)]
        rw [numElAnswer_fast_none epow w q out mem next hw0 hrange' hep hwinNone hnwin
          hpack]
  · -- the window arm
    have hwinSome := numElWindow_eq_some epow w q t hw hhi hrange' hep hbit
    cases hex : elExact (elW w.toNat) (64 - Nat.size w.toNat) t q.toInt with
    | some bits =>
        rw [numElRunAnswer_window_some epow w q t.hi out mem next hhi hw hsub
          hreadHi hreadE hcount hk hbit hep (by
            rw [eShl_toNat w hw, eCast_toNat w hw]; exact hex)]
        rw [numElAnswer_window_some epow w q out mem next hwinSome hex]
        rw [hcounter]
        rfl
    | none =>
        rw [numElRunAnswer_window_none epow w q t.hi out mem next hhi hw hsub
          hreadHi hreadE hcount hk hbit hep (by
            rw [eShl_toNat w hw, eCast_toNat w hw]; exact hex)]
        rw [numElAnswer_window_none epow w q out mem next hwinSome hex]
        rw [hcounter]
        rfl

/-- **The body's answer is the model's**, at the zero mantissa. -/
theorem numElBodyCalls_eq_zero (base : Calls) (epow : Int → Option EPow)
    (q : BitVec 64) (out : Nat) (mem : Mem) (next : Nat)
    (hrange : -45 ≤ q.toInt ∧ q.toInt ≤ 45) :
    numElBodyCalls base epow "num_el_el1" [.int 64 0#64, .int 64 q, .ptr out] mem next =
      numElAnswer epow [.int 64 0#64, .int 64 q, .ptr out] mem next := by
  rw [numElBodyCalls_num_el, numElRunAnswer_zero]
  have hrange' : ¬ (q.toInt < -45 ∨ 45 < q.toInt) := by omega
  have hzero : numElWindow epow (0#64).toNat q.toInt = none := by
    unfold numElWindow
    rw [if_neg hrange']
    simp
  have hel : numElEl1 epow (0#64).toNat q.toInt = some 0 := by
    unfold numElEl1
    rw [if_neg hrange']
    simp
  simp only [numElAnswer, numElAnswerAt, numElWindowAddr]
  rw [hzero, hel]
  rfl

/-! ### Axiom footprints

The arm's own proof uses no choice; `Classical.choice` reaches `numElBodyCalls_eq`
through `eCmp15_eq_one_iff`, the bridge from the emitted `%cmp15` to the model's
`elWindow`, which is proved in this module and is not an assumption about the
body.  The zero-mantissa arm does not go through that bridge and carries the
standard footprint. -/

/-- info: 'LeanLLVM.Refinement.numElBodyCalls_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numElBodyCalls_eq

/-- info: 'LeanLLVM.Refinement.numElBodyCalls_eq_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numElBodyCalls_eq_zero

end LeanLLVM.Refinement
