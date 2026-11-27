/-
The arithmetic the multiply's group loop reads out of the emitted `i128` words.

The body multiplies a 64-bit limb by a 128-bit multiplier and adds a 128-bit carry,
all at `i128`, then keeps the low 64 bits and shifts the rest out.  The model
(`JsonStage2NumFastCalls`'s `stkMulFold`) computes the same two numbers at `Nat`.
This module is the bridge, and it is three facts per limb:

* the widened product and the carry addition do not wrap, because both operands of
  the product are below `2 ^ 64` and the carry is too, so `toNat` of the `i128` sum
  is the `Nat` sum (`stkMulWide_toNat`);
* `>>> 64` at `i128` is the `Nat` division by `2 ^ 64` (`stkMulShr_toNat`), and the
  truncation to `i64` is the `Nat` remainder (`stkMulConv_toNat`);
* so the carry out is `(limb * multiplier + carry) / 2 ^ 64`
  (`stkMulCarry_toNat`), it stays below `2 ^ 64` (`stkMulCarry_lt`), and the word
  written is the model's `% 2 ^ 64` (`stkMulWord_toNat`).

`stkMulFold_cons` then reads one iteration of four limbs as four of these steps, so
the loop's invariant can state its memory as the model's written prefix.
-/
import LeanLLVM.Refinement.JsonStage2NumFastCalleeMulStep

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval

/-! ### The widened sum does not wrap -/

/-- `2 ^ 64 * 2 ^ 64` is `2 ^ 128`. -/
theorem two_pow_sixtyfour_sq : 2 ^ 64 * 2 ^ 64 = 2 ^ 128 := by decide

/-- A 64-bit limb times a multiplier below `2 ^ 64` is below `2 ^ 128`. -/
theorem stkMulProd_lt (x : BitVec 64) (mw : BitVec 128) (hmw : mw.toNat < 2 ^ 64) :
    x.toNat * mw.toNat < 2 ^ 128 := by
  have hx : x.toNat ≤ 2 ^ 64 - 1 := by have := x.isLt; omega
  have hm : mw.toNat ≤ 2 ^ 64 - 1 := by omega
  have hsq : (2 ^ 64 - 1) * (2 ^ 64 - 1) < 2 ^ 128 := by decide
  exact lt_of_le_of_lt (Nat.mul_le_mul hx hm) hsq

/-- The widened product plus a 64-bit carry is below `2 ^ 128`. -/
theorem stkMulSum_lt (x : BitVec 64) (mw cv : BitVec 128)
    (hmw : mw.toNat < 2 ^ 64) (hcv : cv.toNat < 2 ^ 64) :
    x.toNat * mw.toNat + cv.toNat < 2 ^ 128 := by
  have hx : x.toNat ≤ 2 ^ 64 - 1 := by have := x.isLt; omega
  have hm : mw.toNat ≤ 2 ^ 64 - 1 := by omega
  have hprod : x.toNat * mw.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul hx hm
  have hbig : (2 ^ 64 - 1) * (2 ^ 64 - 1) + (2 ^ 64 - 1) < 2 ^ 128 := by decide
  omega

/-- The emitted `i128` sum read at `Nat`: no wrap, so `toNat` distributes. -/
theorem stkMulWide_toNat (x : BitVec 64) (mw cv : BitVec 128)
    (hmw : mw.toNat < 2 ^ 64) (hcv : cv.toNat < 2 ^ 64) :
    (BitVec.ofNat 128 x.toNat * mw + cv).toNat = x.toNat * mw.toNat + cv.toNat := by
  have hx : x.toNat < 2 ^ 128 := by have := x.isLt; omega
  have hprod := stkMulProd_lt x mw hmw
  have hsum := stkMulSum_lt x mw cv hmw hcv
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hprod, Nat.mod_eq_of_lt hsum]

/-! ### The truncation and the shift -/

/-- The emitted `i64` word read at `Nat` is the `Nat` remainder. -/
theorem stkMulConv_toNat (t : BitVec 128) :
    (BitVec.ofNat 64 (t.toNat % 2 ^ 64)).toNat = t.toNat % 2 ^ 64 := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod]

/-- The emitted `>>> 64` read at `Nat` is the `Nat` division. -/
theorem stkMulShr_toNat (t : BitVec 128) : (t >>> 64).toNat = t.toNat / 2 ^ 64 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- One limb step's carry out, at `Nat`. -/
theorem stkMulCarry_toNat (x : BitVec 64) (mw cv : BitVec 128)
    (hmw : mw.toNat < 2 ^ 64) (hcv : cv.toNat < 2 ^ 64) :
    (stkMulCarry x mw cv).toNat = (x.toNat * mw.toNat + cv.toNat) / 2 ^ 64 := by
  rw [stkMulCarry, stkMulShr_toNat, stkMulWide_toNat x mw cv hmw hcv]

/-- The carry out stays below `2 ^ 64`. -/
theorem stkMulCarry_lt (x : BitVec 64) (mw cv : BitVec 128)
    (hmw : mw.toNat < 2 ^ 64) (hcv : cv.toNat < 2 ^ 64) :
    (stkMulCarry x mw cv).toNat < 2 ^ 64 := by
  rw [stkMulCarry_toNat x mw cv hmw hcv, Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 64),
    two_pow_sixtyfour_sq]
  exact stkMulSum_lt x mw cv hmw hcv

/-- The word the limb step writes, at `Nat`: the model's `% 2 ^ 64`. -/
theorem stkMulWord_toNat (x : BitVec 64) (mw cv : BitVec 128)
    (hmw : mw.toNat < 2 ^ 64) (hcv : cv.toNat < 2 ^ 64) :
    (BitVec.ofNat 64 ((BitVec.ofNat 128 x.toNat * mw + cv).toNat % 2 ^ 64)).toNat =
      (x.toNat * mw.toNat + cv.toNat) % 2 ^ 64 := by
  rw [stkMulConv_toNat, stkMulWide_toNat x mw cv hmw hcv]


/-- The word the emitted store puts at the limb's address is the model's, so a
written limb prefix is the model's fold. -/
theorem stkMulStateWrite_eq (s : State) (a : Nat) (iv : BitVec 64) (cv mw : BitVec 128)
    (x : BitVec 64) (hmw : mw.toNat < 2 ^ 64) (hcv : cv.toNat < 2 ^ 64) :
    natToBytes (BitVec.ofNat 64
        ((BitVec.ofNat 128 x.toNat * mw + cv).toNat % 2 ^ 64)).toNat 8 =
      natToBytes ((x.toNat * mw.toNat + cv.toNat) % 2 ^ 64) 8 := by
  rw [stkMulWord_toNat x mw cv hmw hcv]

end LeanLLVM.Refinement
