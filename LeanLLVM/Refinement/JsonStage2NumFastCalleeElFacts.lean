/-
The arithmetic the exponent body's run needs, in its general form.

`JsonStage2NumFastCalleeEl` pins `num_el_el1` and states, for each instruction of
the guard, the natural its name denotes.  Two bridges to the model were missing
from that module and are not about the exponent's numbers:

* **`llvm.ctlz.i64` against the bit length.**  `BitLanes.ctlz x` is the lane walk
  `leadZerosAux x 63`; the model normalises with `64 - Nat.size w`.  This module
  proves the walk counts exactly the lanes above `Nat.size`: for every `i`,
  `leadZerosAux x i` plus the bit length of `x`'s low `i + 1` lanes is `i + 1`
  (`leadZerosAux_add_size`), so on a nonzero word `ctlz x = 64 - x.toNat.size`
  (`ctlz_eq_size`).  The lane walk is read through `BitVec.testBit_toNat`, and the
  bit length through `Nat.size_le`/`Nat.lt_size` at the two residues
  (`size_mod_two_pow_succ_of_testBit`, `mod_two_pow_succ_of_testBit_false`).

* **The `i128` product's readings.**  This Lean has no `BitVec.toNat_ushr`, and
  `>>>` at a width is `Nat.shiftRight`, not a division by definition; the emitted
  body multiplies two widened `i64` words, shifts the `i128` product by 64 and
  truncates twice.  `toNat_mul_mod`, `toNat_ushiftRight_div` and
  `toNat_shiftLeft_of_mul_lt` are the three `toNat` readings that chain needs,
  each at the width the operation carries.

Nothing here names the exponent body's words; the run states them.
-/
import LeanLLVM.Refinement.BitLanes
import Mathlib.Data.Nat.Size

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM

/-! ### A lane's value as a division -/

/-- A set lane `i` of `n` is the oddness of `n / 2 ^ i`.  This is `Nat.testBit`'s
own recursive reading, which `n % 2 ^ (i + 1)` and `Nat.size` are compared at
below. -/
theorem testBit_eq_div_mod (n i : Nat) : n.testBit i = true ↔ n / 2 ^ i % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]

/-- A set lane forces the index below the bit length. -/
theorem pow_le_of_testBit {n i : Nat} (h : n.testBit i = true) : 2 ^ i ≤ n := by
  rw [← Nat.not_lt]
  intro hlt
  rw [Nat.testBit_lt_two_pow hlt] at h
  exact Bool.false_ne_true h

/-- **The bit length of the low lanes at a set lane.**  If lane `i` is set, the
residue modulo `2 ^ (i + 1)` has bit length `i + 1`: its top lane is exactly the
one the hypothesis names. -/
theorem size_mod_two_pow_succ_of_testBit {n i : Nat} (h : n.testBit i = true) :
    Nat.size (n % 2 ^ (i + 1)) = i + 1 := by
  have hdiv : n / 2 ^ i % 2 = 1 := (testBit_eq_div_mod n i).mp h
  obtain ⟨k, hk⟩ : ∃ k, n / 2 ^ i = 2 * k + 1 := by
    refine ⟨n / 2 ^ i / 2, ?_⟩
    have hdecomp := Nat.div_add_mod (n / 2 ^ i) 2
    omega
  have hdecomp' : n = 2 ^ i * (n / 2 ^ i) + n % 2 ^ i := (Nat.div_add_mod n (2 ^ i)).symm
  have hpow : 2 ^ i * (2 * k + 1) = 2 ^ (i + 1) * k + 2 ^ i := by
    rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, ← Nat.pow_succ]
  have hlt : n % 2 ^ i < 2 ^ (i + 1) := by
    have := Nat.mod_lt n (Nat.two_pow_pos i)
    rw [Nat.pow_succ]; omega
  have hlt2 : 2 ^ i + n % 2 ^ i < 2 ^ (i + 1) := by
    have := Nat.mod_lt n (Nat.two_pow_pos i)
    rw [Nat.pow_succ]; omega
  have hn : n = 2 ^ i * (2 * k + 1) + n % 2 ^ i :=
    hdecomp'.trans (congrArg (fun m => 2 ^ i * m + n % 2 ^ i) hk)
  have hres : n % 2 ^ (i + 1) = 2 ^ i + n % 2 ^ i := by
    calc n % 2 ^ (i + 1)
        = (2 ^ i * (2 * k + 1) + n % 2 ^ i) % 2 ^ (i + 1) :=
          congrArg (fun m => m % 2 ^ (i + 1)) hn
      _ = (2 ^ (i + 1) * k + 2 ^ i + n % 2 ^ i) % 2 ^ (i + 1) := by rw [hpow]
      _ = (2 ^ (i + 1) * k + (2 ^ i + n % 2 ^ i)) % 2 ^ (i + 1) := by rw [Nat.add_assoc]
      _ = (2 ^ i + n % 2 ^ i) % 2 ^ (i + 1) := by
            rw [Nat.add_comm (2 ^ (i + 1) * k), Nat.add_mul_mod_self_left]
      _ = 2 ^ i + n % 2 ^ i := Nat.mod_eq_of_lt hlt2
  refine Nat.le_antisymm ?_ ?_
  · rw [Nat.size_le, hres, Nat.pow_succ]; omega
  · rw [Nat.succ_le_iff, Nat.lt_size, hres]; omega

/-- **The bit length is unchanged at a clear lane.**  When lane `i` is clear, the
residue modulo `2 ^ (i + 2)` is the residue modulo `2 ^ (i + 1)`: the extra lane
is the clear one. -/
theorem mod_two_pow_succ_of_testBit_false {n i : Nat} (h : n.testBit i = false) :
    n % 2 ^ (i + 1) = n % 2 ^ i := by
  have hdiv : n / 2 ^ i % 2 ≠ 1 := by
    intro hc
    rw [← testBit_eq_div_mod n i] at hc
    rw [hc] at h
    exact Bool.noConfusion h
  have hdiv0 : n / 2 ^ i % 2 = 0 := by
    have := Nat.mod_lt (n / 2 ^ i) (by decide : 0 < 2)
    omega
  obtain ⟨k, hk⟩ : ∃ k, n / 2 ^ i = 2 * k := by
    refine ⟨n / 2 ^ i / 2, ?_⟩
    have hdecomp := Nat.div_add_mod (n / 2 ^ i) 2
    omega
  have hdecomp' : n = 2 ^ i * (n / 2 ^ i) + n % 2 ^ i := (Nat.div_add_mod n (2 ^ i)).symm
  have hpow : 2 ^ i * (2 * k) = 2 ^ (i + 1) * k := by
    rw [← Nat.mul_assoc, ← Nat.pow_succ]
  have hlt : n % 2 ^ i < 2 ^ (i + 1) := by
    have := Nat.mod_lt n (Nat.two_pow_pos i)
    rw [Nat.pow_succ]; omega
  have hn : n = 2 ^ i * (2 * k) + n % 2 ^ i :=
    hdecomp'.trans (congrArg (fun m => 2 ^ i * m + n % 2 ^ i) hk)
  calc n % 2 ^ (i + 1)
      = (2 ^ i * (2 * k) + n % 2 ^ i) % 2 ^ (i + 1) :=
          congrArg (fun m => m % 2 ^ (i + 1)) hn
    _ = (2 ^ (i + 1) * k + n % 2 ^ i) % 2 ^ (i + 1) := by rw [hpow]
    _ = n % 2 ^ i := by
          rw [Nat.add_comm (2 ^ (i + 1) * k), Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt hlt]

/-! ### The lane walk against the bit length -/

/-- **The lane walk counts the lanes the bit length leaves.**  From lane `i`
downwards, `leadZerosAux` counts the clear lanes above the word's highest set
lane, so it and the bit length of the low `i + 1` lanes sum to `i + 1`. -/
theorem leadZerosAux_add_size {w : Nat} (x : BitVec w) :
    ∀ i, BitLanes.leadZerosAux x i + Nat.size (x.toNat % 2 ^ (i + 1)) = i + 1
  | 0 => by
      rw [BitLanes.leadZerosAux, show (0 + 1 : Nat) = 1 from rfl,
        show (2 : Nat) ^ 1 = 2 from rfl, ← BitVec.testBit_toNat]
      by_cases hb : x.toNat.testBit 0 = true
      · have hmod : x.toNat % 2 = 1 := by
          have h0 := Nat.testBit_zero x.toNat
          rw [hb] at h0
          exact of_decide_eq_true h0.symm
        rw [if_pos hb, hmod]
        simp
      · have hbf : x.toNat.testBit 0 = false := by simpa using hb
        have hmod : x.toNat % 2 = 0 := by
          have h0 := Nat.testBit_zero x.toNat
          rw [hbf] at h0
          have hne := of_decide_eq_false h0.symm
          have hlt2 : x.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
          omega
        rw [if_neg hb, hmod]
        simp
  | i + 1 => by
      rw [BitLanes.leadZerosAux,
        show x.getLsbD (i + 1) = x.toNat.testBit (i + 1) from
          (BitVec.testBit_toNat (x := x) (i := i + 1)).symm]
      by_cases hb : x.toNat.testBit (i + 1) = true
      · have hsz := size_mod_two_pow_succ_of_testBit hb
        rw [if_pos hb, hsz]
        omega
      · have hbf : x.toNat.testBit (i + 1) = false := by simpa using hb
        have hmod := mod_two_pow_succ_of_testBit_false hbf
        rw [if_neg hb, hmod]
        have ih := leadZerosAux_add_size x i
        omega

/-- **The emitted count is `64` minus the word's bit length**, on a nonzero word:
`ctlz` walks lanes `63 … 0`, and the walk plus the bit length is `64`. -/
theorem ctlz_eq_size (x : BitVec 64) (h : x ≠ 0) :
    BitLanes.ctlz x = 64 - Nat.size x.toNat := by
  have hsum := leadZerosAux_add_size x 63
  rw [show (63 + 1 : Nat) = 64 from rfl, Nat.mod_eq_of_lt x.isLt] at hsum
  have hctlz : BitLanes.ctlz x = BitLanes.leadZerosAux x 63 := rfl
  omega

/-! ### The shifts at a width -/

/-- **A left shift is a multiplication** when the product still fits: the `toNat`
of `x <<< n` is `x.toNat * 2 ^ n` at any width the product stays inside. -/
theorem toNat_shiftLeft_of_mul_lt {w : Nat} (x : BitVec w) (n : Nat)
    (h : x.toNat * 2 ^ n < 2 ^ w) :
    (x <<< n).toNat = x.toNat * 2 ^ n := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

/-- **A logical right shift is a division by the power.**  `>>>` at a width is
`Nat.shiftRight`, which is `Nat` division, so this is `toNat_ushiftRight` and
`Nat.shiftRight_eq_div_pow` and nothing else. -/
theorem toNat_ushiftRight_div {w : Nat} (x : BitVec w) (n : Nat) :
    (x >>> n).toNat = x.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- **A product's `toNat` is the product's residue.**  The emitted `mul i128`
reduces modulo `2 ^ 128`; at two widened `i64` words the product is below that,
which is the caller's premise when it reads the high half. -/
theorem toNat_mul_mod {w : Nat} (x y : BitVec w) :
    (x * y).toNat = x.toNat * y.toNat % 2 ^ w :=
  BitVec.toNat_mul x y

/-- A truncation's `toNat`, at the width it truncates to. -/
theorem toNat_trunc {w : Nat} (x : BitVec w) (w' : Nat) :
    (BitVec.ofNat w' (x.toNat % 2 ^ w')).toNat = x.toNat % 2 ^ w' := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod]

/-- A `ofNat` of a value already inside the width is that value, as a word. -/
theorem ofNat_ofNat_of_lt {w n : Nat} (h : n < 2 ^ w) :
    (BitVec.ofNat w n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]


/-! ### The normalising shift's bound

The model's `W = w * 2 ^ (64 - size w)` is the emitted `%shl`; the two facts it
needs are that the shift is a multiplication (`toNat_shiftLeft_of_mul_lt`) and
that the product stays below `2 ^ 64`, which is `wnorm_lt`. -/

/-- `w`'s bit length is one more than its binary logarithm. -/
theorem size_eq_log2_add_one {w : Nat} (h : w ≠ 0) : Nat.size w = Nat.log2 w + 1 := by
  have hb := (Nat.log2_eq_iff h).mp rfl
  have h1 : Nat.log2 w < Nat.size w := Nat.lt_size.mpr hb.1
  have h2 : Nat.size w ≤ Nat.log2 w + 1 := Nat.size_le.mpr hb.2
  omega

/-- **The normalised word is below `2 ^ 64`** for a sixty-four-bit mantissa. -/
theorem wnorm_lt (w : Nat) (h : w < 2 ^ 64) (h0 : w ≠ 0) :
    w * 2 ^ (64 - Nat.size w) < 2 ^ 64 := by
  have hb := (Nat.log2_eq_iff h0).mp rfl
  have hs := size_eq_log2_add_one h0
  have hsle : Nat.size w ≤ 64 := Nat.size_le.mpr h
  calc w * 2 ^ (64 - Nat.size w)
      < 2 ^ (Nat.log2 w + 1) * 2 ^ (64 - Nat.size w) :=
        Nat.mul_lt_mul_of_pos_right hb.2 (Nat.two_pow_pos _)
    _ = 2 ^ (Nat.log2 w + 1 + (64 - Nat.size w)) := by rw [← Nat.pow_add]
    _ = 2 ^ 64 := by rw [hs]; congr 1; omega

end LeanLLVM.Refinement
