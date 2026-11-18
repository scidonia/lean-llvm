/-
Tier 3's emitted ladder: its rows, and the fold's repetition at them.

`JsonStage2NumFastTier3Fold` states the starting approximation at **one** scaling
row per direction: `t3Approx` is the widened head times one table row, and
`t3Fold_two_step` charges the widen and that row.  The emitted loops apply more
than one row — `while.body206.i.i` multiplies by `NUMF_EL1_POW10[%124]` with
`%124 = min(%e10.0.i.i, 22)` and subtracts it from the residual exponent, and
`while.body232.i.i` divides by the same row on the negative side, each loop
iterating until the exponent is spent.  This module states that repetition: the
row list, its exact composition, its length, one rounding per row, and the fold's
bracket at the ladder's own step count.

**The rows.**  `t3Rows e` is `min e 22`, then the rest, until `e` is spent — the
positive side's sequence, and the same rows in the same order on the negative
side.  `t3Rows_sum` is that the rows spend the exponent, `t3Rows_pos` and
`t3Rows_le` that each is a row the table holds, and `t3Rows_prod` that their exact
product is `10 ^ e`: the ladder's repetition is the model's single scaling row,
exactly, with no residue.  `t3Rows_length` bounds the count by the exponent's
decades and `t3Rows_length_le` reads it at the emitted range: `e10 = f - (topn -
1)` with `-324 ≤ f ≤ 308` and `1 ≤ topn ≤ 19` gives `|e10| ≤ 342`, so at most
sixteen rows.

**One rounding per row.**  `t3RowHolds c r` says the table's row at `c` is the code
`r` with `r.ticks = 10 ^ c * 2 ^ 1074` — the table's doubles are exact powers of
ten (`NumFastTables`, and `5 ^ 22 < 2 ^ 53`).  `t3Row_mul_step` and
`t3Row_div_step` are `t3Approx_mul_step`/`t3Approx_div_step` at such a row: each
row is one `roundMag` of the exact scaled product, within one lattice step, so the
ladder adds one rounding per row and nothing else.

**The bracket at the rows.**  `t3Ladder_two_step` is the fold's arithmetic at a
total slack: a value and a boundary within `u` of the emitted double, with the
double at least three slacks above zero, satisfy `V ≤ 2 * B`.
`t3Ladder_steps` is the same at the ladder's own count (`n * u`), and
`t3Ladder_scale` is `t3_scale_of_ulp` at `n * u` rather than one row's step.

**What is not composed.**  The rows' steps are *not* charged at the final row's
scale: the accumulated error obeys `E_{k+1} ≤ 10 ^ c * E_k + 2 ^ 1074 * step_k`,
so a bound in the final row's step needs the monotonicity of `t3RoundStep` in the
running product along the rows.  That induction is arithmetic over `roundMag`'s own
step, and it is not taken here.  Neither is the loop's own `runFuel` simulation:
`while.cond203.i.i` and `while.cond229.i.i` — the two tests the ladder branches on
— have no `findBlock` pin in this tree, so the repetition is stated at its rows
(`t3Approx`'s operations) rather than at those blocks' steps.
-/
import LeanLLVM.Refinement.JsonStage2NumFastTier3Fold

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.NumFastTier1
open LeanLLVM.Refinement.NumFastTier3
open LeanLLVM.Refinement.NumFastTier3Fold
open LeanLLVM.StrtodTier3

namespace NumFastTier3Ladder

/-- The table's stride: `while.body206.i.i`'s `%124 = min(%e10.0.i.i, 22)`, and
`while.body232.i.i`'s `%idxprom242` the same on the negative side. -/
def t3Stride : Nat := 22

theorem t3Stride_eq : t3Stride = 22 := rfl

/-- The exponents the emitted ladder applies, in order: `min e 22` at a time until
the exponent is spent.  The positive side applies `NUMF_EL1_POW10[%124]` under
`fmul`; the negative side applies it under `fdiv`, the same rows in the same
order. -/
def t3Rows : Nat → List Nat
  | 0 => []
  | e + 1 => if e + 1 ≤ t3Stride then [e + 1]
      else t3Stride :: t3Rows (e + 1 - t3Stride)
termination_by e => e
decreasing_by
  simp only [t3Stride] at *
  omega

/-- **The rows spend the exponent.**  The emitted ladder's rows sum to the residual
exponent the fold starts from. -/
theorem t3Rows_sum (e : Nat) : (t3Rows e).sum = e := by
  induction e using t3Rows.induct with
  | case1 => rw [t3Rows]; rfl
  | case2 e h =>
      rw [t3Rows]
      rw [ite_eq_left h]
      simp
  | case3 e h ih =>
      rw [t3Rows]
      rw [ite_eq_right h]
      simp only [List.sum_cons]
      rw [ih]
      simp only [t3Stride] at h ⊢
      omega

theorem t3Rows_pos {e c : Nat} (h : c ∈ t3Rows e) : 0 < c := by
  induction e using t3Rows.induct with
  | case1 => rw [t3Rows] at h; simp at h
  | case2 e hc =>
      rw [t3Rows] at h
      rw [ite_eq_left hc] at h
      simp only [List.mem_singleton] at h
      subst h
      omega
  | case3 e hc ih =>
      rw [t3Rows] at h
      rw [ite_eq_right hc] at h
      rcases List.mem_cons.mp h with rfl | h'
      · simp only [t3Stride]; omega
      · exact ih h'

theorem t3Rows_le {e c : Nat} (h : c ∈ t3Rows e) : c ≤ 22 := by
  induction e using t3Rows.induct with
  | case1 => rw [t3Rows] at h; simp at h
  | case2 e hc =>
      rw [t3Rows] at h
      rw [ite_eq_left hc] at h
      simp only [List.mem_singleton] at h
      subst h
      simp only [t3Stride] at hc
      omega
  | case3 e hc ih =>
      rw [t3Rows] at h
      rw [ite_eq_right hc] at h
      rcases List.mem_cons.mp h with rfl | h'
      · simp only [t3Stride]; omega
      · exact ih h'

/-- **The rows' product is the model's one row.**  Applying the emitted rows one
at a time multiplies by `10 ^ c` each, so the exact product is `10 ^ e`: the
ladder's repetition is the model's single scaling row, exactly. -/
theorem t3Rows_prod (e : Nat) :
    (t3Rows e).foldr (fun c acc => 10 ^ c * acc) 1 = 10 ^ e := by
  induction e using t3Rows.induct with
  | case1 => rw [t3Rows]; rfl
  | case2 e h =>
      rw [t3Rows]
      rw [ite_eq_left h]
      simp only [List.foldr_cons, List.foldr_nil, Nat.mul_one]
  | case3 e h ih =>
      rw [t3Rows]
      rw [ite_eq_right h]
      simp only [List.foldr_cons]
      rw [ih, ← Nat.pow_add]
      congr 1
      simp only [t3Stride] at h ⊢
      omega

/-- The row count is bounded by the exponent: `n` rows carry at most `22 * n` of
exponent, so they need at least one unit each. -/
theorem t3Rows_length (e : Nat) : (t3Rows e).length * 22 ≤ e + 21 := by
  induction e using t3Rows.induct with
  | case1 => rw [t3Rows]; decide
  | case2 e h =>
      rw [t3Rows]
      rw [ite_eq_left h]
      simp only [List.length_singleton, t3Stride] at h ⊢
      omega
  | case3 e h ih =>
      rw [t3Rows]
      rw [ite_eq_right h]
      simp only [List.length_cons]
      simp only [t3Stride] at h ih ⊢
      omega

/-- **At the emitted exponent the ladder is at most sixteen rows.**  The positive
side's residual exponent is `e10 = f - (topn - 1) ≤ 308`, and the negative side's
is at least `-342` (the clamp at `f ≥ -325` and `topn ≤ 19`), so `|e10| ≤ 342`.
`length * 22 ≤ 342 + 21 = 363 < 374 = 17 * 22`, so the count is at most sixteen. -/
theorem t3Rows_length_le {e : Nat} (h : e ≤ 342) : (t3Rows e).length ≤ 16 := by
  have h1 := t3Rows_length e
  omega


/-! ### One row is one rounding

`NumFastTables` fixes the two tables' bytes, and the ladder applies one row of
`NUMF_EL1_POW10` per iteration.  A row is a power of ten: its code's ticks are
`10 ^ c` at the common denominator, so the emitted `fmul`/`fdiv` by it is one
`roundMag` of the exact scaled product.  The table's row at `c` is exact for every
`c ≤ 22` (`5 ^ 22 < 2 ^ 53`), so the rounding is the only error the row adds. -/

/-- A table row: the code the emitted table holds, and its exponent. -/
def t3RowHolds (c : Nat) (r : Code) : Prop :=
  r.IsMag ∧ r.ticks = 10 ^ c * 2 ^ 1074

/-- **The row's product is the exact scaling.**  The row's ticks are `10 ^ c`, so
the product the rounding sees is the carried word scaled by the row, at the common
denominator. -/
theorem t3Row_product {x : Nat} {c : Nat} {r : Code} (hr : t3RowHolds c r) :
    x * r.ticks = x * 10 ^ c * 2 ^ 1074 := by
  rw [hr.2, Nat.mul_assoc]

/-- **The multiply's row is one rounding.** -/
theorem t3Row_mul_step {c₁ : Code} {c : Nat} {r : Code}
    (h₁ : c₁.IsMag) (hr : t3RowHolds c r)
    (hno : ¬ overflowTicks * 2 ^ 1074 ≤ c₁.ticks * r.ticks)
    {k : Code} (hk : roundMag (c₁.ticks * r.ticks) (2 ^ 1074) = .fin k) :
    F64.magTicks (F64.ofBits
        (t3Approx (packMag (.fin c₁) false) (packMag (.fin r) false) false)) = k.ticks ∧
      distNum (c₁.ticks * r.ticks) (2 ^ 1074) k.ticks
        ≤ 2 ^ 1074 * t3RoundStep (c₁.ticks * r.ticks) (2 ^ 1074) :=
  t3Approx_mul_step h₁ hr.1 hno hk

/-- **The divide's row is one rounding.** -/
theorem t3Row_div_step {c₁ : Code} {c : Nat} {r : Code}
    (h₁ : c₁.IsMag) (hr : t3RowHolds c r) (hpos : 0 < r.ticks)
    (hno : ¬ overflowTicks * r.ticks ≤ c₁.ticks * 2 ^ 1074)
    {k : Code} (hk : roundMag (c₁.ticks * 2 ^ 1074) r.ticks = .fin k) :
    F64.magTicks (F64.ofBits
        (t3Approx (packMag (.fin c₁) false) (packMag (.fin r) false) true)) = k.ticks ∧
      distNum (c₁.ticks * 2 ^ 1074) r.ticks k.ticks
        ≤ r.ticks * t3RoundStep (c₁.ticks * 2 ^ 1074) r.ticks :=
  t3Approx_div_step h₁ hr.1 hpos hno hk

/-! ### The bracket at the ladder's rows

`t3Fold_two_step` charges the widen and one scaling: two operations, each within
one step of the exact value.  A ladder of `n` rows charges `n` steps the same way,
because each row is one rounding (`t3Row_mul_step`/`t3Row_div_step`), so the
bracket's constant is `2 * (n + 1)` steps rather than six. -/

/-- **The bracket at a total slack.**  A value and a boundary within a slack `u`
of the emitted double, with the double at least three slacks above zero, put the
boundary at or above half the value: `V ≤ 2 * B`.  (`t3Fold_two_step` is the case
`u = 2 * u₀`, the widen's and the scaling's steps.) -/
theorem t3Ladder_two_step {V w B sV sB u : Nat}
    (hV : V ≤ w + sV) (hB : w ≤ B + sB) (hsV : sV ≤ u) (hsB : sB ≤ u)
    (hw : 3 * u ≤ w) : V ≤ 2 * B := by
  omega

/-- **The bracket at the ladder's rows.**  The slack is the ladder's own row count
times a per-row step: `n` rows cost `n * u`, and the arithmetic is the same
bracket. -/
theorem t3Ladder_steps {V w B sV sB u n : Nat}
    (hV : V ≤ w + sV) (hB : w ≤ B + sB) (hsV : sV ≤ n * u) (hsB : sB ≤ n * u)
    (hw : 3 * (n * u) ≤ w) : V ≤ 2 * B :=
  t3Ladder_two_step hV hB hsV hsB hw

/-- **The ladder's scale hypothesis.**  The same at the cleared coordinates the
fold's hypotheses use, with one per-row step `u` charged `n` times on each side
(`2 * ((n * u) * (tenDen E * twoDen eB))`); `t3_scale_of_ulp` then reads the
bracket as `shift_of_near`'s premise. -/
theorem t3Ladder_scale {m : Nat} {E : Int} {J : Nat} {eB : Int} {w u n : Nat}
    (hm : 0 < m) (hJ : J < 2 ^ 54) (heB : -1075 ≤ eB) (hlead : leadM m E ≤ 308)
    (hV : valNum m E * twoDen eB
      ≤ w * (tenDen E * twoDen eB) + 2 * ((n * u) * (tenDen E * twoDen eB)))
    (hB : w * (tenDen E * twoDen eB)
      ≤ boundNum J eB * tenDen E + 2 * ((n * u) * (tenDen E * twoDen eB)))
    (hw : 6 * ((n * u) * (tenDen E * twoDen eB))
      ≤ w * (tenDen E * twoDen eB)) :
    leadM m E - 767 ≤ eB :=
  t3_scale_of_ulp hm hJ heB hlead hV hB hw

/-! ### What the repetition still owes

The rows are enumerated and their exact product is the model's single row
(`t3Rows_prod`), each row is one rounding of the tree's own `roundMag`
(`t3Row_mul_step`/`t3Row_div_step`), the count is at most sixteen at the emitted
exponent (`t3Rows_length_le`), and the bracket composes over that many steps
(`t3Ladder_two_step`, `t3Ladder_scale`).  What is not composed is the charging of
each row's step **at the final row's scale**: the accumulated error is a weighted
sum, `E_{k+1} ≤ 10 ^ c * E_k + 2 ^ 1074 * step_k`, so a bound in the final row's
step needs the monotonicity of `t3RoundStep` in the running product along the
rows.  That induction is the piece named here; it is arithmetic over `roundMag`'s
own step, not a platform property.  The loop's own `runFuel` simulation is the
second piece: `while.cond203.i.i` and `while.cond229.i.i`, the two tests the
ladder branches on, have no `findBlock` pin in this tree — the tier-3 region's
blocks are pinned from `for.body.i.i566.i.i.epil` onward — so the ladder is stated
at its arithmetic (`t3Approx` and its rows), not at those blocks' steps. -/

/-! ### Axiom footprints -/

#print axioms t3Rows_sum
#print axioms t3Rows_pos
#print axioms t3Rows_le
#print axioms t3Rows_prod
#print axioms t3Rows_length
#print axioms t3Rows_length_le
#print axioms t3Row_product
#print axioms t3Row_mul_step
#print axioms t3Row_div_step
#print axioms t3Ladder_two_step
#print axioms t3Ladder_steps
#print axioms t3Ladder_scale

end NumFastTier3Ladder

end LeanLLVM.Refinement
