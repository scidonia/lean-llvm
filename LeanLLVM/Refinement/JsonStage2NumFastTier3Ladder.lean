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

**The rows' steps at the final row's scale.**  The accumulated error obeys
`E_{k+1} ≤ 10 ^ c * E_k + 2 ^ 1074 * step_k`, a weighted sum rather than a count.
`t3RoundStep` is monotone in the numerator (`t3RoundStep_mono`, through
`binade_mono`) and scales by at most its factor up to two (`t3RoundStep_mul_le`),
so a row's step carried to the last row's scale is within two of the last row's
own (`t3RoundStep_weighted`).  `t3ErrStep_eq` is the recurrence's expansion,
`t3ErrWeight_le` folds it at the row count, and `t3Ladder_charge` reads the three
together: with every numerator normal, no row overflowing, and the running
product dominated by the last, the carried error is at most the initial error at
`10 ^ e` plus `2 * n` final steps (`t3Ladder_charge_sixteen` at the emitted
count).  The subnormal region is where the scaling fails, and it is named rather
than assumed away: there the step is one tick regardless of magnitude, so its
relative size is not the final row's.

**The loops at their pins.**  `while.cond203.i.i` and `while.cond229.i.i` do have
`findBlock` pins in this tree (`JsonStage2HelperIRNumFast`), as do their row
blocks `while.body206.i.i` and `while.body232.i.i`; the earlier note that the
region is pinned only from `for.body.i.i566.i.i.epil` onward was wrong about these
four.  The loops are therefore stated at those blocks: `t3MulLoopOf`/`t3DivLoopOf`
fix each loop's head, exit, bound, cost, invariant and exit test there, and both
of each head's edges — the ladder's start and the back edge — are proved
(`t3_mulHead_step_one`/`_zero` with `_entry`, `t3_divHead_step_one`/`_zero` with
`_entry`).  What the shapes still take as an arm is the negative row block's
per-edge step — one row's `fdiv` at the table's row, the `%cmp246` zero test, and
the `ult`/`mul`/`ashr` index that recovers `min (-e) 22` — while the positive
block's step, with its `%cmp221` overflow test, and the invariant's arithmetic
(`t3Rows`'s first row is `min` of its sum, its sum splits at that row, and
`take`/`drop` at the counter) are `JsonStage2NumFastTier3Rows`', which also
instantiates `t3MulLoopOf` at the emitted rows.

**The join.**  The two loops are not entered from one another directly: the
positive loop's refused test and its row block's overflow test both leave for
`while.cond229.i.i.preheader`, whose two `phi`s carry the residual and the
double's bits into the negative head's cells.  That block is pinned and stepped
here (`t3_join_pin`, `t3_join_denote_from_head`/`_from_body`,
`t3_join_step_from_head`/`_from_body`, `t3_join_run_from_head`/`_from_body`), so
the sign case is the negative head's own test once the join is crossed
(`t3_ladder_join_spent` is the head's refused edge and the join as one `runFuel`
prefix).  What remains at the invariant level is which loop's invariant holds
where the two runs are appended — the ladder's `t3MulLoopOf`/`t3DivLoopOf` runs
know their own exits, not each other's.
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

/-! ### The step at the final row's scale

The accumulated error is the weighted sum the recurrence expands to, not a
count: `E_n = 10 ^ e * E_0 + Σ_k 10 ^ (rows after k) * 2 ^ 1074 * step_k`.  A
bound in one row's step is therefore a statement about `t3RoundStep` along the
running product, and it has two halves.  The first is monotonicity in the
numerator: a larger exact value sits in no lower a binade, so its lattice step is
no smaller (`t3RoundStep_mono`, through `binade_mono`).  The second is scaling:
multiplying the numerator by `m` grows the step by at most `m`, up to a factor of
two, because the binade rises by `log2 m` at least (`t3RoundStep_mul_le`).  With
the running products nondecreasing and dominated by the last, those two facts
give `10 ^ (rows after k) * step_k ≤ 2 * step_n`; the folded recurrence is then at
most `2 * n` final steps (`t3Ladder_charge`).  Everything here is arithmetic over
`roundMag`'s own step, not a platform property.

The one magnitude condition the folding names, rather than assumes away, is that
each row's numerator is normal (`d * 2 ^ 52 ≤ P`): in the subnormal region the
step is one tick regardless of magnitude, so a scaling there is not bounded by
`m` and the charge is not `2` (the per-rounding bound of `roundMag_dist_le_step`
is still exact, but its relative size is not).  The ladder's emitted range keeps
the numerators normal wherever `t3_scale_of_ulp`'s `6 * u ≤ w` premise is met. -/

/-- **The binade grows with the numerator.**  A larger exact value `P / d` is in
no lower a binade: `binade_spec`'s minimality makes the smaller value's binade
exceed the larger one's only by crossing the larger one's own upper bound. -/
theorem binade_mono {P P' d : Nat} (hd : 0 < d) (hle : P ≤ P')
    (hno : ¬ overflowTicks * d ≤ P') :
    binade P d ≤ binade P' d := by
  have hbounded : ∀ Q : Nat, Q ≤ P' → ∃ B, B < 2100 ∧ Q < d * 2 ^ (B + 1) := by
    intro Q hQ
    refine ⟨2097, by decide, ?_⟩
    have h1 : P' < overflowTicks * d := Nat.lt_of_not_le hno
    have h2 : overflowTicks ≤ 2 ^ 2098 := by
      simp only [overflowTicks]; exact Nat.sub_le _ _
    have h3 : overflowTicks * d ≤ 2 ^ 2098 * d := Nat.mul_le_mul_right d h2
    have h4 : 2 ^ 2098 * d = d * 2 ^ (2097 + 1) := by
      rw [show 2097 + 1 = 2098 from by decide, Nat.mul_comm]
    rw [h4] at h3
    omega
  obtain ⟨-, hPmin⟩ := binade_spec (P := P) (d := d) (hbounded P hle)
  obtain ⟨hP'up, -⟩ := binade_spec (P := P') (d := d) (hbounded P' (Nat.le_refl P'))
  by_contra hcon
  have hlt : binade P' d < binade P d := Nat.lt_of_not_le hcon
  have hlow := hPmin (binade P' d) hlt
  have hup : d * 2 ^ (binade P' d + 1) ≤ P' := Nat.le_trans hlow hle
  omega

/-- **The lattice step grows with the numerator.**  Below the normal threshold
the step is one tick; above it the binade's ulp is at least one tick and rises
with the binade (`binade_mono`). -/
theorem t3RoundStep_mono {P P' d : Nat} (hd : 0 < d) (hle : P ≤ P')
    (hno : ¬ overflowTicks * d ≤ P') :
    t3RoundStep P d ≤ t3RoundStep P' d := by
  unfold t3RoundStep
  by_cases hP : P < d * 2 ^ 52
  · rw [ite_eq_left hP]
    by_cases hP' : P' < d * 2 ^ 52
    · rw [ite_eq_left hP']
    · rw [ite_eq_right hP']
      have hB : 52 ≤ binade P' d := (binade_facts hd hno hP').1
      have h1 : (1 : Nat) ≤ ulp P' d := by
        unfold ulp
        calc (1 : Nat) = 2 ^ 0 := (Nat.pow_zero 2).symm
          _ ≤ 2 ^ (binade P' d - 52) :=
              Nat.pow_le_pow_right (by decide) (by omega)
      omega
  · rw [ite_eq_right hP]
    have hsub' : ¬ P' < d * 2 ^ 52 := by omega
    rw [ite_eq_right hsub']
    have hmono := binade_mono hd hle hno
    unfold ulp
    exact Nat.pow_le_pow_right (by decide) (by omega)

/-- **Scaling the numerator scales the step by at most the factor.**  With the
numerator normal, `m * step P ≤ 2 * step (m * P)`: the binade of `m * P` is at
least `log2 m` above `P`'s, so `2 ^ (Bm - B + 1) ≥ m` and the extra factor of two
is the binade's own slack. -/
theorem t3RoundStep_mul_le {P d m : Nat} (hd : 0 < d) (hm : 0 < m)
    (hP : d * 2 ^ 52 ≤ P) (hno : ¬ overflowTicks * d ≤ m * P) :
    m * t3RoundStep P d ≤ 2 * t3RoundStep (m * P) d := by
  have hPle : P ≤ m * P := Nat.le_mul_of_pos_left (m := P) hm
  have hnoP : ¬ overflowTicks * d ≤ P := fun h => hno (Nat.le_trans h hPle)
  have hsubP : ¬ P < d * 2 ^ 52 := Nat.not_lt.mpr hP
  have hsubmP : ¬ m * P < d * 2 ^ 52 := by omega
  obtain ⟨hB52, -, hPlow, -⟩ := binade_facts hd hnoP hsubP
  obtain ⟨hBm52, -, -, hmPup⟩ := binade_facts hd hno hsubmP
  have hBle : binade P d ≤ binade (m * P) d := binade_mono hd hPle hno
  have hstepP : t3RoundStep P d = 2 ^ (binade P d - 52) := by
    unfold t3RoundStep ulp; rw [ite_eq_right hsubP]
  have hstepmP : t3RoundStep (m * P) d = 2 ^ (binade (m * P) d - 52) := by
    unfold t3RoundStep ulp; rw [ite_eq_right hsubmP]
  rw [hstepP, hstepmP]
  have hpow : 2 ^ binade P d ≤ P :=
    Nat.le_trans (Nat.le_mul_of_pos_left (m := 2 ^ binade P d) hd) hPlow
  have hmul : m * 2 ^ binade P d < 2 ^ (binade (m * P) d + 1) := by
    have h1 : d * (m * 2 ^ binade P d) ≤ m * P := by
      calc d * (m * 2 ^ binade P d) = m * (d * 2 ^ binade P d) := by ac_rfl
        _ ≤ m * P := Nat.mul_le_mul_left m hPlow
    by_contra hle
    have h2 : d * 2 ^ (binade (m * P) d + 1) ≤ d * (m * 2 ^ binade P d) :=
      Nat.mul_le_mul_left d (Nat.le_of_not_lt hle)
    omega
  have hBeq : binade (m * P) d - binade P d + 1 + binade P d
      = binade (m * P) d + 1 := by omega
  have hmle : m ≤ 2 ^ (binade (m * P) d - binade P d + 1) := by
    apply Nat.le_of_lt
    apply lt_of_mul_lt_mul_right (c := 2 ^ binade P d)
    rw [← Nat.pow_add, hBeq]
    exact hmul
  have hBeq2 : binade (m * P) d - binade P d + 1 + (binade P d - 52)
      = binade (m * P) d - 51 := by omega
  calc m * 2 ^ (binade P d - 52)
      ≤ 2 ^ (binade (m * P) d - binade P d + 1) * 2 ^ (binade P d - 52) :=
        Nat.mul_le_mul_right _ hmle
    _ = 2 ^ (binade (m * P) d - 51) := by rw [← Nat.pow_add, hBeq2]
    _ = 2 * 2 ^ (binade (m * P) d - 52) := by
        rw [show binade (m * P) d - 51 = (binade (m * P) d - 52) + 1 by omega,
          Nat.pow_succ, Nat.mul_comm]

/-- **A row's step carried to the final scale.**  The rows after a row multiply
its rounding's step to the last row's numerator; monotonicity and scaling put
that carried step within two of the last row's own. -/
theorem t3RoundStep_weighted {P Pn d m : Nat} (hd : 0 < d) (hm : 0 < m)
    (hP : d * 2 ^ 52 ≤ P) (hno : ¬ overflowTicks * d ≤ m * P)
    (hscale : m * P ≤ Pn) (hnoPn : ¬ overflowTicks * d ≤ Pn) :
    m * t3RoundStep P d ≤ 2 * t3RoundStep Pn d :=
  Nat.le_trans (t3RoundStep_mul_le hd hm hP hno)
    (Nat.mul_le_mul_left 2 (t3RoundStep_mono hd hscale hnoPn))

/-! ### Folding the recurrence

`t3ErrStep` is the recurrence over a row list — one row's exponent applied to
the carried error, then its step added — and `t3ErrWeight` is the weighted sum it
expands to.  `t3ErrStep_eq` is that expansion, `t3ErrWeight_le` bounds the sum by
the row count when every row's carried step is within `2 * U`, and
`t3Ladder_charge` reads the two together with `t3RoundStep_weighted` so that `U`
is the final row's own step. -/

/-- The carried error after a row list, in the numerator's units:
`E_{k+1} = 10 ^ c * E_k + s_k`, one row at a time. -/
def t3ErrStep : List (Nat × Nat) → Nat → Nat
  | [], E => E
  | p :: rest, E => t3ErrStep rest (10 ^ p.1 * E + p.2)

/-- A row's step carried to the final scale: the product of the rows after it
multiplies its rounding's step. -/
def t3ErrWeight : List (Nat × Nat) → Nat
  | [] => 0
  | p :: rest => p.2 * 10 ^ (rest.map Prod.fst).sum + t3ErrWeight rest

theorem t3ErrStep_eq (rows : List (Nat × Nat)) (E : Nat) :
    t3ErrStep rows E = 10 ^ (rows.map Prod.fst).sum * E + t3ErrWeight rows := by
  induction rows generalizing E with
  | nil => simp [t3ErrStep, t3ErrWeight]
  | cons p rest ih =>
      rw [t3ErrStep, ih, t3ErrWeight]
      simp only [List.map_cons, List.sum_cons]
      rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add,
        show (rest.map Prod.fst).sum + p.1 = p.1 + (rest.map Prod.fst).sum
          from Nat.add_comm _ _,
        Nat.mul_comm (10 ^ (rest.map Prod.fst).sum) p.2]
      omega

/-- **The weighted sum at the row count.**  If every row's step, carried to the
final scale, is within `2 * U`, the whole sum is at most two steps per row. -/
theorem t3ErrWeight_le {rows : List (Nat × Nat)} {U : Nat}
    (h : ∀ (pre : List (Nat × Nat)) (p : Nat × Nat) (suf : List (Nat × Nat)),
      rows = pre ++ p :: suf → p.2 * 10 ^ (suf.map Prod.fst).sum ≤ 2 * U) :
    t3ErrWeight rows ≤ 2 * rows.length * U := by
  induction rows with
  | nil => simp [t3ErrWeight]
  | cons p rest ih =>
      have hhead : p.2 * 10 ^ (rest.map Prod.fst).sum ≤ 2 * U := h [] p rest rfl
      have hrest : ∀ (pre : List (Nat × Nat)) (q : Nat × Nat) (suf : List (Nat × Nat)),
          rest = pre ++ q :: suf → q.2 * 10 ^ (suf.map Prod.fst).sum ≤ 2 * U := by
        intro pre q suf heq
        exact h (p :: pre) q suf (by rw [heq]; rfl)
      have hih := ih hrest
      have he : 2 * (rest.length + 1) * U = 2 * rest.length * U + 2 * U := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_mul]
      rw [t3ErrWeight, List.length_cons, he]
      omega

/-- **The folded recurrence at a per-row slack.**  The carried error is the
initial error at the rows' exact product plus at most two of the slack per row. -/
theorem t3ErrStep_le {rows : List (Nat × Nat)} {E U : Nat}
    (h : ∀ (pre : List (Nat × Nat)) (p : Nat × Nat) (suf : List (Nat × Nat)),
      rows = pre ++ p :: suf → p.2 * 10 ^ (suf.map Prod.fst).sum ≤ 2 * U) :
    t3ErrStep rows E ≤ 10 ^ (rows.map Prod.fst).sum * E + 2 * rows.length * U := by
  rw [t3ErrStep_eq]
  have := t3ErrWeight_le h
  omega

/-- A decomposition of a mapped list pulls back to one of the source: the
prefix, the element and the suffix that map to the pieces of the target.  This is
what lets a per-position statement about the mapped rows use the statement about
the rows themselves. -/
theorem map_eq_append_cons {α β : Type} (g : α → β) :
    ∀ {l : List α} {pre : List β} {b : β} {suf : List β},
      l.map g = pre ++ b :: suf →
      ∃ (pre' : List α) (p : α) (suf' : List α),
        l = pre' ++ p :: suf' ∧ pre'.map g = pre ∧ g p = b ∧ suf'.map g = suf := by
  intro l
  induction l with
  | nil => intro pre b suf h; simp at h
  | cons a rest ih =>
      intro pre b suf h
      cases pre with
      | nil =>
          simp only [List.map_cons, List.nil_append, List.cons.injEq] at h
          exact ⟨[], a, rest, rfl, rfl, h.1, h.2⟩
      | cons q pre' =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
          obtain ⟨hq, hrest⟩ := h
          obtain ⟨pre'', p, suf', hl, hpre, hgp, hsuf⟩ := ih hrest
          exact ⟨a :: pre'', p, suf', by rw [hl]; rfl, by simp [hq, hpre], hgp, hsuf⟩

/-- **The ladder's charging at the final row's scale.**  `rows` pairs each row's
exponent with the numerator it rounds; with every numerator normal, no row
overflowing, and `10 ^ (rows after k) * P_k ≤ Pn` (the running product's
monotonicity, exact), each row's rounding is within two of the last row's step, so
the carried error is at most the initial error at `10 ^ e` plus `2 * n` final
steps. -/
theorem t3Ladder_charge {rows : List (Nat × Nat)} {d Pn E : Nat}
    (hd : 0 < d)
    (hnorm : ∀ (pre : List (Nat × Nat)) (p : Nat × Nat) (suf : List (Nat × Nat)),
      rows = pre ++ p :: suf → d * 2 ^ 52 ≤ p.2)
    (hno : ∀ (pre : List (Nat × Nat)) (p : Nat × Nat) (suf : List (Nat × Nat)),
      rows = pre ++ p :: suf → ¬ overflowTicks * d ≤ 10 ^ (suf.map Prod.fst).sum * p.2)
    (hscale : ∀ (pre : List (Nat × Nat)) (p : Nat × Nat) (suf : List (Nat × Nat)),
      rows = pre ++ p :: suf → 10 ^ (suf.map Prod.fst).sum * p.2 ≤ Pn)
    (hnoPn : ¬ overflowTicks * d ≤ Pn) :
    t3ErrStep (rows.map (fun p => (p.1, 2 ^ 1074 * t3RoundStep p.2 d))) E
      ≤ 10 ^ (rows.map Prod.fst).sum * E
          + 2 * rows.length * (2 ^ 1074 * t3RoundStep Pn d) := by
  have hmapfst : (rows.map (fun p => (p.1, 2 ^ 1074 * t3RoundStep p.2 d))).map Prod.fst
      = rows.map Prod.fst := by
    rw [List.map_map]; rfl
  have hmapped := t3ErrStep_le
    (rows := rows.map (fun p => (p.1, 2 ^ 1074 * t3RoundStep p.2 d)))
    (E := E) (U := 2 ^ 1074 * t3RoundStep Pn d) ?_
  · rw [hmapfst] at hmapped
    simpa only [List.length_map] using hmapped
  · intro pre p suf heq
    obtain ⟨pre', q, suf', hl, hpre, hgp, hsuf⟩ :=
      map_eq_append_cons (fun p : Nat × Nat => (p.1, 2 ^ 1074 * t3RoundStep p.2 d)) heq
    cases hgp
    have hp := hnorm pre' q suf' hl
    have hn := hno pre' q suf' hl
    have hs := hscale pre' q suf' hl
    have hsum : (suf.map Prod.fst).sum = (suf'.map Prod.fst).sum := by
      rw [← hsuf, List.map_map]; rfl
    rw [hsum]
    have hpow : 0 < 10 ^ (suf'.map Prod.fst).sum := Nat.pow_pos (by decide)
    have h1 : 10 ^ (suf'.map Prod.fst).sum * t3RoundStep q.2 d
        ≤ 2 * t3RoundStep Pn d :=
      t3RoundStep_weighted hd hpow hp hn hs hnoPn
    calc (2 ^ 1074 * t3RoundStep q.2 d) * 10 ^ (suf'.map Prod.fst).sum
        = 2 ^ 1074 * (10 ^ (suf'.map Prod.fst).sum * t3RoundStep q.2 d) := by ac_rfl
      _ ≤ 2 ^ 1074 * (2 * t3RoundStep Pn d) := Nat.mul_le_mul_left _ h1
      _ = 2 * (2 ^ 1074 * t3RoundStep Pn d) := by ac_rfl

/-- **The ladder's charge at the emitted row count.**  At most sixteen rows
(`t3Rows_length_le`) put the folded error within thirty-two final steps. -/
theorem t3Ladder_charge_sixteen {rows : List (Nat × Nat)} {d Pn E : Nat}
    (hd : 0 < d) (hlen : rows.length ≤ 16)
    (hnorm : ∀ (pre : List (Nat × Nat)) (p : Nat × Nat) (suf : List (Nat × Nat)),
      rows = pre ++ p :: suf → d * 2 ^ 52 ≤ p.2)
    (hno : ∀ (pre : List (Nat × Nat)) (p : Nat × Nat) (suf : List (Nat × Nat)),
      rows = pre ++ p :: suf → ¬ overflowTicks * d ≤ 10 ^ (suf.map Prod.fst).sum * p.2)
    (hscale : ∀ (pre : List (Nat × Nat)) (p : Nat × Nat) (suf : List (Nat × Nat)),
      rows = pre ++ p :: suf → 10 ^ (suf.map Prod.fst).sum * p.2 ≤ Pn)
    (hnoPn : ¬ overflowTicks * d ≤ Pn) :
    t3ErrStep (rows.map (fun p => (p.1, 2 ^ 1074 * t3RoundStep p.2 d))) E
      ≤ 10 ^ (rows.map Prod.fst).sum * E + 32 * (2 ^ 1074 * t3RoundStep Pn d) := by
  have h := t3Ladder_charge (E := E) hd hnorm hno hscale hnoPn
  have : 2 * rows.length * (2 ^ 1074 * t3RoundStep Pn d)
      ≤ 32 * (2 ^ 1074 * t3RoundStep Pn d) := by
    have : 2 * rows.length ≤ 32 := by omega
    exact Nat.mul_le_mul_right _ this
  omega

/-! ### The ladder's loops at their pins

The two loops' test blocks and row blocks are entries of `numFastBody`'s own
block list, and `JsonStage2HelperIRNumFast` pins all four (`decide`d `findBlock`
equations).  The ladder is therefore stated at those blocks, not at a model of
them: `t3_mulHead_pin`, `t3_divHead_pin`, `t3_mulBody_pin` and `t3_divBody_pin`
are the pins at the names this module uses, and each head's `denoteCode` and
`step` are the block's own instructions.

The invariant carries the residual exponent and the carried double row by row:
`t3MulInv e d rows` says the state is at `while.cond203.i.i`, its `%e10.0.i.i` is
the sum of the rows after the counter, and its `%d201.0.i.i` is the fold of the
rows before it.  `t3MulLoopOf`/`t3DivLoopOf` fix the loop's shape at that
invariant — head, exit, bound, cost, exit test — so the arms are the emitted
blocks' per-edge steps rather than a re-derivation of the loop. -/

/-- The positive ladder's test block. -/
def t3MulHead : String := "while.cond203.i.i"

/-- The positive ladder's row block. -/
def t3MulBody : String := "while.body206.i.i"

/-- The negative ladder's test block. -/
def t3DivHead : String := "while.cond229.i.i"

/-- The negative ladder's row block. -/
def t3DivBody : String := "while.body232.i.i"

/-- The ladder's join: the negative loop's test preheader, which the positive
loop leaves for and the negative loop is entered through. -/
def t3LadderJoin : String := "while.cond229.i.i.preheader"

theorem t3MulHead_eq : t3MulHead = "while.cond203.i.i" := rfl
theorem t3MulBody_eq : t3MulBody = "while.body206.i.i" := rfl
theorem t3DivHead_eq : t3DivHead = "while.cond229.i.i" := rfl
theorem t3DivBody_eq : t3DivBody = "while.body232.i.i" := rfl
theorem t3LadderJoin_eq : t3LadderJoin = "while.cond229.i.i.preheader" := rfl

/-- The positive loop's test block, from its pin. -/
def t3MulHeadInstrs : List Instr :=
  [Instr.phi "%e10.0.i.i" (Ty.int 64) [("if.end198.i.i", (Operand.reg "%sub200.i.i")),
                                   ("while.body206.i.i", (Operand.reg "%sub219.i.i"))],
   Instr.phi "%d201.0.i.i" Ty.double [("if.end198.i.i", (Operand.reg "%conv202.i.i")),
                                   ("while.body206.i.i", (Operand.reg "%mul217.i.i"))],
   Instr.icmp "%cmp204.i.i" (IPred.sgt) 64 (Operand.reg "%e10.0.i.i")
     (Operand.imm (Const.int 64 0x0000000000000000#64))]

theorem t3_mulHead_pin :
    numFastBody.findBlock t3MulHead =
      some ⟨t3MulHead, t3MulHeadInstrs,
        Term.condbr (Operand.reg "%cmp204.i.i") t3MulBody t3LadderJoin⟩ := by
  simpa only [t3MulHead, t3MulBody, t3LadderJoin, t3MulHeadInstrs]
    using numFast_findBlock_while_cond203_i_i

/-- The negative loop's test block, from its pin. -/
def t3DivHeadInstrs : List Instr :=
  [Instr.phi "%e10.2.i.i" (Ty.int 64) [("while.body232.i.i", (Operand.reg "%add245.i.i")),
                                   ("while.cond229.i.i.preheader", (Operand.reg "%e10.2.i.i.ph"))],
   Instr.phi "%d201.2.i.i" Ty.double [("while.body232.i.i", (Operand.reg "%div.i.i")),
                                   ("while.cond229.i.i.preheader", (Operand.reg "%d201.2.i.i.ph"))],
   Instr.icmp "%cmp230.i.i" (IPred.slt) 64 (Operand.reg "%e10.2.i.i")
     (Operand.imm (Const.int 64 0x0000000000000000#64))]

theorem t3_divHead_pin :
    numFastBody.findBlock t3DivHead =
      some ⟨t3DivHead, t3DivHeadInstrs,
        Term.condbr (Operand.reg "%cmp230.i.i") t3DivBody "while.end253.i.i"⟩ := by
  simpa only [t3DivHead, t3DivBody, t3DivHeadInstrs]
    using numFast_findBlock_while_cond229_i_i

/-- The positive loop's row block, at this module's name for it: the fold module's
pin. -/
theorem t3_mulBody_pin :
    numFastBody.findBlock t3MulBody =
      some ⟨t3MulBody,
        [Instr.icmp "%124.min" (IPred.ult) 64 (Operand.reg "%e10.0.i.i")
          (Operand.imm (Const.int 64 0x0000000000000016#64)),
         Instr.select "%124" (Ty.int 64) (Operand.reg "%124.min")
          (Operand.reg "%e10.0.i.i") (Operand.imm (Const.int 64 0x0000000000000016#64)),
         Instr.gep "%arrayidx216.i.i" Ty.double (Operand.global "@NUMF_EL1_POW10")
          (Operand.reg "%124"),
         Instr.load "%125" Ty.double (Operand.reg "%arrayidx216.i.i"),
         Instr.fmul "%mul217.i.i" (Operand.reg "%d201.0.i.i") (Operand.reg "%125"),
         Instr.binop "%sub219.i.i" (BinOp.sub) 64 (Operand.reg "%e10.0.i.i")
          (Operand.reg "%124"),
         Instr.bitcastToInt "%.cast.i.i.i" (Operand.reg "%mul217.i.i"),
         Instr.icmp "%cmp221.i.i" (IPred.ugt) 64 (Operand.reg "%.cast.i.i.i")
          (Operand.imm (Const.int 64 0x7fefffffffffffff#64))],
        Term.condbr (Operand.reg "%cmp221.i.i") t3LadderJoin t3MulHead⟩ := by
  simpa only [t3MulBody, t3MulHead, t3LadderJoin] using t3_mul_find

/-- The negative loop's row block, at this module's name for it. -/
theorem t3_divBody_pin :
    numFastBody.findBlock t3DivBody =
      some ⟨t3DivBody,
        [Instr.icmp "%cmp234.i.i" (IPred.ult) 64 (Operand.reg "%e10.2.i.i")
          (Operand.imm (Const.int 64 0xffffffffffffffea#64)),
         Instr.binop "%.neg.i.i" (BinOp.mul) 64 (Operand.reg "%e10.2.i.i")
          (Operand.imm (Const.int 64 0xffffffff00000000#64)),
         Instr.binop "%126" (BinOp.ashr) 64 (Operand.reg "%.neg.i.i")
          (Operand.imm (Const.int 64 0x0000000000000020#64)),
         Instr.select "%idxprom242.i.i" (Ty.int 64) (Operand.reg "%cmp234.i.i")
          (Operand.imm (Const.int 64 0x0000000000000016#64)) (Operand.reg "%126"),
         Instr.gep "%arrayidx243.i.i" Ty.double (Operand.global "@NUMF_EL1_POW10")
          (Operand.reg "%idxprom242.i.i"),
         Instr.load "%127" Ty.double (Operand.reg "%arrayidx243.i.i"),
         Instr.fdiv "%div.i.i" (Operand.reg "%d201.2.i.i") (Operand.reg "%127"),
         Instr.binop "%add245.i.i" (BinOp.add) 64 (Operand.reg "%idxprom242.i.i")
          (Operand.reg "%e10.2.i.i"),
         Instr.fcmp "%cmp246.i.i" (FPred.oeq) (Operand.reg "%div.i.i")
          (Operand.imm (Const.float 0x0000000000000000#64))],
        Term.condbr (Operand.reg "%cmp246.i.i") "while.end253.i.i" t3DivHead⟩ := by
  simpa only [t3DivBody, t3DivHead] using t3_div_find

/-! ### The positive loop's head, both edges

The head is the two carried `phi`s and the test `%cmp204.i.i = %e10.0.i.i >s 0`.
It is entered from `if.end198.i.i` (the ladder's start, counter zero) or from
`while.body206.i.i` (the back edge), so the `phi` selection is the predecessor's;
the block's own instructions are the same either way. -/

/-- The environment the positive loop's head leaves: the two carried cells and
the test's bit. -/
def t3MulHeadEnv (env : Env) (e d : BitVec 64) : Env :=
  ("%cmp204.i.i", .int 1 (evalICmp .sgt e 0x0000000000000000#64)) ::
  ("%d201.0.i.i", .float d) :: ("%e10.0.i.i", .int 64 e) :: env

/-- The head's `denoteCode` from the ladder's start. -/
theorem t3_mulHead_denote_entry {calls : Calls} {env : Env} {s : State}
    {e d : BitVec 64}
    (hpre : s.pre = some "if.end198.i.i")
    (he : lookupName env "%sub200.i.i" = some (.int 64 e))
    (hd : lookupName env "%conv202.i.i" = some (.float d)) :
    denoteCode calls t3MulHeadInstrs (stateAt env s) =
      some (stateAt (t3MulHeadEnv env e d) s) := by
  unfold t3MulHeadInstrs
  block_phi_run
  · rw [denoteCode_icmp_sgt_imm _ _ _ "%cmp204.i.i" "%e10.0.i.i" (by block_lk) _]
    block_close
  all_goals block_close

/-- The head's `denoteCode` from the back edge. -/
theorem t3_mulHead_denote_back {calls : Calls} {env : Env} {s : State}
    {e d : BitVec 64}
    (hpre : s.pre = some "while.body206.i.i")
    (he : lookupName env "%sub219.i.i" = some (.int 64 e))
    (hd : lookupName env "%mul217.i.i" = some (.float d)) :
    denoteCode calls t3MulHeadInstrs (stateAt env s) =
      some (stateAt (t3MulHeadEnv env e d) s) := by
  unfold t3MulHeadInstrs
  block_phi_run
  · rw [denoteCode_icmp_sgt_imm _ _ _ "%cmp204.i.i" "%e10.0.i.i" (by block_lk) _]
    block_close
  all_goals block_close

/-- The positive loop's back edge: the test holds, so the head jumps to its row
block. -/
theorem t3_mulHead_step_one {calls : Calls} {env : Env} {s : State} {e d : BitVec 64}
    (hpc : s.pc = t3MulHead)
    (hpre : s.pre = some "while.body206.i.i")
    (he : lookupName env "%sub219.i.i" = some (.int 64 e))
    (hd : lookupName env "%mul217.i.i" = some (.float d))
    (hbit : evalICmp .sgt e 0x0000000000000000#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3MulHeadEnv env e d)
        { s with pc := t3MulBody, pre := some t3MulHead }) := by
  refine numFast_step_at (s' := stateAt (t3MulHeadEnv env e d) s)
    (b := ⟨t3MulHead, t3MulHeadInstrs,
      Term.condbr (Operand.reg "%cmp204.i.i") t3MulBody t3LadderJoin⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_mulHead_pin
  · simpa only [denoteCode_nil] using t3_mulHead_denote_back hpre he hd
  · have hlk : lookupName (t3MulHeadEnv env e d) "%cmp204.i.i"
        = some (.int 1 (evalICmp .sgt e 0x0000000000000000#64)) := by
      simp only [t3MulHeadEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_one _ "%cmp204.i.i" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- The positive loop's exit: the test fails, so the head jumps to the join. -/
theorem t3_mulHead_step_zero {calls : Calls} {env : Env} {s : State} {e d : BitVec 64}
    (hpc : s.pc = t3MulHead)
    (hpre : s.pre = some "while.body206.i.i")
    (he : lookupName env "%sub219.i.i" = some (.int 64 e))
    (hd : lookupName env "%mul217.i.i" = some (.float d))
    (hbit : evalICmp .sgt e 0x0000000000000000#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3MulHeadEnv env e d)
        { s with pc := t3LadderJoin, pre := some t3MulHead }) := by
  refine numFast_step_at (s' := stateAt (t3MulHeadEnv env e d) s)
    (b := ⟨t3MulHead, t3MulHeadInstrs,
      Term.condbr (Operand.reg "%cmp204.i.i") t3MulBody t3LadderJoin⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_mulHead_pin
  · simpa only [denoteCode_nil] using t3_mulHead_denote_back hpre he hd
  · have hlk : lookupName (t3MulHeadEnv env e d) "%cmp204.i.i"
        = some (.int 1 (evalICmp .sgt e 0x0000000000000000#64)) := by
      simp only [t3MulHeadEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_zero _ "%cmp204.i.i" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- `%d = icmp slt i64 %a, <c>`. -/
theorem step_icmp_slt_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64} (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.icmp d .slt 64 (.reg a) (.imm (.int 64 c))) =
      some (stateAt ((d, .int 1 (evalICmp .slt x c)) :: env) s) := by
  have ha' : evalOperand (stateAt env s) (.reg a) = some (.int 64 x) :=
    evalOperand_reg_of env s a (.int 64 x) ha
  have h := JsonS1MasksIR.evalInstr_icmp (calls := calls) (s := stateAt env s) (d := d)
    (pred := .slt) (w := 64) (a := (.reg a)) (b := (.imm (.int 64 c)))
    ha' (evalOperand_lit_of (stateAt env s) 64 c)
  rw [h]
  simp only [evalICmpNat_toNat, stateAt, State.bind]

theorem denoteCode_icmp_slt_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64} (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.icmp d .slt 64 (.reg a) (.imm (.int 64 c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .slt x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_icmp_slt_imm calls env s d a ha)]

/-- The environment the negative loop's head leaves. -/
def t3DivHeadEnv (env : Env) (e d : BitVec 64) : Env :=
  ("%cmp230.i.i", .int 1 (evalICmp .slt e 0x0000000000000000#64)) ::
  ("%d201.2.i.i", .float d) :: ("%e10.2.i.i", .int 64 e) :: env

/-- The negative head's `denoteCode` from its test preheader. -/
theorem t3_divHead_denote_entry {calls : Calls} {env : Env} {s : State}
    {e d : BitVec 64}
    (hpre : s.pre = some "while.cond229.i.i.preheader")
    (he : lookupName env "%e10.2.i.i.ph" = some (.int 64 e))
    (hd : lookupName env "%d201.2.i.i.ph" = some (.float d)) :
    denoteCode calls t3DivHeadInstrs (stateAt env s) =
      some (stateAt (t3DivHeadEnv env e d) s) := by
  unfold t3DivHeadInstrs
  block_phi_run
  · rw [denoteCode_icmp_slt_imm _ _ _ "%cmp230.i.i" "%e10.2.i.i" (by block_lk) _]
    block_close
  all_goals block_close

/-- The negative head's `denoteCode` from the division loop's back edge. -/
theorem t3_divHead_denote_back {calls : Calls} {env : Env} {s : State}
    {e d : BitVec 64}
    (hpre : s.pre = some "while.body232.i.i")
    (he : lookupName env "%add245.i.i" = some (.int 64 e))
    (hd : lookupName env "%div.i.i" = some (.float d)) :
    denoteCode calls t3DivHeadInstrs (stateAt env s) =
      some (stateAt (t3DivHeadEnv env e d) s) := by
  unfold t3DivHeadInstrs
  block_phi_run
  · rw [denoteCode_icmp_slt_imm _ _ _ "%cmp230.i.i" "%e10.2.i.i" (by block_lk) _]
    block_close
  all_goals block_close

/-- The negative loop's back edge: the test holds (the residual is negative), so
the head jumps to its division block. -/
theorem t3_divHead_step_one {calls : Calls} {env : Env} {s : State} {e d : BitVec 64}
    (hpc : s.pc = t3DivHead)
    (hpre : s.pre = some "while.body232.i.i")
    (he : lookupName env "%add245.i.i" = some (.int 64 e))
    (hd : lookupName env "%div.i.i" = some (.float d))
    (hbit : evalICmp .slt e 0x0000000000000000#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3DivHeadEnv env e d)
        { s with pc := t3DivBody, pre := some t3DivHead }) := by
  refine numFast_step_at (s' := stateAt (t3DivHeadEnv env e d) s)
    (b := ⟨t3DivHead, t3DivHeadInstrs,
      Term.condbr (Operand.reg "%cmp230.i.i") t3DivBody "while.end253.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_divHead_pin
  · simpa only [denoteCode_nil] using t3_divHead_denote_back hpre he hd
  · have hlk : lookupName (t3DivHeadEnv env e d) "%cmp230.i.i"
        = some (.int 1 (evalICmp .slt e 0x0000000000000000#64)) := by
      simp only [t3DivHeadEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_one _ "%cmp230.i.i" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- The negative loop's exit: the test fails (the residual is spent), so the head
jumps to `while.end253.i.i`. -/
theorem t3_divHead_step_zero {calls : Calls} {env : Env} {s : State} {e d : BitVec 64}
    (hpc : s.pc = t3DivHead)
    (hpre : s.pre = some "while.body232.i.i")
    (he : lookupName env "%add245.i.i" = some (.int 64 e))
    (hd : lookupName env "%div.i.i" = some (.float d))
    (hbit : evalICmp .slt e 0x0000000000000000#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3DivHeadEnv env e d)
        { s with pc := "while.end253.i.i", pre := some t3DivHead }) := by
  refine numFast_step_at (s' := stateAt (t3DivHeadEnv env e d) s)
    (b := ⟨t3DivHead, t3DivHeadInstrs,
      Term.condbr (Operand.reg "%cmp230.i.i") t3DivBody "while.end253.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_divHead_pin
  · simpa only [denoteCode_nil] using t3_divHead_denote_back hpre he hd
  · have hlk : lookupName (t3DivHeadEnv env e d) "%cmp230.i.i"
        = some (.int 1 (evalICmp .slt e 0x0000000000000000#64)) := by
      simp only [t3DivHeadEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_zero _ "%cmp230.i.i" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- The positive loop's first iteration: entered from the ladder's start, the
test holds, so the head jumps to its row block with the widen's cells selected. -/
theorem t3_mulHead_step_one_entry {calls : Calls} {env : Env} {s : State}
    {e d : BitVec 64}
    (hpc : s.pc = t3MulHead)
    (hpre : s.pre = some "if.end198.i.i")
    (he : lookupName env "%sub200.i.i" = some (.int 64 e))
    (hd : lookupName env "%conv202.i.i" = some (.float d))
    (hbit : evalICmp .sgt e 0x0000000000000000#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3MulHeadEnv env e d)
        { s with pc := t3MulBody, pre := some t3MulHead }) := by
  refine numFast_step_at (s' := stateAt (t3MulHeadEnv env e d) s)
    (b := ⟨t3MulHead, t3MulHeadInstrs,
      Term.condbr (Operand.reg "%cmp204.i.i") t3MulBody t3LadderJoin⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_mulHead_pin
  · simpa only [denoteCode_nil] using t3_mulHead_denote_entry hpre he hd
  · have hlk : lookupName (t3MulHeadEnv env e d) "%cmp204.i.i"
        = some (.int 1 (evalICmp .sgt e 0x0000000000000000#64)) := by
      simp only [t3MulHeadEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_one _ "%cmp204.i.i" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- The positive loop's exit at counter zero: entered from the ladder's start
with the exponent already spent, the head jumps straight to the join. -/
theorem t3_mulHead_step_zero_entry {calls : Calls} {env : Env} {s : State}
    {e d : BitVec 64}
    (hpc : s.pc = t3MulHead)
    (hpre : s.pre = some "if.end198.i.i")
    (he : lookupName env "%sub200.i.i" = some (.int 64 e))
    (hd : lookupName env "%conv202.i.i" = some (.float d))
    (hbit : evalICmp .sgt e 0x0000000000000000#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3MulHeadEnv env e d)
        { s with pc := t3LadderJoin, pre := some t3MulHead }) := by
  refine numFast_step_at (s' := stateAt (t3MulHeadEnv env e d) s)
    (b := ⟨t3MulHead, t3MulHeadInstrs,
      Term.condbr (Operand.reg "%cmp204.i.i") t3MulBody t3LadderJoin⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_mulHead_pin
  · simpa only [denoteCode_nil] using t3_mulHead_denote_entry hpre he hd
  · have hlk : lookupName (t3MulHeadEnv env e d) "%cmp204.i.i"
        = some (.int 1 (evalICmp .sgt e 0x0000000000000000#64)) := by
      simp only [t3MulHeadEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_zero _ "%cmp204.i.i" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- The negative loop's first iteration: entered from its test preheader, the
test holds, so the head jumps to its division block. -/
theorem t3_divHead_step_one_entry {calls : Calls} {env : Env} {s : State}
    {e d : BitVec 64}
    (hpc : s.pc = t3DivHead)
    (hpre : s.pre = some "while.cond229.i.i.preheader")
    (he : lookupName env "%e10.2.i.i.ph" = some (.int 64 e))
    (hd : lookupName env "%d201.2.i.i.ph" = some (.float d))
    (hbit : evalICmp .slt e 0x0000000000000000#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3DivHeadEnv env e d)
        { s with pc := t3DivBody, pre := some t3DivHead }) := by
  refine numFast_step_at (s' := stateAt (t3DivHeadEnv env e d) s)
    (b := ⟨t3DivHead, t3DivHeadInstrs,
      Term.condbr (Operand.reg "%cmp230.i.i") t3DivBody "while.end253.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_divHead_pin
  · simpa only [denoteCode_nil] using t3_divHead_denote_entry hpre he hd
  · have hlk : lookupName (t3DivHeadEnv env e d) "%cmp230.i.i"
        = some (.int 1 (evalICmp .slt e 0x0000000000000000#64)) := by
      simp only [t3DivHeadEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_one _ "%cmp230.i.i" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- The negative loop's exit at counter zero: the exponent is already spent at
the preheader, so the head jumps to `while.end253.i.i`. -/
theorem t3_divHead_step_zero_entry {calls : Calls} {env : Env} {s : State}
    {e d : BitVec 64}
    (hpc : s.pc = t3DivHead)
    (hpre : s.pre = some "while.cond229.i.i.preheader")
    (he : lookupName env "%e10.2.i.i.ph" = some (.int 64 e))
    (hd : lookupName env "%d201.2.i.i.ph" = some (.float d))
    (hbit : evalICmp .slt e 0x0000000000000000#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3DivHeadEnv env e d)
        { s with pc := "while.end253.i.i", pre := some t3DivHead }) := by
  refine numFast_step_at (s' := stateAt (t3DivHeadEnv env e d) s)
    (b := ⟨t3DivHead, t3DivHeadInstrs,
      Term.condbr (Operand.reg "%cmp230.i.i") t3DivBody "while.end253.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_divHead_pin
  · simpa only [denoteCode_nil] using t3_divHead_denote_entry hpre he hd
  · have hlk : lookupName (t3DivHeadEnv env e d) "%cmp230.i.i"
        = some (.int 1 (evalICmp .slt e 0x0000000000000000#64)) := by
      simp only [t3DivHeadEnv, lookupName_cons_self]
    rw [numFast_execTerm_condbr_zero _ "%cmp230.i.i" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### The join block: `while.cond229.i.i.preheader`

The positive loop leaves for this block on two edges — the head's test refused
(the residual is not positive) and the row block's overflow test taken (the
double's bits are above `DBL_MAX`) — and both carry the residual and the
double's bits forward, from `%e10.0.i.i`/`%d201.0.i.i` on the first and
`%sub219.i.i`/`%mul217.i.i` on the second.  The block's two `phi`s select them
and its `br` enters the negative loop's head, so the join is one control step
whose successor is `t3DivHead` with exactly the two cells
`t3_divHead_denote_entry` reads.  The sign case is then the head's own test
(`t3DivHead_step_one_entry`/`_zero_entry`), not a second reading of it. -/

/-- The join block's instructions, from its pin. -/
def t3JoinInstrs : List Instr :=
  [Instr.phi "%e10.2.i.i.ph" (Ty.int 64)
      [("while.cond203.i.i", (Operand.reg "%e10.0.i.i")),
       ("while.body206.i.i", (Operand.reg "%sub219.i.i"))],
   Instr.phi "%d201.2.i.i.ph" Ty.double
      [("while.cond203.i.i", (Operand.reg "%d201.0.i.i")),
       ("while.body206.i.i", (Operand.reg "%mul217.i.i"))]]

/-- The join's pin: its two `phi`s and its `br` to the negative head. -/
theorem t3_join_pin :
    numFastBody.findBlock t3LadderJoin =
      some ⟨t3LadderJoin, t3JoinInstrs, Term.br t3DivHead⟩ := by
  simpa only [t3LadderJoin, t3DivHead, t3JoinInstrs]
    using numFast_findBlock_while_cond229_i_i_preheader

/-- The environment the join leaves: the two carried cells. -/
def t3JoinEnv (env : Env) (e d : BitVec 64) : Env :=
  ("%d201.2.i.i.ph", .float d) :: ("%e10.2.i.i.ph", .int 64 e) :: env

/-- The join's `denoteCode` from the positive head's refused test. -/
theorem t3_join_denote_from_head {calls : Calls} {env : Env} {s : State}
    {e d : BitVec 64}
    (hpre : s.pre = some "while.cond203.i.i")
    (he : lookupName env "%e10.0.i.i" = some (.int 64 e))
    (hd : lookupName env "%d201.0.i.i" = some (.float d)) :
    denoteCode calls t3JoinInstrs (stateAt env s) =
      some (stateAt (t3JoinEnv env e d) s) := by
  unfold t3JoinInstrs
  block_phi_run
  all_goals block_close

/-- The join's `denoteCode` from the row block's overflow edge. -/
theorem t3_join_denote_from_body {calls : Calls} {env : Env} {s : State}
    {e d : BitVec 64}
    (hpre : s.pre = some "while.body206.i.i")
    (he : lookupName env "%sub219.i.i" = some (.int 64 e))
    (hd : lookupName env "%mul217.i.i" = some (.float d)) :
    denoteCode calls t3JoinInstrs (stateAt env s) =
      some (stateAt (t3JoinEnv env e d) s) := by
  unfold t3JoinInstrs
  block_phi_run
  all_goals block_close

/-- The join's step from the positive head's refused test. -/
theorem t3_join_step_from_head {calls : Calls} {env : Env} {s : State}
    {e d : BitVec 64}
    (hpc : s.pc = t3LadderJoin)
    (hpre : s.pre = some "while.cond203.i.i")
    (he : lookupName env "%e10.0.i.i" = some (.int 64 e))
    (hd : lookupName env "%d201.0.i.i" = some (.float d)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3JoinEnv env e d)
        { s with pc := t3DivHead, pre := some t3LadderJoin }) := by
  refine numFast_step_at (s' := stateAt (t3JoinEnv env e d) s)
    (b := ⟨t3LadderJoin, t3JoinInstrs, Term.br t3DivHead⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, t3LadderJoin] using t3_join_pin
  · simpa only [denoteCode_nil] using t3_join_denote_from_head hpre he hd
  · simp only [execTerm, stateAt, hpc]

/-- The join's step from the row block's overflow edge. -/
theorem t3_join_step_from_body {calls : Calls} {env : Env} {s : State}
    {e d : BitVec 64}
    (hpc : s.pc = t3LadderJoin)
    (hpre : s.pre = some "while.body206.i.i")
    (he : lookupName env "%sub219.i.i" = some (.int 64 e))
    (hd : lookupName env "%mul217.i.i" = some (.float d)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3JoinEnv env e d)
        { s with pc := t3DivHead, pre := some t3LadderJoin }) := by
  refine numFast_step_at (s' := stateAt (t3JoinEnv env e d) s)
    (b := ⟨t3LadderJoin, t3JoinInstrs, Term.br t3DivHead⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, t3LadderJoin] using t3_join_pin
  · simpa only [denoteCode_nil] using t3_join_denote_from_body hpre he hd
  · simp only [execTerm, stateAt, hpc]

/-- **The join's run, from the positive head's refused test.**  One control step
carries the residual and the double's bits into the negative head. -/
theorem t3_join_run_from_head {calls : Calls} {env : Env} {s : State}
    {e d : BitVec 64} {k : Nat}
    (hpc : s.pc = t3LadderJoin)
    (hpre : s.pre = some "while.cond203.i.i")
    (he : lookupName env "%e10.0.i.i" = some (.int 64 e))
    (hd : lookupName env "%d201.0.i.i" = some (.float d)) :
    runFuel calls (1 + k) numFastBody (stateAt env s) =
      runFuel calls k numFastBody
        (stateAt (t3JoinEnv env e d)
          { s with pc := t3DivHead, pre := some t3LadderJoin }) :=
  runFuel_jump_prefix (t3_join_step_from_head hpc hpre he hd) k

/-- **The join's run, from the row block's overflow edge.** -/
theorem t3_join_run_from_body {calls : Calls} {env : Env} {s : State}
    {e d : BitVec 64} {k : Nat}
    (hpc : s.pc = t3LadderJoin)
    (hpre : s.pre = some "while.body206.i.i")
    (he : lookupName env "%sub219.i.i" = some (.int 64 e))
    (hd : lookupName env "%mul217.i.i" = some (.float d)) :
    runFuel calls (1 + k) numFastBody (stateAt env s) =
      runFuel calls k numFastBody
        (stateAt (t3JoinEnv env e d)
          { s with pc := t3DivHead, pre := some t3LadderJoin }) :=
  runFuel_jump_prefix (t3_join_step_from_body hpc hpre he hd) k

/-- **The ladder's join at a spent exponent.**  At the ladder's start with the
residual already spent (the head's test refused), two control steps — the head's
and the join's — reach the negative head with the residual and the double's bits
in the cells its `phi`s read, so the sign case is decided there. -/
theorem t3_ladder_join_spent {calls : Calls} {env : Env} {s : State}
    {e d : BitVec 64} {k : Nat}
    (hpc : s.pc = t3MulHead)
    (hpre : s.pre = some "if.end198.i.i")
    (he : lookupName env "%sub200.i.i" = some (.int 64 e))
    (hd : lookupName env "%conv202.i.i" = some (.float d))
    (hbit : evalICmp .sgt e 0x0000000000000000#64 = (0 : BitVec 1)) :
    runFuel calls (2 + k) numFastBody (stateAt env s) =
      runFuel calls k numFastBody
        (stateAt (t3JoinEnv (t3MulHeadEnv env e d) e d)
          { s with pc := t3DivHead, pre := some t3LadderJoin }) := by
  have h1 : step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3MulHeadEnv env e d)
        { s with pc := t3LadderJoin, pre := some t3MulHead }) :=
    t3_mulHead_step_zero_entry (calls := calls) hpc hpre he hd hbit
  have h2 : step calls numFastBody
      (stateAt (t3MulHeadEnv env e d)
        { s with pc := t3LadderJoin, pre := some t3MulHead }) =
      .jump (stateAt (t3JoinEnv (t3MulHeadEnv env e d) e d)
        { s with pc := t3DivHead, pre := some t3LadderJoin }) := by
    refine t3_join_step_from_head (calls := calls) (env := t3MulHeadEnv env e d)
      (s := { s with pc := t3LadderJoin, pre := some t3MulHead }) rfl rfl ?_ ?_
    · simp only [t3MulHeadEnv]
      block_lk
    · simp only [t3MulHeadEnv]
      block_lk
  rw [show 2 + k = 1 + (1 + k) from by omega,
    runFuel_jump_prefix h1, runFuel_jump_prefix h2]

/-! ### The loops' shapes at the pins -/

/-- The carried double after the positive ladder's first `c` rows. -/
def t3MulCarried (d : BitVec 64) (rows : List Nat) (c : Nat) : BitVec 64 :=
  (rows.take c).foldl (fun d r => fmulBits d (uitofpBits (10 ^ r))) d

/-- The carried double after the negative ladder's first `c` rows. -/
def t3DivCarried (d : BitVec 64) (rows : List Nat) (c : Nat) : BitVec 64 :=
  (rows.take c).foldl (fun d r => fdivBits d (uitofpBits (10 ^ r))) d

/-- The positive loop at its head: the residual is the remaining rows' sum, the
carried double is the fold over the spent rows, and the budget counts the rows
left.  The edge's predecessor is fixed by the counter, so the head's `phi`
selection is the invariant's. -/
def t3MulInv (d0 : BitVec 64) (rows : List Nat) : Nat → State → Nat → Prop :=
  fun r s c =>
    s.pc = t3MulHead ∧ c + r = rows.length ∧
    s.pre = (if c = 0 then some "if.end198.i.i" else some t3MulBody) ∧
    (c = 0 →
      lookupName s.env "%sub200.i.i"
          = some (.int 64 (BitVec.ofNat 64 ((rows.drop c).sum))) ∧
        lookupName s.env "%conv202.i.i" = some (.float (t3MulCarried d0 rows c))) ∧
    (0 < c →
      lookupName s.env "%sub219.i.i"
          = some (.int 64 (BitVec.ofNat 64 ((rows.drop c).sum))) ∧
        lookupName s.env "%mul217.i.i" = some (.float (t3MulCarried d0 rows c)))

/-- The positive loop's exit test: the remaining exponent is spent. -/
def t3MulAtBound (rows : List Nat) (_s : State) (c : Nat) : Bool :=
  decide ((rows.drop c).sum = 0)

/-- What the positive loop's exit state carries: the join's predecessor is the
head, and the two cells the preheader's `phi`s read, at their values.  The join's
`phi`s read `%e10.0.i.i` and `%d201.0.i.i`, so a word that named only their
presence could not be composed with the join: the residual at the bound is zero
and the carried double is the fold over every row, and those are the two values
the join hands the negative ladder. -/
def t3MulExitWord (d0 : BitVec 64) (rows : List Nat) : State → Prop := fun s =>
  s.pre = some t3MulHead ∧
    lookupName s.env "%e10.0.i.i" =
      some (.int 64 (BitVec.ofNat 64 ((rows.drop rows.length).sum))) ∧
    lookupName s.env "%d201.0.i.i" = some (.float (t3MulCarried d0 rows rows.length))

/-- **The positive loop's shape.**  Head, exit, bound, cost, invariant and exit
test are fixed at the emitted blocks; the two arms are the head's and the row
block's per-edge steps. -/
def t3MulLoopOf (calls : Calls) (d0 : BitVec 64) (rows : List Nat)
    (step_exit : ∀ (r : Nat) (s : State) (c : Nat),
      t3MulInv d0 rows r s c → t3MulAtBound rows s c = true →
      ∃ (e : State) (j : Nat), j ≤ 2 ∧ e.pc = t3LadderJoin ∧ t3MulExitWord d0 rows e ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e)
    (step_loop : ∀ (r : Nat) (s : State) (c : Nat),
      t3MulInv d0 rows (r + 1) s c → t3MulAtBound rows s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 2 ∧ e.pc = t3MulHead ∧ c < c' ∧
        t3MulInv d0 rows r e c' ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e) :
    BoundLoop calls numFastBody where
  head := t3MulHead
  exitBlock := t3LadderJoin
  N := rows.length
  cost := 2
  Inv := t3MulInv d0 rows
  atBound := t3MulAtBound rows
  Exit := fun e => e.pc = t3LadderJoin
  ExitWord := t3MulExitWord d0 rows
  step_exit := step_exit
  step_loop := step_loop
  exit_at_zero := by
    intro s c h
    obtain ⟨-, hcr, -, -, -⟩ := h
    unfold t3MulAtBound
    rw [decide_eq_true_eq, List.drop_eq_nil_of_le (by omega)]
    rfl
  budget := by
    intro r s c h
    obtain ⟨-, hcr, -, -, -⟩ := h
    omega

/-- **The positive loop from its head.**  At the whole bound as its budget the
run reaches the join within `(rows.length + 1) * 2` control steps. -/
theorem t3MulLoop_run_at (calls : Calls) (d0 : BitVec 64) (rows : List Nat)
    (step_exit : ∀ (r : Nat) (s : State) (c : Nat),
      t3MulInv d0 rows r s c → t3MulAtBound rows s c = true →
      ∃ (e : State) (j : Nat), j ≤ 2 ∧ e.pc = t3LadderJoin ∧ t3MulExitWord d0 rows e ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e)
    (step_loop : ∀ (r : Nat) (s : State) (c : Nat),
      t3MulInv d0 rows (r + 1) s c → t3MulAtBound rows s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 2 ∧ e.pc = t3MulHead ∧ c < c' ∧
        t3MulInv d0 rows r e c' ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e)
    (s : State) (c : Nat) (h : t3MulInv d0 rows rows.length s c) (k : Nat)
    {o : Outcome}
    (hcont : ∀ (e : State), e.pc = t3LadderJoin → t3MulExitWord d0 rows e →
      runFuel calls k numFastBody e = some o) :
    runFuel calls ((rows.length + 1) * 2 + k) numFastBody s = some o :=
  (t3MulLoopOf calls d0 rows step_exit step_loop).run_at s c h k hcont

/-- The negative loop at its head: the residual is minus the remaining rows' sum
and the carried double is the division fold over the spent rows. -/
def t3DivInv (d0 : BitVec 64) (rows : List Nat) : Nat → State → Nat → Prop :=
  fun r s c =>
    s.pc = t3DivHead ∧ c + r = rows.length ∧
    s.pre = (if c = 0 then some "while.cond229.i.i.preheader" else some t3DivBody) ∧
    (c = 0 →
      lookupName s.env "%e10.2.i.i.ph"
          = some (.int 64 (BitVec.ofInt 64 (-((rows.drop c).sum : Int)))) ∧
        lookupName s.env "%d201.2.i.i.ph" = some (.float (t3DivCarried d0 rows c))) ∧
    (0 < c →
      lookupName s.env "%add245.i.i"
          = some (.int 64 (BitVec.ofInt 64 (-((rows.drop c).sum : Int)))) ∧
        lookupName s.env "%div.i.i" = some (.float (t3DivCarried d0 rows c)))

/-- The negative loop's exit test: the remaining exponent is spent. -/
def t3DivAtBound (rows : List Nat) (_s : State) (c : Nat) : Bool :=
  decide ((rows.drop c).sum = 0)

/-- What the negative loop's exit state carries. -/
def t3DivExitWord (s : State) : Prop :=
  s.pre = some t3DivHead ∧
    lookupName s.env "%e10.2.i.i" ≠ none ∧
    lookupName s.env "%d201.2.i.i" ≠ none

/-- **The negative loop's shape**, at the emitted blocks: the head is
`while.cond229.i.i` and the exit is `while.end253.i.i`. -/
def t3DivLoopOf (calls : Calls) (d0 : BitVec 64) (rows : List Nat)
    (step_exit : ∀ (r : Nat) (s : State) (c : Nat),
      t3DivInv d0 rows r s c → t3DivAtBound rows s c = true →
      ∃ (e : State) (j : Nat), j ≤ 2 ∧ e.pc = "while.end253.i.i" ∧ t3DivExitWord e ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e)
    (step_loop : ∀ (r : Nat) (s : State) (c : Nat),
      t3DivInv d0 rows (r + 1) s c → t3DivAtBound rows s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 2 ∧ e.pc = t3DivHead ∧ c < c' ∧
        t3DivInv d0 rows r e c' ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e) :
    BoundLoop calls numFastBody where
  head := t3DivHead
  exitBlock := "while.end253.i.i"
  N := rows.length
  cost := 2
  Inv := t3DivInv d0 rows
  atBound := t3DivAtBound rows
  Exit := fun e => e.pc = "while.end253.i.i"
  ExitWord := t3DivExitWord
  step_exit := step_exit
  step_loop := step_loop
  exit_at_zero := by
    intro s c h
    obtain ⟨-, hcr, -, -, -⟩ := h
    unfold t3DivAtBound
    rw [decide_eq_true_eq, List.drop_eq_nil_of_le (by omega)]
    rfl
  budget := by
    intro r s c h
    obtain ⟨-, hcr, -, -, -⟩ := h
    omega

/-- **The negative loop from its head.** -/
theorem t3DivLoop_run_at (calls : Calls) (d0 : BitVec 64) (rows : List Nat)
    (step_exit : ∀ (r : Nat) (s : State) (c : Nat),
      t3DivInv d0 rows r s c → t3DivAtBound rows s c = true →
      ∃ (e : State) (j : Nat), j ≤ 2 ∧ e.pc = "while.end253.i.i" ∧ t3DivExitWord e ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e)
    (step_loop : ∀ (r : Nat) (s : State) (c : Nat),
      t3DivInv d0 rows (r + 1) s c → t3DivAtBound rows s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 2 ∧ e.pc = t3DivHead ∧ c < c' ∧
        t3DivInv d0 rows r e c' ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e)
    (s : State) (c : Nat) (h : t3DivInv d0 rows rows.length s c) (k : Nat)
    {o : Outcome}
    (hcont : ∀ (e : State), e.pc = "while.end253.i.i" → t3DivExitWord e →
      runFuel calls k numFastBody e = some o) :
    runFuel calls ((rows.length + 1) * 2 + k) numFastBody s = some o :=
  (t3DivLoopOf calls d0 rows step_exit step_loop).run_at s c h k hcont

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
#print axioms binade_mono
#print axioms t3RoundStep_mono
#print axioms t3RoundStep_mul_le
#print axioms t3RoundStep_weighted
#print axioms t3ErrStep_eq
#print axioms t3ErrWeight_le
#print axioms t3ErrStep_le
#print axioms map_eq_append_cons
#print axioms t3Ladder_charge
#print axioms t3Ladder_charge_sixteen
#print axioms t3_mulHead_pin
#print axioms t3_divHead_pin
#print axioms t3_mulBody_pin
#print axioms t3_divBody_pin
#print axioms t3_mulHead_denote_entry
#print axioms t3_mulHead_denote_back
#print axioms t3_mulHead_step_one
#print axioms t3_mulHead_step_zero
#print axioms step_icmp_slt_imm
#print axioms t3_divHead_denote_entry
#print axioms t3_divHead_denote_back
#print axioms t3_divHead_step_one
#print axioms t3_divHead_step_zero
#print axioms t3_mulHead_step_one_entry
#print axioms t3_mulHead_step_zero_entry
#print axioms t3_divHead_step_one_entry
#print axioms t3_divHead_step_zero_entry
#print axioms t3MulLoopOf
#print axioms t3MulLoop_run_at
#print axioms t3DivLoopOf
#print axioms t3DivLoop_run_at
#print axioms t3_join_pin
#print axioms t3_join_denote_from_head
#print axioms t3_join_denote_from_body
#print axioms t3_join_step_from_head
#print axioms t3_join_step_from_body
#print axioms t3_join_run_from_head
#print axioms t3_join_run_from_body
#print axioms t3_ladder_join_spent

end NumFastTier3Ladder

end LeanLLVM.Refinement
