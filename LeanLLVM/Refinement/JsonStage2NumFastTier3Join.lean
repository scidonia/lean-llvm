/-
Tier 3's ladder at the state: the join's two shapes.

`JsonStage2NumFastTier3LadderRun.t3_ladder_run` composes the ladder's two loops
at the **invariant**: from the positive loop's invariant at its whole bound, the
positive loop's run, one control step for the join, and the negative loop's exit
arm at the empty row list.  What it does not say is what the emitted ladder does
with **which residual it was entered at**, and the two answers differ:

* a **positive** residual spends itself in `while.cond203.i.i` (the rows are
  `t3Rows E`), and the join reads a spent `%e10.0.i.i = 0`, so the negative loop
  is entered with nothing to do — `t3_ladder_run`'s shape;
* a **negative** residual refuses `while.cond203.i.i`'s test at once (the rows
  are `[]`), and the join hands `%e10.2.i.i.ph = -E` to the negative loop, which
  applies `t3Rows E`.

This module states the second shape and the entry states of both: `%sub200.i.i`
and `%conv202.i.i` are the cells `if.end198.i.i` leaves the head's `phi`s, so a
caller that names them at the model's residual and double has the run at the
actual state, not at an invariant it was handed.  `t3_join_divInv_rows` is
`t3_join_divInv`'s dual: the join's state is the negative loop's entry at the
whole row list, with the positive loop's spent residual (`0`) read as the
negative invariant's `-residual` at a seed that never moved.

The budgets are the loops' own: `(0 + 1) * 2` for the positive loop entered at
`[]` (its exit test is `t3MulAtBound_nil`), the join's one control step, and
`((t3Rows E).length + 1) * 2` for the negative loop.  What stays a hypothesis is
`t3_ladder_run`'s: the staging's rows and packing (`hstage`, `hpack`, `hno`) and
the last value's positivity (`hfinal`).
-/
import LeanLLVM.Refinement.JsonStage2NumFastTier3LadderRun

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.NumFastTier3
open LeanLLVM.Refinement.NumFastTier3Ladder
open LeanLLVM.Refinement.NumFastTier3Rows
open LeanLLVM.Refinement.NumFastTier3LadderRun
open LeanLLVM.StrtodTier3

namespace NumFastTier3Join

/-! ### The positive loop entered at no rows

A negative residual refuses the positive loop's test before its first visit, so
the loop's run is its exit arm at the empty row list and counter zero. -/

/-- The positive loop at no rows is at its bound at every counter. -/
theorem t3MulAtBound_nil (s : State) (c : Nat) : t3MulAtBound [] s c = true := by
  unfold t3MulAtBound
  simp only [List.drop_nil, List.sum_nil, decide_true]

/-- The positive loop's exit at no rows: the head's refused test and the join,
one control step, leaving the join's two cells at `0` and the seed. -/
theorem t3MulLoop_exit_nil (calls : Calls) (d0 : BitVec 64) :
    ∀ (r : Nat) (s : State) (c : Nat),
      t3MulInv d0 [] r s c → t3MulAtBound [] s c = true →
      ∃ (e : State) (j : Nat), j ≤ 2 ∧ e.pc = t3LadderJoin ∧ t3MulExitWord d0 [] e ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e := by
  intro r s c hinv hbound
  obtain ⟨hpc, hcr, hpre, hc0, hcpos⟩ := hinv
  have hcr0 : c + r = 0 := by simpa using hcr
  have hc : c = 0 := by omega
  subst hc
  have hr : r = 0 := by omega
  subst hr
  obtain ⟨he, hd⟩ := hc0 rfl
  have hpre0 : s.pre = some "if.end198.i.i" := by
    rw [hpre, ite_eq_left rfl]
  have he0 : lookupName s.env "%sub200.i.i"
      = some (.int 64 (0#64)) := by
    simpa only [List.drop_nil, List.sum_nil] using he
  refine ⟨stateAt (t3MulHeadEnv s.env 0 d0)
      { s with pc := t3LadderJoin, pre := some t3MulHead }, 1, by omega, rfl, ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_⟩
    · simp only [stateAt, t3MulHeadEnv]
      block_lk
      simp
    · simp only [stateAt, t3MulHeadEnv, t3MulCarried]
      block_lk
      simp
  · intro k
    refine runFuel_jump_prefix
      (t3_mulHead_step_zero_entry (calls := calls) (env := s.env) (s := s)
        (e := 0) (d := d0) hpc hpre0 he0 hd ?_) k
    decide

/-! ### The join's dual: the negative loop's entry at the whole row list

When the positive loop was entered at no rows the join's `%e10.2.i.i.ph` is the
residual it was entered at — `-E`, the exponent's own magnitude negated — and
`%d201.2.i.i.ph` is the seed the positive fold never moved.  That is
`t3DivInv` at the whole row list, counter zero. -/

/-- **The join at a spent positive loop is the negative loop's entry at the whole
row list.**  With no rows applied, the carried double is the seed and the
residual is `-E`, so the state the join leaves is `t3DivInv`'s at counter zero
with `t3Rows E` still to spend. -/
theorem t3_join_divInv_rows (d0 : BitVec 64) (E : Nat) (env : Env) (base : State) :
    t3DivInv d0 (t3Rows E) (t3Rows E).length
      (stateAt (t3JoinEnv env (BitVec.ofInt 64 (-(((t3Rows E).sum : Nat) : Int))) d0)
        { base with pc := t3DivHead, pre := some t3LadderJoin }) 0 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · rw [Nat.zero_add]
  · simp only [t3LadderJoin, t3DivHead]
    rfl
  · intro _
    refine ⟨?_, ?_⟩
    · simp only [stateAt, t3JoinEnv]
      block_lk
      simp
    · simp only [stateAt, t3JoinEnv, t3DivCarried]
      block_lk
      simp
  · intro hpos
    exact absurd hpos (by omega)

/-! ### The head's spent test at a negative residual -/

/-- The positive head's test refuses at a negative residual: `%e10.0.i.i >s 0`
is `0` at `-E` for a positive `E`. -/
theorem evalICmp_sgt_ofInt_neg_zero {E : Nat} (h0 : 0 < E) (hE : E < 2 ^ 63) :
    evalICmp .sgt (BitVec.ofInt 64 (-(E : Int))) (0 : BitVec 64) =
      (0 : BitVec 1) := by
  have htoInt : (BitVec.ofInt 64 (-(E : Int))).toInt = -(E : Int) := by
    refine BitVec.toInt_ofInt_eq_self (by decide) ?_ ?_ <;> omega
  rw [show evalICmp .sgt (BitVec.ofInt 64 (-(E : Int))) (0 : BitVec 64)
      = BitVec.ofBool ((0 : BitVec 64).slt (BitVec.ofInt 64 (-(E : Int)))) from rfl]
  have hz : BitVec.toInt (0 : BitVec 64) = 0 := by decide
  rw [BitVec.slt_eq_decide, htoInt, hz]
  rw [show decide ((0 : Int) < -(E : Int)) = false from by
    rw [decide_eq_false_iff_not]
    omega]
  rfl

/-! ### The ladder at the state, negative first -/

/-- `stateAt` at a state's own environment is the state. -/
theorem t3j_stateAt_self (s : State) : stateAt s.env s = s := rfl

/-- **The ladder, a negative residual first.**  From the head with `%sub200.i.i`
at `-E` and `%conv202.i.i` at the seed, the run refuses the positive test, takes
the join, and spends `t3Rows E` in the negative loop, reaching
`while.end253.i.i` in `(0 + 1) * 2` for the positive loop's non-entry, one control
step for the join, and the negative loop's own budget. -/
theorem t3_ladder_run_neg (calls : Calls) (d0 : BitVec 64) (E address : Nat)
    (hE : E ≤ 342) (hpos : 0 < E)
    (hpack : ∀ c, c ≤ (t3Rows E).length →
      ∃ k : Code, t3DivCarried d0 (t3Rows E) c = packMag (.fin k) false ∧
        k.IsMag ∧ 0 < k.ticks)
    (hstage : ∀ (env : Env) (s : State) (k : Nat) (d : BitVec 64),
      lookupName env "%e10.2.i.i" = some (.int 64 (BitVec.ofInt 64 (-(k : Int)))) →
      lookupName env "%d201.2.i.i" = some (.float d) →
        lookupName env "@NUMF_EL1_POW10" = some (.ptr address) ∧
        readBytes s.mem (address + min k 22 * 8) 8
          = some (natToBytes (uitofpBits (10 ^ min k 22)).toNat 8))
    (s : State) (hpc : s.pc = t3MulHead) (hpre : s.pre = some "if.end198.i.i")
    (he : lookupName s.env "%sub200.i.i"
      = some (.int 64 (BitVec.ofInt 64 (-(E : Int)))))
    (hd : lookupName s.env "%conv202.i.i" = some (.float d0))
    (k : Nat) {o : Outcome}
    (hcont : ∀ (e : State), e.pc = "while.end253.i.i" → t3DivExitWord e →
      runFuel calls k numFastBody e = some o) :
    runFuel calls (((0 + 1) * 2) + (1 + (((t3Rows E).length + 1) * 2) + k))
      numFastBody s = some o := by
  have hbit : evalICmp .sgt (BitVec.ofInt 64 (-(E : Int))) (0 : BitVec 64) =
      (0 : BitVec 1) := evalICmp_sgt_ofInt_neg_zero hpos (by omega)
  -- the head's refused test: one control step to the join
  have h1 : step calls numFastBody (stateAt s.env s) =
      .jump (stateAt (t3MulHeadEnv s.env (BitVec.ofInt 64 (-(E : Int))) d0)
        { s with pc := t3LadderJoin, pre := some t3MulHead }) :=
    t3_mulHead_step_zero_entry (calls := calls) (env := s.env) (s := s)
      (e := BitVec.ofInt 64 (-(E : Int))) (d := d0) hpc hpre he hd hbit
  -- the join: one control step to the negative head, carrying the two cells
  have h2 : step calls numFastBody
      (stateAt (t3MulHeadEnv s.env (BitVec.ofInt 64 (-(E : Int))) d0)
        { s with pc := t3LadderJoin, pre := some t3MulHead }) =
      .jump (stateAt
        (t3JoinEnv (t3MulHeadEnv s.env (BitVec.ofInt 64 (-(E : Int))) d0)
          (BitVec.ofInt 64 (-(E : Int))) d0)
        { s with pc := t3DivHead, pre := some t3LadderJoin }) := by
    refine t3_join_step_from_head (calls := calls)
      (env := t3MulHeadEnv s.env (BitVec.ofInt 64 (-(E : Int))) d0)
      (s := { s with pc := t3LadderJoin, pre := some t3MulHead }) rfl rfl ?_ ?_
    · simp only [t3MulHeadEnv]
      block_lk
    · simp only [t3MulHeadEnv]
      block_lk
  -- the negative loop's entry invariant: the join's cells at the whole row list
  have hsum : ((t3Rows E).sum : Nat) = E := t3Rows_sum E
  have hinv : t3DivInv d0 (t3Rows E) (t3Rows E).length
      (stateAt
        (t3JoinEnv (t3MulHeadEnv s.env (BitVec.ofInt 64 (-(E : Int))) d0)
          (BitVec.ofInt 64 (-(E : Int))) d0)
        { s with pc := t3DivHead, pre := some t3LadderJoin }) 0 := by
    simpa only [hsum] using
      t3_join_divInv_rows d0 E (t3MulHeadEnv s.env (BitVec.ofInt 64 (-(E : Int))) d0) s
  have hjoin : runFuel calls (((t3Rows E).length + 1) * 2 + k) numFastBody
      (stateAt
        (t3JoinEnv (t3MulHeadEnv s.env (BitVec.ofInt 64 (-(E : Int))) d0)
          (BitVec.ofInt 64 (-(E : Int))) d0)
        { s with pc := t3DivHead, pre := some t3LadderJoin }) = some o :=
    t3DivLoop_run_t3Rows calls d0 E address hE hpack hstage _ 0 hinv k hcont
  -- the run at the steps the two edges and the negative loop actually take
  have hrun : runFuel calls (2 + (((t3Rows E).length + 1) * 2 + k)) numFastBody s
      = some o := by
    rw [show 2 + (((t3Rows E).length + 1) * 2 + k)
        = 1 + (1 + (((t3Rows E).length + 1) * 2 + k)) from by omega]
    rw [t3j_stateAt_self] at h1
    rw [runFuel_jump_prefix h1 (1 + (((t3Rows E).length + 1) * 2 + k)),
      runFuel_jump_prefix h2 (((t3Rows E).length + 1) * 2 + k)]
    exact hjoin
  exact runFuel_mono_le (n := 2 + (((t3Rows E).length + 1) * 2 + k)) (by omega) hrun

/-! ### The ladder at the state, positive first

The other shape is `t3_ladder_run`'s, read at the cells `if.end198.i.i` leaves:
`%sub200.i.i = E` and `%conv202.i.i` the seed is `t3MulInv` at its whole bound and
counter zero. -/

/-- **The ladder, a positive residual first.**  From the head with `%sub200.i.i`
at `E` and `%conv202.i.i` at the seed, the run spends `t3Rows E` in the positive
loop, takes the join, and leaves the negative loop its exit arm, reaching
`while.end253.i.i` within `t3_ladder_run`'s own budget. -/
theorem t3_ladder_run_pos (calls : Calls) (d0 : BitVec 64) (E address : Nat)
    (hE : E ≤ 342)
    (hpack : ∀ c, c ≤ (t3Rows E).length →
      ∃ k : Code, t3MulCarried d0 (t3Rows E) c = packMag (.fin k) false ∧ k.IsMag)
    (hstage : ∀ (env : Env) (s : State) (resid : Nat) (d : BitVec 64),
      lookupName env "%e10.0.i.i" = some (.int 64 (BitVec.ofNat 64 resid)) →
      lookupName env "%d201.0.i.i" = some (.float d) →
        lookupName env "@NUMF_EL1_POW10" = some (.ptr address) ∧
        readBytes s.mem (address + min resid 22 * 8) 8
          = some (natToBytes (uitofpBits (10 ^ min resid 22)).toNat 8))
    (hno : ∀ c, c < (t3Rows E).length →
      ¬ overflowTicks * 2 ^ 1074
        ≤ F64.magTicks (F64.ofBits (t3MulCarried d0 (t3Rows E) c))
            * (10 ^ min (t3Resid E c) 22 * 2 ^ 1074))
    (hfinal : ∃ k : Code,
      t3MulCarried d0 (t3Rows E) (t3Rows E).length = packMag (.fin k) false ∧
        k.IsMag ∧ 0 < k.ticks)
    (s : State) (hpc : s.pc = t3MulHead) (hpre : s.pre = some "if.end198.i.i")
    (he : lookupName s.env "%sub200.i.i" = some (.int 64 (BitVec.ofNat 64 E)))
    (hd : lookupName s.env "%conv202.i.i" = some (.float d0))
    (k : Nat) {o : Outcome}
    (hcont : ∀ (e : State), e.pc = "while.end253.i.i" → t3DivExitWord e →
      runFuel calls k numFastBody e = some o) :
    runFuel calls (((t3Rows E).length + 1) * 2 + (1 + ((0 + 1) * 2) + k))
      numFastBody s = some o := by
  have hsum : ((t3Rows E).sum : Nat) = E := t3Rows_sum E
  have hinv : t3MulInv d0 (t3Rows E) (t3Rows E).length s 0 := by
    refine ⟨hpc, by simp, ?_, ?_, ?_⟩
    · exact hpre
    · intro _
      refine ⟨?_, ?_⟩
      · simp only [List.drop_zero, hsum]
        exact he
      · simp only [t3MulCarried, List.take_zero, List.foldl_nil]
        exact hd
    · intro hpos
      omega
  exact t3_ladder_run calls d0 E address hE hpack hstage hno hfinal s 0 hinv k hcont

/-! ### The ladder's two shapes with their exit states

The seam that continues past `while.end253.i.i` needs the state the ladder leaves,
not only its outcome: the epilogue's boundary is read at that state.  `BoundLoop.run`
hands the exit state back, so the two shapes below are the same compositions as
`t3_ladder_run_neg`/`t3_ladder_run_pos` with the continuation replaced by the exit
state and a fuel left for the caller. -/

/-- The negative loop's exit at the empty row list: the head's zero test refuses
at `-0`. -/
theorem t3DivLoop_exit_nil (calls : Calls) (d0 : BitVec 64) :
    ∀ (r : Nat) (s : State) (c : Nat),
      t3DivInv d0 [] r s c → t3DivAtBound [] s c = true →
      ∃ (e : State) (j : Nat), j ≤ 2 ∧ e.pc = "while.end253.i.i" ∧ t3DivExitWord e ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e := by
  intro r s c hinv hbound
  obtain ⟨hpc, hcr, hpre, hc0, hcpos⟩ := hinv
  have hcr0 : c + r = 0 := by simpa using hcr
  have hc : c = 0 := by omega
  subst hc
  have hr : r = 0 := by omega
  subst hr
  obtain ⟨he, hd⟩ := hc0 rfl
  have hpre0 : s.pre = some "while.cond229.i.i.preheader" := by
    rw [hpre, ite_eq_left rfl]
  have hbit : evalICmp .slt (BitVec.ofInt 64 (-(((([] : List Nat).drop 0).sum : Nat) : Int)))
      (0 : BitVec 64) = (0 : BitVec 1) := by
    decide
  refine ⟨stateAt (t3DivHeadEnv s.env (BitVec.ofInt 64 (-(((([] : List Nat).drop 0).sum : Nat) : Int))) d0)
      { s with pc := "while.end253.i.i", pre := some t3DivHead }, 1, by omega, rfl, ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_⟩
    · have hl : lookupName
          (t3DivHeadEnv s.env (BitVec.ofInt 64 (-(((([] : List Nat).drop 0).sum : Nat) : Int))) d0)
          "%e10.2.i.i" = some (.int 64 (BitVec.ofInt 64 (-(((([] : List Nat).drop 0).sum : Nat) : Int)))) := by
        simp only [t3DivHeadEnv]
        block_lk
      simp only [stateAt, hl]
      simp
    · have hl : lookupName
          (t3DivHeadEnv s.env (BitVec.ofInt 64 (-(((([] : List Nat).drop 0).sum : Nat) : Int))) d0)
          "%d201.2.i.i" = some (.float d0) := by
        simp only [t3DivHeadEnv]
        block_lk
      simp only [stateAt, hl]
      simp
  · intro k
    exact runFuel_jump_prefix
      (t3_divHead_step_zero_entry (calls := calls) (env := s.env) (s := s)
        (e := BitVec.ofInt 64 (-(((([] : List Nat).drop 0).sum : Nat) : Int))) (d := d0)
        hpc hpre0 he hd hbit) k

/-- **The ladder, a negative residual first, with its exit state.** -/
theorem t3_ladder_run_neg_exit (calls : Calls) (d0 : BitVec 64) (E address : Nat)
    (hE : E ≤ 342) (hpos : 0 < E)
    (hpack : ∀ c, c ≤ (t3Rows E).length →
      ∃ k : Code, t3DivCarried d0 (t3Rows E) c = packMag (.fin k) false ∧
        k.IsMag ∧ 0 < k.ticks)
    (hstage : ∀ (env : Env) (s : State) (k : Nat) (d : BitVec 64),
      lookupName env "%e10.2.i.i" = some (.int 64 (BitVec.ofInt 64 (-(k : Int)))) →
      lookupName env "%d201.2.i.i" = some (.float d) →
        lookupName env "@NUMF_EL1_POW10" = some (.ptr address) ∧
        readBytes s.mem (address + min k 22 * 8) 8
          = some (natToBytes (uitofpBits (10 ^ min k 22)).toNat 8))
    (s : State) (hpc : s.pc = t3MulHead) (hpre : s.pre = some "if.end198.i.i")
    (he : lookupName s.env "%sub200.i.i"
      = some (.int 64 (BitVec.ofInt 64 (-(E : Int)))))
    (hd : lookupName s.env "%conv202.i.i" = some (.float d0))
    (k : Nat) :
    ∃ (e : State) (j : Nat),
      j ≤ ((0 + 1) * 2) + (1 + (((t3Rows E).length + 1) * 2)) ∧
      e.pc = "while.end253.i.i" ∧ t3DivExitWord e ∧
      runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e := by
  have hbit : evalICmp .sgt (BitVec.ofInt 64 (-(E : Int))) (0 : BitVec 64) =
      (0 : BitVec 1) := evalICmp_sgt_ofInt_neg_zero hpos (by omega)
  have h1 : step calls numFastBody (stateAt s.env s) =
      .jump (stateAt (t3MulHeadEnv s.env (BitVec.ofInt 64 (-(E : Int))) d0)
        { s with pc := t3LadderJoin, pre := some t3MulHead }) :=
    t3_mulHead_step_zero_entry (calls := calls) (env := s.env) (s := s)
      (e := BitVec.ofInt 64 (-(E : Int))) (d := d0) hpc hpre he hd hbit
  have h2 : step calls numFastBody
      (stateAt (t3MulHeadEnv s.env (BitVec.ofInt 64 (-(E : Int))) d0)
        { s with pc := t3LadderJoin, pre := some t3MulHead }) =
      .jump (stateAt
        (t3JoinEnv (t3MulHeadEnv s.env (BitVec.ofInt 64 (-(E : Int))) d0)
          (BitVec.ofInt 64 (-(E : Int))) d0)
        { s with pc := t3DivHead, pre := some t3LadderJoin }) := by
    refine t3_join_step_from_head (calls := calls)
      (env := t3MulHeadEnv s.env (BitVec.ofInt 64 (-(E : Int))) d0)
      (s := { s with pc := t3LadderJoin, pre := some t3MulHead }) rfl rfl ?_ ?_
    · simp only [t3MulHeadEnv]
      block_lk
    · simp only [t3MulHeadEnv]
      block_lk
  have hsum : ((t3Rows E).sum : Nat) = E := t3Rows_sum E
  have hinv : t3DivInv d0 (t3Rows E) (t3Rows E).length
      (stateAt
        (t3JoinEnv (t3MulHeadEnv s.env (BitVec.ofInt 64 (-(E : Int))) d0)
          (BitVec.ofInt 64 (-(E : Int))) d0)
        { s with pc := t3DivHead, pre := some t3LadderJoin }) 0 := by
    simpa only [hsum] using
      t3_join_divInv_rows d0 E (t3MulHeadEnv s.env (BitVec.ofInt 64 (-(E : Int))) d0) s
  obtain ⟨e, j', hj', hexit, hword, hrun⟩ :=
    (t3DivLoop_t3Rows calls d0 E address hE hpack hstage).run_from
      ((t3Rows E).length)
      (stateAt
        (t3JoinEnv (t3MulHeadEnv s.env (BitVec.ofInt 64 (-(E : Int))) d0)
          (BitVec.ofInt 64 (-(E : Int))) d0)
        { s with pc := t3DivHead, pre := some t3LadderJoin }) 0 hinv
  refine ⟨e, 2 + j', ?_, hexit, hword, ?_⟩
  · have hj'' : j' ≤ ((t3Rows E).length + 1) * 2 := hj'
    show 2 + j' ≤ (0 + 1) * 2 + (1 + ((t3Rows E).length + 1) * 2)
    omega
  · rw [t3j_stateAt_self] at h1
    rw [show 2 + j' + k = 1 + (1 + (j' + k)) from by omega,
      runFuel_jump_prefix h1 (1 + (j' + k)), runFuel_jump_prefix h2 (j' + k)]
    exact hrun k

/-- **The ladder, a positive residual first, with its exit state.** -/
theorem t3_ladder_run_pos_exit (calls : Calls) (d0 : BitVec 64) (E address : Nat)
    (hE : E ≤ 342)
    (hpack : ∀ c, c ≤ (t3Rows E).length →
      ∃ k : Code, t3MulCarried d0 (t3Rows E) c = packMag (.fin k) false ∧ k.IsMag)
    (hstage : ∀ (env : Env) (s : State) (resid : Nat) (d : BitVec 64),
      lookupName env "%e10.0.i.i" = some (.int 64 (BitVec.ofNat 64 resid)) →
      lookupName env "%d201.0.i.i" = some (.float d) →
        lookupName env "@NUMF_EL1_POW10" = some (.ptr address) ∧
        readBytes s.mem (address + min resid 22 * 8) 8
          = some (natToBytes (uitofpBits (10 ^ min resid 22)).toNat 8))
    (hno : ∀ c, c < (t3Rows E).length →
      ¬ overflowTicks * 2 ^ 1074
        ≤ F64.magTicks (F64.ofBits (t3MulCarried d0 (t3Rows E) c))
            * (10 ^ min (t3Resid E c) 22 * 2 ^ 1074))
    (s : State) (hpc : s.pc = t3MulHead) (hpre : s.pre = some "if.end198.i.i")
    (he : lookupName s.env "%sub200.i.i" = some (.int 64 (BitVec.ofNat 64 E)))
    (hd : lookupName s.env "%conv202.i.i" = some (.float d0))
    (k : Nat) :
    ∃ (e : State) (j : Nat),
      j ≤ (((t3Rows E).length + 1) * 2 + (1 + ((0 + 1) * 2))) ∧
      e.pc = "while.end253.i.i" ∧ t3DivExitWord e ∧
      runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e := by
  have hsum : ((t3Rows E).sum : Nat) = E := t3Rows_sum E
  have hinv : t3MulInv d0 (t3Rows E) (t3Rows E).length s 0 := by
    refine ⟨hpc, by simp, ?_, ?_, ?_⟩
    · exact hpre
    · intro _
      refine ⟨?_, ?_⟩
      · simp only [List.drop_zero, hsum]
        exact he
      · simp only [t3MulCarried, List.take_zero, List.foldl_nil]
        exact hd
    · intro hpos
      omega
  obtain ⟨e1, j1, hj1, hexit1, hword1, hrun1⟩ :=
    (t3MulLoop_t3Rows calls d0 E address hE hpack hstage hno).run_from
      ((t3Rows E).length) s 0 hinv
  obtain ⟨hpre1, he1, hd1⟩ := hword1
  have hjoin : step calls numFastBody (stateAt e1.env e1) =
      .jump (stateAt (t3JoinEnv e1.env
        (BitVec.ofNat 64 ((t3Rows E).drop (t3Rows E).length).sum)
        (t3MulCarried d0 (t3Rows E) (t3Rows E).length))
        { e1 with pc := t3DivHead, pre := some t3LadderJoin }) :=
    t3_join_step_from_head (calls := calls) (env := e1.env) (s := e1)
      hexit1 hpre1 he1 hd1
  have hinv2 : t3DivInv (t3MulCarried d0 (t3Rows E) (t3Rows E).length) []
      0
      (stateAt
        (t3JoinEnv e1.env (BitVec.ofNat 64 ((t3Rows E).drop (t3Rows E).length).sum)
          (t3MulCarried d0 (t3Rows E) (t3Rows E).length))
        { e1 with pc := t3DivHead, pre := some t3LadderJoin }) 0 := by
    simpa only [t3Rows_zero] using
      t3_join_divInv d0 (t3Rows E) e1.env e1
  have hb2 : ∀ (st : State), t3DivAtBound [] st 0 = true := fun st => by
    unfold t3DivAtBound
    simp only [List.drop_nil, List.sum_nil]
    rfl
  obtain ⟨e2, j2, hj2, hexit2, hword2, hrun2⟩ :=
    t3DivLoop_exit_nil calls (t3MulCarried d0 (t3Rows E) (t3Rows E).length)
      0 _ 0 hinv2 (hb2 _)
  refine ⟨e2, j1 + (1 + j2), ?_, hexit2, hword2, ?_⟩
  · have hj1' : j1 ≤ ((t3Rows E).length + 1) * 2 := hj1
    omega
  · rw [t3j_stateAt_self] at hjoin
    rw [show j1 + (1 + j2) + k = j1 + (1 + (j2 + k)) from by omega,
      hrun1 (1 + (j2 + k)), runFuel_jump_prefix hjoin (j2 + k)]
    exact hrun2 k

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.NumFastTier3Join.t3MulAtBound_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms t3MulAtBound_nil

/-- info: 'LeanLLVM.Refinement.NumFastTier3Join.t3MulLoop_exit_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms t3MulLoop_exit_nil

/-- info: 'LeanLLVM.Refinement.NumFastTier3Join.t3_join_divInv_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms t3_join_divInv_rows

/-- info: 'LeanLLVM.Refinement.NumFastTier3Join.evalICmp_sgt_ofInt_neg_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evalICmp_sgt_ofInt_neg_zero

/-- info: 'LeanLLVM.Refinement.NumFastTier3Join.t3_ladder_run_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t3_ladder_run_neg

/-- info: 'LeanLLVM.Refinement.NumFastTier3Join.t3_ladder_run_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t3_ladder_run_pos

end NumFastTier3Join

end LeanLLVM.Refinement
