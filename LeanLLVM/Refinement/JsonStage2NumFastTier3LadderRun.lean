/-
Tier 3's ladder as one run: the invariant-level join.

`JsonStage2NumFastTier3Rows` instantiates the two loops at the emitted rows: the
positive loop `while.cond203.i.i` multiplies by `10 ^ row` until the residual is
spent and leaves for `while.cond229.i.i.preheader`; the negative loop
`while.cond229.i.i` divides until the residual is spent and leaves for
`while.end253.i.i`.  What joined them so far is the block: `t3_join_step_from_head`
steps `while.cond229.i.i.preheader`'s two `phi`s and its `br`.  What that does not
say is *which loop's invariant holds where the two runs are appended*, and that is
what this module states.

**The two loops' rows differ, and the join is where that is decided.**  The
ladder is one pair of loops over one exponent: when the residual the ladder starts
from is positive the positive loop applies `t3Rows E` and the negative loop is
entered with nothing left to do; when it is negative the positive loop is entered
with an empty row list and the negative loop applies `t3Rows E`.  So the state the
join leaves is in the **negative** loop's invariant at counter zero with the
**empty** row list (`t3Rows 0 = []`), carrying the positive loop's final carried
double as the negative loop's seed.  `t3_join_divInv` is that statement, cell by
cell: the join's `%e10.2.i.i.ph` is the positive loop's spent residual — `0` at the
bound — read as the negative invariant's `-residual`, and its `%d201.2.i.i.ph` is
the positive fold's last value, which is the negative fold's seed at zero rows.

**The composition.**  `t3_ladder_run` appends them: the positive loop's run at its
whole budget (its `BoundLoop` from `JsonStage2NumFastTier3Rows`), one control step
for the join, the negative loop's exit arm at the empty row list (one step, within
the `(0 + 1) * 2` its own budget allows), and the caller's continuation.  The
budget is a term of the arguments: `((rows.length + 1) * 2) + 1 + ((0 + 1) * 2) + k`.

The one fact the composition needs beyond the two loops' own hypotheses is that
the positive fold's last value is a *positive* finite code: the negative loop's
zero test refuses on that, and at an empty row list the value it tests is the
positive fold's own last value (`t3_final_ticks`).  It is a hypothesis rather than
a theorem because the emitted tables' rows are the staging's, not the
arithmetic's — the same reason the two loops take `hpack` and `hstage`.
-/
import LeanLLVM.Refinement.JsonStage2NumFastTier3Rows

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.NumFastTier3
open LeanLLVM.Refinement.NumFastTier3Ladder
open LeanLLVM.Refinement.NumFastTier3Rows
open LeanLLVM.StrtodTier3

namespace NumFastTier3LadderRun

/-- The empty row list is `t3Rows 0`: the ladder applies no row when nothing is
left to spend. -/
theorem t3Rows_zero : t3Rows 0 = [] := by rw [t3Rows]

/-! ### The join state is the negative loop's entry

The join's two `phi`s read the positive loop's exit word — `%e10.0.i.i` and
`%d201.0.i.i` — and write `%e10.2.i.i.ph` and `%d201.2.i.i.ph`, which are the two
cells the negative invariant reads at counter zero.  At the bound the first of
them is zero, so the negative invariant's `-residual` is zero as well, and the
second is the positive fold over every row, which is the negative fold's seed at
an empty row list. -/

/-- **The join state is the negative loop's entry, at the empty row list.**  At
the positive loop's bound the join's state satisfies `t3DivInv` with the rows
`[]`, counter zero and the seed the positive fold's last value — the invariant the
negative loop's `BoundLoop` is entered in. -/
theorem t3_join_divInv (d0 : BitVec 64) (rows : List Nat) (env : Env) (base : State) :
    t3DivInv (t3MulCarried d0 rows rows.length) [] 0
      (stateAt
        (t3JoinEnv env (BitVec.ofNat 64 ((rows.drop rows.length).sum))
          (t3MulCarried d0 rows rows.length))
        { base with pc := t3DivHead, pre := some t3LadderJoin }) 0 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro _
    refine ⟨?_, ?_⟩
    · simp only [stateAt, t3JoinEnv]
      block_lk
      simp only [List.drop_length, List.sum_nil]
      rfl
    · simp only [stateAt, t3JoinEnv]
      block_lk
      rfl
  · intro hpos
    exact absurd hpos (by omega)

/-- The negative loop's exit test at the empty row list and counter zero is the
branch it takes: nothing is left to spend. -/
theorem t3DivAtBound_nil (s : State) : t3DivAtBound (t3Rows 0) s 0 = true := by
  rw [t3DivAtBound, t3Rows_zero]
  rfl

/-! ### The ladder as one run -/

/-- **The ladder as one run: the positive loop, the join, and the negative loop.**
From the positive loop's invariant at its whole bound, the run reaches the
negative loop's exit block within the positive loop's own budget — `(rows.length +
1) * 2` — one control step for the join, and the negative loop's budget at the
empty row list — `(0 + 1) * 2` — plus the caller's continuation.

The row lists differ, and that is the invariant-level content: the state the join
hands on is the negative loop's invariant at counter zero with rows `[]`
(`t3_join_divInv`), whose carried double is the positive fold's last value, so the
negative loop's exit test is `t3DivAtBound_nil` and its exit arm is the branch it
takes.  `hfinal` is the one fact the emitted code reads and does not compute: that
last value is a positive finite code. -/
theorem t3_ladder_run (calls : Calls) (d0 : BitVec 64) (E address : Nat)
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
    (s : State) (c : Nat) (h : t3MulInv d0 (t3Rows E) (t3Rows E).length s c)
    (k : Nat) {o : Outcome}
    (hcont : ∀ (e : State), e.pc = "while.end253.i.i" → t3DivExitWord e →
      runFuel calls k numFastBody e = some o) :
    runFuel calls (((t3Rows E).length + 1) * 2 + (1 + ((0 + 1) * 2) + k))
        numFastBody s = some o := by
  refine t3MulLoop_run_t3Rows calls d0 E address hE hpack hstage hno s c h
    (1 + ((0 + 1) * 2) + k) ?_
  intro e hpc hword
  obtain ⟨hpre, he10, hd201⟩ := hword
  -- the join's step: one control step from the positive loop's exit
  have hjoin : step calls numFastBody e =
      .jump (stateAt
        (t3JoinEnv e.env (BitVec.ofNat 64 ((t3Rows E).drop (t3Rows E).length).sum)
          (t3MulCarried d0 (t3Rows E) (t3Rows E).length))
        { e with pc := t3DivHead, pre := some t3LadderJoin }) :=
    t3_join_step_from_head (calls := calls) (env := e.env) (s := e) hpc hpre he10 hd201
  -- the negative loop's entry invariant at the empty row list
  have hinv : t3DivInv (t3MulCarried d0 (t3Rows E) (t3Rows E).length) (t3Rows 0) 0
      (stateAt
        (t3JoinEnv e.env (BitVec.ofNat 64 ((t3Rows E).drop (t3Rows E).length).sum)
          (t3MulCarried d0 (t3Rows E) (t3Rows E).length))
        { e with pc := t3DivHead, pre := some t3LadderJoin }) 0 := by
    simpa only [← t3Rows_zero] using
      t3_join_divInv d0 (t3Rows E) e.env e
  -- the negative loop's exit arm: at the empty row list it leaves at once
  obtain ⟨e', j, hj, hpc', hword', hrun⟩ :=
    t3DivLoop_exit calls (t3MulCarried d0 (t3Rows E) (t3Rows E).length) 0 0 _ 0 hinv
      (t3DivAtBound_nil _)
  have htail : runFuel calls (((0 + 1) * 2) + k) numFastBody
      (stateAt
        (t3JoinEnv e.env (BitVec.ofNat 64 ((t3Rows E).drop (t3Rows E).length).sum)
          (t3MulCarried d0 (t3Rows E) (t3Rows E).length))
        { e with pc := t3DivHead, pre := some t3LadderJoin }) = some o :=
    runFuel_mono_le (n := j + k) (by omega) (by rw [hrun k]; exact hcont e' hpc' hword')
  rw [show 1 + ((0 + 1) * 2) + k = 1 + (((0 + 1) * 2) + k) from by omega]
  rw [runFuel_jump_prefix hjoin (((0 + 1) * 2) + k)]
  exact htail

/-! ### Axiom footprints -/

#print axioms t3Rows_zero
#print axioms t3_join_divInv
#print axioms t3DivAtBound_nil
#print axioms t3_ladder_run

end NumFastTier3LadderRun

end LeanLLVM.Refinement
