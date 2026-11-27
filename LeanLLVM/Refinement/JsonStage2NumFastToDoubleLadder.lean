/-
The multiply exit's two edges into the ladder.

`NumFastToDouble.end176_run_ladder` carries `while.end176.i.i`'s **empty**
residual edge through `if.end198.i.i`'s fold to the ladder's head,
`while.cond203.i.i`, with the fold's environment `t3FoldEnv` — the residual
`%sub200.i.i = (%add110.i.i - %topn.0711.i.i) + 1` and the widened head
`%conv202.i.i`.  This module closes the pair: the same exit's **non-empty**
edge (`if.then178.i.i`'s `stk_mul_u64`, whose merge is `if.end198.i.i` again) is
carried to the same head, and the head state the empty edge produces is handed to
the ladder as a run, so the two pieces' fuel adds.

**The empty arm.**  `end176_run_ladder_neg` composes
`NumFastToDouble.end176_run_ladder` (two control steps) with
`NumFastTier3Join.t3_ladder_run_neg`.  The ladder is entered at a **negative**
residual: `%sub200.i.i = -E` for a positive `E`, so its positive loop is entered
at the empty row list and its own `BoundLoop.run_at` charges
`(0 + 1) * 2`, one control step for the join and
`((t3Rows E).length + 1) * 2` for the negative loop.  The composition's fuel is
the sum, `2 + (((0 + 1) * 2) + (1 + (((t3Rows E).length + 1) * 2) + k))`.
`end176_run_ladder_neg_exit` is the same composition with the exit state handed
back, which is the shape the seam past `while.end253.i.i` reads.
`hneg` is not implied by the exit's word: `%sub175.i.i` is the group count's
residual, and the ladder's residual is the fold's own arithmetic, so the sign is
the caller's fact.

**The non-empty arm.**  `end176_step_then` (one step) reaches
`if.then178.i.i`; `numFast_step_ifThen178_jump` (one step) takes it to
`if.end198.i.i`; `NumFastTier3Fold.t3_fold_step` (one step) forms the ladder's
two inputs, so the arm's fuel is `3 + j`.  But the middle piece states only
`∃ t, step ... = .jump t`: the call's answer writes memory and binds no cell, and
the target state is not exposed.  `end176_run_ladder_then` therefore takes that
state as a named hypothesis, `htarget`, whose statement is exactly what
`t3_fold_step` consumes — the fold's pin and the three cells `%add110.i.i`,
`%topn.0711.i.i`, `%top.0709.i.i`.  No lemma is invented for it here.

What such a producer would need: `numFast_ifThen178_denote_some` returns only
`∃ s', denoteCode ... = some s'`.  Returning the state itself — the environment
`(("%107", .int 64 v) :: ("%arrayidx180.i.i", .ptr (p10 + (k.signExtend 64).toNat *
(Ty.int 64).sizeBytes)) :: ("%k168.0.lcssa829.i.i", .int 64 k) :: env)` and the
`stk_mul_u64` answer's memory — makes `numFast_step_ifThen178_jump`'s witness the
fold's entry at `pc := "if.end198.i.i"`, `pre := some "if.then178.i.i"`.  The
fold's three cells are not bound by that block: `if.then178.i.i` binds
`%k168.0.lcssa829.i.i`, `%arrayidx180.i.i` and `%107` and the call binds nothing,
so `%add110.i.i`, `%topn.0711.i.i` and `%top.0709.i.i` are the exit's own cells
carried through the new prefix.  That is a restatement of the two lemmas in
`JsonStage2NumFastCalls`, not a new argument: exposing the state exposes the
pin, and the three lookups are `lookupName_cons_ne` from the caller's `hu`,
`htn` and `ht`.
-/
import LeanLLVM.Refinement.JsonStage2NumFastToDouble
import LeanLLVM.Refinement.JsonStage2NumFastTier3Join

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.NumFastTier1
open LeanLLVM.Refinement.NumFastTier3
open LeanLLVM.Refinement.NumFastTier3Ladder
open LeanLLVM.Refinement.NumFastTier3Rows
open LeanLLVM.Refinement.NumFastTier3Join
open LeanLLVM.StrtodTier3

namespace NumFastToDouble

/-! ### The empty arm: through the fold, into a negative ladder -/

/-- **The exit's run into a negative ladder.**  From `while.end176.i.i` with an
empty residual, the fold's two steps and the ladder's own run reach
`while.end253.i.i`: `2 + (((0 + 1) * 2) + (1 + (((t3Rows E).length + 1) * 2) +
k))` control steps, the exit's prefix plus the ladder's `BoundLoop.run_at`
budgets.  The ladder is entered at `%sub200.i.i = -E`, `hneg`; its
`hpack`/`hstage` are the negative loop's own. -/
theorem end176_run_ladder_neg {calls : Calls} {env : Env} {s : State}
    {k0 : BitVec 32} {n : Nat} {r u re top : BitVec 64}
    (hpc : s.pc = "while.end176.i.i")
    (hn : lookupName env "%n.i539.i.i" = some (.ptr n))
    (hk : lookupName env "%inc12.us.i.i581758.i.i" = some (.int 32 k0))
    (hr : lookupName env "%sub175.i.i" = some (.int 64 r))
    (hu : lookupName env "%add110.i.i" = some (.int 64 u))
    (htn : lookupName env "%topn.0711.i.i" = some (.int 64 re))
    (ht : lookupName env "%top.0709.i.i" = some (.int 64 top))
    (hbit : evalICmp .eq r 0x0#64 = (1 : BitVec 1))
    (E address : Nat) (hE : E ≤ 342) (hpos : 0 < E)
    (hneg : (u - re) + 0x1#64 = BitVec.ofInt 64 (-(E : Int)))
    (hpack : ∀ c, c ≤ (t3Rows E).length →
      ∃ k : Code, t3DivCarried (uitofpBits top.toNat) (t3Rows E) c
        = packMag (.fin k) false ∧ k.IsMag ∧ 0 < k.ticks)
    (hstage : ∀ (env : Env) (s : State) (k : Nat) (d : BitVec 64),
      lookupName env "%e10.2.i.i" = some (.int 64 (BitVec.ofInt 64 (-(k : Int)))) →
      lookupName env "%d201.2.i.i" = some (.float d) →
        lookupName env "@NUMF_EL1_POW10" = some (.ptr address) ∧
        readBytes s.mem (address + min k 22 * 8) 8
          = some (natToBytes (uitofpBits (10 ^ min k 22)).toNat 8))
    {o : Outcome} (kf : Nat)
    (hcont : ∀ (e : State), e.pc = "while.end253.i.i" → t3DivExitWord e →
      runFuel calls kf numFastBody e = some o) :
    runFuel calls (2 + (((0 + 1) * 2) + (1 + (((t3Rows E).length + 1) * 2) + kf)))
      numFastBody (stateAt env s) = some o := by
  have hrun := end176_run_ladder (calls := calls) (env := env) (s := s)
    (k := k0) (n := n) (r := r) (u := u) (re := re) (top := top)
    hpc hn hk hr hu htn ht hbit
  have hd : lookupName
      (NumFastTier3Fold.t3FoldEnv (end176Env env r) u re top.toNat)
      "%conv202.i.i" = some (.float (uitofpBits top.toNat)) :=
    lookupName_cons_self _ _ _
  have he : lookupName
      (NumFastTier3Fold.t3FoldEnv (end176Env env r) u re top.toNat)
      "%sub200.i.i" = some (.int 64 (BitVec.ofInt 64 (-(E : Int)))) := by
    rw [NumFastTier3Fold.t3FoldEnv, lookupName_cons_ne _ _ (by decide),
      lookupName_cons_self, hneg]
  have hL := t3_ladder_run_neg calls (uitofpBits top.toNat) E address hE hpos
    hpack hstage
    (stateAt (NumFastTier3Fold.t3FoldEnv (end176Env env r) u re top.toNat)
      { s with pc := "while.cond203.i.i", pre := some "if.end198.i.i",
               mem := writeBytes s.mem n (natToBytes k0.toNat 4) })
    (by rfl) (by rfl) he hd kf hcont
  exact (hrun (((0 + 1) * 2) + (1 + (((t3Rows E).length + 1) * 2) + kf))).trans hL

/-- **The exit's run into a negative ladder, with its exit state.**  The same
composition as `end176_run_ladder_neg`, handing back the state the ladder leaves
at `while.end253.i.i` and its fuel bound — the seam past the ladder reads that
state, not only the outcome. -/
theorem end176_run_ladder_neg_exit {calls : Calls} {env : Env} {s : State}
    {k0 : BitVec 32} {n : Nat} {r u re top : BitVec 64}
    (hpc : s.pc = "while.end176.i.i")
    (hn : lookupName env "%n.i539.i.i" = some (.ptr n))
    (hk : lookupName env "%inc12.us.i.i581758.i.i" = some (.int 32 k0))
    (hr : lookupName env "%sub175.i.i" = some (.int 64 r))
    (hu : lookupName env "%add110.i.i" = some (.int 64 u))
    (htn : lookupName env "%topn.0711.i.i" = some (.int 64 re))
    (ht : lookupName env "%top.0709.i.i" = some (.int 64 top))
    (hbit : evalICmp .eq r 0x0#64 = (1 : BitVec 1))
    (E address : Nat) (hE : E ≤ 342) (hpos : 0 < E)
    (hneg : (u - re) + 0x1#64 = BitVec.ofInt 64 (-(E : Int)))
    (hpack : ∀ c, c ≤ (t3Rows E).length →
      ∃ k : Code, t3DivCarried (uitofpBits top.toNat) (t3Rows E) c
        = packMag (.fin k) false ∧ k.IsMag ∧ 0 < k.ticks)
    (hstage : ∀ (env : Env) (s : State) (k : Nat) (d : BitVec 64),
      lookupName env "%e10.2.i.i" = some (.int 64 (BitVec.ofInt 64 (-(k : Int)))) →
      lookupName env "%d201.2.i.i" = some (.float d) →
        lookupName env "@NUMF_EL1_POW10" = some (.ptr address) ∧
        readBytes s.mem (address + min k 22 * 8) 8
          = some (natToBytes (uitofpBits (10 ^ min k 22)).toNat 8))
    (kf : Nat) :
    ∃ (e : State) (j : Nat),
      j ≤ 2 + (((0 + 1) * 2) + (1 + (((t3Rows E).length + 1) * 2))) ∧
      e.pc = "while.end253.i.i" ∧ t3DivExitWord e ∧
      runFuel calls (j + kf) numFastBody (stateAt env s)
        = runFuel calls kf numFastBody e := by
  have hrun := end176_run_ladder (calls := calls) (env := env) (s := s)
    (k := k0) (n := n) (r := r) (u := u) (re := re) (top := top)
    hpc hn hk hr hu htn ht hbit
  have hd : lookupName
      (NumFastTier3Fold.t3FoldEnv (end176Env env r) u re top.toNat)
      "%conv202.i.i" = some (.float (uitofpBits top.toNat)) :=
    lookupName_cons_self _ _ _
  have he : lookupName
      (NumFastTier3Fold.t3FoldEnv (end176Env env r) u re top.toNat)
      "%sub200.i.i" = some (.int 64 (BitVec.ofInt 64 (-(E : Int)))) := by
    rw [NumFastTier3Fold.t3FoldEnv, lookupName_cons_ne _ _ (by decide),
      lookupName_cons_self, hneg]
  obtain ⟨e, j, hj, hexit, hword, hE'⟩ := t3_ladder_run_neg_exit calls
    (uitofpBits top.toNat) E address hE hpos hpack hstage
    (stateAt (NumFastTier3Fold.t3FoldEnv (end176Env env r) u re top.toNat)
      { s with pc := "while.cond203.i.i", pre := some "if.end198.i.i",
               mem := writeBytes s.mem n (natToBytes k0.toNat 4) })
    (by rfl) (by rfl) he hd kf
  refine ⟨e, 2 + j, by omega, hexit, hword, ?_⟩
  rw [show 2 + j + kf = 2 + (j + kf) from by omega, hrun (j + kf)]
  exact hE'

/-! ### The non-empty arm: the call's target state is not stated -/

/-- **The exit's run through the big multiply into the ladder's head.**  From
`while.end176.i.i` with a residual group left, `if.then178.i.i`'s `stk_mul_u64`
and `if.end198.i.i`'s fold reach `while.cond203.i.i` in `3 + j` control steps,
leaving the fold's environment at the cells `%add110.i.i`, `%topn.0711.i.i` and
`%top.0709.i.i`.

`htarget` is the fact `numFast_step_ifThen178_jump` does not state: its `∃ t` is
opaque.  It is required here because `t3_fold_step` reads the call target's
environment and pin; the producer is the restatement described at the head of
this module. -/
theorem end176_run_ladder_then
    (epow : Int → Option EPow) {env : Env} {s : State}
    {k0 : BitVec 32} {n : Nat} {r : BitVec 64} {p10 pow : Nat} {v : BitVec 64}
    {env' : Env} {base : State} {u re top : BitVec 64}
    (hpc : s.pc = "while.end176.i.i")
    (hn : lookupName env "%n.i539.i.i" = some (.ptr n))
    (hk : lookupName env "%inc12.us.i.i581758.i.i" = some (.int 32 k0))
    (hr : lookupName env "%sub175.i.i" = some (.int 64 r))
    (hbit : evalICmp .eq r 0x0#64 = (0 : BitVec 1))
    (hpos : (r.signExtend 64).toNat < 2 ^ 63)
    (hg : lookupName env "@NUMF_EL1_P10" = some (.ptr p10))
    (hpow : lookupName env "%pow.i.i" = some (.ptr pow))
    (hread : readBytes (writeBytes s.mem n (natToBytes k0.toNat 4))
      (p10 + (r.signExtend 64).toNat * (Ty.int 64).sizeBytes) 8
      = some (natToBytes v.toNat 8))
    (htarget : ∀ (t : State),
      step (stage2NumFastCalls epow) numFastBody
        (stateAt (end176Env env r)
          { s with mem := writeBytes s.mem n (natToBytes k0.toNat 4),
                   pc := "if.then178.i.i", pre := some "while.end176.i.i" }) = .jump t →
      t = stateAt env'
        { base with pc := "if.end198.i.i", pre := some "if.then178.i.i" } ∧
      lookupName env' "%add110.i.i" = some (.int 64 u) ∧
      lookupName env' "%topn.0711.i.i" = some (.int 64 re) ∧
      lookupName env' "%top.0709.i.i" = some (.int 64 top)) :
    ∀ j, runFuel (stage2NumFastCalls epow) (3 + j) numFastBody (stateAt env s)
      = runFuel (stage2NumFastCalls epow) j numFastBody
          (stateAt (NumFastTier3Fold.t3FoldEnv env' u re top.toNat)
            { base with pc := "while.cond203.i.i", pre := some "if.end198.i.i" }) := by
  intro j
  have hs1 := end176_step_then (calls := stage2NumFastCalls epow)
    (env := env) (s := s) (k := k0) (n := n) (r := r) hpc hn hk hr hbit
  obtain ⟨t, ht⟩ := numFast_step_ifThen178_jump epow
    (env := end176Env env r)
    (s := { s with mem := writeBytes s.mem n (natToBytes k0.toNat 4),
                   pc := "if.then178.i.i", pre := some "while.end176.i.i" })
    (p10 := p10) (pow := pow) (k := r) (v := v) rfl rfl
    (end176Env_lookup hr (by decide))
    (end176Env_lookup hg (by decide))
    hpos hread
    (end176Env_lookup hpow (by decide))
  obtain ⟨htgt, hu', htn', ht'⟩ := htarget t ht
  have hs3 := NumFastTier3Fold.t3_fold_step (calls := stage2NumFastCalls epow)
    (env := env')
    (s := { base with pc := "if.end198.i.i", pre := some "if.then178.i.i" })
    (u := u) (re := re) (top := top) rfl hu' htn' ht'
  rw [show 3 + j = 1 + (1 + (1 + j)) from by omega,
    runFuel_jump_prefix hs1 (1 + (1 + j)),
    runFuel_jump_prefix ht (1 + j), htgt,
    runFuel_jump_prefix hs3 j]

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.NumFastToDouble.end176_run_ladder_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms end176_run_ladder_neg

/-- info: 'LeanLLVM.Refinement.NumFastToDouble.end176_run_ladder_neg_exit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms end176_run_ladder_neg_exit

/-- info: 'LeanLLVM.Refinement.NumFastToDouble.end176_run_ladder_then' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms end176_run_ladder_then

end NumFastToDouble

end LeanLLVM.Refinement
