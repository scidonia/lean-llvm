/-
The loop's step at the dispatch's three outcomes.

`WalkDispatchThree` (`JsonStage2WalkAssembly`) states a dispatch as one of three
outcomes — `cont`: a counted segment to the merge with the selected index below the
stream; `finish`: the same at the terminal index; `refuse`: a counted segment to the
refusal finalisation with the error position.  It had no consumer: the loop's
endpoint (`walkLoopStep_of_dispatch_exit`) split on `C.k + 1 < G.nep` and selected a
revolution in the first case, so the split was on the entry index *before* the
dispatch ran rather than on what the dispatch did.  This module consumes the three
outcomes instead.

* **`WalkLoopStepThree`** is the loop's step at those outcomes, and the mapping is
  `cont` → the revolution (a segment back to the head, the index advanced, the
  potential spent) and `finish`/`refuse` → the terminal branch (the dispatch's own
  segment, then the terminal run from the state it reaches).  The terminal branch's
  verdict is existential.  `finish` is *entry-stream exhaustion at the merge*, not
  parser acceptance: the merge's index reaching the stream's end says no entry is
  left, and the finalisation that follows still decides between acceptance and
  refusal — an unclosed container or an unfinished root is refused there.  So the
  branch states `∃ v` and never `v = 1`.
* **`WalkTargetRun`** is the terminal run at the dispatch's target: the state's own
  count, its own verdict, and the two terminal steps.  A single fixed verdict is not
  merely stronger than what the body supports, it is false of it.  At `cleanup478.i`
  the accepted route returns `1` (`walkExitTailRun_exit`) and the two refusal routes
  return `0` (`walkExitTailRun_refuse`, `walkExitTailRun_refuse488`), and all three
  are proved from states `hlastMergeF f` builds at that block under the same
  invariant — which is exactly what `ExitTail` records.  So the terminal branch
  carries the result each state reaches, and no uniformity across states is assumed
  here.
* **`walkLoopFinishesThree`** and **`walkCompletes_of_loop_three`** are the
  consumers: the completion is the same kind of fact `walkCompletes_of_loop` states —
  a return, at a verdict the walk does not fix — reached from the three outcomes
  rather than from the index split.

`WalkDispatchOutcome.cont`'s fields are `WalkDispatch`'s, field for field, so the
revolution's composition is `WalkDispatch.revolution`'s, repeated here because that
lemma takes a `WalkDispatch` — a statement about *every* head state — and one state's
outcome cannot supply it.  The three-outcome premise is what makes that a repetition
of a composition rather than of a premise.

The one fact the `finish` branch needs beside its own outcome is the merge's `%nep`
value: `WalkInv` does not carry that register, so the layer supplies its value at the
states it is read at, as the last entry's bundle does (`HlastFacts.hnepM`, with the
count `BitVec.ofNat 64 G.nep`).  `walkLoopStepThree_of_dispatchThree`'s `hnepBound`
is that supply in the only form the branch uses: the value is no larger than the
stream.
-/
import LeanLLVM.Refinement.JsonStage2WalkAssembly
import LeanLLVM.Refinement.JsonStage2WalkExitProducer

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The terminal run at a dispatch's target

The dispatch's terminal outcomes both end at a block of the walk's finalisation —
`cleanup478.i`, the merge whose false edge leaves the loop, or `if.then`, the refusal
copy the two refusal routes and the merge's refused arm both enter.  What the loop's
step needs from such a state is a counted run to a return, and the *verdict that state
reaches*: `if.end` returns the walk's bit, `1` on the accepted route and `0` on the
refusal ones.  Both are results of the same block, so the verdict is existential here
rather than a parameter. -/

/-- **A terminal run from a state**: `q` steps reach a pre-return state, and the two
terminal steps follow — one jump and the return, at the state's own verdict.  The
count is inside the finalisation allowance less the seed's three steps and the two
terminal ones (`walkExitFits`), which is the `27` `ExitTail` states its tails at. -/
def WalkTargetRun (calls : Calls) (s : State) : Prop :=
  ∃ (q : Nat) (v : Value) (s1 s2 sret : State),
    (∀ n, runFuel calls (q + n) stage2Body s = runFuel calls n stage2Body s1) ∧
    q + 2 ≤ 27 ∧
    step calls stage2Body s1 = .jump s2 ∧
    step calls stage2Body s2 = .ret (some v) sret

/-- **The refusal target's terminal run, from its two blocks.**  A state at the
refusal copy reaches a return in the two terminal steps alone (`q = 0`): the copy's own
step jumps to `if.end` (`walkIfThen_step`) and `if.end` returns
(`walkIfEnd_step`) at this arm's `phi` value, the literal zero
(`walkIfEnd_refusal_phi`).  So the refusal premise of
`walkLoopStepThree_of_dispatchThree` is a fact about `if.then`'s two blocks and
nothing about the dispatch. -/
theorem WalkTargetRun.ifThen {sub : Calls} {s s₁ : State} {pe pz ps : Nat} {v : BitVec 64}
    (hpc : s.pc = "if.then")
    (hden : denoteCode (stage2Calls sub) walkIfThenBlock.instrs s = some s₁)
    (hpc₁ : s₁.pc = s.pc)
    (he : lookupName s₁.env "%e" = some (.ptr pe))
    (hz : lookupName s₁.env "%z" = some (.ptr pz))
    (hs : lookupName s₁.env "%s" = some (.ptr ps))
    (hv : v = BitVec.ofNat 64 0) :
    WalkTargetRun (stage2Calls sub) s := by
  refine ⟨0, .int 64 v, s, { s₁ with pc := "if.end", pre := some s.pc },
    stateAt (("%tobool.not151", .int 64 (BitVec.ofNat 64 0)) ::
      ({ s₁ with pc := "if.end", pre := some s.pc }).env)
      { s₁ with pc := "if.end", pre := some s.pc }, ?_, ?_, ?_, ?_⟩
  · intro n
    simp only [Nat.zero_add]
  · decide
  · exact walkIfThen_step s hpc hden hpc₁
  · exact walkIfEnd_step { s₁ with pc := "if.end", pre := some s.pc } rfl he hz hs rfl
      (by rw [hpc]; exact walkIfEnd_refusal_phi) hv.symm

/-- **The merge target's terminal run is `ExitTail`.**  `ExitTail` states the same
counted run at the same allowance, with the verdict as a parameter rather than an
existential; its three producers (`walkExitTailRun_exit`, `walkExitTailRun_refuse`,
`walkExitTailRun_refuse488`) are the accepted route's and the two refusal routes' tails
from `cleanup478.i`.  So the merge premise of
`walkLoopStepThree_of_dispatchThree` is the statement the layer's tails already prove,
read at one state instead of at every last-entry head. -/
theorem WalkTargetRun.ofExitTail {calls : Calls} {s : State} {v : Value}
    (h : ExitTail calls s v) : WalkTargetRun calls s := by
  obtain ⟨q, s1, s2, sret, hrun, hq, hjump, hret⟩ := h
  exact ⟨q, v, s1, s2, sret, hrun, hq, hjump, hret⟩

/-! ### Two facts about the potential the terminal branches read -/

/-- **The entry stream's end is position zero.**  Past the last entry the lane list has
no entry at all and `entryPos` reads `0`.  The `finish` outcome's index is exactly the
stream's end (`WalkDispatchOutcome.finish`'s `hterm`), so the entry credit it consumed
is `32 · (nep - C.k)` with no byte term, and this is what says so. -/
theorem walkEntryPos_at_nep {m0 : Mem} (G : WalkGeom m0) : entryPos G G.nep = 0 := by
  have hlen : G.ent.length = G.nep := by
    rw [← readLanes32_length m0 G.ep G.nep G.ent G.entries]
  have hnone : G.ent[G.nep]? = none := List.getElem?_eq_none (by omega)
  simp only [entryPos, List.getD_eq_getElem?_getD, hnone, Option.getD_none]

/-- **The `finish` outcome's credit is inside the potential.**  Its price is stated
against `32 · Δk + 8 · ΔA` at the index the merge selected, and the potential is the
same shape at the stream's end.  An index at the stream's end and one before it are
the two cases: before it the positions advance with the index
(`entryPos_mono`), at it the byte term is zero (`walkEntryPos_at_nep`).

The conclusion is the credit form and not the potential's fold: a hypothesis that
`C.k ≤ k2` is what the outcome's own fields give in the `cont` branch and not in
`finish`'s, so the branch splits on it and the negative case is closed by the price
itself — at an index below the head's the credit is zero, which `p + 2 ≤ 0` denies. -/
theorem walkFinishCredit_le {m0 : Mem} (G : WalkGeom m0) {C : WalkCarry G} {k2 : Nat}
    (hk : C.k < G.nep) (hkm : C.k ≤ k2) (hk2 : k2 ≤ G.nep) :
    stage2EntryAllowance * (k2 - C.k) +
      stage2ByteAllowance * (entryPos G k2 - entryPos G C.k) ≤ walkPotential G C := by
  rcases Nat.lt_or_eq_of_le hk2 with hlt | heq
  · have hmono := entryPos_mono G hkm hlt
    have hA : entryPos G C.k ≤ G.n := le_of_lt (entryPos_lt G hk)
    have hA2 : entryPos G k2 ≤ G.n := le_of_lt (entryPos_lt G hlt)
    simp only [walkPotential, stage2EntryAllowance, stage2ByteAllowance]
    omega
  · subst heq
    rw [walkEntryPos_at_nep G]
    simp only [Nat.zero_sub, Nat.mul_zero, walkPotential, stage2EntryAllowance,
      stage2ByteAllowance]
    omega

/-- **A segment followed by a counted run is one at the sum's count.**  The step's
terminal branches are a dispatch's segment and then the target state's own run, and
this is the prefix arithmetic they share. -/
theorem WalkSegment.andRun {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s s₁ : State} {Cd : WalkCarry G} {sd : State} {p q : Nat}
    (hseg : WalkSegment calls G C s Cd sd p)
    (hrun : ∀ n, runFuel calls (q + n) stage2Body sd = runFuel calls n stage2Body s₁) :
    ∀ n, runFuel calls (p + q + n) stage2Body s = runFuel calls n stage2Body s₁ := by
  intro n
  rw [show p + q + n = p + (q + n) from by omega, hseg.run (q + n), hrun n]

/-! ### The loop's step at the three outcomes

One predicate, and the branch a dispatch selects is its outcome rather than the entry
index: `cont` is the revolution, `finish` and `refuse` are the terminal branch.  The
terminal branch's bound is the same credit-plus-allowance `WalkLoopStep` states, and
its verdict is existential for the reason `WalkTargetRun` records. -/

/-- **The loop's next step, stated at the dispatch's three outcomes**: at the head,
with the invariant and an entry left, either one revolution back to the head with the
potential spent, or the loop's terminal run at a verdict the walk reaches and does not
fix.

The terminal disjunct is the dispatch's own segment (inside the credit it consumed)
followed by the state's terminal run (`WalkTargetRun`, inside the finalisation
allowance), so the two dispositions `WalkDispatchOutcome` names beside `cont` — the
terminal index at the merge, and the refusal before it — both land here, each at its
own verdict. -/
def WalkLoopStepThree (calls : Calls) {m0 : Mem} (G : WalkGeom m0) (F : Nat) : Prop :=
  ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead → C.k < G.nep →
    (∃ (C' : WalkCarry G) (s' : State) (p : Nat),
        WalkSegment calls G C s C' s' p ∧ C'.block = walkLoopHead ∧
        C.k < C'.k ∧ C'.k < G.nep ∧ p + walkPotential G C' ≤ walkPotential G C)
    ∨ (∃ (q : Nat) (v : Value) (s1 s2 sret : State),
        q ≤ walkPotential G C + F ∧
        (∀ n, runFuel calls (q + n) stage2Body s = runFuel calls n stage2Body s1) ∧
        step calls stage2Body s1 = .jump s2 ∧
        step calls stage2Body s2 = .ret (some v) sret)

/-! ### A revolution, from the `cont` outcome's own fields

`WalkDispatch.revolution` composes the merge's step and the header's pass on top of
the dispatch's segment, and it takes a `WalkDispatch`, whose statement binds every
loop-head state at once.  The `cont` outcome carries that statement's fields at one
state, so the composition is restated here at them rather than assumed: everything
`walkBack_step_at` and `whileBody_step` read is a field of the outcome, and the price
is its `hprice`. -/

/-- **One revolution from a `cont` outcome's evidence.**  The segment to
`cleanup478.i`, the merge's step at the selected `phi` values, and the header's pass;
the price is the dispatch's plus the two steps, and the potential falls by the
dispatch's spending because only the index has moved. -/
theorem walkContRevolution {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} {Cd : WalkCarry G} {sd : State}
    {p spv k2 : Nat} {prev : String} {spOp kOp : Operand} {nepv : BitVec 64}
    (hseg : WalkSegment calls G C s Cd sd p)
    (hblock : Cd.block = "cleanup478.i") (hkC : Cd.k = C.k)
    (hpre : sd.pre = some prev)
    (hsp : phiIncoming prev cleanupSpIncoming = some spOp)
    (hspv : evalOperand sd spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hkOp : phiIncoming prev cleanupKIncoming = some kOp)
    (hk2 : evalOperand sd kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    (hnepv : lookupName sd.env "%nep" = some (.int 64 nepv))
    (hbelow : k2 < nepv.toNat) (hnep : k2 < G.nep) (hadvance : C.k < k2)
    (hspcap : spv ≤ stage2StackExtent) (hspw : spv ≤ Cd.wlen)
    (hprice : p + 2 ≤ stage2EntryAllowance * (k2 - C.k) +
      stage2ByteAllowance * (entryPos G k2 - entryPos G C.k)) :
    ∃ (C' : WalkCarry G) (s' : State) (p' : Nat),
      WalkSegment calls G C s C' s' p' ∧ C'.block = walkLoopHead ∧
      C.k < C'.k ∧ C'.k < G.nep ∧ p' + walkPotential G C' ≤ walkPotential G C := by
  obtain ⟨hstepB, hInvB, hrunB⟩ :=
    walkBack_step_at G Cd sd hseg.inv' hblock hpre hsp hspv hkOp hk2 hnepv (by omega)
  obtain ⟨s', hstepH, hInvH, _hmono, hrunH⟩ :=
    whileBody_step (G := G)
      (C := { Cd with block := "while.body.i", inner := walkInnerCap G })
      (s := cleanup478Out sd spv k2) hInvB rfl (cleanup478Out_pre) (cleanup478Out_k)
      (cleanup478Out_sp) (by rw [hkC]; exact hadvance) hnep hspcap hspw
  let C' : WalkCarry G :=
    { { Cd with block := "while.body.i", inner := walkInnerCap G } with
        block := walkLoopHead, k := k2, sp := spv }
  refine ⟨C', s', p + 1 + 1, ?_, rfl, ?_, ?_, ?_⟩
  · refine ⟨fun n => ?_, hInvH⟩
    rw [show p + 1 + 1 + n = p + (1 + (1 + n)) from by omega,
      hseg.run (1 + (1 + n)), hrunB (1 + n), hrunH n]
  · show C.k < k2
    exact hadvance
  · show k2 < G.nep
    exact hnep
  · have hmono : entryPos G C.k ≤ entryPos G k2 :=
      entryPos_mono G (le_of_lt hadvance) hnep
    have hp : entryPos G C.k ≤ G.n := le_of_lt (entryPos_lt G (by omega))
    have hp' : entryPos G k2 ≤ G.n := le_of_lt (entryPos_lt G hnep)
    have hspend := walkPotential_spend (G := G) (C := C) (C' := C') (p := p + 2)
      (le_of_lt hadvance) (le_of_lt hnep) hp hp' hmono hprice
    simpa using hspend

/-! ### The step, from the three-outcome premise -/

/-- **The loop's step, from `WalkDispatchThree`.**  No `WalkDispatch` and no split on
`C.k + 1 < G.nep`: the outcome the dispatch reaches decides the branch.

| outcome | branch |
|---|---|
| `cont` | the revolution, from the segment and the merge's `phi` facts it carries |
| `finish` | the terminal branch: its segment, then the merge state's terminal run |
| `refuse` | the terminal branch: its segment, then the refusal state's terminal run |

The two terminal branches spend the dispatch's own price (`hprice`) and the terminal
run's allowance, and both are inside `walkPotential G C + F` at `F ≥ 27`.  Neither
asserts acceptance, and neither fixes the verdict: the `finish` branch's price uses
`hnepBound` because `WalkInv` does not carry `%nep`, and states nothing else about
what the finalisation decides.

`htail` is weaker than the `WalkExit` the index split consumed, in three ways: its
verdict is the state's rather than one shared by every last-entry head state, its run
is read at the dispatch's target rather than through the head path, and it asks
nothing of `%z`/`%s` at the head (the two registers the copy reads are the terminal
states' own).  `refuse`'s error bound (`Cd.eoff ≤ G.n`) is not read either: its price
is stated against the entry's whole remaining credit, so the position it stored is
not what bounds the tail. -/
theorem walkLoopStepThree_of_dispatchThree {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {F : Nat} (hF : 27 ≤ F)
    (hthree : WalkDispatchThree calls G)
    (htail : ∀ (Cd : WalkCarry G) (sd : State), WalkInv G Cd sd →
      (Cd.block = "cleanup478.i" ∨ Cd.block = "if.then") → WalkTargetRun calls sd)
    (hnepBound : ∀ (Cd : WalkCarry G) (sd : State) (nepv : BitVec 64),
      WalkInv G Cd sd → Cd.block = "cleanup478.i" →
      lookupName sd.env "%nep" = some (.int 64 nepv) → nepv.toNat ≤ G.nep) :
    WalkLoopStepThree calls G F := by
  intro C s hInv hhead hk
  rcases hthree C s hInv hhead with
    ⟨Cd, sd, p, spv, k2, prev, spOp, kOp, nepv, hseg, hblock, hkc, hpre, hsp, hspv,
      hkOp, hk2, hnepv, hbelow, hnep, hadvance, hspcap, hspw, hprice⟩ |
    ⟨Cd, sd, p, k2, prev, kOp, nepv, hseg, hblock, hpre, hkOp, hk2, hnepv, hterm,
      hprice⟩ |
    ⟨Cd, sd, p, hseg, hblock, _herr, hprice⟩
  · exact Or.inl (walkContRevolution hseg hblock hkc hpre hsp hspv hkOp hk2 hnepv
      hbelow hnep hadvance hspcap hspw hprice)
  · obtain ⟨q₂, v, s1, s2, sret, hrun₂, hq₂, hjump, hret⟩ :=
      htail Cd sd hseg.inv' (Or.inl hblock)
    refine Or.inr ⟨p + q₂, v, s1, s2, sret, ?_, hseg.andRun hrun₂, hjump, hret⟩
    · have hk2nep : k2 ≤ G.nep := by
        have := hnepBound Cd sd nepv hseg.inv' hblock hnepv
        omega
      have hcredit : stage2EntryAllowance * (k2 - C.k) +
          stage2ByteAllowance * (entryPos G k2 - entryPos G C.k) ≤ walkPotential G C := by
        by_cases hkm : C.k ≤ k2
        · exact walkFinishCredit_le G hk hkm hk2nep
        · exfalso
          have hmono : entryPos G k2 ≤ entryPos G C.k := entryPos_mono G (by omega) hk
          simp only [stage2EntryAllowance, stage2ByteAllowance] at hprice
          omega
      simp only [walkPotential, stage2EntryAllowance, stage2ByteAllowance] at hcredit hprice ⊢
      omega
  · obtain ⟨q₂, v, s1, s2, sret, hrun₂, hq₂, hjump, hret⟩ :=
      htail Cd sd hseg.inv' (Or.inr hblock)
    refine Or.inr ⟨p + q₂, v, s1, s2, sret, ?_, hseg.andRun hrun₂, hjump, hret⟩
    · simp only [walkPotential, stage2EntryAllowance, stage2ByteAllowance] at hprice hq₂ ⊢
      omega

/-! ### Its consumers

The step's completion is the same well-founded recursion `walkLoopFinishes` runs —
strong recursion on `nep - C.k`, which a revolution shortens — with the verdict
threaded through instead of fixed.  The completion at the budget is the fact
`walkCompletes_of_loop` states: a return, whose value the walk does not fix, inside
`walkPotential` plus the finalisation allowance. -/

/-- **The loop finishes, and its run is inside the potential.**  One verdict for the
whole run, carried from the terminal state the recursion reaches. -/
theorem walkLoopFinishesThree {calls : Calls} {m0 : Mem} {G : WalkGeom m0} {F : Nat}
    (hstep : WalkLoopStepThree calls G F) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead) (hk : C.k < G.nep) :
    ∃ (q : Nat) (v : Value) (s1 s2 sret : State),
      (∀ n, runFuel calls (q + n) stage2Body s = runFuel calls n stage2Body s1) ∧
      step calls stage2Body s1 = .jump s2 ∧ step calls stage2Body s2 = .ret (some v) sret ∧
      q ≤ walkPotential G C + F := by
  have key : ∀ (m : Nat), ∀ (C : WalkCarry G) (s : State), G.nep - C.k = m →
      WalkInv G C s → C.block = walkLoopHead → C.k < G.nep →
      ∃ (q : Nat) (v : Value) (s1 s2 sret : State),
        (∀ n, runFuel calls (q + n) stage2Body s = runFuel calls n stage2Body s1) ∧
        step calls stage2Body s1 = .jump s2 ∧ step calls stage2Body s2 = .ret (some v) sret ∧
        q ≤ walkPotential G C + F := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro C s hm hInv hhead hk
        rcases hstep C s hInv hhead hk with
          ⟨C', s', p, hseg, hhead', hklt, hklt', hpot⟩ |
          ⟨q, v, s1, s2, sret, hq, hrun, hstep1, hret⟩
        · obtain ⟨q, v, t1, t2, tret, hrun', hs1, hs2, hq'⟩ :=
            ih (G.nep - C'.k) (by omega) C' s' rfl hseg.inv' hhead' hklt'
          exact ⟨p + q, v, t1, t2, tret, hseg.andRun hrun', hs1, hs2, by omega⟩
        · exact ⟨q, v, s1, s2, sret, hrun, hstep1, hret, by omega⟩
  exact key (G.nep - C.k) C s rfl hInv hhead hk

/-- **The completion at the potential's budget**: the seed's `j` steps, the loop's run
and the returning step, at whatever verdict the terminal state reaches. -/
theorem walkCompletes_of_loop_three {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s sEntry : State} {j F : Nat}
    (hseed : ∀ n, runFuel calls (j + n) stage2Body sEntry = runFuel calls n stage2Body s)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead) (hk : C.k < G.nep)
    (hstep : WalkLoopStepThree calls G F) (hF : j + F + 2 ≤ stage2FinalisationAllowance) :
    ∃ (v' : Option Value) (m : Mem),
      runFuel calls (walkPotential G C + stage2FinalisationAllowance) stage2Body sEntry =
        some (.ret v' m) := by
  obtain ⟨q, v, s1, s2, sret, hrun, hstep1, hret, hq⟩ :=
    walkLoopFinishesThree hstep C s hInv hhead hk
  have hfin : runFuel calls (q + 2) stage2Body s = some (.ret (some v) sret.mem) := by
    rw [hrun 2]
    simp only [runFuel, hstep1, hret]
  have htotal : runFuel calls (j + (q + 2)) stage2Body sEntry =
      some (.ret (some v) sret.mem) := by
    rw [hseed (q + 2)]
    exact hfin
  have hle : j + (q + 2) ≤ walkPotential G C + stage2FinalisationAllowance := by omega
  exact ⟨some v, sret.mem, runFuel_mono_le hle htotal⟩

/-- **The completion at the record's two counted terms**: the potential is inside
`32 * nep + 8 * n` at the invariant, so the walk completes there plus the finalisation
allowance — `stage2Budget` without the escape-position term, at the verdict the walk
reaches rather than a fixed one. -/
theorem walkCompletes_of_loop_three_budget {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s sEntry : State} {j F : Nat}
    (hseed : ∀ n, runFuel calls (j + n) stage2Body sEntry = runFuel calls n stage2Body s)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead) (hk : C.k < G.nep)
    (hstep : WalkLoopStepThree calls G F) (hF : j + F + 2 ≤ stage2FinalisationAllowance) :
    ∃ (v' : Option Value) (m : Mem),
      runFuel calls (32 * G.nep + 8 * G.n + 32) stage2Body sEntry = some (.ret v' m) := by
  obtain ⟨v', m, hrun⟩ := walkCompletes_of_loop_three hseed hInv hhead hk hstep hF
  have hle : walkPotential G C + stage2FinalisationAllowance ≤ 32 * G.nep + 8 * G.n + 32 := by
    have h := walkPotential_le G C hInv
    simp only [stage2EntryAllowance, stage2ByteAllowance, stage2FinalisationAllowance] at h ⊢
    omega
  exact ⟨v', m, runFuel_mono_le hle hrun⟩

/-! ### Axiom footprints -/

#print axioms LeanLLVM.Refinement.WalkScope.WalkTargetRun.ifThen
#print axioms LeanLLVM.Refinement.WalkScope.WalkTargetRun.ofExitTail
#print axioms LeanLLVM.Refinement.WalkScope.WalkSegment.andRun
#print axioms LeanLLVM.Refinement.WalkScope.walkEntryPos_at_nep
#print axioms LeanLLVM.Refinement.WalkScope.walkFinishCredit_le
#print axioms LeanLLVM.Refinement.WalkScope.walkContRevolution
#print axioms LeanLLVM.Refinement.WalkScope.walkLoopStepThree_of_dispatchThree
#print axioms LeanLLVM.Refinement.WalkScope.walkLoopFinishesThree
#print axioms LeanLLVM.Refinement.WalkScope.walkCompletes_of_loop_three
#print axioms LeanLLVM.Refinement.WalkScope.walkCompletes_of_loop_three_budget

end WalkScope

end LeanLLVM.Refinement
