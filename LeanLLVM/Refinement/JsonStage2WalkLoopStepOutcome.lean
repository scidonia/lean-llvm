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

* **`walkLoopStepThree_of_dispatchThree`** is the rule, and it produces
  `WalkLoopStepThree` (`JsonStage2WalkTraverse`, where the loop step and its
  completion live).  The mapping is `cont` → the revolution (a segment back to the
  head, the index advanced, the potential spent) and `finish`/`refuse` → the terminal
  branch (the dispatch's own segment, then the terminal run from the state it
  reaches, with the record's boundary at the memory it returns).  `finish` is
  *entry-stream exhaustion at the merge*, not parser
  acceptance: the merge's index reaching the stream's end says no entry is left, and
  the finalisation that follows still decides between acceptance and refusal — an
  unclosed container or an unfinished root is refused there.  So the terminal branch
  states `∃ v` and never `v = 1`.
* **`WalkTargetPost`** (`JsonStage2WalkTraverse`) is the terminal vocabulary the
  branch carries: a count, the verdict, the *returned memory*, and `stage2Boundary`
  there.  `WalkTargetRun` is the same run without the memory, and it is retained
  rather than consumed: `WalkLoopStepThree`'s terminal disjunct is the post, because
  the record's post is stated at the memory the run returns and `WalkTargetRun` is
  existential in it.  What `WalkTargetRun` still states is the one fact that decided
  the vocabulary's shape — a single fixed verdict is not merely stronger than what the
  body supports, it is false of it.  At `cleanup478.i`
  the accepted route returns `1` (`walkExitTailRun_exit`) and the two refusal routes
  return `0` (`walkExitTailRun_refuse`, `walkExitTailRun_refuse488`), and all three
  are proved from states `hlastMergeF f` builds at that block under the same
  invariant — which is exactly what `ExitTail` records, and why `ExitTail` supplies
  this predicate (`WalkTargetRun.ofExitTail`).  So the verdict is existential here
  too, and no uniformity across states is assumed.

**Its producer, and what its premise can carry.**  `walkLoopStepThree_of_dispatchResult`
(`JsonStage2WalkDispatchThreeOfRun`) is the rule the layer applies; it is stated
directly on `WalkDispatchResult`, because the `finish` outcome's data is what the
merge's `phi` cells are and `WalkDispatchOutcome.finish` does not carry the depth
operand's value, which decides the accept/refuse split at `if.then485.i`.  This rule's
own `htail` is the per-state form, so it is the *statement* of the terminal branch and
not the layer's supply: a per-state post at `cleanup478.i` is not derivable from
`WalkInv` alone (the merge's `phi` cells are the state's `pre` and its registers), which
is why `WalkDispatchResult`'s arm is where the composition happens.

**What this rule supersedes, and why that is a retirement rather than a tidy-up.**  The
loop's endpoint used to take `WalkExit` (`JsonStage2WalkAssembly`), whose producer
composes the last entry's head path with one of three tails
(`walkExit_ofLastFacts`/`walkExit_at_stage2Calls`, `JsonStage2WalkExitProducer`).
`WalkExit` fixes one verdict `v` for *every* last-entry head state, and the three tails
it consumes do not agree: from `cleanup478.i` the accepted route returns `1`
(`walkExitTailRun_exit`) and the two refusal routes return `0` (`walkExitTailRun_refuse`,
`walkExitTailRun_refuse488`), all three proved from states built at that block under the
same invariant.  So the old premise is over-strong at states the body has — one verdict
cannot cover them — and the route is retired rather than tidied.

The switch, in the order it is done: the loop's step becomes `WalkLoopStepThree`
(`JsonStage2WalkTraverse`, whose `walkLoopFinishesThree`, `walkCompletes_of_loop` and
`walkCompletes_of_loop_budget` keep their conclusions); `walkLoopStep_of_staging`'s
premise becomes this rule, with `WalkLoopEnd`'s single tail restated as the two terminal
blocks' *words* (`WalkMergeWords`, `WalkRefuseWords`) beside the merge's `%nep` bound
(`JsonStage2WalkPremisesOfStaging`), from which `WalkLoopEnd.merge`/`.refuse` produce the
post; `WalkHeadPtrs` goes, because the copy's pointer
registers are the terminal states' own; and `walkLoopStep_of_dispatch_exit` is deleted
with the statement it produced.  The exit predicate and its two producers
(`WalkExit`, `walkExit_ofLastFacts`, `walkExit_at_stage2Calls`) were the old route's
last pieces; they are deleted too, since nothing consumed them.  `ExitTail` survives
that deletion: it is this predicate's merge-side supply (`WalkTargetRun.ofExitTail`),
and its three producers are the record that one verdict cannot cover the last-entry
states.

**Its producer.**  `WalkDispatchThree` cannot be produced by testing `C.k + 1 < G.nep`:
that test is true at a standalone string (`C.k = 0`, `G.nep = 2`) while the merge's index
is `2`, the stream's end, so the outcome there is `finish` and an index split has no route
to it.  `WalkDispatchResult` (`JsonStage2WalkDispatchThreeOfRun`) states the dispatch's
actual result — a counted segment classified by the block it reached — and
`WalkDispatchThree.ofResult` produces this predicate from it, with
`walkLoopStepThree_of_dispatchResult` as the composition straight to the loop's step.

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
terminal ones (`walkExitFits`), which is the `27` `ExitTail` states its tails at.

**It is not the loop's terminal route any more.**  `WalkLoopStepThree`'s terminal
disjunct is `WalkTargetPost`, which carries the *returned memory* beside the run — the
record's post is `stage2Boundary` there, and this predicate is existential in the
memory.  What remains here is the vocabulary `JsonStage2WalkExitProducer`'s three tails
are stated at (`ExitTail`) and the bridge from it (`WalkTargetRun.ofExitTail`), and the
fact the vocabulary records: one verdict cannot cover the finalisation's routes. -/
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
(`walkIfEnd_refusal_phi`).  So this is a fact about `if.then`'s two blocks and
nothing about the dispatch.  (The loop's post names the same two steps at the returned
memory: `walkFinishPost_copy`, `JsonStage2WalkTargetPost`.) -/
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

/-- **The merge target's terminal run is `ExitTail`.**  `ExitTail` states a counted run
at the same allowance, with the verdict as a parameter rather than an existential; its
three producers (`walkExitTailRun_exit`, `walkExitTailRun_refuse`,
`walkExitTailRun_refuse488`) are the accepted route's and the two refusal routes' tails
from `cleanup478.i`.  This is the bridge between the two terminal vocabularies, kept
because it is what states that the tails are terminal runs; the loop's branch reads
`WalkTargetPost` instead, which is this run's memory named. -/
theorem WalkTargetRun.ofExitTail {calls : Calls} {s : State} {v : Value}
    (h : ExitTail calls s v) : WalkTargetRun calls s := by
  obtain ⟨q, s1, s2, sret, hrun, hq, hjump, hret⟩ := h
  exact ⟨q, v, s1, s2, sret, hrun, hq, hjump, hret⟩

/-! ### Two facts about the potential the terminal branches read -/

/-- **The entry stream's end is position zero.**  Past the last entry the lane list has
no entry at all and `entryPos` reads `0`.  This is a fact about the *stream*, not about
the credit: the terminal outcomes' byte term is read at `boundary`, which is `G.n` there
(`boundary_nep`), and it is the `entryPos` spelling that this zeroes — which is why a
terminal price stated through `entryPos` charges nothing for the document the walk has
left. -/
theorem walkEntryPos_at_nep {m0 : Mem} (G : WalkGeom m0) : entryPos G G.nep = 0 := by
  have hlen : G.ent.length = G.nep := by
    rw [← readLanes32_length m0 G.ep G.nep G.ent G.entries]
  have hnone : G.ent[G.nep]? = none := List.getElem?_eq_none (by omega)
  simp only [entryPos, List.getD_eq_getElem?_getD, hnone, Option.getD_none]

/-- **The `entryPos` spelling of the terminal credit is inside the potential.**  This is
the form the `merge` arm states (`JsonStage2WalkDispatchThreeOfRun`), and it is what its
`finish` case reads: `32 · Δk + 8 · ΔA` at the index the merge selected, against the
potential at the same shape.  An index at the stream's end and one before it are the two
cases: before it the positions advance with the index (`entryPos_mono`), at it the byte
term is zero (`walkEntryPos_at_nep`).  The `finish` *outcome* carries the boundary
spelling instead, whose credit lemma is `walkFinishCreditBoundary_le`.

The conclusion is the credit form and not the potential's fold: a hypothesis that
`C.k ≤ k2` is what the `merge` arm's own fields give, so the branch splits on it and the
negative case is closed by the price itself — at an index below the head's the credit is
zero, which `p + 2 ≤ 0` denies. -/
theorem walkFinishCredit_le {m0 : Mem} (G : WalkGeom m0) {C : WalkCarry G} {k2 : Nat}
    (hk : C.k < G.nep) (hkm : C.k ≤ k2) (hk2 : k2 ≤ G.nep) :
    stage2EntryAllowance * (k2 - C.k) +
      stage2ByteAllowance * (entryPos G k2 - entryPos G C.k) ≤ walkPotential G C := by
  rcases Nat.lt_or_eq_of_le hk2 with hlt | heq
  · have hmono := entryPos_mono G hkm hlt
    have hA : entryPos G C.k ≤ G.n := le_of_lt (entryPos_lt G hk)
    have hA2 : entryPos G k2 ≤ G.n := le_of_lt (entryPos_lt G hlt)
    simp only [walkPotential, boundary_eq_entryPos G hk, stage2EntryAllowance,
      stage2ByteAllowance]
    omega
  · subst heq
    rw [walkEntryPos_at_nep G]
    simp only [Nat.zero_sub, Nat.mul_zero, walkPotential, boundary_eq_entryPos G hk,
      stage2EntryAllowance, stage2ByteAllowance]
    omega

/-- **The `finish` outcome's credit is inside the potential, read at the boundary.**  Its
price is `32·(k2 - C.k) + 8·(boundary G k2 - boundary G C.k)` — the entries consumed and
the document bytes between the two indices, the latter read at the credit boundary rather
than through `entryPos`.  At `k2 ≤ G.nep` the boundary at `k2` is at most the document's
length (`boundary_le`) and the boundary at `C.k` is the entry's position, so the whole is
at most the potential's entry and byte terms.  No case split on the index: the two terms
move monotonically and the byte term needs only the length's bound. -/
theorem walkFinishCreditBoundary_le {m0 : Mem} (G : WalkGeom m0) {C : WalkCarry G}
    {k2 : Nat} (hk : C.k < G.nep) (hk2 : k2 ≤ G.nep) :
    stage2EntryAllowance * (k2 - C.k) +
      stage2ByteAllowance * (boundary G k2 - boundary G C.k) ≤ walkPotential G C := by
  have hb : boundary G k2 ≤ G.n := boundary_le G k2
  have hbc : boundary G C.k = entryPos G C.k := boundary_eq_entryPos G hk
  simp only [walkPotential, hbc, stage2EntryAllowance, stage2ByteAllowance]
  omega

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
  · refine ⟨fun n => ?_, hInvH, hseg.stage_eq⟩
    rw [show p + 1 + 1 + n = p + (1 + (1 + n)) from by omega,
      hseg.run (1 + (1 + n)), hrunB (1 + n), hrunH n]
  · show C.k < k2
    exact hadvance
  · show k2 < G.nep
    exact hnep
  · have hpriceB : p + 2 ≤ stage2EntryAllowance * (k2 - C.k) +
        stage2ByteAllowance * (boundary G k2 - boundary G C.k) := by
      rw [price_eq_of_lt G (by omega) hnep]
      exact hprice
    have hspend := walkPotential_spend (G := G) (C := C) (C' := C') (p := p + 2)
      (le_of_lt hadvance) (le_of_lt hnep) hpriceB
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

`htail` is the terminal post at the finalisation's two entry blocks, and it is weaker
than the fixed-verdict exit the index split consumed, in three ways: its
verdict is the run's rather than one shared by every last-entry head state, it carries
the returned memory and the boundary there rather than a bare run, and it asks
nothing of `%z`/`%s` at the head (the two registers the copy reads are the terminal
states' own).  `refuse`'s error bound (`Cd.eoff ≤ G.n`) is not read either: its price
is stated against the entry's whole remaining credit, so the position it stored is
not what bounds the tail.

**What this statement is, and what it is not.**  It is the composition of the three
outcomes into the loop's step, and it is *sound*: a per-state post at `cleanup478.i`
implies the branch's disjunct, with the segment's count added to the terminal run's.
It is not the layer's supply.  A post at a state at `cleanup478.i` is not derivable
from `WalkInv` alone — the merge's `phi` cells are the state's predecessor and its
registers, and `WalkDispatchOutcome.finish` does not carry the depth operand's value,
which decides the accept/refuse split at `if.then485.i`.  So the layer's rule is
`walkLoopStepThree_of_dispatchResult` (`JsonStage2WalkDispatchThreeOfRun`), stated on
`WalkDispatchResult`, whose `merge` arm carries the cells the post producers take. -/
theorem walkLoopStepThree_of_dispatchThree {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {F : Nat} (hF : 27 ≤ F)
    (hthree : WalkDispatchThree calls G)
    (htail : ∀ (Cd : WalkCarry G) (sd : State), WalkInv G Cd sd →
      (Cd.block = "cleanup478.i" ∨ Cd.block = "if.then") → WalkTargetPost calls G Cd sd)
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
  · obtain ⟨q, v, m, hq, hrun, hb⟩ := htail Cd sd hseg.inv' (Or.inl hblock)
    rw [hseg.stage_eq] at hb
    refine Or.inr ⟨p + q, v, m, ?_, ?_, hb⟩
    · have hk2nep : k2 ≤ G.nep := by
        have := hnepBound Cd sd nepv hseg.inv' hblock hnepv
        omega
      have hcredit := walkFinishCreditBoundary_le (G := G) (C := C) hk hk2nep
      have hbound := boundary_le G k2
      simp only [walkPotential, boundary_eq_entryPos G hk, stage2EntryAllowance,
        stage2ByteAllowance] at hcredit hprice hq ⊢
      omega
    · rw [show p + q + 2 = p + (q + 2) from by omega, hseg.run (q + 2)]
      exact hrun
  · obtain ⟨q, v, m, hq, hrun, hb⟩ := htail Cd sd hseg.inv' (Or.inr hblock)
    rw [hseg.stage_eq] at hb
    refine Or.inr ⟨p + q, v, m, ?_, ?_, hb⟩
    · simp only [walkPotential, boundary_eq_entryPos G hk, stage2EntryAllowance,
        stage2ByteAllowance] at hprice hq ⊢
      omega
    · rw [show p + q + 2 = p + (q + 2) from by omega, hseg.run (q + 2)]
      exact hrun

/-! ### Axiom footprints -/

#print axioms LeanLLVM.Refinement.WalkScope.WalkTargetRun.ifThen
#print axioms LeanLLVM.Refinement.WalkScope.WalkTargetRun.ofExitTail
#print axioms LeanLLVM.Refinement.WalkScope.walkEntryPos_at_nep
#print axioms LeanLLVM.Refinement.WalkScope.walkFinishCredit_le
#print axioms LeanLLVM.Refinement.WalkScope.walkFinishCreditBoundary_le
#print axioms LeanLLVM.Refinement.WalkScope.walkContRevolution
#print axioms LeanLLVM.Refinement.WalkScope.walkLoopStepThree_of_dispatchThree

end WalkScope

end LeanLLVM.Refinement
