/-
The pipeline's body discharge: the loop instance, its bound, its cost and its
seed, and the tail's target.

`JsonPipelineRefine.pipeline_satisfies_of_units` takes the body's facts as
`PipelineBodyFacts`, and `JsonStage2Contract.pipeline_satisfies_at_stage2` pins
that bundle's `Γ2` at `Γ_stage2` and still takes it.  Four of the bundle's five
fields are theorems about `pipelineBody` at the staging, and this module proves
them at the staging's own block count:

* `loop` — `PipelineBodyStep.pipelineLoop`, whose `step` is the four arms' steps
  per entry shape and whose `exit` is the spent budget;
* `N_eq` — the iteration bound is `pipelineBlocks (pipelineArgLen args)`, the
  number the loop was instantiated at;
* `cost_le` — the instance's cost is one step, inside the record's per-block
  allowance of four;
* `seed` — `PipelineBodyStep.pipelineSeed`, the three control steps from
  `EntryState` to the loop's first iteration, at the split shape.

# The exit predicate takes the caller's argument list

The fifth field is the tail: from any exit state, the run and the record's own
post.  `pipelineLoopExit` is the predicate the loop hands over, and it is stated
at the caller's memory **and at the caller's argument list**.  The argument list
is not decoration.  The predicate's frame is `UnchangedOutside mem s.mem
(pipelineLoopWrites S)`, whose regions are the carried record's addresses
(`S.sc`, `S.maskSlot`, `S.entw`, `S.xcarry`, …), while every consumer downstream
states its claims at the *caller's* (`sc`, `mk`, `entw`, `xcarry`, …): the UTF-8
window, `Γ_stage2.pre`'s staged objects, and `Γ_pipeline_units.post`'s
`UnchangedOutside`.  Stated at the state alone the predicate says nothing about
which addresses are the caller's, so `S.sc` and `args.sc` were two different
addresses until something said they were the same — and the exit predicate is the
only thing in scope at the moment the claim is made.  `exitArgs` is that tie: the
slot-match between the argument list and `S`, produced by the seed when it builds
`S` from the staging's witnesses and carried by the split and back shapes, so
every step hands it on and the tie arrives with the state rather than being
assumed at the tail.  `PipelineLoop.Exit` and `PipelineLoop.Inv` therefore take
the list — the retype is four-way (`Exit`, `Inv`, `step`, `exit`) because
`PipelineLoop.exit : Inv mem args 0 s → ∃ e, Exit mem args e` cannot produce an
argument-tied exit from an argument-free invariant.

# What the exit predicate carries, and what the tail still owes

`pipelineLoopExit` carries the exit block's program counter, the argument-list
match, the entry stream's read, order, document and block bounds, the
predecessor, the fourteen tail cells, the exiting count, the escape count slot's
content at the exit's memory, its growth, the document read at the exit's memory,
the escape stream's presence at the exit's count, the frame at the caller's
memory, the resumed block index's bound and the caller escape slot's *initial*
count together with its width bound.  The two escape-count facts and the document
read are the loop's own (the invariant's escaped slot, count growth, window read
and emitter writes), and the eight exit-producing steps are where they reach the
predicate.

`PipelineTailTarget` is the `exit` field's conclusion at that predicate: the
run's three steps and the record's own post.  **It is still supplied by the
caller** in this tree.  The retype above removes the structural obstruction — the
predicate can now name the caller, so the UTF-8 window, `Γ_stage2.pre` and the
post's frame are statements about addresses the state carries — but the
assembly of the run and the post at the exit's witnesses is the remaining work,
and the two calls' preconditions are where it starts: the UTF-8 window is
`[0,0,0] ++ S.doc` at `S.b - 3`, and stage 2's staging is the pipeline staging's
clauses at `S`'s fields, with its `DisjointRegions` derived from
`pipelineRegions` once the loop's write extents are seen to be sub-extents
(`S.k ≤ 64 * S.i` from the entry stream's order and length, `S.xn ≤ S.xn0 + 64 *
S.i` and `S.xn0 = nxp0` from the carried slot and bound).  `pipelineExit_run`
supplies the three control steps; `PipelineUnits.utf8` and `PipelineUnits.stage2`
supply the call outcomes and their posts; `positionsBytes` is where the escape
list's read becomes the post's witness.

Nothing here narrows a record or weakens a post: the tail's target is stated at
the same predicate the loop hands over, now with the caller's arguments in it.
-/
import LeanLLVM.Refinement.JsonStage2Contract
import LeanLLVM.Refinement.PipelineBodyStep

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonPipelineIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### The loop's block count, from the staging -/

/-- **The staging's block bound, at the length argument's block count.**  The
staging states `64 * pipelineBlocks bs.length + 63 < 2 ^ 32`, and `pipelineArgLen`
reads the second slot, which the staging pins to `bs.length`, so the count the
loop is instantiated at is the one the staging bounds. -/
theorem pipelineBlocks_argLen_cap {tab base : Nat} {args : List Value} {mem : Mem}
    (hst : pipelineStaging tab base args mem) :
    64 * pipelineBlocks (pipelineArgLen args) + 63 < 2 ^ 32 := by
  obtain ⟨sc, mk, entw, ep, nk, xp, nxp, xcarry, dst, ndst, ev, nev, err, nxp0, ndst0,
    nev0, n, epcap, xpcap, dstcap, evcap, arm, bs, hargs, hn, hlim, hwin, htail, hb3,
    hzero3, hpos, htab, hsc, hcarry, hnk, hnxp, hepcap, hxp, hdstcap, hdst, hev, hevcap,
    hndst, hnev, hroomk, hroomxn, hblk, -⟩ := hst
  have hlen : pipelineArgLen args = bs.length := by
    rw [hargs]
    simp only [pipelineArgLen, hn]
  rw [hlen]
  exact hblk

/-! ### The loop instance and its three arithmetic fields -/

/-- **The loop instance, at the staging's block count.**  `PipelineBodyStep.pipelineLoop`
takes the block bound as a parameter because the invariant is about the state and
not about the arguments; the staging supplies it, so the instance exists at every
staged argument list. -/
def pipelineLoop_of_staging {tab base : Nat} {args : List Value} {mem : Mem}
    (hst : pipelineStaging tab base args mem) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) :
    PipelineLoop (pipelineCalls tab base s2) pipelineBody :=
  pipelineLoop tab base s2 Γ2 units (pipelineBlocks (pipelineArgLen args))
    (pipelineBlocks_argLen_cap hst)

/-- The instance's iteration bound is the staging's block count, by construction. -/
theorem pipelineLoop_of_staging_N {tab base : Nat} {args : List Value} {mem : Mem}
    (hst : pipelineStaging tab base args mem) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) :
    (pipelineLoop_of_staging hst s2 Γ2 units).N = pipelineBlocks (pipelineArgLen args) :=
  rfl

/-- The instance's per-iteration cost is one control step. -/
theorem pipelineLoop_of_staging_cost {tab base : Nat} {args : List Value} {mem : Mem}
    (hst : pipelineStaging tab base args mem) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) :
    (pipelineLoop_of_staging hst s2 Γ2 units).cost = 1 :=
  rfl

/-- One control step is inside the record's per-block allowance of four. -/
theorem pipelineLoop_of_staging_cost_le {tab base : Nat} {args : List Value} {mem : Mem}
    (hst : pipelineStaging tab base args mem) (s2 : Calls) (Γ2 : MemContract)
    (units : PipelineUnits tab base s2 Γ2) :
    (pipelineLoop_of_staging hst s2 Γ2 units).cost ≤ pipelineBlockAllowance := by
  rw [pipelineLoop_of_staging_cost, pipelineBlockAllowance]
  decide

/-! ### The tail's target -/

/-- **The tail's target**: the field `PipelineBodyFacts.exit` states at
`pipelineLoopExit`, the predicate the loop hands over — at the caller's memory
*and* at the caller's argument list, which is what lets the target name the UTF-8
window, stage 2's staging and the post's frame at the caller's addresses.

The statement is the run's three steps and the record's own post.
`PipelineBodyStep.pipelineExit_run` supplies the steps once the two call
preconditions hold; this module does not yet supply them, so the target is a
*hypothesis* of `pipelineBodyFacts_of_exitStage2`, as it was before the retype.
What the retype changed is that the hypothesis is now statable: the predicate's
`exitArgs` identifies `S`'s addresses with the argument list's, and its document
read, escape-slot content and count bounds are the state facts the preconditions
are derived from.  The remaining obligation is the derivation itself, not a gap
in what the predicate names. -/
def PipelineTailTarget (tab base : Nat) (s2 : Calls)
    (args : List Value) (mem : Mem) (next : Nat) : Prop :=
  ∀ e : State, pipelineLoopExit mem args e →
    ∃ (verdict : BitVec 64) (m : Mem),
      runFuel (pipelineCalls tab base s2) 3 pipelineBody e =
        some (.ret (some (.int 64 verdict)) m) ∧
      (Γ_pipeline_units tab base).post args mem next
        (.ret (some (.int 64 verdict)) m)

/-! ### The bundle, from the four fields and the tail -/

/-- **`PipelineBodyFacts` from the proved fields and the tail's target.**  The
loop, `N_eq`, `cost_le` and the seed are the theorems above; the fifth field is
the target at the exit predicate the loop produces.  `pipelineLoopExit` is the
loop's own exit and it now carries the caller's argument list, so the target's
domain is the field's domain and is stated at the caller's addresses; the target
itself is the caller's until the tail's assembly is proved. -/
def pipelineBodyFacts_of_exitStage2 {tab base : Nat} {s2 : Calls}
    {Γ2 : MemContract} {args : List Value} {mem : Mem} {next : Nat}
    (hst : pipelineStaging tab base args mem) (units : PipelineUnits tab base s2 Γ2)
    (tail : PipelineTailTarget tab base s2 args mem next) :
    PipelineBodyFacts tab base s2 Γ2 args mem next :=
  { loop := pipelineLoop_of_staging hst s2 Γ2 units
    N_eq := pipelineLoop_of_staging_N hst s2 Γ2 units
    cost_le := pipelineLoop_of_staging_cost_le hst s2 Γ2 units
    seed := pipelineSeed hst
    exit := fun e he => tail e he }

/-- **The assembled pipeline satisfies its unit-level record, from the four
fields and the tail's target.**  `pipeline_satisfies_at_stage2`'s `hbody` is
supplied by `pipelineBodyFacts_of_exitStage2`, so the remaining inputs are the
stage-2 selection `h2` and the tail target — the run from the exit the loop
leaves, which the excluded `PipelineBodyFacts.exit` field states. -/
theorem pipeline_satisfies_at_stage2_of_exitStage2 (tab : Nat) (s2 : Calls)
    (h2 : CallSatisfies s2 Γ_stage2 stage2Sym)
    (tail : ∀ (base : Nat) (args : List Value) (mem : Mem) (next : Nat),
      pipelineStaging tab base args mem → PipelineUnits tab base s2 Γ_stage2 →
      PipelineTailTarget tab base s2 args mem next) :
    ∀ base, Satisfies (pipelineCalls tab base s2) pipelineBody
      (Γ_pipeline_units tab base) :=
  pipeline_satisfies_at_stage2 tab s2 h2
    (fun base args mem next hpre units =>
      pipelineBodyFacts_of_exitStage2 hpre units
        (tail base args mem next hpre units))

/-! ### Axiom footprints

The four fields are `PipelineBodyStep`'s instance and two closed comparisons; the
tail's target is a definition; the bundle is the structure's constructor at them.
Nothing here adds a carrier: the tail is a named target whose proof is
`PipelineBodyStep.pipelineExit_run`, and the exit's three facts arrive with the
loop's producers.
-/

/-- info: 'LeanLLVM.Refinement.pipelineBlocks_argLen_cap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pipelineBlocks_argLen_cap

/-- info: 'LeanLLVM.Refinement.pipelineLoop_of_staging' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineLoop_of_staging

/-- info: 'LeanLLVM.Refinement.pipelineLoop_of_staging_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineLoop_of_staging_N

/-- info: 'LeanLLVM.Refinement.pipelineLoop_of_staging_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineLoop_of_staging_cost_le

/-- info: 'LeanLLVM.Refinement.pipelineLoop_of_staging_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineLoop_of_staging_cost

/-- info: 'LeanLLVM.Refinement.PipelineTailTarget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PipelineTailTarget

/-- info: 'LeanLLVM.Refinement.pipelineBodyFacts_of_exitStage2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineBodyFacts_of_exitStage2

/-- info: 'LeanLLVM.Refinement.pipeline_satisfies_at_stage2_of_exitStage2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pipeline_satisfies_at_stage2_of_exitStage2

end LeanLLVM.Refinement
