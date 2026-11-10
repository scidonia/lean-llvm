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

The fifth field is the tail, and it is not proved here.  `pipelineLoopExit` —
the predicate the loop hands over — carries the exit block's program counter, the
entry stream's read, order, document bound and block bound, the predecessor, the
fourteen tail cells, the exiting count, the escape count slot's content, the
escape count's growth and the frame at the caller's memory.  The three facts the
tail's stage-2 call reads arrived with the loop's own producers rather than being
stated beside it:

1. **the document bound** `∀ q ∈ S.ent, q < S.n.toNat`.  `Γ_stage2.pre` asks for
   the document's own length; at a one-byte document the block bound `64 * S.i`
   and `n = 1` differ, so the bound is not a weakening of it.  It is the arms'
   — `PipelineBodyStep.streamDocSucc`, from the last block's entry word, whose
   identity with the body's store the emitter's post supplies;
2. **the escape count slot's content**, `readBytes s.mem S.nxp 8 =
   some (wordBytes 8 S.xn)`.  The exit names the `%nxp` *cell*, and the tail's
   call reads the slot's word; without the content the argument the call passes
   is unconstrained, and `HasBytes s.mem S.xp (4 * thatWord)` cannot be bounded
   by the staging's extent `4 * (nxp0 + 64 * blocks + 8)`;
3. **the escape count's growth**, `S.xn ≤ S.xn0 + 64 * S.i`, and with it the
   `DisjointRegions` sub-extent argument for stage 2's extents.  It is the
   invariant's growth clause and the escape list's own `len ≤ 64` at the exit
   step.

The two escape-count facts are conjuncts of `pipelineLoopInv`'s live shapes; the
document bound is derived at each exit from the block bound the live shapes carry
and the last block's own entry word.  The eight exit-producing steps — the four
back-edge exits and the four split steps' budget-one branches — are where all
three reach `pipelineLoopExit`.  So the predicate the tail reads is the one the
loop produces: there is no seam to assume.  `PipelineTailTarget` is the `exit`
field's conclusion at that predicate — the run's three steps and the record's own
post — and `pipelineBodyFacts_of_exitStage2` shows that the four proved fields and
that target are exactly what `PipelineBodyFacts` asks for.  The target is the
tail's statement, not a gap in the loop: the run is
`PipelineBodyStep.pipelineExit_run` at the cells and the two call inputs the
exit's facts supply.

Nothing here narrows a record or weakens a post: the tail's target is stated at
the same predicate the loop hands over.
-/
import LeanLLVM.Vellum.JsonStage2Contract
import LeanLLVM.Vellum.PipelineBodyStep

set_option autoImplicit false

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.Vellum.JsonPipelineIR
open LeanLLVM.Vellum.JsonEntryIR (readLanes32)

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
`pipelineLoopExit`, the predicate the loop hands over.  It is a statement about
the run and the record's own post, with nothing parameterised: the tail's three
steps are `PipelineBodyStep.pipelineExit_run`, and the two call inputs — the
UTF-8 call's resolution and stage-2's `pre` at the store's memory — are what this
target's proof supplies from the predicate's facts. -/
def PipelineTailTarget (tab base : Nat) (s2 : Calls)
    (args : List Value) (mem : Mem) (next : Nat) : Prop :=
  ∀ e : State, pipelineLoopExit mem e →
    ∃ (verdict : BitVec 64) (m : Mem),
      runFuel (pipelineCalls tab base s2) 3 pipelineBody e =
        some (.ret (some (.int 64 verdict)) m) ∧
      (Γ_pipeline_units tab base).post args mem next
        (.ret (some (.int 64 verdict)) m)

/-! ### The bundle, from the four fields and the tail -/

/-- **`PipelineBodyFacts` from the proved fields and the tail's target.**  The
loop, `N_eq`, `cost_le` and the seed are the theorems above; the fifth field is
the target at the exit predicate the loop produces.  No seam stands between them:
`pipelineLoopExit` is the loop's own exit, so the target's domain is the field's
domain. -/
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

/-- info: 'LeanLLVM.Vellum.pipelineBlocks_argLen_cap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pipelineBlocks_argLen_cap

/-- info: 'LeanLLVM.Vellum.pipelineLoop_of_staging' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineLoop_of_staging

/-- info: 'LeanLLVM.Vellum.pipelineLoop_of_staging_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineLoop_of_staging_N

/-- info: 'LeanLLVM.Vellum.pipelineLoop_of_staging_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineLoop_of_staging_cost_le

/-- info: 'LeanLLVM.Vellum.pipelineLoop_of_staging_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineLoop_of_staging_cost

/-- info: 'LeanLLVM.Vellum.PipelineTailTarget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PipelineTailTarget

/-- info: 'LeanLLVM.Vellum.pipelineBodyFacts_of_exitStage2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineBodyFacts_of_exitStage2

/-- info: 'LeanLLVM.Vellum.pipeline_satisfies_at_stage2_of_exitStage2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_satisfies_at_stage2_of_exitStage2

end LeanLLVM.Vellum
