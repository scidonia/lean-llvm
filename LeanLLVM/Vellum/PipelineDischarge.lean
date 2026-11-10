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
entry stream's read, order and *block* bound, the predecessor, the fourteen tail
cells, the exiting count and the frame at the caller's memory.  The tail's
stage-2 call needs three facts that predicate does not carry:

1. **the document bound** `∀ q ∈ S.ent, q < S.n.toNat`.  The exit states
   `q < 64 * S.i`, and `Γ_stage2.pre` asks for the document's own length; at a
   one-byte document the two differ (`64 * S.i = 64` against `n = 1`), so the
   bound is not a weakening of the block bound.  It is the arms' —
   `PipelineBodyFacts.streamDocBound_append`, from the last block's entry word —
   and the exit predicate is where it has to arrive to reach the tail;
2. **the escape count slot's content**, `readBytes s.mem S.nxp 8 =
   some (wordBytes 8 S.xn)`.  The exit names the `%nxp` *cell*, and the tail's
   call reads the slot's word; without the content the argument the call passes
   is unconstrained, and `HasBytes s.mem S.xp (4 * thatWord)` cannot be bounded
   by the staging's extent `4 * (nxp0 + 64 * blocks + 8)`;
3. **the escape count's growth**, `S.xn ≤ S.xn0 + 64 * S.i`, and with it the
   `DisjointRegions` sub-extent argument for stage 2's extents.  Both are
   invariant conjuncts that vanish at `r = 0`.

`pipelineLoopExitStage2` below is the exit predicate as the tail needs it: the
same conjunct list with those three facts, at the same carried record, so the
tail reads one `S` rather than a second existential.  `PipelineTailTarget` is the
`exit` field's conclusion at that predicate — the run's three steps and the
record's own post — and `pipelineBodyFacts_of_exitStage2` shows that the four
proved fields, that target and the seam `pipelineLoopExit → pipelineLoopExitStage2`
are exactly what `PipelineBodyFacts` asks for.  The seam is the retype's
obligation, not a hypothesis about the run: the loop's producers (the twelve arm
and split steps) are what must hand the stronger predicate over.

Nothing here narrows a record or weakens a post: the gap is named where the
consumer meets it, and the three facts are its statement.
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

/-! ### The tail's exit extension -/

/-- **The exit the tail needs.**  `pipelineLoopExit`'s conjunct list at the same
carried record, with the three facts the tail's stage-2 call reads and the spent
budget's predicate does not carry: the document bound over the whole entry stream,
the escape count slot's content, and the escape count's growth bound.  The
document bound replaces nothing — the block bound stays, because it is what the
entry emitters' posts hand on — and the count's content is stated at the slot
rather than at the cell, because that is the word the call passes.

The three facts are the retype's obligation: `pipelineLoopExit` is what the loop
produces today, and the seam between the two predicates is named, not assumed,
in `pipelineBodyFacts_of_exitStage2`. -/
def pipelineLoopExitStage2 (mem : Mem) (s : State) : Prop :=
  ∃ (S : PipelineLoopCarried),
    s.pc = "for.cond.cleanup" ∧
    readLanes32 s.mem S.ep S.k = some S.ent ∧
    S.ent.Pairwise (· < ·) ∧
    -- 1. the document bound, beside the block bound the emitters hand on
    (∀ q ∈ S.ent, q < S.n.toNat) ∧
    (∀ q ∈ S.ent, q < 64 * S.i) ∧
    s.pre = some S.arm.head ∧
    tailCells S s.env ∧
    PipelineLoopCount S s ∧
    -- 2. the escape count slot's content, which is the word the call passes
    readBytes s.mem S.nxp 8 = some (wordBytes 8 S.xn) ∧
    -- 3. the escape count's growth, which bounds the staging's extent
    S.xn ≤ S.xn0 + 64 * S.i ∧
    UnchangedOutside mem s.mem (pipelineLoopWrites S)

/-- **The extension contains the exit.**  Every state the tail's predicate admits
is an exit state at the same carried record, so a consumer that reads
`pipelineLoopExit`'s facts is reading a consequence of the stronger statement. -/
theorem pipelineLoopExitStage2.exit {mem : Mem} {s : State}
    (h : pipelineLoopExitStage2 mem s) : pipelineLoopExit mem s := by
  obtain ⟨S, hpc, hent, hord, _hdoc, hbnd, hpre, hcells, hcnt, _hnxp, _hxn, hframe⟩ := h
  exact ⟨S, hpc, hent, hord, hbnd, hpre, hcells, hcnt, hframe⟩

/-- The document bound, as a projection: the clause the tail's stage-2 call reads
and the exit predicate does not carry. -/
theorem pipelineLoopExitStage2.docBound {mem : Mem} {s : State}
    (h : pipelineLoopExitStage2 mem s) :
    ∃ S : PipelineLoopCarried, ∀ q ∈ S.ent, q < S.n.toNat := by
  obtain ⟨S, -, -, -, hdoc, -⟩ := h
  exact ⟨S, hdoc⟩

/-- The escape count slot's content, as a projection. -/
theorem pipelineLoopExitStage2.countSlot {mem : Mem} {s : State}
    (h : pipelineLoopExitStage2 mem s) :
    ∃ S : PipelineLoopCarried, readBytes s.mem S.nxp 8 = some (wordBytes 8 S.xn) := by
  obtain ⟨S, -, -, -, -, -, -, -, -, hnxp, -⟩ := h
  exact ⟨S, hnxp⟩

/-- The escape count's growth bound, as a projection. -/
theorem pipelineLoopExitStage2.countGrowth {mem : Mem} {s : State}
    (h : pipelineLoopExitStage2 mem s) :
    ∃ S : PipelineLoopCarried, S.xn ≤ S.xn0 + 64 * S.i := by
  obtain ⟨S, -, -, -, -, -, -, -, -, -, hxn, -⟩ := h
  exact ⟨S, hxn⟩

/-- **The tail's target**, at the exit extension: the field
`PipelineBodyFacts.exit` states at `pipelineLoopExit`, read at the predicate that
carries the three facts its stage-2 call needs.  It is a statement about the run
and the record's own post, with nothing parameterised: the tail's three steps are
`PipelineBodyStep.pipelineExit_run`, and the two call inputs — the UTF-8 call's
resolution and stage-2's `pre` at the store's memory — are what this target's
proof supplies from the predicate's facts. -/
def PipelineTailTarget (tab base : Nat) (s2 : Calls)
    (args : List Value) (mem : Mem) (next : Nat) : Prop :=
  ∀ e : State, pipelineLoopExitStage2 mem e →
    ∃ (verdict : BitVec 64) (m : Mem),
      runFuel (pipelineCalls tab base s2) 3 pipelineBody e =
        some (.ret (some (.int 64 verdict)) m) ∧
      (Γ_pipeline_units tab base).post args mem next
        (.ret (some (.int 64 verdict)) m)

/-! ### The bundle, from the four fields and the tail -/

/-- **`PipelineBodyFacts` from the proved fields and the tail's target.**  The
loop, `N_eq`, `cost_le` and the seed are the theorems above; the fifth field is
the target at the extension, read back at `pipelineLoopExit` through the seam
`hseam`.  The seam is the one thing a caller of this module must hold, and it is
the retype's: that the loop's producers hand the stronger exit over. -/
def pipelineBodyFacts_of_exitStage2 {tab base : Nat} {s2 : Calls}
    {Γ2 : MemContract} {args : List Value} {mem : Mem} {next : Nat}
    (hst : pipelineStaging tab base args mem) (units : PipelineUnits tab base s2 Γ2)
    (hseam : ∀ e : State, pipelineLoopExit mem e → pipelineLoopExitStage2 mem e)
    (tail : PipelineTailTarget tab base s2 args mem next) :
    PipelineBodyFacts tab base s2 Γ2 args mem next :=
  { loop := pipelineLoop_of_staging hst s2 Γ2 units
    N_eq := pipelineLoop_of_staging_N hst s2 Γ2 units
    cost_le := pipelineLoop_of_staging_cost_le hst s2 Γ2 units
    seed := pipelineSeed hst
    exit := fun e he => tail e (hseam e he) }

/-- **The assembled pipeline satisfies its unit-level record, from the four
fields and the tail's target.**  `pipeline_satisfies_at_stage2`'s `hbody` is
supplied by `pipelineBodyFacts_of_exitStage2`, so the remaining inputs are its
two — the stage-2 selection `h2`, and the seam and the target that stand where
the tail is not yet discharged. -/
theorem pipeline_satisfies_at_stage2_of_exitStage2 (tab : Nat) (s2 : Calls)
    (h2 : CallSatisfies s2 Γ_stage2 stage2Sym)
    (hseam : ∀ (base : Nat) (args : List Value) (mem : Mem) (next : Nat),
      pipelineStaging tab base args mem → ∀ e : State,
        pipelineLoopExit mem e → pipelineLoopExitStage2 mem e)
    (tail : ∀ (base : Nat) (args : List Value) (mem : Mem) (next : Nat),
      pipelineStaging tab base args mem → PipelineUnits tab base s2 Γ_stage2 →
      PipelineTailTarget tab base s2 args mem next) :
    ∀ base, Satisfies (pipelineCalls tab base s2) pipelineBody
      (Γ_pipeline_units tab base) :=
  pipeline_satisfies_at_stage2 tab s2 h2
    (fun base args mem next hpre units =>
      pipelineBodyFacts_of_exitStage2 hpre units (hseam base args mem next hpre)
        (tail base args mem next hpre units))

/-! ### Axiom footprints

The four fields are `PipelineBodyStep`'s instance and two closed comparisons; the
exit extension and the target are definitions; the bundle is the structure's
constructor at them.  Nothing here adds a carrier, and nothing here is a
`sorry`-shaped placeholder: the tail is a named target, and the seam is its
producer.
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

/-- info: 'LeanLLVM.Vellum.pipelineLoopExitStage2.docBound' does not depend on any axioms -/
#guard_msgs in
#print axioms pipelineLoopExitStage2.docBound

/-- info: 'LeanLLVM.Vellum.pipelineLoopExitStage2.countSlot' does not depend on any axioms -/
#guard_msgs in
#print axioms pipelineLoopExitStage2.countSlot

/-- info: 'LeanLLVM.Vellum.pipelineLoopExitStage2.countGrowth' does not depend on any axioms -/
#guard_msgs in
#print axioms pipelineLoopExitStage2.countGrowth

/-- info: 'LeanLLVM.Vellum.pipelineLoopExitStage2' does not depend on any axioms -/
#guard_msgs in
#print axioms pipelineLoopExitStage2

/-- info: 'LeanLLVM.Vellum.pipelineLoopExitStage2.exit' does not depend on any axioms -/
#guard_msgs in
#print axioms pipelineLoopExitStage2.exit

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
