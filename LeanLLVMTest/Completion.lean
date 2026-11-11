/-
Completion, and the vacuity of behaviour inclusion alone.

`Beh` observes the outcomes a run reaches, and a run that never finishes reaches
none.  `Refines` is inclusion of the target's behaviours in the source's, so it
accepts a non-terminating target against a terminating source.  The first
section pins that vacuity at concrete bodies, the record that rejects it, and the
executable runs behind both.  The second pins the completion requirement at the
five shipped stage records: each unit's `Satisfies` theorem already carries the
run at its declared budget, so completion is derived from the unit's stronger
statement rather than assumed.
-/
import LeanLLVM

namespace LeanLLVMTest.Completion

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonEntryIR
open LeanLLVM.Refinement.JsonUtf8IR
open LeanLLVM.Refinement.JsonEscapeIR

/-! ### The vacuously accepted loop -/

-- Executed witnesses: the loop reaches no outcome at any finite budget, and the
-- constant body returns `7` in one step.
#guard (runFuel noCalls 64 spinningFunction (initState spinningFunction [])).isNone
#guard runFuel noCalls 1 constantFunction (initState constantFunction []) =
  some (.ret (some (.int 64 7)) ([] : Mem))

-- Under behaviour inclusion alone the looping target is accepted.
theorem loop_refines_constant :
    LeanLLVM.Refines noCalls spinningFunction constantFunction :=
  spinning_refines_constant noCalls

-- It produces none of the source's behaviours, which is why it is accepted.
theorem loop_has_no_constant_behaviour :
    ¬ Beh noCalls spinningFunction [] (.ret (some (.int 64 7)) ([] : Mem)) :=
  spinning_no_beh noCalls [] _

-- The completion-added claim rejects the candidate.
theorem loop_not_refinesCompleting :
    ¬ RefinesCompleting noCalls unconstrainedContract spinningFunction
        constantFunction :=
  spinning_not_refinesCompleting noCalls

-- The acceptance is target-side: the terminating body does not refine the loop,
-- because its return has no source behaviour to match.
theorem constant_not_refines_loop :
    ¬ LeanLLVM.Refines noCalls constantFunction spinningFunction :=
  constant_not_refines_spinning noCalls

/-! ### The five shipped stage records carry completion

Each `Satisfies` theorem's first conjunct is the run at the record's declared
budget; `Satisfies.completes` extracts it, so the completion requirement is the
units' stronger statement, not a new promise. -/

theorem masks_completes :
    Completes s1Calls s1MasksFunction Γ_masks :=
  Satisfies.completes masks_satisfies

theorem entry_pos8_completes :
    Completes entryCalls entryPos8Function Γ_entry_pos8 :=
  Satisfies.completes entry_pos8_satisfies

theorem entry_b8_completes :
    Completes entryCalls entryB8Function Γ_entry_b8 :=
  Satisfies.completes entry_b8_satisfies

theorem utf8_completes :
    Completes utf8Calls utf8Function Γ_utf8 :=
  Satisfies.completes utf8_satisfies

theorem escape_completes (base : Nat) :
    Completes (escapeListCalls Γ_xl_batch) escapeListFunction
      (Γ_escape_positions base escapePositionsBudget) :=
  Satisfies.completes (escape_positions_satisfies base)

/-! ### Axiom footprints

The vacuity and the completion predicate add no carrier: they sit at the
development's `[propext, Quot.sound]` ceiling.  The five stage records and the
pipeline certificate inherit `Classical.choice` from the unit `Satisfies`
theorems and from `optimisationPipeline_sound`, exactly as their existing pins
record; the completion requirement itself adds nothing.
-/

/-- info: 'LeanLLVM.Refinement.spinning_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms spinning_step

/-- info: 'LeanLLVM.Refinement.spinning_runFuel_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms spinning_runFuel_none

/-- info: 'LeanLLVM.Refinement.spinning_no_beh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms spinning_no_beh

/-- info: 'LeanLLVM.Refinement.constant_beh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms constant_beh

/-- info: 'LeanLLVM.Refinement.refines_of_no_beh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refines_of_no_beh

/-- info: 'LeanLLVM.Refinement.spinning_refines_constant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms spinning_refines_constant

/-- info: 'LeanLLVM.Refinement.constant_not_refines_spinning' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms constant_not_refines_spinning

/-- info: 'LeanLLVM.Refinement.spinning_not_refinesCompleting' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms spinning_not_refinesCompleting

/-- info: 'LeanLLVM.Refinement.Completes.initState' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Completes.initState

/-- info: 'LeanLLVM.Refinement.Satisfies.completes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Satisfies.completes

/-- info: 'LeanLLVM.Refinement.RefinesCompleting.refl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RefinesCompleting.refl

/-- info: 'LeanLLVM.Refinement.RefinesCompleting.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RefinesCompleting.trans

/-- info: 'LeanLLVM.Pass.comp_preservesCompletion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pass.comp_preservesCompletion

/-- info: 'LeanLLVM.Pass.pipeline_preservesCompletion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pass.pipeline_preservesCompletion

/-- info: 'LeanLLVM.constantPropagation_preservesCompletion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms constantPropagation_preservesCompletion

/-- info: 'LeanLLVM.branchFolding_preservesCompletion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms branchFolding_preservesCompletion

/-- info: 'LeanLLVM.strengthReduction_preservesCompletion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms strengthReduction_preservesCompletion

/-- info: 'LeanLLVM.optimisationPipeline_preservesCompletion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms optimisationPipeline_preservesCompletion

/-- info: 'LeanLLVM.optimisationPipeline_soundCompleting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms optimisationPipeline_soundCompleting

/-- info: 'LeanLLVMTest.Completion.masks_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms masks_completes

/-- info: 'LeanLLVMTest.Completion.entry_pos8_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entry_pos8_completes

/-- info: 'LeanLLVMTest.Completion.entry_b8_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entry_b8_completes

/-- info: 'LeanLLVMTest.Completion.utf8_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms utf8_completes

/-- info: 'LeanLLVMTest.Completion.escape_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms escape_completes

end LeanLLVMTest.Completion
