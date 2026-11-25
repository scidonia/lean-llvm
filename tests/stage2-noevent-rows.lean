/-
The no-event walk's row tier, checked at the kernel.

The milestone's conclusion is `Stage2NoEventWalkRows` from one producer per head
class; this file checks that the assembly states it, that the step corollary is
the dispatch's own corollary, that the container rows are the generic seam's
instances, and that the F1 state — the one the old premise admitted with no head
read — still refuses a row.  Each check is a `#check` at the public interface plus
an axiom pin, so a name that drifts or a proof that picks up a carrier fails here
rather than silently downstream.

Run with `nix develop -c lake env lean tests/stage2-noevent-rows.lean`.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsAssemble
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsContainerB
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsBrace

open LeanLLVM
open LeanLLVM.Refinement

/-! ### The assembly's interface -/

#check @stage2NoEventWalkRows_of_ready
#check @stage2NoEventWalkStep_of_ready
#check @stage2NoEventWalkRows_of_classes
#check @stage2NoEventWalkStep_of_classes

/-! ### The producers the assembly consumes -/

#check @stage2NoEventWalkRow_cont_of_afterValue
#check @stage2NoEventWalkRow_cont_bracketPair
#check @stage2NoEventWalkRow_cont_bracePair

/-! ### The state the old premise admitted and the new one excludes -/

#check @stage2NoEventWalkF1_notRow
#check @stage2NoEventWalkF1_notRows

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkRows_of_ready
#print axioms stage2NoEventWalkStep_of_ready
#print axioms stage2NoEventWalkRows_of_classes
#print axioms stage2NoEventWalkStep_of_classes
#print axioms stage2NoEventWalkRow_cont_of_afterValue
#print axioms stage2NoEventWalkRow_cont_bracketPair
#print axioms stage2NoEventWalkRow_cont_bracePair
#print axioms stage2NoEventWalkF1_notRow
#print axioms stage2NoEventWalkF1_notRows
