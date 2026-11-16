/-
The two facts the arm table and the closing delimiter's region share.

The arm table (`JsonStage2WalkDispatchArms`) splits every one-bit comparison's two values
when it builds the head switch's census, and each region's refusals are packaged as the
dispatch's `refuse` alternative.  Both facts are stated here, below the table and below
`JsonStage2WalkDispatchClosers`, so that each builds on them instead of restating them:
the table cannot import the closing region (the region's proofs are the table's own
conclusions' producers), so what they share has to sit under both.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitness
import LeanLLVM.Refinement.JsonStage2WalkDispatchThreeOfRun

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- A one-bit value that is not `1` is `0`. -/
theorem bitZeroOfNeOne {b : BitVec 1} (h : ¬ b = 1) : b = 0 := by
  have h2 : b.toNat < 2 := b.isLt
  have h1 : b.toNat ≠ 1 := by
    intro hh
    exact h (BitVec.eq_of_toNat_eq (by rw [hh]; rfl))
  have h0 : b.toNat = 0 := by omega
  exact BitVec.eq_of_toNat_eq (by rw [h0]; rfl)

/-- **A refusal is the dispatch's `refuse` alternative.**  A counted run from the head to
the refusal copy, with the word the copy loads and a price inside the remaining credit,
*is* that alternative: the segment, its endpoint's block and word, and the endpoint's
offset bound are the fields, field for field.  So a region whose run is a refusal builds
its result from the witness without restating any of it. -/
theorem WalkDispatchResult.ofRefuseAt {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (h : WalkRefuseAt calls G C s) :
    WalkDispatchResult calls G C s := by
  obtain ⟨Cd, sd, p, hseg, herr, hprice⟩ := h
  exact WalkDispatchResult.refuse Cd sd p hseg.seg hseg.block hseg.word herr hprice

end WalkScope
end LeanLLVM.Refinement
