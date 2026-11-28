/-
# The seam's value-position answer at H₁

`HcontSeamStage.hval` is *not* a universal consequence of `WalkInv`: at a head with
`tyMap 0 = 1`, `stMap 0 = 0` and `sp = 1`, `stage2ValuePos` takes the `ctv = 1`
branch and answers `0` (`if csv = 2 then 1 else 0`), so `hval`'s `some 1` is false.
That is why the row is a field and why a `∀ C` supply cannot be proved.  At the
head `[1]` actually reaches — `H₁ = headPassC C₁ 1 1`, with `C₁` the opener's
`openC₉ (openHeadC (walkSeed G S)) 0x5B` — the push is what makes it true:
`tyMap 0 = ifEnd24TyByte 0x5B = 2` and `stMap 0 = ifEnd24StByte = 0`.  The
composition never reads the seam at any other head, so the specialization is the
whole of what the chain needs.

The five-byte window is separable at this seam: `C.stage.separate`'s first region
is `(b, n + stage2ReadTail)` (`stage2Regions`, `JsonStage2Contract:338`), so
`stage2StagedWrites_against` puts the token record away from the document plus its
read-past tail, not only from the `n` document bytes `WalkInv.doc_outside` covers.
`hbase`/`he` are therefore the only environment rows the seam needs.

The cell facts are proved here; the `stage2ValuePos` step that consumes them is
the first goal not closed (reported outside the module).

There is no `sorry`, `admit` or `native_decide`.
-/
import LeanLLVM.Refinement.JsonEventCallerResultSeamWords
import LeanLLVM.Refinement.JsonStage2WalkHcontSeamInv

set_option autoImplicit false

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR

/-! ### The opener's stack cells -/

/-- The opener pushes the bracket's marker `2` at the seed's depth. -/
theorem evb_C₁_tyMap {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} :
    (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)).tyMap
        (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)).sp = 2 := by
  show (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)).tyMap 0 = 2
  simp only [openC₉, openHeadC, walkSeed]
  decide

/-- The opener pushes the empty state byte `0` at the seed's depth. -/
theorem evb_C₁_stMap {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} :
    (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)).stMap
        (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)).sp = 0 := by
  show (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)).stMap 0 = 0
  simp [openC₉, openHeadC, walkSeed, ifEnd24StByte_zero]

/-- The header pass keeps the opener's stack cells at index `0`, and its depth is
`1`: the three cells `HcontSeamStage.hval` reads at H₁. -/
theorem evb_H₁_pushCells {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} :
    (headPassC (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)) 1 1).sp = 1 ∧
    (headPassC (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)) 1 1).tyMap 0 = 2 ∧
    (headPassC (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)) 1 1).stMap 0 = 0 := by
  refine ⟨rfl, ?_, ?_⟩
  · show (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)).tyMap 0 = 2
    simp only [openC₉, openHeadC, walkSeed]
    decide
  · show (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)).stMap 0 = 0
    simp [openC₉, openHeadC, walkSeed, ifEnd24StByte_zero]

/-! ### Axiom footprints -/

#print axioms evb_C₁_tyMap
#print axioms evb_C₁_stMap
#print axioms evb_H₁_pushCells

end WalkScope
end LeanLLVM.Refinement
