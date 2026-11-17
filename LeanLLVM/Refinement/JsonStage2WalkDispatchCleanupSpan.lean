/-
The byte's class's span, from the bundle's own fields.

`contPrefixLand` (`JsonStage2WalkRevolutionPrefix`) is the continuing head's eight links to
the byte's `NodeBlock41` state, and `contByteSegScanFree`/`contByteSegLow`/`contByteSegHigh`
are the byte's three routes from there to the seam.  This module applies the composition to
`HcontCleanupFacts` (`JsonStage2WalkRevolution`): every hypothesis the head reads is one of
the bundle's fields, the byte's class is the bundle's `hb`, so the chain to the class's seam
is a theorem rather than a segment a producer supplies, at the class's own count.

Two consumers read it:

* `hcontPrefixCleanupSeg` — the class's chain to the merge's entry (the span's `nH + 5` and
  the tail's three calls on their empty arm, at `nH + 5 + 3 ≤ 20`);
* `walkRevolutionMergeSeg` (`JsonStage2WalkRevolutionSeg`) — the merge itself, whose three
  cells are read at the endpoint the composition names.

The class-C span's five are `walkHeadChainCSeg`'s on the bundle's second byte (`126`/`127`
clear `slt 125`, so `LeafBlock58`'s else arm is the route); its count does not depend on
the byte before the entry's end.
-/
import LeanLLVM.Refinement.JsonStage2WalkRevolution

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- The `NodeBlock41` state the bundle's own fields name: every route starts here. -/
abbrev contLandF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontCleanupFacts G C s) : State :=
  contLandS C s f.x f.inc f.nep f.ep f.v f.ix f.b35

/-- The class's seam at the bundle's own fields. -/
abbrev contSeamF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontCleanupFacts G C s) : State :=
  contSeamByte (contLandF f) f.v.toNat C.stage.tok f.b35 f.b8 f.hb

/-- **The class's chain to the seam, from the bundle's own fields.**  Every hypothesis
`contPrefixLand` reads is a field of `HcontCleanupFacts`, and the byte's route is the
bundle's `hb`: the scan-free class takes the four links
`NodeBlock41 → NodeBlock39 → LeafBlock35 → if.end372.i`, the low leaf three and the high
leaf four, so the count is twelve or eleven. -/
theorem hcontHeadSegCleanup {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (f : HcontCleanupFacts G C s) (hb : HcontByteRoute (cont35 f.b35)) :
    ∃ nH, nH ≤ 12 ∧
      WalkSegment (stage2Calls stage2SubCalls) G C s (ContSeamC C)
        (contSeamByte (contLandF f) f.v.toNat C.stage.tok f.b35 f.b8 hb) nH := by
  have hseg8 : WalkSegment (stage2Calls stage2SubCalls) G C s (ContAC₄ C)
      (contLandF f) 8 :=
    contPrefixLand (G := G) (C := C) (s := s) hInv hblock f.h8 f.hlt91 f.hlt123 f.hlt125
      f.hne125 f.hinc f.hnep f.hnext f.h5 f.hi63 f.hread f.hidx5 f.htok5 f.hgap5 f.hugt
      f.hread35
  have h35 : evalOperand (contLandF f) (.reg "%35") =
      some (.int 8 (cont35 f.b35)) := by
    simp only [evalOperand, contLandF]
    exact contLandS_35 C s f.x f.inc f.nep f.ep f.v f.ix f.b35
  have hcond : lookupName (contLandF f).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 f.v.toNat)) := by
    simp only [contLandF]
    exact contLandS_cond C s f.x f.inc f.nep f.ep f.v f.ix f.b35
  rcases hb with ⟨hb13, hb32, hbne13⟩ | ⟨hb13, hbns⟩ | ⟨hb13, hb32, hbne32⟩
  · exact ⟨8 + 4, by omega,
      hseg8.trans (Seg.measure (contByteSegScanFree (ContAC₄ C) (contLandF f) hseg8.inv' rfl
        h35 hcond f.hend f.h8end f.hbit hb13 hb32 hbne13))⟩
  · exact ⟨8 + 3, by omega,
      hseg8.trans (Seg.measure (contByteSegLow (ContAC₄ C) (contLandF f) hseg8.inv' rfl
        h35 hcond f.hend f.h8end f.hbit hb13 hbns))⟩
  · exact ⟨8 + 4, by omega,
      hseg8.trans (Seg.measure (contByteSegHigh (ContAC₄ C) (contLandF f) hseg8.inv' rfl
        h35 hcond f.hend f.h8end f.hbit hb13 hb32 hbne32))⟩

/-- **The class's chain to its own seam, at the bundle's route.** -/
theorem hcontHeadSeg12_of_cleanup {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (f : HcontCleanupFacts G C s) :
    ∃ nH, nH ≤ 12 ∧
      WalkSegment (stage2Calls stage2SubCalls) G C s (ContSeamC C)
        (contSeamF f) nH :=
  hcontHeadSegCleanup hInv hblock f f.hb

/-- **The class's chain to the tail's start.**  The head's `nH` links and the class-C
span's five; `126`/`127` clear `slt 125`, so the span is `walkHeadChainCSeg`'s
`LeafBlock58` else arm, and the tail's start is the span's `HeadS413` target. -/
theorem hcontSpan17_of_cleanup {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (f : HcontCleanupFacts G C s) :
    ∃ nP, nP ≤ 17 ∧
      WalkSegment (stage2Calls stage2SubCalls) G C s (ContTailStartC C)
        (contTailStartF f) nP := by
  obtain ⟨nH, hnH, hhead⟩ := hcontHeadSeg12_of_cleanup hInv hblock f
  have hspan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C) (contSeamF f)
      (ContTailStartC C) (contTailStartF f) 5 := by
    simp only [contTailStartF, contSeamF]
    exact walkHeadChainCSeg (G := G) (C := ContSeamC C) (s := contSeamF f) hhead.inv' rfl
      f.h8c f.hc110 f.hc116 f.hceq116
  exact ⟨nH + 5, by omega, hhead.trans (Seg.measure hspan)⟩

/-- **The class's continuing entry's path to the merge's entry, at `nP + 3`.**  The class's
chain and the tail's three calls on their empty arm: the copy call's test is `ult v v`, so
its successor is `if.end473.i` and the walk never enters the extra-token scan.

Nothing here is the whitespace arm's: no scan entry, no landing, no latch, and no span
`[ei, v.toNat)` — the token ends where the entry does. -/
theorem hcontPrefixCleanupSeg {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (f : HcontCleanupFacts G C s) :
    ∃ n, n ≤ 20 ∧
      WalkSegment (stage2Calls stage2SubCalls) G C s
        (TailCarryEnd (ContTailStartC C) f.ev) (contCleanupEndF f) n := by
  obtain ⟨nP, hnP, hspan⟩ := hcontSpan17_of_cleanup hInv hblock f
  exact ⟨nP + 3, by omega, hspan.trans f.hTail⟩

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontHeadSeg12_of_cleanup
#print axioms LeanLLVM.Refinement.WalkScope.hcontSpan17_of_cleanup
#print axioms LeanLLVM.Refinement.WalkScope.hcontPrefixCleanupSeg

end WalkScope
end LeanLLVM.Refinement
