/-
The scan-free continuing class's span, from the bundle's own fields.

`hcontToSpan` (`JsonStage2WalkRevolutionPrefix`) is the continuing head's twelve links and
the class-C span's five, composed at `ContSeamC`.  This module applies the same composition
to `HcontCleanupFacts` (`JsonStage2WalkRevolution`): every hypothesis the head reads is one
of the bundle's fields, and the span's four bits are the bundle's class bits, so the
seventeen links reaching the tail's start are a theorem rather than a segment a producer
supplies.

Two consumers read it:

* `hcontPrefixCleanupSeg` — the twenty links to the merge's entry (the span's seventeen and
  the tail's three calls on their empty arm);
* `walkRevolutionMergeSeg` (`JsonStage2WalkRevolutionSeg`) — the merge itself, whose three
  cells are read at the endpoint the composition names.

The head's twelve are `hcontHeadSeg12`'s, and the span's five are `walkHeadChainCSeg`'s on
the bundle's class bits (`126`/`127` clear `slt 125` and are not `116`, so `LeafBlock58`'s
else arm is the route).  The class's other bytes are `HcontArm.classC`'s, whose span is the
byte's own and enters as an arm field.
-/
import LeanLLVM.Refinement.JsonStage2WalkRevolution

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- **The scan-free bundle's twelve links, from its own fields.**  Every hypothesis
`hcontHeadSeg12` reads is a field of `HcontCleanupFacts`, so the head chain is a theorem
rather than a segment a producer must supply. -/
theorem hcontHeadSeg12_of_cleanup {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (f : HcontCleanupFacts G C s) :
    WalkSegment (stage2Calls stage2SubCalls) G C s (ContSeamC C)
      (contSeamS C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.b8) 12 :=
  hcontHeadSeg12 (G := G) (C := C) (s := s) hInv hblock f.h8 f.hlt91 f.hlt123 f.hlt125
    f.hne125 f.hinc f.hnep f.hnext f.h5 f.hi63 f.hread f.hidx5 f.htok5 f.hgap5 f.hugt
    f.hread35 f.hb13 f.hb32 f.hbne13 f.hend f.h8end f.hbit

/-- **The bundle's seventeen links, to the tail's start.**  The head's twelve and the
class-C span's five; `126`/`127` clear `slt 125`, so the span is `walkHeadChainCSeg`'s
`LeafBlock58` else arm. -/
theorem hcontSpan17_of_cleanup {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (f : HcontCleanupFacts G C s) :
    WalkSegment (stage2Calls stage2SubCalls) G C s (ContTailStartC C)
      (contTailStart C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.b8 f.x1) 17 := by
  have hhead := hcontHeadSeg12_of_cleanup hInv hblock f
  have hspan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
      (contSeamS C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.b8) (ContTailStartC C)
      (contTailStart C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.b8 f.x1) 5 :=
    walkHeadChainCSeg (G := G) (C := ContSeamC C)
      (s := contSeamS C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.b8) hhead.inv' rfl
      f.h8c f.hc110 f.hc116 f.hceq116
  exact hhead.trans (Seg.measure hspan)

/-- **The scan-free continuing entry's path to the merge's entry, counted at twenty.**
The span's seventeen links and the tail's three calls on their empty arm: the copy call's
test is `ult v v`, so its successor is `if.end473.i` and the walk never enters the
extra-token scan.

Nothing here is the whitespace arm's: no scan entry, no landing, no latch, and no span
`[ei, v.toNat)` — the token ends where the entry does. -/
theorem hcontPrefixCleanupSeg {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (f : HcontCleanupFacts G C s) :
    WalkSegment (stage2Calls stage2SubCalls) G C s (TailCarryEnd (ContTailStartC C) f.ev)
      (contCleanupEndF f) 20 :=
  (hcontSpan17_of_cleanup hInv hblock f).trans f.hTail

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontHeadSeg12_of_cleanup
#print axioms LeanLLVM.Refinement.WalkScope.hcontSpan17_of_cleanup
#print axioms LeanLLVM.Refinement.WalkScope.hcontPrefixCleanupSeg

end WalkScope
end LeanLLVM.Refinement
