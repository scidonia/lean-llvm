/-
# The whitespace route's seam carries no emit group

`HcontWsRows.tail` (`JsonStage2WalkDispatchWsRows`) is the `.defaultValueHigh` × `.wsByte`
row, and it states an **emit** group at the seam `contWsTailStart`:

* `HcontWsTail.calls : HcontSeamCalls G (ContTailStartC C)
  (contWsTailStart C (wsSlS G C s …) k x1 x1)`,
* `HcontWsTail.hcA : calls.cA = BitVec.ofNat 32 0`.

The second is `if.else405.i`'s `phi` incoming: `HcontWsSeam.hphi`
(`JsonStage2WalkDispatchSeams`) hard-codes it, and `hcontWsSeam_of_body` obtains the seam
from the class-C span `walkHeadChainCSeg`, whose three else bits (`hc110`, `hc116`,
`hceq116`) are exactly what `hcontFacts_of_rows` passes at the class's own `hlt125`.  At a
kind literal `0`, `stage2ScalarValue` takes its first arm and answers `0`
(`s2ScalarValue_refused`), while `HcontSeamCalls.hret₂` demands the emit arm's answer `1`;
`hcontSeamCalls_no_literal_zero` (`JsonStage2WalkDispatchSeamCalls`) is that contradiction.
So `HcontWsTail` has no inhabitant, and the group's `tail` field has no value at any
instantiation, not merely at the class's.

This is the same defect the class rows' repair removed: there, the four `if.else405.i`
rows were restated as `HcontSeamRefusal` and their consumers build `HcontArm.badToken` from
`HcontSeamRefusal` plus `refuseSeg`.  `HcontSeamStaging.scanRefuse` and
`HcontSeamAbi.scanRefuse` already name the else edge as a refusal group; `HcontWsTail` is
the remaining structure that still demands the emit group there.

## What the refutation leaves inconsistent

`hcontFacts_of_rows` cannot be applied: its `hw : HcontWsRows G` has no inhabitant at the
continuing case's own hypotheses, because the `tail` field's codomain is empty there.
Through it `hcontArm_ws_of_rows` has no input, so `walkContinueArm_of_payload`'s
`.defaultValueHigh` × `.wsByte` branch (`JsonStage2WalkDispatchContinuing`, the
`hcontArm_ws_of_rows` call in the `defaultValueHigh` case) cannot close.  The
`HcontFacts.hTail` three-call segment `hcontScanTail_of_seam` produces is exactly what the
empty `calls` field was supposed to feed.

## The repair the structures need

The class rows' move, applied to the run class's tail.  Field types that change:

* `HcontWsTail.calls` — `HcontSeamCalls G (ContTailStartC C) (contWsTailStart …)`, replaced
  by the refusal group `HcontSeamRefusal G (ContTailStartC C) (contWsTailStart …)
  (BitVec.ofNat 32 0)` (the mid pair, `hcA`, `hroot`, and `refuse`), which
  `hcontSeamRefusalOf` populates from `HcontSeamStage`.  The emit-only fields
  `HcontWsTail.hcA : calls.cA = BitVec.ofNat 32 0` and `HcontWsTail.happ :
  s2ScalarValueAppend calls.r₁.mem calls.r₂.mem …` go with it: the refusal's record is
  `HcontSeamRefuse.hmem`, not an appended emit record.
* `HcontWsTail.hroot`'s stated memory and `hreadS`/`h47`/`hlatch`'s rows name
  `calls.r₁ … calls.xA`; under the refusal group they name the mid's two outcomes and the
  refusal's memory.
* `HcontWsRows.tail : ∀ (C) (s), WalkInv G C s → … → HcontWsTail G C s v (contB35 G v)
  (contIx G C) k (hlastByte G C)` — the field whose codomain is empty.

Consumers that change with it:

* `hcontWsTail_of_landing` (`JsonStage2WalkDispatchWsRowsProduce`) takes
  `calls hcA hroot happ`; those arguments become the refusal group.
* `hcontFacts_of_rows` and `hcontArm_ws_of_rows` (`JsonStage2WalkDispatchWsRows`) read
  `hw.tail`, `hcontWsSeam_of_body`, `hcontScanTail_of_seam`, and `hcontFacts_of_staging`'s
  `hTail` (`HcontFacts.hTail`).  That `hTail` is a three-call `WalkSegment` at
  `contWsTailStart`, and `hcontFacts_of_staging` takes it as an argument: at the else edge
  there is no producer for it, so the `.ws` arm's bundle has none either.  At `126`/`127`
  the class's three other byte routes already take the refusal arm's shape
  (`hcontArm_cleanup_of_class`, `HcontArm.badToken`), which is the route the `wsByte`
  branch needs.
* `walkContinueArm_of_payload`'s `wsByte` branch and `walkContinueFacts_of_payload`
  (`JsonStage2WalkDispatchContinuing`), and the `hws : HcontWsRows G` parameter chain that
  feeds them (`JsonStage2WalkPremisesOfStaging`, `JsonStage2WalkFlushPost`,
  `PipelineDischarge`).
* `HcontWsSeam`, `hcontWsSeam_of_body` and `hcontScanTail_of_seam`
  (`JsonStage2WalkDispatchSeams`) lose their remaining client once the route is the
  refusal's.

The theorems below are the fact that repair rests on; they are stated at the structures'
own field types, so each one's statement is the field it refutes.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchWsRows
import LeanLLVM.Refinement.JsonStage2WalkDispatchSeamCalls

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The tail's emit group at the `if.else405.i` literal -/

/-- **`HcontWsTail` is empty.**  The structure's `calls` field is a `HcontSeamCalls` at the
seam state, and its `hcA` fixes that group's literal at `if.else405.i`'s `0`; no group
exists at a zero kind (`hcontSeamCalls_no_literal_zero`).  Every parameter is free, so the
refutation is not specific to a seam instance or to a document. -/
theorem hcontWsTail_not_nonempty {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {v : BitVec 32} {b35 : UInt8} {ix : BitVec 64} {k : Nat} {x1 : BitVec 8} :
    ¬ Nonempty (HcontWsTail G C s v b35 ix k x1) := by
  rintro ⟨tl⟩
  exact hcontSeamCalls_no_literal_zero tl.calls tl.hcA

/-- **The group's `tail` field has no value at the continuing case's state.**  This is
`hcontWsTail_not_nonempty` at the field's own codomain: `hw.tail` at a head state, the
continuing count's inequality and any stop and byte is the empty structure. -/
theorem hcontWsRows_tail_false {m0 : Mem} {G : WalkGeom m0} (hw : HcontWsRows G)
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep) (v : BitVec 32) (k : Nat) :
    False :=
  hcontSeamCalls_no_literal_zero (hw.tail C s hInv hblock hk v k).calls
    (hw.tail C s hInv hblock hk v k).hcA

/-- **The whitespace cell's producer has no input.**  `hcontArm_ws_of_rows`'s argument list
is the payload, the group, the head's invariant and block, the continuing count, the
class's two clear bits, the lane row and the document byte's whitespace disjunct; the group
is already contradictory at the class's own state, before any of the document's rows are
read.  The other premises are named to keep the cell's statement visible. -/
theorem hcontArm_ws_of_rows_vacuous {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (_hp : HcontPayload G) (hw : HcontWsRows G) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (_hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (_hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (r : HcontDefaultRow G C s) (_hws : wsStop G (r.v.toNat - 1)) : False :=
  hcontWsRows_tail_false hw hInv hblock hk r.v 0

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontWsTail_not_nonempty
#print axioms LeanLLVM.Refinement.WalkScope.hcontWsRows_tail_false
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_ws_of_rows_vacuous

end WalkScope
end LeanLLVM.Refinement
