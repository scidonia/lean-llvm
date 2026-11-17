/-
# The continuing bundle, from the payload's rows

`WalkContinueFacts` (`JsonStage2WalkPremisesOfStaging`) asks for one `HcontArm` at every
head state with an entry left.  The arm is the head switch's class — `HcontClass`
(`JsonStage2WalkDispatchHcontArms`), exhaustive by `HcontClass.complete` — beside the
class of the byte before the entry's end (`HcontByteClass`, from the payload's
`defaultLane` row).  So the case is two-dimensional: the head class does not fix the next
byte's class.

This module is that case, one branch per cell, and the bundle it produces.  Each branch
names its row's consumer:

| head class | continuing byte class | consumer |
|---|---|---|
| `.stringOpener`, `C.sp = 0` | any | `hcontArm_twoEntry_of_payload` (the payload's lane and its two calls) |
| `.stringOpener`, `C.sp ≠ 0` | any | `hcontArm_stringOpenAboveZero_of_class` (the class's row `deep`) |
| `.comma`, `.colon`, `.closeBracket`, `.closeBrace` | any | `hcontArm_of_derivedClass` (the invariant's own cells) |
| `.openBracket`, `.openBrace` | any | the payload's `abi.openCall` and the opener producers |
| `.value` | `wsByte` | `hcontArm_scalarRun_of_class` (the class's `scalarRun` row) |
| `.value` | the three leaves | `hcontArm_value_of_lane` (the payload's default lane) |
| `.defaultValueHigh` | `wsByte` | `hcontArm_ws_of_rows` (the whitespace group) |
| `.defaultValueHigh` | the three leaves | `hcontArm_cleanup_of_class` (the class's `cleanup`/`cleanupRow`) |
| the six tag-clear default classes | `wsByte` | `hcontArm_run_defaultValueLow` … `_defaultValueBrace` (the class's run rows) |
| the six tag-clear default classes | the three leaves | `hcontArm_defaultValueLow` … `_defaultValueBrace` (the class's seam rows) |

No branch holds an arm, a bundle or a segment: the groups are rows about the document and
the call environment, and every segment the arms carry is a producer's conclusion.

**Why the case is `Nonempty`.**  `HcontArm` is `Type` and `HcontClass` is `Prop`, so the
census cannot be eliminated into the arm directly (`Nonempty.casesOn` can only eliminate
into `Prop`).  The branch is therefore stated as `Nonempty (HcontArm …)`, where the
elimination is legal, and the bundle is `Classical.choice` of it — the same escape every
`Nonempty`-valued producer in the head-switch modules takes, and one that adds no
assumption about the walk: the `Nonempty` is derived from the rows alone.

**The three groups.**  `HcontPayload` is the payload's document row and its call rows,
`HcontClassRows` is the bytes' rows at each head class, and `HcontWsRows` is the
whitespace class's own document rows (`HcontFacts`' run, tail and traversal), which the
head class `126`/`127` splits on.  All three are `∀`s over the states their rows are read
at, and none of them is an arm.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchWsRows
import LeanLLVM.Refinement.JsonStage2WalkDispatchRunRow
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassTransport

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The arm at one head state -/

/-- **The continuing entry's arm, from the three groups.**  `HcontClass.complete` decides
the head switch's class, and the payload's `defaultLane` row decides the byte before the
entry's end; the branch is the cell's producer.  `h8` is the head's `%8` cell
(`cont_reg8`), which the default arm's producers take in place of a byte hypothesis. -/
theorem walkContinueArm_of_payload {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hp : HcontPayload G) (hc : HcontClassRows G) (hw : HcontWsRows G)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have h8 : evalOperand s (.reg "%8") = some (.int 8 (hlastByte G C)) := cont_reg8 hInv
  let r : HcontDefaultRow G C s := hp.lane.defaultLane C s hInv hblock hk
  cases HcontClass.complete (hlastByte G C) with
  | stringOpener h34 =>
      by_cases hsp : C.sp = 0
      · exact ⟨hcontArm_twoEntry_of_payload hInv hblock hk h34 hsp hp⟩
      · exact ⟨hcontArm_stringOpenAboveZero_of_class hInv hblock hk h34 hsp hp hc⟩
  | comma _ h44eq => exact hcontArm_of_derivedClass hInv (Or.inl h44eq)
  | colon _ _ h58eq => exact hcontArm_of_derivedClass hInv (Or.inr (Or.inl h58eq))
  | openBracket _ _ _ h91eq =>
      obtain ⟨rdv, hread, hpreV, ret, hcall⟩ := hp.abi.openCall C s hInv hblock hk
      rcases s2ValuePos_ret_zero_or_one hcall with h1 | h0
      · by_cases hsp : C.sp ≤ 519
        · exact ⟨hcontArm_containerOpen91_of_staging C s hInv h91eq hsp hread hpreV ret
            hcall h1⟩
        · have h520 : C.sp = 520 := by
            have hcap := hInv.depth_cap
            simp only [stage2StackExtent] at hcap
            omega
          exact ⟨hcontArm_openAtCap91_of_staging C s hInv h91eq h520 hread hpreV ret
            hcall h1⟩
      · exact ⟨hcontArm_containerOpenRefuse91_of_staging C s hInv h91eq hread hpreV ret
          hcall h0⟩
  | closeBracket _ _ _ h93eq =>
      exact hcontArm_of_derivedClass hInv (Or.inr (Or.inr (Or.inl h93eq)))
  | openBrace _ _ _ h123eq =>
      obtain ⟨rdv, hread, hpreV, ret, hcall⟩ := hp.abi.openCall C s hInv hblock hk
      rcases s2ValuePos_ret_zero_or_one hcall with h1 | h0
      · by_cases hsp : C.sp ≤ 519
        · exact ⟨hcontArm_containerOpen123_of_staging C s hInv h123eq hsp hread hpreV ret
            hcall h1⟩
        · have h520 : C.sp = 520 := by
            have hcap := hInv.depth_cap
            simp only [stage2StackExtent] at hcap
            omega
          exact ⟨hcontArm_openAtCap123_of_staging C s hInv h123eq h520 hread hpreV ret
            hcall h1⟩
      · exact ⟨hcontArm_containerOpenRefuse123_of_staging C s hInv h123eq hread hpreV ret
          hcall h0⟩
  | closeBrace _ _ _ h125eq =>
      exact hcontArm_of_derivedClass hInv (Or.inr (Or.inr (Or.inr h125eq)))
  | value h91 h44 h58 hne44 hbit =>
      cases r.hclass with
      | wsByte _ => exact hcontArm_scalarRun_of_class hInv hblock hk hc
      | scanFree f =>
          exact hcontArm_value_of_lane hInv hblock hk h8 h44 h58 hne44 hbit r
            (HcontHeadByte.scanFree f) hc
      | lowLeaf h1 h2 =>
          exact hcontArm_value_of_lane hInv hblock hk h8 h44 h58 hne44 hbit r
            (HcontHeadByte.lowLeaf h1 h2) hc
      | highLeaf h1 h2 h3 =>
          exact hcontArm_value_of_lane hInv hblock hk h8 h44 h58 hne44 hbit r
            (HcontHeadByte.highLeaf h1 h2 h3) hc
  | otherValue h91 h44 h58 hne44 hbit =>
      cases r.hclass with
      | wsByte hws =>
          exact hcontArm_run_otherValue hc hInv hblock hk r hws h8 h91 h44 h58 hne44 hbit
      | scanFree f =>
          exact hcontArm_otherValue hInv hblock hk h8 h91 h44 h58 hne44 hbit r
            (HcontHeadByte.scanFree f) hc
      | lowLeaf h1 h2 =>
          exact hcontArm_otherValue hInv hblock hk h8 h91 h44 h58 hne44 hbit r
            (HcontHeadByte.lowLeaf h1 h2) hc
      | highLeaf h1 h2 h3 =>
          exact hcontArm_otherValue hInv hblock hk h8 h91 h44 h58 hne44 hbit r
            (HcontHeadByte.highLeaf h1 h2 h3) hc
  | defaultValueLow h91 h44 hne34 =>
      cases r.hclass with
      | wsByte hws =>
          exact hcontArm_run_defaultValueLow hc hInv hblock hk r hws h8 h91 h44 hne34
      | scanFree f =>
          exact hcontArm_defaultValueLow hInv hblock hk h8 h91 h44 hne34 r
            (HcontHeadByte.scanFree f) hc
      | lowLeaf h1 h2 =>
          exact hcontArm_defaultValueLow hInv hblock hk h8 h91 h44 hne34 r
            (HcontHeadByte.lowLeaf h1 h2) hc
      | highLeaf h1 h2 h3 =>
          exact hcontArm_defaultValueLow hInv hblock hk h8 h91 h44 hne34 r
            (HcontHeadByte.highLeaf h1 h2 h3) hc
  | defaultValueMid h91 h44 h58 hne58 =>
      cases r.hclass with
      | wsByte hws =>
          exact hcontArm_run_defaultValueMid hc hInv hblock hk r hws h8 h91 h44 h58 hne58
      | scanFree f =>
          exact hcontArm_defaultValueMid hInv hblock hk h8 h91 h44 h58 hne58 r
            (HcontHeadByte.scanFree f) hc
      | lowLeaf h1 h2 =>
          exact hcontArm_defaultValueMid hInv hblock hk h8 h91 h44 h58 hne58 r
            (HcontHeadByte.lowLeaf h1 h2) hc
      | highLeaf h1 h2 h3 =>
          exact hcontArm_defaultValueMid hInv hblock hk h8 h91 h44 h58 hne58 r
            (HcontHeadByte.highLeaf h1 h2 h3) hc
  | defaultValueBracket h91 h123 h93 hne91 =>
      cases r.hclass with
      | wsByte hws =>
          exact hcontArm_run_defaultValueBracket hc hInv hblock hk r hws h8 h91 h123 h93
            hne91
      | scanFree f =>
          exact hcontArm_defaultValueBracket hInv hblock hk h8 h91 h123 h93 hne91 r
            (HcontHeadByte.scanFree f) hc
      | lowLeaf h1 h2 =>
          exact hcontArm_defaultValueBracket hInv hblock hk h8 h91 h123 h93 hne91 r
            (HcontHeadByte.lowLeaf h1 h2) hc
      | highLeaf h1 h2 h3 =>
          exact hcontArm_defaultValueBracket hInv hblock hk h8 h91 h123 h93 hne91 r
            (HcontHeadByte.highLeaf h1 h2 h3) hc
  | defaultValueBracketHigh h91 h123 h93 hne93 =>
      cases r.hclass with
      | wsByte hws =>
          exact hcontArm_run_defaultValueBracketHigh hc hInv hblock hk r hws h8 h91 h123
            h93 hne93
      | scanFree f =>
          exact hcontArm_defaultValueBracketHigh hInv hblock hk h8 h91 h123 h93 hne93 r
            (HcontHeadByte.scanFree f) hc
      | lowLeaf h1 h2 =>
          exact hcontArm_defaultValueBracketHigh hInv hblock hk h8 h91 h123 h93 hne93 r
            (HcontHeadByte.lowLeaf h1 h2) hc
      | highLeaf h1 h2 h3 =>
          exact hcontArm_defaultValueBracketHigh hInv hblock hk h8 h91 h123 h93 hne93 r
            (HcontHeadByte.highLeaf h1 h2 h3) hc
  | defaultValueBrace h91 h123 h125 hne123 =>
      cases r.hclass with
      | wsByte hws =>
          exact hcontArm_run_defaultValueBrace hc hInv hblock hk r hws h8 h91 h123 h125
            hne123
      | scanFree f =>
          exact hcontArm_defaultValueBrace hInv hblock hk h8 h91 h123 h125 hne123 r
            (HcontHeadByte.scanFree f) hc
      | lowLeaf h1 h2 =>
          exact hcontArm_defaultValueBrace hInv hblock hk h8 h91 h123 h125 hne123 r
            (HcontHeadByte.lowLeaf h1 h2) hc
      | highLeaf h1 h2 h3 =>
          exact hcontArm_defaultValueBrace hInv hblock hk h8 h91 h123 h125 hne123 r
            (HcontHeadByte.highLeaf h1 h2 h3) hc
  | defaultValueHigh _ _ h125 hne125 =>
      cases r.hclass with
      | wsByte hws =>
          exact ⟨hcontArm_ws_of_rows hp hw hInv hblock hk h125 hne125 r hws⟩
      | scanFree f =>
          exact hcontArm_cleanup_of_class hInv hblock hk h125 hne125 r
            (HcontHeadByte.toRoute rfl (HcontHeadByte.scanFree f)) hc
      | lowLeaf h1 h2 =>
          exact hcontArm_cleanup_of_class hInv hblock hk h125 hne125 r
            (HcontHeadByte.toRoute rfl (HcontHeadByte.lowLeaf h1 h2)) hc
      | highLeaf h1 h2 h3 =>
          exact hcontArm_cleanup_of_class hInv hblock hk h125 hne125 r
            (HcontHeadByte.toRoute rfl (HcontHeadByte.highLeaf h1 h2 h3)) hc

/-- **The continuing bundle, from the three groups.**  `WalkContinueFacts` is data, so the
class case's `Nonempty` is read by `Classical.choice`: every cell's arm is the producer's
conclusion from the rows, and the choice adds no hypothesis about the walk. -/
noncomputable def walkContinueFacts_of_payload {m0 : Mem} {G : WalkGeom m0}
    (hp : HcontPayload G) (hc : HcontClassRows G) (hw : HcontWsRows G) :
    WalkContinueFacts G :=
  fun C s hInv hblock hk =>
    Classical.choice (walkContinueArm_of_payload hp hc hw (C := C) (s := s) hInv hblock hk)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.walkContinueArm_of_payload
#print axioms LeanLLVM.Refinement.WalkScope.walkContinueFacts_of_payload

end WalkScope
end LeanLLVM.Refinement
