/-
# The continuing census's class case, one branch per class

`HcontClass` (`JsonStage2WalkDispatchHcontArms`) classifies the head byte, and
`HcontClass.complete` proves every byte has a class.  This module states the case's
branches: at each class, the arm the class's producer builds from the payload's rows.

Each branch is one theorem and reads one field of `HcontClassRows`
(`JsonStage2WalkDispatchClassRows`) — that group is the producers' remaining argument
lists, so a branch is the projection of the class's row into the producer the arm was
already proved to need.  Nothing here holds an arm or a bundle: the fields are the seam's
three callee rows with the kind literal and the root slot's word, the class's document row,
and (for the positive-depth opener) the route the arm itself carries.

## The branches

| class | branch | the field it reads |
|---|---|---|
| `.value`, at a scan-free document byte | `hcontArm_scalar_of_class` | `scalar` — the prefix's seam row |
| `.defaultValueHigh`, at a scan-free document byte | `hcontArm_cleanup_of_class` | `cleanupRow`, and `cleanup` for the document row |
| the default arm's scan-free classes | `hcontArm_letters_of_class`, `hcontArm_fLetter_of_class`, `hcontArm_classC_56True_of_class` … `hcontArm_classC_58Else_of_class` | `letters`, `fLetter`, `c56True` … `c58Else` |
| `.stringOpener` at `C.sp ≠ 0` | `hcontArm_stringOpenAboveZero_of_class` | `deep`, and the payload's `abi.openCall` |

The classes whose producer is the invariant's own — the four derived delimiters
(`hcontArm_of_derivedClass`) and the container openers
(`walkDispatch_at_open91_of_payload`, `walkDispatch_at_open123_of_payload`) — need no
branch here: their rows are the payload's `abi.openCall` and the invariant's cells, and
they are proved where they are stated.

## What the case still needs

Three things stand between these branches and `walkContinueFacts_of_payload`:

* the run class's row — its arm takes `RunFacts`, and no producer joins the check state's
  rows and the seam's state group to that bundle at the class's short prefix, so the
  whitespace document byte has no branch;
* the default arm's other document-byte classes — the byte below `13` or at or above `32`
  takes `LeafBlock33`/`LeafBlock37` to `if.end372.i`, and no chain producer states those
  routes, so a state whose document byte is one of them has no arm to select;
* the byte selection itself — which of `letters`/`fLetter`/`classC` a scan-free state takes
  is decided by the head byte, so the case needs the class bits' transport into those three
  arms' own bits, and the brace class `124`'s chain (`contBrcHeadSeg` has no `_of_lane`
  wrapper yet).
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassCLeaves
import LeanLLVM.Refinement.JsonStage2WalkDispatchScalarRows
import LeanLLVM.Refinement.JsonStage2WalkDispatchDefaultLane
import LeanLLVM.Refinement.JsonStage2WalkDispatchHcontStringDeep
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassRows

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The plain-value class -/

/-- **The plain-value class's continuing arm, from the class's row.**  The class's producer
is `hcontArm_scalar_of_rows`; its remaining inputs are the seam's three callee rows, the
kind literal and the root slot's word, which `HcontClassRows.scalar` carries at the class's
own prefix. -/
theorem hcontArm_scalar_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (pre : HcontScalarPrefix G C s) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  obtain ⟨calls, hcA, hroot⟩ := hc.scalar C s pre
  exact hcontArm_scalar_of_rows hInv hblock hk pre calls hcA hroot

/-! ### The default arm's scan-free classes -/

/-- **The letters class's continuing arm, from the class's row.**  The head chain is the
caller's (the class's own count and endpoint); the seam's three callee rows, their kind
literal `0` and the root slot's word are the row's. -/
theorem hcontArm_letters_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0)
    (ch : HcontHeadChain G C s x) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  obtain ⟨calls, hcA, hroot⟩ := hc.letters C s ch
  exact hcontArm_letters_of_rows hInv hk h8 hbit h110 hne102 ch calls hcA hroot

/-- **The `'f'` leaf's continuing arm, from the class's row.** -/
theorem hcontArm_fLetter_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (h102 : evalICmp .eq x (BitVec.ofNat 8 102) = 1)
    (ch : HcontHeadChain G C s x) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  obtain ⟨calls, hcA, hroot⟩ := hc.fLetter C s ch
  exact hcontArm_fLetter_of_rows hInv hk h8 hbit h110 h102 ch calls hcA hroot

/-- **`110`'s continuing arm, from the class's row.** -/
theorem hcontArm_classC_56True_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x (BitVec.ofNat 8 116) = 1)
    (h110eq : evalICmp .eq x (BitVec.ofNat 8 110) = 1)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  obtain ⟨calls, hcA, hroot⟩ := hc.c56True C s ch
  exact hcontArm_classC_56True_of_rows hInv hk h8 h110 h116 h110eq h125 ch calls hcA hroot

/-- **`111 … 115`'s continuing arm, from the class's row.** -/
theorem hcontArm_classC_56Else_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x (BitVec.ofNat 8 116) = 1)
    (h110eq : evalICmp .eq x (BitVec.ofNat 8 110) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  obtain ⟨calls, hcA, hroot⟩ := hc.c56Else C s ch
  exact hcontArm_classC_56Else_of_rows hInv hk h8 h110 h116 h110eq h125 ch calls hcA hroot

/-- **`116`'s continuing arm, from the class's row.** -/
theorem hcontArm_classC_58True_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq x (BitVec.ofNat 8 116) = 1)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  obtain ⟨calls, hcA, hroot⟩ := hc.c58True C s ch
  exact hcontArm_classC_58True_of_rows hInv hk h8 h110 h116 h116eq h125 ch calls hcA hroot

/-- **`117 … 125`'s continuing arm, from the class's row.** -/
theorem hcontArm_classC_58Else_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq x (BitVec.ofNat 8 116) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  obtain ⟨calls, hcA, hroot⟩ := hc.c58Else C s ch
  exact hcontArm_classC_58Else_of_rows hInv hk h8 h110 h116 h116eq h125 ch calls hcA hroot

/-! ### The scan-free high-byte class -/

/-- **The high-byte route's scan-free arm, from the class's rows.**  The document row is
produced from the payload's own default row (`hcontCleanupDoc_of_lane`), and the seam's
three callee rows are the class's; the root slot's word is the state's own, so the arm is
total over it. -/
theorem hcontArm_cleanup_of_class {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (r : HcontDefaultRow G C s) (hf : HcontScanFree G r.v) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  let doc := hcontCleanupDoc_of_lane hk r hf
  obtain ⟨calls, hcA, hroot⟩ := hc.cleanupRow C s doc
  exact hcontArm_cleanup_of_rows hInv hblock hk hlt125 hne125 doc hroot calls hcA rfl

/-! ### The string opener above depth zero -/

/-- **The positive-depth opener's arm, from the class's row.**  The class's own facts are
derived — the byte from `cont_reg8`, the two stack bytes from the carry's maps, the call's
staging and answer from `HcontOpenCall` — and the route is the row: the merge's counted
segment or the refusal's witness.  So the arm the class takes is exactly the route the
state's own memory and stack bytes select, and nothing the arm establishes is assumed. -/
def hcontArm_stringOpenAboveZero_of_class {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (h34 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1) (hsp : C.sp ≠ 0)
    (hp : HcontPayload G) (hc : HcontClassRows G) :
    HcontArm (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨rdv, _hread, hpreV, r, hcall⟩ := hp.abi.openCall C s hInv hblock hk
  cases hc.deep C s hInv hblock hk h34 hsp with
  | merge Cd sd p k2 nepv hseg hblockD hkC prev hprev hpre hinc hnepv hadvance hcap hprice =>
    exact hcontArm_stringOpenAboveZeroMerge_of_staging C s hInv h34 hsp hpreV r hcall
      Cd sd p k2 nepv hseg hblockD hkC prev hprev hpre hinc hnepv hadvance hcap hprice
  | refuse href =>
    exact hcontArm_stringOpenAboveZeroRefuse_of_staging hInv h34 hsp hpreV r hcall href

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_scalar_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_letters_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_fLetter_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_classC_56True_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_classC_56Else_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_classC_58True_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_classC_58Else_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_cleanup_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_stringOpenAboveZero_of_class

end WalkScope
end LeanLLVM.Refinement
