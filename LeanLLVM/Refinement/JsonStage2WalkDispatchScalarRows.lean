/-
# The plain-value route's arm, at its rows

`HcontScalarPrefix` (`JsonStage2WalkDispatchScalarOfStaging`) is the class's document row
and lane word beside the head state's own cells, and `HcontSeamCalls` at the byte's own
seam `scSeamByte` is its three calls' rows.  This module composes the arm from exactly
those two, so the class's producer hands its document cells and the callee group and
nothing else:

* the **seam invariant** is `scSeamInv_of_cells`'s, from the prefix's cells
  (`JsonStage2WalkHcontSeamInv`) — not a premise;
* the **predecessor and its `phi`**, and the kind word the `phi` selects, are the seam's
  own: `%phi.sink372` lists `if.end372.i`'s literal `7` (`scalar_phiKind`,
  `JsonStage2WalkDispatchScalar`), and the seam's `pre` names `if.end372.i` by definition;
* the **static cells** `%kind404.i`, `%root_done.i`, `%c.i`, `%t352.i` and `%z` are
  `WalkInv.regs`' at the seam's invariant;
* the **root slot's word** is the head's, transported across the route's token-record
  stores (`sLand_rootRead`, `scSeamByte_rootRead`), the token's position and gap and its
  end;
* the **tail** is `scTailByte_of_calls`'s, whose one input beside the rows is the seam's
  invariant.

What remains beside the rows is the class's agreement with its own seam: the kind literal
the group carries is `7` (`hcA`), and the root word it carries is the slot's (`hroot`).

## Why the root word is a row and not a zero

The scan-free class's root word is the lane's `0`, because its copy call runs at a
continuing entry whose root is not yet written.  The plain-value class's row is the same
slot read at the head's memory, which is what `hroot` states: at this class the slot's word
is not fixed by the class, so transporting it is a read rather than a substitution.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassRows
import LeanLLVM.Refinement.JsonStage2WalkDispatchScalarOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchSeamRows
import LeanLLVM.Refinement.JsonStage2WalkDispatchSegments
import LeanLLVM.Refinement.JsonStage2WalkHcontSeamInv

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The arm, at the rows -/

/-- **The plain-value continuing arm, at its rows.**  The prefix's cells supply the head's
class and lane, the seam's invariant is `scSeamInv_of_cells`'s at the prefix's route, the
tail is `scTailByte_of_calls`'s, and the two word agreements tie the group to the state:
the kind literal is `7` and the root word is the slot's. -/
theorem hcontArm_scalar_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (doc : HcontScalarPrefix G C s)
    (calls : HcontSeamCalls G (HeadC₄₁₃ (ContAC₇ C))
      (scSeamByte (sLand C s doc.x doc.inc doc.nep doc.ep doc.v doc.ix doc.b35)
        doc.v.toNat doc.x C.stage.tok doc.b35 doc.hb))
    (hcA : calls.cA = BitVec.ofNat 32 7)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hInvS := scSeamInv_of_cells hInv hblock doc
  have hopS : evalOperand
      (stateAt (scSeamByte (sLand C s doc.x doc.inc doc.nep doc.ep doc.v doc.ix doc.b35)
        doc.v.toNat doc.x C.stage.tok doc.b35 doc.hb).env
        (scSeamByte (sLand C s doc.x doc.inc doc.nep doc.ep doc.v doc.ix doc.b35)
          doc.v.toNat doc.x C.stage.tok doc.b35 doc.hb))
      (.imm (.int 32 (BitVec.ofNat 32 7))) = some (.int 32 calls.cA) := by
    rw [hcA]
    rfl
  have hkindS := hInvS.regs ("%kind404.i", .ptr (C.stage.tok + 16))
    (by simp [walkStaticRegs])
  have hrdS := hInvS.regs ("%root_done.i", .ptr (G.next0 + 8))
    (by simp [walkStaticRegs])
  have hcS := hInvS.regs ("%c.i", .ptr (TailCarry₂ (HeadC₄₁₃ (ContAC₇ C))).stage.c)
    (by simp [walkStaticRegs])
  have htS := hInvS.regs ("%t352.i", .ptr (TailCarry₂ (HeadC₄₁₃ (ContAC₇ C))).stage.tok)
    (by simp [walkStaticRegs])
  have hzS := hInvS.regs ("%z", .ptr (TailCarry₂ (HeadC₄₁₃ (ContAC₇ C))).stage.z)
    (by simp [walkStaticRegs])
  have hreadRoot := scSeamByte_rootRead (G := G) (C := C)
    (q4 := sLand C s doc.x doc.inc doc.nep doc.ep doc.v doc.ix doc.b35)
    doc.v.toNat doc.x doc.b35 doc.hb (cA := calls.cA) (rdv := calls.rdv)
    (sLand_rootRead (G := G) (C := C) (s := s) doc.x doc.inc doc.nep doc.ep doc.v doc.ix
      doc.b35 hroot)
  have htightS : (HeadC₄₁₃ (ContAC₇ C)).events.length ≤ (HeadC₄₁₃ (ContAC₇ C)).k :=
    hInv.events_le_of_tight (by rw [hblock]; decide)
  have hkltS : (HeadC₄₁₃ (ContAC₇ C)).k < G.nep := Nat.lt_of_succ_lt hk
  obtain ⟨ev, hTail⟩ :=
    scTailByte_of_calls G C (sLand C s doc.x doc.inc doc.nep doc.ep doc.v doc.ix doc.b35)
      (vN := doc.v.toNat) (x := doc.x) doc.b35 doc.hb calls.r₁ calls.r₂ calls.r₃
      (cA := calls.cA) (rdv := calls.rdv) (xA := calls.xA)
      (sLand_cond C s doc.x doc.inc doc.nep doc.ep doc.v doc.ix doc.b35) hInvS
      (pT := "if.end372.i")
      "if.end372.i"
      (scSeamByte_pre (sLand C s doc.x doc.inc doc.nep doc.ep doc.v doc.ix doc.b35)
        doc.v.toNat doc.x C.stage.tok doc.b35 doc.hb)
      scalar_phiKind hopS hkindS hrdS hreadRoot calls.hpre₁ calls.hcall₁
      calls.hret₁ calls.hbit0 calls.hzread hcS htS hzS calls.hpre₂ calls.hcall₂
      calls.hret₂ calls.hev64 htightS hkltS calls.hpre₃ calls.hcall₃
      (by have := doc.v.isLt; omega)
  exact ⟨HcontArm.scalar (hcontScalarFacts_of_staging G C s doc calls.r₁ calls.r₂ calls.r₃
    ev (cA := calls.cA) (rdv := calls.rdv) (xA := calls.xA) hTail)⟩

/-- **The plain-value continuing dispatch, at its rows.** -/
theorem walkDispatch_at_scalar_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep) (doc : HcontScalarPrefix G C s)
    (calls : HcontSeamCalls G (HeadC₄₁₃ (ContAC₇ C))
      (scSeamByte (sLand C s doc.x doc.inc doc.nep doc.ep doc.v doc.ix doc.b35)
        doc.v.toNat doc.x C.stage.tok doc.b35 doc.hb))
    (hcA : calls.cA = BitVec.ofNat 32 7)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨arm⟩ := hcontArm_scalar_of_rows hInv hblock hk doc calls hcA hroot
  exact HcontArm.dispatch hInv hblock hk arm

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_scalar_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_scalar_of_rows

end WalkScope
end LeanLLVM.Refinement
