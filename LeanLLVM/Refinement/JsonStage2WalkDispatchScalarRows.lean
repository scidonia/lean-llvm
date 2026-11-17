/-
# The plain-value route's arm, at its rows

`HcontScalarPrefix` (`JsonStage2WalkDispatchScalarOfStaging`) is the class's document row
and lane word beside the head state's own cells, and `HcontSeamCalls` at `scSeamS` is its
three calls' rows.  This module composes the arm from exactly those two, so the class's
producer hands its document cells and the callee group and nothing else:

* the **seam invariant** is `scSeamInv_of_cells`'s, from the prefix's cells
  (`JsonStage2WalkHcontSeamInv`) — not a premise;
* the **predecessor and its `phi`**, and the kind word the `phi` selects, are the seam's
  own: `%phi.sink372` lists `if.end372.i`'s literal `7` (`scalar_phiKind`,
  `JsonStage2WalkDispatchScalar`), and the seam's `pre` names `if.end372.i` by definition;
* the **static cells** `%kind404.i`, `%root_done.i`, `%c.i`, `%t352.i` and `%z` are
  `WalkInv.regs`' at the seam's invariant;
* the **root slot's word** is the head's, transported across the route's three token-record
  stores (`scSeam_rootRead`), the token's position and gap and its end;
* the **tail** is `scContTail_of_calls`'s, whose one input beside the rows is the seam's
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

/-! ### The root slot across the scalar route's stores -/

/-- **The root slot's word at the tail's own read.**  The seam's memory is the head's with
the token's position (`%t352.i`), gap (`%gap.i`) and end (`%end.i`) stored inside the token
record; the kind store is the tail's first step.  All four lie inside the record's staged
extent, which ends below the root slot (`WalkStage.sevenEnd`), so the slot's word is the
head's read. -/
theorem scSeam_rootRead {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (cA : BitVec 32) {rdv : BitVec 32}
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)) :
    readBytes
      (writeBytes (scSeamS C s x inc nep ep v ix b35).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4) := by
  have h4a : (natToBytes cA.toNat 4).length = 4 := natToBytes_length _ _
  have h8v : (natToBytes (BitVec.ofNat 64 v.toNat).toNat 8).length = 8 :=
    natToBytes_length _ _
  have h4g : (natToBytes (BitVec.ofNat 32 1).toNat 4).length = 4 := natToBytes_length _ _
  simp only [scSeamS, seamFin, sP35, sP39, sP41, sLand, sEnd, condEnd349OutAt, cte345OutAt,
    scS₅, scS₄, scS₃, scS₂, scS₁, stateAt, cells, State.bind]
  rw [walkReadBytes_rootSlot_of_tokStore (off := 16) (len := 4) (v := natToBytes cA.toNat 4)
    (by decide) h4a]
  rw [walkReadBytes_rootSlot_of_tokStore (off := 8) (len := 8)
    (v := natToBytes (BitVec.ofNat 64 v.toNat).toNat 8) (by decide) h8v]
  rw [walkReadBytes_rootSlot_of_tokStore (off := 20) (len := 4)
    (v := natToBytes (BitVec.ofNat 32 1).toNat 4) (by decide) h4g]
  have h0 : readBytes (writeBytes s.mem C.stage.tok (natToBytes ix.toNat 8))
      (G.next0 + 8) 4 = readBytes s.mem (G.next0 + 8) 4 := by
    refine walkReadBytes_writeBytes_outside (start := C.stage.tok) (addr := G.next0 + 8)
      (n := 4) ?_
    right
    have h := C.stage.sevenEnd (C.stage.tok, stage2TokenExtent)
      (by simp [stage2StagedWrites])
    have hlen : (natToBytes ix.toNat 8).length = 8 := natToBytes_length _ _
    simp only [stage2TokenExtent] at h
    omega
  rw [h0]
  exact hroot

/-! ### The arm, at the rows -/

/-- **The plain-value continuing arm, at its rows.**  The prefix's cells supply the head's
class and lane, the seam's invariant is `scSeamInv_of_cells`'s, the tail is
`scContTail_of_calls`'s, and the two word agreements tie the group to the state: the kind
literal is `7` and the root word is the slot's. -/
theorem hcontArm_scalar_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (doc : HcontScalarPrefix G C s)
    (calls : HcontSeamCalls G (HeadC₄₁₃ (ContAC₇ C))
      (scSeamS C s doc.x doc.inc doc.nep doc.ep doc.v doc.ix doc.b35))
    (hcA : calls.cA = BitVec.ofNat 32 7)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hInvS := scSeamInv_of_cells hInv hblock doc
  have hopS : evalOperand
      (stateAt (scSeamS C s doc.x doc.inc doc.nep doc.ep doc.v doc.ix doc.b35).env
        (scSeamS C s doc.x doc.inc doc.nep doc.ep doc.v doc.ix doc.b35))
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
  have hreadRoot := scSeam_rootRead (G := G) (C := C) (s := s) doc.x doc.inc doc.nep doc.ep
    doc.v doc.ix doc.b35 calls.cA hroot
  have htightS : (HeadC₄₁₃ (ContAC₇ C)).events.length ≤ (HeadC₄₁₃ (ContAC₇ C)).k :=
    hInv.events_le_of_tight (by rw [hblock]; decide)
  have hkltS : (HeadC₄₁₃ (ContAC₇ C)).k < G.nep := Nat.lt_of_succ_lt hk
  obtain ⟨ev, hTail⟩ :=
    scContTail_of_calls G C s doc.x doc.inc doc.nep doc.ep doc.v doc.ix doc.b35
      calls.r₁ calls.r₂ calls.r₃ (cA := calls.cA) (rdv := calls.rdv) (xA := calls.xA) hInvS
      (pT := "if.end372.i") "if.end372.i" rfl scalar_phiKind hopS hkindS hrdS hreadRoot
      calls.hpre₁ calls.hcall₁ calls.hret₁ calls.hbit0 calls.hzread hcS htS hzS
      calls.hpre₂ calls.hcall₂ calls.hret₂ calls.hev64 htightS hkltS calls.hpre₃
      calls.hcall₃ (by have := doc.v.isLt; omega)
  exact ⟨HcontArm.scalar (hcontScalarFacts_of_staging G C s doc calls.r₁ calls.r₂ calls.r₃
    ev (cA := calls.cA) (rdv := calls.rdv) (xA := calls.xA) hTail)⟩

/-- **The plain-value continuing dispatch, at its rows.** -/
theorem walkDispatch_at_scalar_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep) (doc : HcontScalarPrefix G C s)
    (calls : HcontSeamCalls G (HeadC₄₁₃ (ContAC₇ C))
      (scSeamS C s doc.x doc.inc doc.nep doc.ep doc.v doc.ix doc.b35))
    (hcA : calls.cA = BitVec.ofNat 32 7)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨arm⟩ := hcontArm_scalar_of_rows hInv hblock hk doc calls hcA hroot
  exact HcontArm.dispatch hInv hblock hk arm

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.scSeam_rootRead
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_scalar_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_scalar_of_rows

end WalkScope
end LeanLLVM.Refinement
