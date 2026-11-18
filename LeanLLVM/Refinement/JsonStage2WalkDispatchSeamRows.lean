/-
# The default-value route's seam, as cells the state supplies

`JsonStage2WalkDispatchSegments` builds `.cleanup`'s arm and its tail from three callee
rows, and every other premise it takes at the seam is a **cell of the seam's own state**:
the predecessor and its `phi`, the kind word that `phi` selects, `%kind404.i`,
`%root_done.i`, `%c.i`, `%t352.i`, `%z`, and the root slot's word the copy call's argument
list carries.  This module produces them, so a producer of the class hands its document
row and the callee rows and nothing else:

* the **seam invariant**, from the class's document row alone
  (`contTailStartInv_of_doc`): the head's eight links (`contPrefixLand`), the byte's
  route (the scan-free leaf's four, the low leaf's three or the high leaf's four) and the
  class-C span's five (`walkHeadChainCSeg`);
* the **environment cells**, from that invariant's `regs` (`contTailStartByte_envKind` and
  its siblings): every one of the names is in `walkStaticRegs`, and the seam's blocks bind
  none of them;
* the **predecessor and its `phi`** (`contTailStartByte_pre`, `contTailStart_phi`) and the
  kind word it selects (`contTailStartByte_op`), which is the literal `0` at
  `if.else405.i`;
* the **root slot's word**, transported across the seam's three token-record stores
  (`contTailStartByte_mem`, `contTailStartByte_rootRead`) from the lane's `root` row;
* the **tail itself**, `hcontTailByte_of_calls`'s at the byte's route, and the **arm**
  (`hcontArm_cleanup_of_rows`) at the callee rows and those cells.

The row's `hb : HcontByteRoute (cont35 (contB35 G v))` is the document's content, not one
asserted leaf: all three non-whitespace routes reach `if.end372.i` without a run, so the
same producer serves them and the caller no longer narrows the entry's last byte.

## The rows this does not produce, and why

The callee rows themselves — `HcontSeamCalls`'s three preconditions and three answers at
the staged argument lists — are the helper contracts' applications at the walk's own
arguments.  `JsonStage2WalkDispatchSeams` states the group and
`JsonStage2WalkDispatchSegments` consumes it; this module neither restates them nor
assumes them: the arm below takes the group.

The group carries two **word** fields, `cA` (the kind literal at `%kind404.i`) and `rdv`
(the root-done slot's word).  Both are cells of the seam state, and this module produces
both — `contTailStart_phi` names the first `0` and `contTailStartByte_rootRead` the second
— so the two equalities `hcontArm_cleanup_of_rows` takes (`hcA`, `hrdv`) are the
*agreement* of the caller's group with the state, not a second reading of it.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassRows
import LeanLLVM.Refinement.JsonStage2WalkDispatchCleanupSpan
import LeanLLVM.Refinement.JsonStage2WalkDispatchCleanupOfStaging

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The seam's state, named from the class's row -/

/-- **The seam state a document row names**: `contTailStartByte` at the row's word and
byte, the invariant's index, the counts and the entry's byte. -/
abbrev contTailStartOfDoc {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (doc : HcontCleanupDoc G C s) : State :=
  contTailStartByte C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v (contIx G C)
    (contB35 G doc.v) (hlastByte G C) (hlastByte G C) doc.hb

/-! ### The seventeen links, from the row

The head's eight links to the byte's `NodeBlock41` state, the byte's route to the seam and
the class-C span's five.  Every hypothesis the head reads is one of the document row's, the
invariant's or the class's, so the chain is a theorem at the row and the class. -/

/-- **The class's seventeen links, at its document row and the byte's route.** -/
theorem hcontSpan17_of_doc {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (doc : HcontCleanupDoc G C s) :
    ∃ nP, nP ≤ 17 ∧
      WalkSegment (stage2Calls stage2SubCalls) G C s (ContTailStartC C)
        (contTailStartOfDoc (G := G) C s doc) nP := by
  have hspan : doc.v.toNat ≤ entryPos G (C.k + 1) := doc.hspan
  have hgt : entryPos G C.k < doc.v.toNat := contLane_gt G C hk doc.hugt
  have heicd : doc.v.toNat - 1 < doc.v.toNat := by omega
  -- the head's eight links, to the byte's `NodeBlock41` state
  have hseg8 : WalkSegment (stage2Calls stage2SubCalls) G C s (ContAC₄ C)
      (contLandS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
        (contIx G C) (contB35 G doc.v)) 8 :=
    contPrefixLand (G := G) (C := C) (s := s) hInv hblock
      (x := hlastByte G C) (inc := hlastIncV C) (nep := hlastNepV G) (ep := G.ep)
      (v := doc.v) (ix := contIx G C) (b35 := contB35 G doc.v)
      (LeanLLVM.evalOperand_reg_of hInv.iter.reg8)
      (hlast_slt_zero_of_toInt_le (by decide) hlt125)
      (hlast_slt_zero_of_toInt_le (by decide) hlt125)
      hlt125 hne125
      (by
        refine LeanLLVM.evalOperand_reg_of ?_
        rw [headAS4_envInc s (hlastByte G C)]
        exact hInv.inc_reg)
      (by
        refine LeanLLVM.evalOperand_reg_of ?_
        rw [headAS4_envNep s (hlastByte G C)]
        exact hInv.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep))
          (by simp [walkStaticRegs]))
      (cont_ult_one G C hk)
      (contAS5_env5 C s (hlastByte G C) (hlastIncV C) (hlastNepV G) hInv)
      (cont_hi63 G C hk)
      doc.hread
      (contAS5_envIdx s (hlastByte G C) (hlastIncV C) (hlastNepV G) (contIx G C)
        hInv.idx_reg)
      (contAS5_envTok C s (hlastByte G C) (hlastIncV C) (hlastNepV G)
        (cont_static_tok hInv))
      (contAS5_envGap C s (hlastByte G C) (hlastIncV C) (hlastNepV G)
        (hInv.regs ("%gap.i", .ptr (C.stage.tok + 20)) (by simp [walkStaticRegs])))
      doc.hugt
      (cont_hread35 G C s hInv hk hspan heicd)
  -- the cells the byte's route reads at `NodeBlock41`
  have h35 : evalOperand (contLandS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep
      doc.v (contIx G C) (contB35 G doc.v)) (.reg "%35") =
      some (.int 8 (cont35 (contB35 G doc.v))) := by
    simp only [evalOperand]
    exact contLandS_35 C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
      (contIx G C) (contB35 G doc.v)
  have hcond : lookupName (contLandS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep
      doc.v (contIx G C) (contB35 G doc.v)).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 doc.v.toNat)) := by
    simp only [contLandS]
    exact contLandS_cond C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
      (contIx G C) (contB35 G doc.v)
  have hend : lookupName (contLandS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep
      doc.v (contIx G C) (contB35 G doc.v)).env "%end.i" =
      some (.ptr (C.stage.tok + 8)) := by
    rw [contLandS_envEnd]
    exact hInv.regs ("%end.i", .ptr (C.stage.tok + 8)) (by simp [walkStaticRegs])
  have h8end : lookupName (contLandS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep
      doc.v (contIx G C) (contB35 G doc.v)).env "%8" =
      some (.int 8 (hlastByte G C)) := by
    rw [contLandS_env8]
    exact hInv.iter.reg8
  have hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 :=
    hlast_bit6_of_class hlt125 hne125
  -- the byte's route, to the seam
  have hseam : ∃ nR, nR ≤ 4 ∧
      Seg (stage2Calls stage2SubCalls) G (ContAC₄ C)
        (contLandS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
          (contIx G C) (contB35 G doc.v))
        { ContAC₄ C with block := "if.else387.i" }
        (contSeamByte (contLandS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep
          doc.v (contIx G C) (contB35 G doc.v)) doc.v.toNat C.stage.tok
          (contB35 G doc.v) (hlastByte G C) doc.hb) nR := by
    rcases doc.hb with ⟨hb13, hb32, hbne13⟩ | ⟨hb13, hbns⟩ | ⟨hb13, hb32, hbne32⟩
    · exact ⟨4, by omega, contByteSegScanFree (ContAC₄ C) _ hseg8.inv' rfl h35 hcond hend
        h8end hbit hb13 hb32 hbne13⟩
    · exact ⟨3, by omega, contByteSegLow (ContAC₄ C) _ hseg8.inv' rfl h35 hcond hend
        h8end hbit hb13 hbns⟩
    · exact ⟨4, by omega, contByteSegHigh (ContAC₄ C) _ hseg8.inv' rfl h35 hcond hend
        h8end hbit hb13 hb32 hbne32⟩
  obtain ⟨nR, hnR, hseam⟩ := hseam
  have hhead : WalkSegment (stage2Calls stage2SubCalls) G C s (ContSeamC C)
      (contSeamByte (contLandS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
        (contIx G C) (contB35 G doc.v)) doc.v.toNat C.stage.tok (contB35 G doc.v)
        (hlastByte G C) doc.hb) (8 + nR) :=
    hseg8.trans (Seg.measure hseam)
  -- the class-C span's five
  have h8c : evalOperand (contSeamByte (contLandS C s (hlastByte G C) (hlastIncV C)
      (hlastNepV G) G.ep doc.v (contIx G C) (contB35 G doc.v)) doc.v.toNat C.stage.tok
      (contB35 G doc.v) (hlastByte G C) doc.hb) (.reg "%8") =
      some (.int 8 (hlastByte G C)) := by
    refine LeanLLVM.evalOperand_reg_of ?_
    rw [contSeamByte_env8, contLandS_env8]
    exact hInv.iter.reg8
  have hspan5 : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
      (contSeamByte (contLandS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
        (contIx G C) (contB35 G doc.v)) doc.v.toNat C.stage.tok (contB35 G doc.v)
        (hlastByte G C) doc.hb) (ContTailStartC C)
      (contTailStartOfDoc (G := G) C s doc) 5 :=
    walkHeadChainCSeg (G := G) (C := ContSeamC C)
      (s := contSeamByte (contLandS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep
        doc.v (contIx G C) (contB35 G doc.v)) doc.v.toNat C.stage.tok (contB35 G doc.v)
        (hlastByte G C) doc.hb) hhead.inv' rfl h8c
      (hlast_slt_zero_of_toInt_le (by decide) hlt125)
      (hlast_slt_zero_of_toInt_le (by decide) hlt125)
      (hlast_eq_zero_of_slt_zero (by decide) hlt125)
  exact ⟨(8 + nR) + 5, by omega, hhead.trans (Seg.measure hspan5)⟩

/-- **The seam carries the invariant**, from the row: the chain's own `inv'`. -/
theorem contTailStartInv_of_doc {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (doc : HcontCleanupDoc G C s) :
    WalkInv G (ContTailStartC C) (contTailStartOfDoc (G := G) C s doc) := by
  obtain ⟨nP, _hnP, hseg⟩ := hcontSpan17_of_doc hInv hblock hk hlt125 hne125 doc
  exact hseg.inv'

/-! ### The seam's cells, from that invariant

The seam's own blocks bind `%Pivot63`, `%SwitchLeaf55`, `%SwitchLeaf59`, `%or.cond677.i`,
`%or.cond524.i`, `%37`, `%cmp376.i`, `%ee.1.i`, `%cmp343.i`, `%34`, `%conv347.i`,
`%cond350.i`, `%35`, `%gep`, `%Pivot42`, `%Pivot40` and `%SwitchLeaf36`.  None of them is
a cell read below, so each lookup is the head's, read through the binds.  The peels are
`contTailStartByte`'s (`JsonStage2WalkDispatchSegments`), at the route this row names. -/

theorem contTailStartOfDoc_envKind {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (doc : HcontCleanupDoc G C s)
    (h : lookupName s.env "%kind404.i" = some (.ptr (C.stage.tok + 16))) :
    lookupName (contTailStartOfDoc (G := G) C s doc).env "%kind404.i" =
      some (.ptr (C.stage.tok + 16)) :=
  contTailStartByte_envKind C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
    (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C) doc.hb h

theorem contTailStartOfDoc_envRootDone {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (doc : HcontCleanupDoc G C s)
    (h : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8))) :
    lookupName (contTailStartOfDoc (G := G) C s doc).env "%root_done.i" =
      some (.ptr (G.next0 + 8)) :=
  contTailStartByte_envRootDone C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
    (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C) doc.hb h

theorem contTailStartOfDoc_envC {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (doc : HcontCleanupDoc G C s)
    (h : lookupName s.env "%c.i" = some (.ptr C.stage.c)) :
    lookupName (contTailStartOfDoc (G := G) C s doc).env "%c.i" = some (.ptr C.stage.c) :=
  contTailStartByte_envC C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
    (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C) doc.hb h

theorem contTailStartOfDoc_envTok {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (doc : HcontCleanupDoc G C s)
    (h : lookupName s.env "%t352.i" = some (.ptr C.stage.tok)) :
    lookupName (contTailStartOfDoc (G := G) C s doc).env "%t352.i" =
      some (.ptr C.stage.tok) :=
  contTailStartByte_envTok C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
    (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C) doc.hb h

theorem contTailStartOfDoc_envZ {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (doc : HcontCleanupDoc G C s)
    (h : lookupName s.env "%z" = some (.ptr C.stage.z)) :
    lookupName (contTailStartOfDoc (G := G) C s doc).env "%z" = some (.ptr C.stage.z) :=
  contTailStartByte_envZ C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
    (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C) doc.hb h

theorem contTailStartOfDoc_pre {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (doc : HcontCleanupDoc G C s) :
    (contTailStartOfDoc (G := G) C s doc).pre = some "if.else405.i" :=
  contTailStartByte_pre C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
    (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C) doc.hb

/-- **The seam's `phi` selects the literal `0` on that edge.**  The kind word `%kind404.i`
carries is the incoming literal the block's `phi` names, and `if.else405.i`'s entry is
`0`. -/
theorem contTailStart_phi :
    phiIncoming "if.else405.i"
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] =
      some (.imm (.int 32 (BitVec.ofNat 32 0))) := by
  decide

theorem contTailStartOfDoc_op {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (doc : HcontCleanupDoc G C s) :
    evalOperand (stateAt (contTailStartOfDoc (G := G) C s doc).env
      (contTailStartOfDoc (G := G) C s doc)) (.imm (.int 32 (BitVec.ofNat 32 0))) =
      some (.int 32 (BitVec.ofNat 32 0)) :=
  contTailStartByte_op C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
    (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C) doc.hb

/-- **The root slot's word at the seam is the head's**, across the seam's three stores. -/
theorem contTailStartOfDoc_rootRead {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (doc : HcontCleanupDoc G C s) {rdv : BitVec 32}
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)) :
    readBytes (contTailStartOfDoc (G := G) C s doc).mem (G.next0 + 8) 4 =
      some (natToBytes rdv.toNat 4) :=
  contTailStartByte_rootRead C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
    (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C) doc.hb hroot

/-! ### The class's arm, at the rows

`hcontArm_cleanup_of_calls` takes the seam's cells as premises; the producers above
supply them from the row and the invariant, and the tail is `hcontTailByte_of_calls`'s at
the byte's route.  So what the arm takes beside the row and the lane's root word is the
three callee rows and the two word agreements. -/

/-- **The default-value class's continuing arm, at the rows.**  The tail is
`hcontTailByte_of_calls`'s at the row's own seam, the chain is `hcontSpan17_of_doc`'s, the
seam's cells are the lemmas above, and the two words `cA`/`rdv` are the state's — the
callee group must carry those, which is the pair of equalities below. -/
theorem hcontArm_cleanup_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (doc : HcontCleanupDoc G C s)
    {rdv0 : BitVec 32}
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv0.toNat 4))
    (calls : HcontSeamCalls G (ContTailStartC C) (contTailStartOfDoc (G := G) C s doc))
    (hcA : calls.cA = BitVec.ofNat 32 0) (hrdv : calls.rdv = rdv0) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hInvS := contTailStartInv_of_doc hInv hblock hk hlt125 hne125 doc
  have hopS : evalOperand
      (stateAt (contTailStartOfDoc (G := G) C s doc).env
        (contTailStartOfDoc (G := G) C s doc)) (.imm (.int 32 (BitVec.ofNat 32 0))) =
      some (.int 32 calls.cA) := by
    rw [hcA]
    exact contTailStartOfDoc_op (G := G) (C := C) (s := s) doc
  have hrootS : readBytes (contTailStartOfDoc (G := G) C s doc).mem (G.next0 + 8) 4 =
      some (natToBytes rdv0.toNat 4) :=
    contTailStartOfDoc_rootRead (G := G) (C := C) (s := s) doc hroot
  have hreadRoot : readBytes
      (writeBytes (contTailStartOfDoc (G := G) C s doc).mem (C.stage.tok + 16)
        (natToBytes calls.cA.toNat 4)) (G.next0 + 8) 4 =
      some (natToBytes calls.rdv.toNat 4) := by
    rw [hcA, hrdv]
    rw [walkReadBytes_writeBytes_outside (v := natToBytes (BitVec.ofNat 32 0).toNat 4)
      (start := C.stage.tok + 16) (addr := G.next0 + 8) (n := 4) ?_]
    · exact hrootS
    · right
      have h := C.stage.sevenEnd (C.stage.tok, stage2TokenExtent)
        (by simp [stage2StagedWrites])
      have hlen : (natToBytes (BitVec.ofNat 32 0).toNat 4).length = 4 :=
        natToBytes_length _ _
      simp only [stage2TokenExtent] at h
      omega
  have hkindS := contTailStartOfDoc_envKind (G := G) (C := C) (s := s) doc
    (hInv.regs ("%kind404.i", .ptr (C.stage.tok + 16)) (by simp [walkStaticRegs]))
  have hrdS := contTailStartOfDoc_envRootDone (G := G) (C := C) (s := s) doc
    (hInv.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs]))
  have hcS := contTailStartOfDoc_envC (G := G) (C := C) (s := s) doc
    (hInv.regs ("%c.i", .ptr C.stage.c) (by simp [walkStaticRegs]))
  have htS := contTailStartOfDoc_envTok (G := G) (C := C) (s := s) doc
    (hInv.regs ("%t352.i", .ptr C.stage.tok) (by simp [walkStaticRegs]))
  have hzS := contTailStartOfDoc_envZ (G := G) (C := C) (s := s) doc
    (hInv.regs ("%z", .ptr C.stage.z) (by simp [walkStaticRegs]))
  have htightS : (ContTailStartC C).events.length ≤ (ContTailStartC C).k :=
    hInv.events_le_of_tight (by rw [hblock]; decide)
  have hkltS : (ContTailStartC C).k < G.nep := Nat.lt_of_succ_lt hk
  obtain ⟨ev, hTail⟩ :=
    hcontTailByte_of_calls G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
      (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C) doc.hb
      calls.r₁ calls.r₂ calls.r₃ hInvS rfl "if.else405.i"
      (contTailStartOfDoc_pre (G := G) (C := C) (s := s) doc) contTailStart_phi hopS
      hkindS hrdS hreadRoot
      calls.hpre₁ calls.hcall₁ calls.hret₁ calls.hbit0 calls.hzread hcS htS hzS
      calls.hpre₂ calls.hcall₂ calls.hret₂ calls.hev64 htightS hkltS
      calls.hpre₃ calls.hcall₃ (by have := doc.v.isLt; omega)
  exact ⟨hcontArm_cleanup_of_staging G C s hInv hk hlt125 hne125 doc.hread doc.hspan
    doc.hugt doc.hb calls.r₁ calls.r₂ calls.r₃ ev (cA := calls.cA) (rdv := calls.rdv)
    (xA := calls.xA) hTail⟩

/-- **The default-value class's continuing dispatch, at the rows.** -/
theorem walkDispatch_at_cleanup_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (doc : HcontCleanupDoc G C s)
    {rdv0 : BitVec 32}
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv0.toNat 4))
    (calls : HcontSeamCalls G (ContTailStartC C) (contTailStartOfDoc (G := G) C s doc))
    (hcA : calls.cA = BitVec.ofNat 32 0) (hrdv : calls.rdv = rdv0) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨arm⟩ := hcontArm_cleanup_of_rows hInv hblock hk hlt125 hne125 doc hroot calls
    hcA hrdv
  exact HcontArm.dispatch hInv hblock hk arm

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontSpan17_of_doc
#print axioms LeanLLVM.Refinement.WalkScope.contTailStartInv_of_doc
#print axioms LeanLLVM.Refinement.WalkScope.contTailStartOfDoc_envKind
#print axioms LeanLLVM.Refinement.WalkScope.contTailStartOfDoc_envRootDone
#print axioms LeanLLVM.Refinement.WalkScope.contTailStartOfDoc_envC
#print axioms LeanLLVM.Refinement.WalkScope.contTailStartOfDoc_envTok
#print axioms LeanLLVM.Refinement.WalkScope.contTailStartOfDoc_envZ
#print axioms LeanLLVM.Refinement.WalkScope.contTailStartOfDoc_pre
#print axioms LeanLLVM.Refinement.WalkScope.contTailStartOfDoc_op
#print axioms LeanLLVM.Refinement.WalkScope.contTailStartOfDoc_rootRead
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_cleanup_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_cleanup_of_rows

end WalkScope
end LeanLLVM.Refinement
