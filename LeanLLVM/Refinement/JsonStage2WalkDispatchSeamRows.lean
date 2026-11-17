/-
# The high-byte route's seam, as cells the state supplies

`JsonStage2WalkDispatchSegments` builds `.cleanup`'s arm and its tail from three callee
rows, and every other premise it takes at the seam is a **cell of the seam's own state**:
the predecessor and its `phi`, the kind word that `phi` selects, `%kind404.i`,
`%root_done.i`, `%c.i`, `%t352.i`, `%z`, and the root slot's word the copy call's argument
list carries.  This module produces them, so a producer of the class hands its document
row and the callee rows and nothing else:

* the **seam invariant**, from the class's document row alone
  (`contTailStartInv_of_doc`): the head's twelve links (`hcontHeadSeg12`) and the class-C
  span's five (`walkHeadChainCSeg`) at the row's own word, byte and class;
* the **environment cells**, from that invariant's `regs` (`contTailStart_envKind` and its
  four siblings): every one of the names is in `walkStaticRegs`, and the seam's blocks bind
  none of them;
* the **predecessor and its `phi`** (`contTailStart_pre`, `contTailStart_phi`) and the kind
  word it selects (`contTailStart_op`), which is the literal `0` at `if.else405.i`;
* the **root slot's word**, `0`, transported across the seam's one store
  (`contTailStart_mem`, `contTailStart_rootRead`) from the lane's `root` row;
* the **arm itself** (`hcontArm_cleanup_of_rows`), at the callee rows and those cells.

## The rows this does not produce, and why

The callee rows themselves — `HcontSeamCalls`'s three preconditions and three answers at
the staged argument lists — are the helper contracts' applications at the walk's own
arguments.  `JsonStage2WalkDispatchSeams` states the group and
`JsonStage2WalkDispatchSegments` consumes it; this module neither restates them nor
assumes them: the arm below takes the group.

The group carries two **word** fields, `cA` (the kind literal at `%kind404.i`) and `rdv`
(the root-done slot's word).  Both are cells of the seam state, and this module produces
both — `contTailStart_phi` names the first `0` and `contTailStart_rootRead` the second — so
the two equalities `hcontArm_cleanup_of_rows` takes (`hcA`, `hrdv`) are the *agreement* of
the caller's group with the state, not a second reading of it.  A caller that supplied the
head's words instead of the seam's would fail them, which is what makes the pair worth
stating rather than folding into the group.
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

/-- **The seam state a document row names**: `contTailStart` at the row's word and byte,
the invariant's index, the counts and the entry's byte. -/
abbrev contTailStartOfDoc {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (doc : HcontCleanupDoc G C s) : State :=
  contTailStart C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v (contIx G C)
    (contB35 G doc.v) (hlastByte G C) (hlastByte G C)

/-! ### The seventeen links, from the row

`hcontSpan17_of_cleanup` reads the bundle's fields; the bundle's non-tail fields are the
document row's, the invariant's and the class's, so the same seventeen links are stated at
those and the bundle is no longer an input. -/

/-- **The class's seventeen links, at its document row.**  The head's twelve
(`hcontHeadSeg12`) and the class-C span's five (`walkHeadChainCSeg`), at the row's word,
its byte and its class.  Every argument of the head chain is a cell the invariant or the
row supplies (`cont_ult_one`, `contAS5_env*`, `cont_hi63`, `cont_hread35`, the two static
rows), so the only inputs are the invariant, the head block, the class's two bits and the
row. -/
theorem hcontSpan17_of_doc {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (doc : HcontCleanupDoc G C s) :
    WalkSegment (stage2Calls stage2SubCalls) G C s (ContTailStartC C)
      (contTailStartOfDoc (G := G) C s doc) 17 := by
  have hspan : doc.v.toNat ≤ entryPos G (C.k + 1) := doc.hspan
  have hgt : entryPos G C.k < doc.v.toNat := contLane_gt G C hk doc.hugt
  have heicd : doc.v.toNat - 1 < doc.v.toNat := by omega
  have hhead :
      WalkSegment (stage2Calls stage2SubCalls) G C s (ContSeamC C)
        (contSeamS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v (contIx G C)
          (contB35 G doc.v) (hlastByte G C)) 12 :=
    hcontHeadSeg12 (G := G) (C := C) (s := s) hInv hblock
      (x := hlastByte G C) (inc := hlastIncV C) (nep := hlastNepV G) (ep := G.ep)
      (v := doc.v) (ix := contIx G C) (b35 := contB35 G doc.v) (b8 := hlastByte G C)
      (by
        show evalOperand s (.reg "%8") = some (.int 8 (hlastByte G C))
        simp only [evalOperand]
        exact hInv.iter.reg8)
      (hlast_slt_zero_of_toInt_le (by decide) hlt125)
      (hlast_slt_zero_of_toInt_le (by decide) hlt125)
      hlt125 hne125
      (by
        show evalOperand (headAS₄ s (hlastByte G C)) (.reg "%inc.i") =
          some (.int 64 (hlastIncV C))
        simp only [evalOperand]
        rw [headAS4_envInc s (hlastByte G C)]
        exact hInv.inc_reg)
      (by
        show evalOperand (headAS₄ s (hlastByte G C)) (.reg "%nep") =
          some (.int 64 (hlastNepV G))
        simp only [evalOperand]
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
      doc.hb13 doc.hb32 doc.hbne13
      (by
        show lookupName (contP35S C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
          (contIx G C) (contB35 G doc.v)).env "%end.i" = some (.ptr (C.stage.tok + 8))
        rw [contP35S_envEnd]
        exact hInv.regs ("%end.i", .ptr (C.stage.tok + 8)) (by simp [walkStaticRegs]))
      (by
        show lookupName (contP35S C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
          (contIx G C) (contB35 G doc.v)).env "%8" = some (.int 8 (hlastByte G C))
        rw [contP35S_env8]
        exact hInv.iter.reg8)
      (hlast_bit6_of_class hlt125 hne125)
  have hspan5 : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
      (contSeamS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v (contIx G C)
        (contB35 G doc.v) (hlastByte G C)) (ContTailStartC C)
      (contTailStartOfDoc (G := G) C s doc) 5 :=
    walkHeadChainCSeg (G := G) (C := ContSeamC C)
      (s := contSeamS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v (contIx G C)
        (contB35 G doc.v) (hlastByte G C)) hhead.inv' rfl
      (by
        show evalOperand (contSeamS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
          (contIx G C) (contB35 G doc.v) (hlastByte G C)) (.reg "%8") =
          some (.int 8 (hlastByte G C))
        simp only [evalOperand]
        rw [contSeamS_env8, contP35S_env8]
        exact hInv.iter.reg8)
      (hlast_slt_zero_of_toInt_le (by decide) hlt125)
      (hlast_slt_zero_of_toInt_le (by decide) hlt125)
      (hlast_eq_zero_of_slt_zero (by decide) hlt125)
  exact hhead.trans (Seg.measure hspan5)

/-- **The seam carries the invariant**, from the row: the chain's own `inv'`. -/
theorem contTailStartInv_of_doc {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (doc : HcontCleanupDoc G C s) :
    WalkInv G (ContTailStartC C) (contTailStartOfDoc (G := G) C s doc) :=
  (hcontSpan17_of_doc hInv hblock hk hlt125 hne125 doc).inv'

/-! ### The seam's cells, from that invariant

The seam's own blocks bind `%Pivot63`, `%SwitchLeaf55`, `%SwitchLeaf59`, `%or.cond677.i`,
`%or.cond524.i`, `%37`, `%cmp376.i`, `%ee.1.i`, `%cmp343.i`, `%34`, `%conv347.i`,
`%cond350.i`, `%35`, `%gep`, `%Pivot42`, `%Pivot40` and `%SwitchLeaf36`.  None of them is
a cell read below, so each lookup is the head's, read through the binds. -/

/-- **`%kind404.i` at the seam** is the token record's kind slot: `walkStaticRegs`'s row,
which the seam binds nothing over. -/
theorem contTailStart_envKind {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8)
    (h : lookupName s.env "%kind404.i" = some (.ptr (C.stage.tok + 16))) :
    lookupName (contTailStart C s x inc nep ep v ix b35 b8 x1).env "%kind404.i" =
      some (.ptr (C.stage.tok + 16)) := by
  simp only [contTailStart, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, contSeamS, seamS,
    seamFin, contP35S, contP39S, contP41S, contLandS, contEndS, cte345OutAt,
    condEnd349OutAt, contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- **`%root_done.i` at the seam** is the root slot's pointer. -/
theorem contTailStart_envRootDone {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8)
    (h : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8))) :
    lookupName (contTailStart C s x inc nep ep v ix b35 b8 x1).env "%root_done.i" =
      some (.ptr (G.next0 + 8)) := by
  simp only [contTailStart, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, contSeamS, seamS,
    seamFin, contP35S, contP39S, contP41S, contLandS, contEndS, cte345OutAt,
    condEnd349OutAt, contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- **`%c.i` at the seam** is the cursor record. -/
theorem contTailStart_envC {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8)
    (h : lookupName s.env "%c.i" = some (.ptr C.stage.c)) :
    lookupName (contTailStart C s x inc nep ep v ix b35 b8 x1).env "%c.i" =
      some (.ptr C.stage.c) := by
  simp only [contTailStart, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, contSeamS, seamS,
    seamFin, contP35S, contP39S, contP41S, contLandS, contEndS, cte345OutAt,
    condEnd349OutAt, contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- **`%t352.i` at the seam** is the token record's base. -/
theorem contTailStart_envTok {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8)
    (h : lookupName s.env "%t352.i" = some (.ptr C.stage.tok)) :
    lookupName (contTailStart C s x inc nep ep v ix b35 b8 x1).env "%t352.i" =
      some (.ptr C.stage.tok) := by
  simp only [contTailStart, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, contSeamS, seamS,
    seamFin, contP35S, contP39S, contP41S, contLandS, contEndS, cte345OutAt,
    condEnd349OutAt, contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- **`%z` at the seam** is the log. -/
theorem contTailStart_envZ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8)
    (h : lookupName s.env "%z" = some (.ptr C.stage.z)) :
    lookupName (contTailStart C s x inc nep ep v ix b35 b8 x1).env "%z" =
      some (.ptr C.stage.z) := by
  simp only [contTailStart, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, contSeamS, seamS,
    seamFin, contP35S, contP39S, contP41S, contLandS, contEndS, cte345OutAt,
    condEnd349OutAt, contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- **The seam's predecessor is `if.else405.i`**: `if.end372.i`'s empty body leaves for
`if.then413.i` on that arm, and `HeadS413` names the predecessor. -/
theorem contTailStart_pre {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8) :
    (contTailStart C s x inc nep ep v ix b35 b8 x1).pre = some "if.else405.i" := by
  simp only [contTailStart, HeadS413, HeadS405]

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

/-- **The kind word the seam's `phi` selects** is `0`: the operand is a literal, so no
environment cell is read. -/
theorem contTailStart_op {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8) :
    evalOperand (stateAt (contTailStart C s x inc nep ep v ix b35 b8 x1).env
      (contTailStart C s x inc nep ep v ix b35 b8 x1))
      (.imm (.int 32 (BitVec.ofNat 32 0))) =
      some (.int 32 (BitVec.ofNat 32 0)) := by
  simp only [evalOperand, Const.toValue]

/-! ### The seam's memory

The chain stores three times, all inside the token record: `cond.true345.i`'s end word at
`%t352.i`, `cond.end349.i`'s gap at `+ 20`, and `if.end372.i`'s token end at `+ 8`.  Every
other link binds cells.  The root slot is above every staged object
(`WalkStage.sevenEnd`), so its word is the lane's.

The three stores are audited by the register's own extent rather than one at a time: a
store at an offset whose record extent covers it leaves the root slot alone
(`walkReadBytes_rootSlot_of_tokStore`). -/

/-- **The seam's memory, exactly**: the head's with the three token-record stores.  The
chain's binds leave the memory alone, and `seamFin`'s token end is the outermost. -/
theorem contTailStart_mem {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8) :
    (contTailStart C s x inc nep ep v ix b35 b8 x1).mem =
      writeBytes (writeBytes (writeBytes s.mem C.stage.tok (natToBytes ix.toNat 8))
        (C.stage.tok + 20) (natToBytes (BitVec.ofNat 32 1).toNat 4)) (C.stage.tok + 8)
        (natToBytes (BitVec.ofNat 64 v.toNat).toNat 8) := by
  simp only [contTailStart, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, contSeamS, seamS,
    seamFin, contP35S, contP39S, contP41S, contLandS, contEndS, cte345OutAt,
    condEnd349OutAt, contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, stateAt, cells, State.bind]

/-- **The root slot's word at the seam is the head's.**  The three stores are inside the
token record, so the word the copy call's argument list carries is the lane's zero. -/
theorem contTailStart_rootRead {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4)) :
    readBytes (contTailStart C s x inc nep ep v ix b35 b8 x1).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4) := by
  rw [contTailStart_mem]
  rw [walkReadBytes_rootSlot_of_tokStore (off := 8) (len := 8)
    (v := natToBytes (BitVec.ofNat 64 v.toNat).toNat 8) (by decide) (natToBytes_length _ _)]
  rw [walkReadBytes_rootSlot_of_tokStore (off := 20) (len := 4)
    (v := natToBytes (BitVec.ofNat 32 1).toNat 4) (by decide) (natToBytes_length _ _)]
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

/-! ### The same cells at the row's own state name

The lemmas above are stated at `contTailStart`'s own parameters; the arm reads
`contTailStartOfDoc`, so each is restated there once.  Nothing is proved twice: each is
the general lemma at the row's witness. -/

theorem contTailStartOfDoc_envKind {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (doc : HcontCleanupDoc G C s)
    (h : lookupName s.env "%kind404.i" = some (.ptr (C.stage.tok + 16))) :
    lookupName (contTailStartOfDoc (G := G) C s doc).env "%kind404.i" =
      some (.ptr (C.stage.tok + 16)) :=
  contTailStart_envKind C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
    (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C) h

theorem contTailStartOfDoc_envRootDone {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (doc : HcontCleanupDoc G C s)
    (h : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8))) :
    lookupName (contTailStartOfDoc (G := G) C s doc).env "%root_done.i" =
      some (.ptr (G.next0 + 8)) :=
  contTailStart_envRootDone C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
    (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C) h

theorem contTailStartOfDoc_envC {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (doc : HcontCleanupDoc G C s)
    (h : lookupName s.env "%c.i" = some (.ptr C.stage.c)) :
    lookupName (contTailStartOfDoc (G := G) C s doc).env "%c.i" = some (.ptr C.stage.c) :=
  contTailStart_envC C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
    (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C) h

theorem contTailStartOfDoc_envTok {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (doc : HcontCleanupDoc G C s)
    (h : lookupName s.env "%t352.i" = some (.ptr C.stage.tok)) :
    lookupName (contTailStartOfDoc (G := G) C s doc).env "%t352.i" =
      some (.ptr C.stage.tok) :=
  contTailStart_envTok C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
    (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C) h

theorem contTailStartOfDoc_envZ {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (doc : HcontCleanupDoc G C s)
    (h : lookupName s.env "%z" = some (.ptr C.stage.z)) :
    lookupName (contTailStartOfDoc (G := G) C s doc).env "%z" = some (.ptr C.stage.z) :=
  contTailStart_envZ C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
    (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C) h

theorem contTailStartOfDoc_pre {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (doc : HcontCleanupDoc G C s) :
    (contTailStartOfDoc (G := G) C s doc).pre = some "if.else405.i" :=
  contTailStart_pre G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
    (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C)

theorem contTailStartOfDoc_op {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (doc : HcontCleanupDoc G C s) :
    evalOperand (stateAt (contTailStartOfDoc (G := G) C s doc).env
      (contTailStartOfDoc (G := G) C s doc)) (.imm (.int 32 (BitVec.ofNat 32 0))) =
      some (.int 32 (BitVec.ofNat 32 0)) :=
  contTailStart_op G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
    (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C)

/-! ### The class's arm, at the rows

`hcontArm_cleanup_of_calls` takes the seam's cells as premises; the two producers above
supply them from the row and the invariant, so what this theorem takes is the document row,
the lane's root word, the three callee rows and the two word agreements. -/

/-- **The scan-free continuing arm, at the rows.**  The chain is `hcontSpan17_of_doc`'s,
the seam's cells are the lemmas above, and the two words `cA`/`rdv` are the state's
(`contTailStart_phi`, `contTailStart_rootRead`) — the callee group must carry those, which
is the pair of equalities below. -/
theorem hcontArm_cleanup_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (doc : HcontCleanupDoc G C s)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (calls : HcontSeamCalls G (ContTailStartC C) (contTailStartOfDoc (G := G) C s doc))
    (hcA : calls.cA = BitVec.ofNat 32 0) (hrdv : calls.rdv = BitVec.ofNat 32 0) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hInvS := contTailStartInv_of_doc hInv hblock hk hlt125 hne125 doc
  have hopS : evalOperand
      (stateAt (contTailStartOfDoc (G := G) C s doc).env
        (contTailStartOfDoc (G := G) C s doc)) (.imm (.int 32 (BitVec.ofNat 32 0))) =
      some (.int 32 calls.cA) := by
    rw [hcA]
    exact contTailStartOfDoc_op (G := G) (C := C) (s := s) doc
  have hrootS : readBytes (contTailStartOfDoc (G := G) C s doc).mem (G.next0 + 8) 4 =
      some (natToBytes 0 4) :=
    contTailStart_rootRead (G := G) (C := C) (s := s) (x := hlastByte G C)
      (inc := hlastIncV C) (nep := hlastNepV G) (ep := G.ep) (v := doc.v) (ix := contIx G C)
      (b35 := contB35 G doc.v) (b8 := hlastByte G C) (x1 := hlastByte G C) hroot
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
  exact hcontArm_cleanup_of_calls G C s hInv hk hlt125 hne125 doc.hread doc.hspan doc.hugt
    doc.hb13 doc.hb32 doc.hbne13 calls.r₁ calls.r₂ calls.r₃
    (cA := calls.cA) (rdv := calls.rdv) (xA := calls.xA) "if.else405.i" hInvS rfl
    (contTailStartOfDoc_pre (G := G) (C := C) (s := s) doc) contTailStart_phi hopS hkindS
    hrdS hreadRoot
    calls.hpre₁ calls.hcall₁ calls.hret₁ calls.hbit0 calls.hzread hcS htS hzS
    calls.hpre₂ calls.hcall₂ calls.hret₂ calls.hev64 htightS hkltS
    calls.hpre₃ calls.hcall₃ (by have := doc.v.isLt; omega)

/-- **The scan-free continuing dispatch, at the rows.** -/
theorem walkDispatch_at_cleanup_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (doc : HcontCleanupDoc G C s)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (calls : HcontSeamCalls G (ContTailStartC C) (contTailStartOfDoc (G := G) C s doc))
    (hcA : calls.cA = BitVec.ofNat 32 0) (hrdv : calls.rdv = BitVec.ofNat 32 0) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨arm⟩ := hcontArm_cleanup_of_rows hInv hblock hk hlt125 hne125 doc hroot calls
    hcA hrdv
  exact HcontArm.dispatch hInv hblock hk arm

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontSpan17_of_doc
#print axioms LeanLLVM.Refinement.WalkScope.contTailStartInv_of_doc
#print axioms LeanLLVM.Refinement.WalkScope.contTailStart_envKind
#print axioms LeanLLVM.Refinement.WalkScope.contTailStart_envRootDone
#print axioms LeanLLVM.Refinement.WalkScope.contTailStart_envC
#print axioms LeanLLVM.Refinement.WalkScope.contTailStart_envTok
#print axioms LeanLLVM.Refinement.WalkScope.contTailStart_envZ
#print axioms LeanLLVM.Refinement.WalkScope.contTailStart_pre
#print axioms LeanLLVM.Refinement.WalkScope.contTailStart_phi
#print axioms LeanLLVM.Refinement.WalkScope.contTailStart_op
#print axioms LeanLLVM.Refinement.WalkScope.contTailStart_mem
#print axioms LeanLLVM.Refinement.WalkScope.contTailStart_rootRead
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_cleanup_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_cleanup_of_rows

end WalkScope
end LeanLLVM.Refinement
