/-
# The default arm's scan-free classes, at their rows

`JsonStage2WalkDispatchDefaultLane` produces the default arm's head chain for all six
head-switch classes and hands the three scan-free arms a tail as an argument.  This module
produces that tail from the callee rows, so the classes' arms take a head chain and one
group of calls and nothing else:

* the **seam invariant** is the chain's own `inv'` extended by the class's span
  (`lettersSeamInv_of_chain`, `fLetterSeamInv_of_chain`);
* the **seam's cells** are one structure, `HcontSeamCells`: the predecessor and the `phi`
  it selects with the value that `phi` names, the four static pointers, the root slot's
  word, and the two test cells `%ee.1.i`/`%cond350.i`.  For the letters route and its
  `'f'` leaf it is produced from the chain (`lettersSeamCells_of_chain`,
  `fLetterSeamCells_of_chain`): the pair is the lane's one `Nat` (`contSeamMid_ee`,
  `contSeamMid_cond`), the root word is the head's transported across the suffix's three
  token-record stores (`contSeamMid_rootRead`), and the kind literal is the arm's own;
* the **tail** is `emptyTail_of_cells`, which is `emptyTailSeg_of_calls` at one seam's
  cells, so the three calls' outcomes are the callee rows' and no segment is taken;
* the **arms** are `hcontArm_letters_of_rows`, `hcontArm_fLetter_of_rows` and
  `hcontArm_classC_of_rows`.

## What the class-C arm still takes, and why

The class-C span returns its endpoint existentially (`classCSpan_at`): which of four leaves
the byte takes decides the target carry *and* the state, and the four differ.  The arm
therefore takes the endpoint's `HcontSeamCells` as its row — the three cells plus the four
pointers and the `phi` at that state — while the tail itself is produced.  For the letters
route and its leaf, whose seams are the named states `LetS413` and `FS413`, the cells are
produced instead, which is why those two arms take no seam row at all.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchSeamRows
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassRows
import LeanLLVM.Refinement.JsonStage2WalkDispatchDefaultLane
import LeanLLVM.Refinement.JsonStage2WalkDispatchFLetter

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The seam's cells, as one structure

`emptyTailSeg_of_calls` reads, beside the callee rows: the predecessor, the `phi` it
selects and the value that `phi` names (the kind literal), the four static pointers, the
root slot's word at the post-store memory, and the two test cells.  Stated as data so a
class whose seam is a named state produces them once and a class whose seam is an
existential endpoint states them as its row.
-/

/-- **The seam's own cells**: everything `emptyTailSeg_of_calls` reads at a tail start
beside the callee rows, at the callee group's own kind literal `cA` and root word `rdv`.
`cd` is the one `Nat` both of the copy call's test cells hold. -/
structure HcontSeamCells {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (cA rdv : BitVec 32) : Type where
  /-- The block `s` came from: the `phi`'s predecessor. -/
  p : String
  /-- The operand the `phi` selects there. -/
  op : Operand
  hpre : s.pre = some p
  hphi : phiIncoming p
    [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
     ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
     ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
     ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
     ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some op
  hop : evalOperand (stateAt s.env s) op = some (.int 32 cA)
  hkind : lookupName s.env "%kind404.i" = some (.ptr (C.stage.tok + 16))
  hrd : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8))
  hc : lookupName s.env "%c.i" = some (.ptr (TailCarry₂ C).stage.c)
  ht : lookupName s.env "%t352.i" = some (.ptr (TailCarry₂ C).stage.tok)
  ho : lookupName s.env "%z" = some (.ptr (TailCarry₂ C).stage.z)
  /-- The root slot's word at the memory the first call reads. -/
  hreadRoot : readBytes
    (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)) (G.next0 + 8) 4 =
      some (natToBytes rdv.toNat 4)
  /-- The copy call's two test cells: the token's end and the entry's span bound. -/
  cd : Nat
  hei : lookupName s.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 cd))
  hcd : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd))
  hcd64 : cd < 2 ^ 64

/-! ### The tail, at those cells -/

/-- **The scan-free tail, at a seam's cells and the callee rows.**  `emptyTailSeg_of_calls`
at the cells above: the three calls, then the copy call's `ult cd cd`, so the segment ends
at `if.end473.i` with no scan entered.  The cells are stated at the callee group's own kind
literal and root word, so there is no agreement equation beside them. -/
theorem emptyTail_of_cells {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (calls : HcontSeamCalls G C s) (cells : HcontSeamCells C s calls.cA calls.rdv)
    (hInv : WalkInv G C s)
    (hblock : C.block = "if.then413.i") (htight : C.events.length ≤ C.k)
    (hklt : C.k < G.nep) :
    ∃ ev : EventRecord,
      WalkSegment (stage2Calls stage2SubCalls) G C s (TailCarryEnd C ev)
        (ScanEntry s calls.r₁ calls.r₂ calls.r₃ cells.cd cells.cd calls.cA calls.rdv
          calls.xA) 3 :=
  emptyTailSeg_of_calls G C s calls.r₁ calls.r₂ calls.r₃ cells.cd hInv hblock
    "if.else405.i" cells.hpre cells.hphi cells.hop cells.hkind cells.hrd cells.hreadRoot
    calls.hpre₁ calls.hcall₁ calls.hret₁ calls.hbit0 calls.hzread cells.hc cells.ht cells.ho
    calls.hpre₂ calls.hcall₂ calls.hret₂ calls.hev64 htight hklt calls.hpre₃ calls.hcall₃
    cells.hei cells.hcd cells.hcd64

/-- **`%t352.i` at the tail's end is the seam's token record.**  The three calls bind
their own cells and none is the record's base, so the copy call's argument reads the
seam's. -/
theorem scanEntry_envTok (s : State) (r₁ r₂ r₃ : CallOutcome)
    {ei cd : Nat} (cA rdv xA : BitVec 32) {tok : Nat}
    (h : lookupName s.env "%t352.i" = some (.ptr tok)) :
    lookupName (ScanEntry s r₁ r₂ r₃ ei cd cA rdv xA).env "%t352.i" = some (.ptr tok) := by
  simp only [ScanEntry, TailS₃, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-! ### The letters route's seam, from the chain -/

/-- **The letters seam carries the invariant**, from the chain: the head chain's own
`inv'` at `if.else387.i` composed with `lettersSpan`'s four links. -/
theorem lettersSeamInv_of_chain {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    {x : BitVec 8} (ch : HcontHeadChain G C s x)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0) :
    WalkInv G (HeadC₄₁₃ (LetC₄₀₅ ch.Cm)) (LetS413 ch.sm x) := by
  have hspan : Seg (stage2Calls stage2SubCalls) G ch.Cm ch.sm
      (HeadC₄₁₃ (LetC₄₀₅ ch.Cm)) (LetS413 ch.sm x) 4 :=
    lettersSpan (calls := stage2Calls stage2SubCalls) (G := G) (C := ch.Cm) (s := ch.sm)
      ch.seg.inv' ch.hblock ch.h8 h110 hne102
  exact (ch.seg.trans (Seg.measure hspan)).inv'

/-- **The `'f'` leaf's seam carries the invariant**, from the chain and the leaf's bit. -/
theorem fLetterSeamInv_of_chain {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    {x : BitVec 8} (ch : HcontHeadChain G C s x)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (h102 : evalICmp .eq x (BitVec.ofNat 8 102) = 1) :
    WalkInv G (FC₄₁₃ ch.Cm) (FS413 ch.sm x) := by
  have hspan : Seg (stage2Calls stage2SubCalls) G ch.Cm ch.sm (FC₄₁₃ ch.Cm)
      (FS413 ch.sm x) 4 :=
    fSpan (calls := stage2Calls stage2SubCalls) (G := G) (C := ch.Cm) (s := ch.sm)
      ch.seg.inv' ch.hblock ch.h8 h110 h102
  exact (ch.seg.trans (Seg.measure hspan)).inv'

/-! ### `LetS413`'s and `FS413`'s cells, from the chain's

The span below `if.else387.i` binds two cells (`%Pivot63` and `%SwitchLeaf55`) and the
class's edge names the successor; `LetS413`/`FS413` bind nothing else, so each of the
endpoint's cells is the chain endpoint's, read through those two binds. -/

/-- `%ee.1.i` at the letters seam is the chain endpoint's. -/
theorem letS413_env_ee (sm : State) (x : BitVec 8) (v : BitVec 32)
    (h : lookupName sm.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))) :
    lookupName (LetS413 sm x).env "%ee.1.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [LetS413, LetS405, LetS54, HeadS62, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- `%cond350.i` at the letters seam is the chain endpoint's. -/
theorem letS413_env_cond (sm : State) (x : BitVec 8) (v : BitVec 32)
    (h : lookupName sm.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))) :
    lookupName (LetS413 sm x).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [LetS413, LetS405, LetS54, HeadS62, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- `%ee.1.i` at the `'f'` leaf's seam is the chain endpoint's. -/
theorem fs413_env_ee (sm : State) (x : BitVec 8) (v : BitVec 32)
    (h : lookupName sm.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))) :
    lookupName (FS413 sm x).env "%ee.1.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [FS413, FS397, LetS54, HeadS62, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- `%cond350.i` at the `'f'` leaf's seam is the chain endpoint's. -/
theorem fs413_env_cond (sm : State) (x : BitVec 8) (v : BitVec 32)
    (h : lookupName sm.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))) :
    lookupName (FS413 sm x).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [FS413, FS397, LetS54, HeadS62, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- The letters seam's predecessor is `if.else405.i` — the leaf's clear arm. -/
theorem letS413_pre (sm : State) (x : BitVec 8) :
    (LetS413 sm x).pre = some "if.else405.i" := by
  simp only [LetS413, LetS405, LetS54, HeadS62]

/-- The `'f'` leaf's seam's predecessor is `if.then397.i` — the leaf's true arm. -/
theorem fs413_pre (sm : State) (x : BitVec 8) :
    (FS413 sm x).pre = some "if.then397.i" := by
  simp only [FS413, FS397, LetS54, HeadS62]

/-- **The seam's `phi` selects the leaf's kind `9`** when `LeafBlock54`'s true arm sent the
walk there. -/
theorem fs413_phi :
    phiIncoming "if.then397.i"
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] =
      some (.imm (.int 32 (BitVec.ofNat 32 9))) := by
  decide

/-- The letters seam's memory is the chain endpoint's: the span binds cells only. -/
theorem letS413_mem (sm : State) (x : BitVec 8) :
    (LetS413 sm x).mem = sm.mem := rfl

/-- The `'f'` leaf's seam's memory is the chain endpoint's. -/
theorem fs413_mem (sm : State) (x : BitVec 8) :
    (FS413 sm x).mem = sm.mem := rfl

/-- **The root slot's word at the letters seam.**  The seam's one store is the kind literal
inside the token record, so the copy call's argument reads the word the chain endpoint's
memory holds. -/
theorem letS413_rootRead {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (sm : State)
    (x : BitVec 8) (cA rdv : BitVec 32)
    (hroot : readBytes sm.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)) :
    readBytes (writeBytes (LetS413 sm x).mem (C.stage.tok + 16) (natToBytes cA.toNat 4))
      (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4) := by
  rw [letS413_mem,
    walkReadBytes_rootSlot_of_tokStore (C := C) (off := 16) (len := 4)
      (v := natToBytes cA.toNat 4) (by decide) (natToBytes_length _ _)]
  exact hroot

/-- **The root slot's word at the `'f'` leaf's seam.** -/
theorem fs413_rootRead {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (sm : State)
    (x : BitVec 8) (cA rdv : BitVec 32)
    (hroot : readBytes sm.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)) :
    readBytes (writeBytes (FS413 sm x).mem (C.stage.tok + 16) (natToBytes cA.toNat 4))
      (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4) := by
  rw [fs413_mem,
    walkReadBytes_rootSlot_of_tokStore (C := C) (off := 16) (len := 4)
      (v := natToBytes cA.toNat 4) (by decide) (natToBytes_length _ _)]
  exact hroot

/-- **The letters seam's cells**, from the chain's: the kind literal is the leaf's clear
arm's `0`, the four pointers and the root word are the invariant's, and the pair is the
chain's one `Nat`. -/
noncomputable def lettersSeamCells_of_chain {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {x : BitVec 8} (ch : HcontHeadChain G C s x)
    (hInvS : WalkInv G (HeadC₄₁₃ (LetC₄₀₅ ch.Cm)) (LetS413 ch.sm x))
    (cA : BitVec 32) (hcA : cA = BitVec.ofNat 32 0)
    (rdv : BitVec 32)
    (hroot : readBytes ch.sm.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)) :
    HcontSeamCells (HeadC₄₁₃ (LetC₄₀₅ ch.Cm)) (LetS413 ch.sm x) cA rdv where
  p := "if.else405.i"
  op := .imm (.int 32 (BitVec.ofNat 32 0))
  hpre := letS413_pre ch.sm x
  hphi := contTailStart_phi
  hop := by rw [hcA]; simp only [evalOperand, Const.toValue]
  hkind := hInvS.regs ("%kind404.i", .ptr (ch.Cm.stage.tok + 16))
    (by simp [walkStaticRegs])
  hrd := hInvS.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs])
  hc := hInvS.regs ("%c.i", .ptr (ch.Cm.stage.c)) (by simp [walkStaticRegs])
  ht := hInvS.regs ("%t352.i", .ptr (ch.Cm.stage.tok)) (by simp [walkStaticRegs])
  ho := hInvS.regs ("%z", .ptr (ch.Cm.stage.z)) (by simp [walkStaticRegs])
  hreadRoot := letS413_rootRead (C := HeadC₄₁₃ (LetC₄₀₅ ch.Cm)) ch.sm x
    cA rdv hroot
  cd := ch.v.toNat
  hei := letS413_env_ee ch.sm x ch.v ch.hee
  hcd := letS413_env_cond ch.sm x ch.v ch.hcond
  hcd64 := by have := ch.v.isLt; omega

/-- **The `'f'` leaf's seam's cells**, from the chain's: the kind literal is the leaf's
true arm's `9`. -/
noncomputable def fLetterSeamCells_of_chain {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {x : BitVec 8} (ch : HcontHeadChain G C s x)
    (hInvS : WalkInv G (FC₄₁₃ ch.Cm) (FS413 ch.sm x))
    (cA : BitVec 32) (hcA : cA = BitVec.ofNat 32 9)
    (rdv : BitVec 32)
    (hroot : readBytes ch.sm.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)) :
    HcontSeamCells (FC₄₁₃ ch.Cm) (FS413 ch.sm x) cA rdv where
  p := "if.then397.i"
  op := .imm (.int 32 (BitVec.ofNat 32 9))
  hpre := fs413_pre ch.sm x
  hphi := fs413_phi
  hop := by rw [hcA]; simp only [evalOperand, Const.toValue]
  hkind := hInvS.regs ("%kind404.i", .ptr (ch.Cm.stage.tok + 16))
    (by simp [walkStaticRegs])
  hrd := hInvS.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs])
  hc := hInvS.regs ("%c.i", .ptr (ch.Cm.stage.c)) (by simp [walkStaticRegs])
  ht := hInvS.regs ("%t352.i", .ptr (ch.Cm.stage.tok)) (by simp [walkStaticRegs])
  ho := hInvS.regs ("%z", .ptr (ch.Cm.stage.z)) (by simp [walkStaticRegs])
  hreadRoot := fs413_rootRead (C := FC₄₁₃ ch.Cm) ch.sm x
    cA rdv hroot
  cd := ch.v.toNat
  hei := fs413_env_ee ch.sm x ch.v ch.hee
  hcd := fs413_env_cond ch.sm x ch.v ch.hcond
  hcd64 := by have := ch.v.isLt; omega

/-! ### The three arms, at the rows

Each takes the chain (or the class's span at its endpoint), the class's bits, and one call
group at the seam it names; the tail, the seam invariant and — for the two letters classes —
the seam's cells are produced.  What remains beside the group is the root word's agreement
with the state, one equation. -/

/-- **The letters continuing arm, at its rows.** -/
theorem hcontArm_letters_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s)
    (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0)
    (ch : HcontHeadChain G C s x)
    (calls : HcontSeamCalls G (HeadC₄₁₃ (LetC₄₀₅ ch.Cm)) (LetS413 ch.sm x))
    (hcA : calls.cA = BitVec.ofNat 32 0)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hInvS := lettersSeamInv_of_chain ch h110 hne102
  have hrootSm := ch.hroot hroot
  have hcells : HcontSeamCells (HeadC₄₁₃ (LetC₄₀₅ ch.Cm)) (LetS413 ch.sm x) calls.cA
      calls.rdv :=
    lettersSeamCells_of_chain ch hInvS calls.cA hcA calls.rdv hrootSm
  have htight : (HeadC₄₁₃ (LetC₄₀₅ ch.Cm)).events.length ≤ (HeadC₄₁₃ (LetC₄₀₅ ch.Cm)).k :=
    ch.seg.inv'.events_le_of_tight (by rw [ch.hblock]; decide)
  have hklt : (HeadC₄₁₃ (LetC₄₀₅ ch.Cm)).k < G.nep := by
    show ch.Cm.k < G.nep
    rw [ch.hk]
    exact Nat.lt_of_succ_lt hk
  obtain ⟨ev, hTail⟩ :=
    emptyTail_of_cells (G := G) (C := HeadC₄₁₃ (LetC₄₀₅ ch.Cm)) (s := LetS413 ch.sm x)
      calls hcells hInvS rfl htight hklt
  exact ⟨hcontArm_letters_of_lane hInv h8 hbit h110 hne102 ch hTail rfl
    (by rw [show (TailCarryEnd (HeadC₄₁₃ (LetC₄₀₅ ch.Cm)) ev).k = ch.Cm.k from rfl, ch.hk])
    (scanEntry_envTok (LetS413 ch.sm x) calls.r₁ calls.r₂ calls.r₃ calls.cA calls.rdv
      calls.xA (hInvS.regs ("%t352.i", .ptr (ch.Cm.stage.tok)) (by simp [walkStaticRegs])))⟩

/-- **The letters continuing dispatch, at its rows.** -/
theorem walkDispatch_at_letters_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0)
    (ch : HcontHeadChain G C s x)
    (calls : HcontSeamCalls G (HeadC₄₁₃ (LetC₄₀₅ ch.Cm)) (LetS413 ch.sm x))
    (hcA : calls.cA = BitVec.ofNat 32 0)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨arm⟩ :=
    hcontArm_letters_of_rows hInv hk h8 hbit h110 hne102 ch calls hcA hroot
  exact HcontArm.dispatch hInv hblock hk arm

/-- **The `'f'` leaf's continuing arm, at its rows.** -/
theorem hcontArm_fLetter_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s)
    (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (h102 : evalICmp .eq x (BitVec.ofNat 8 102) = 1)
    (ch : HcontHeadChain G C s x)
    (calls : HcontSeamCalls G (FC₄₁₃ ch.Cm) (FS413 ch.sm x))
    (hcA : calls.cA = BitVec.ofNat 32 9)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hInvS := fLetterSeamInv_of_chain ch h110 h102
  have hrootSm := ch.hroot hroot
  have hcells : HcontSeamCells (FC₄₁₃ ch.Cm) (FS413 ch.sm x) calls.cA calls.rdv :=
    fLetterSeamCells_of_chain ch hInvS calls.cA hcA calls.rdv hrootSm
  have htight : (FC₄₁₃ ch.Cm).events.length ≤ (FC₄₁₃ ch.Cm).k :=
    ch.seg.inv'.events_le_of_tight (by rw [ch.hblock]; decide)
  have hklt : (FC₄₁₃ ch.Cm).k < G.nep := by
    show ch.Cm.k < G.nep
    rw [ch.hk]
    exact Nat.lt_of_succ_lt hk
  obtain ⟨ev, hTail⟩ :=
    emptyTail_of_cells (G := G) (C := FC₄₁₃ ch.Cm) (s := FS413 ch.sm x)
      calls hcells hInvS rfl htight hklt
  exact ⟨hcontArm_fLetter_of_lane hInv h8 hbit h110 h102 ch hTail rfl
    (by rw [show (TailCarryEnd (FC₄₁₃ ch.Cm) ev).k = ch.Cm.k from rfl, ch.hk])
    (scanEntry_envTok (FS413 ch.sm x) calls.r₁ calls.r₂ calls.r₃ calls.cA calls.rdv
      calls.xA (hInvS.regs ("%t352.i", .ptr (ch.Cm.stage.tok)) (by simp [walkStaticRegs])))⟩

/-- **The `'f'` leaf's continuing dispatch, at its rows.** -/
theorem walkDispatch_at_fLetter_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (h102 : evalICmp .eq x (BitVec.ofNat 8 102) = 1)
    (ch : HcontHeadChain G C s x)
    (calls : HcontSeamCalls G (FC₄₁₃ ch.Cm) (FS413 ch.sm x))
    (hcA : calls.cA = BitVec.ofNat 32 9)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨arm⟩ :=
    hcontArm_fLetter_of_rows hInv hk h8 hbit h110 h102 ch calls hcA hroot
  exact HcontArm.dispatch hInv hblock hk arm

/-- **The class-C continuing arm, at its rows.**  The span's endpoint is existential, so
the seam's cells are taken there — `cells` at the span's own `(Cs, ss)` — while the tail is
produced from the callee rows. -/
theorem hcontArm_classC_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s)
    (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x)
    {Cs : WalkCarry G} {ss : State} {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G ch.Cm ch.sm Cs ss nS)
    (hs : Cs.block = "if.then413.i") (hnS : nS ≤ 5)
    (hkCs : Cs.k = C.k)
    (calls : HcontSeamCalls G Cs ss)
    (cells : HcontSeamCells Cs ss calls.cA calls.rdv) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have htight : Cs.events.length ≤ Cs.k :=
    hSpan.measure.inv'.events_le_of_tight (by rw [hs]; decide)
  have hklt : Cs.k < G.nep := by rw [hkCs]; exact Nat.lt_of_succ_lt hk
  obtain ⟨ev, hTail⟩ :=
    emptyTail_of_cells (G := G) (C := Cs) (s := ss) calls cells
      hSpan.measure.inv' hs htight hklt
  exact ⟨hcontArm_classC_of_lane hInv h8 h110 h125 ch hSpan hs hnS hTail rfl
    (by rw [show (TailCarryEnd Cs ev).k = Cs.k from rfl, hkCs])
    (scanEntry_envTok ss calls.r₁ calls.r₂ calls.r₃ calls.cA calls.rdv calls.xA cells.ht)⟩

/-- **The class-C continuing dispatch, at its rows.** -/
theorem walkDispatch_at_classC_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x)
    {Cs : WalkCarry G} {ss : State} {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G ch.Cm ch.sm Cs ss nS)
    (hs : Cs.block = "if.then413.i") (hnS : nS ≤ 5)
    (hkCs : Cs.k = C.k)
    (calls : HcontSeamCalls G Cs ss)
    (cells : HcontSeamCells Cs ss calls.cA calls.rdv) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨arm⟩ :=
    hcontArm_classC_of_rows hInv hk h8 h110 h125 ch hSpan hs hnS hkCs calls cells
  exact HcontArm.dispatch hInv hblock hk arm

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.emptyTail_of_cells
#print axioms LeanLLVM.Refinement.WalkScope.lettersSeamInv_of_chain
#print axioms LeanLLVM.Refinement.WalkScope.fLetterSeamInv_of_chain
#print axioms LeanLLVM.Refinement.WalkScope.letS413_rootRead
#print axioms LeanLLVM.Refinement.WalkScope.fs413_rootRead
#print axioms LeanLLVM.Refinement.WalkScope.lettersSeamCells_of_chain
#print axioms LeanLLVM.Refinement.WalkScope.fLetterSeamCells_of_chain
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_letters_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_letters_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_fLetter_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_fLetter_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_classC_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_classC_of_rows

end WalkScope
end LeanLLVM.Refinement
