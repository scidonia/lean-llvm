/-
The class-C span's leaves, at their named seams.

## Why the endpoint is a term here

`classCSpan_at` returns its target existentially: which of the four leaves the byte takes
decides both the target carry and the state.  `JsonStage2WalkDispatchClassC` states one
span theorem per leaf and each concludes at a named state — `ClsS413T` (`110`),
`ClsS413F` (`111 … 115`), `ClsS58T` (`116`) and `HeadS413` (`117 … 125`) — so a producer
that takes the leaf's own span has the endpoint in hand and can build the seam's cells at
it, exactly as `lettersSeamCells_of_chain` and `fLetterSeamCells_of_chain` do for the
letters route and its `'f'` leaf.

The spans bind cells only — the two pivots and the two empty bodies write no memory — so
each endpoint's `%ee.1.i`/`%cond350.i` is the chain endpoint's, read through that leaf's
binds, and the root slot's word is the chain's, transported across the kind record's store
at `%kind404.i` (`classCSeam_rootRead`).  The kind literal is the leaf's own `phi`
incoming: `10` on `if.then403.i`'s edge, `0` on `if.else405.i`'s (which both clear arms
name), and `8` on `LeafBlock58`'s own.

## What each producer takes

The chain (`HcontHeadChain`), the leaf's three bits, its call group at the named seam, and
the root word's agreement at the head.  The seam's invariant is the chain's own `inv'`
composed with the span (`hspan.measure.inv'`), and the tail is `emptyTail_of_cells` at the
produced cells, so nothing is taken at an unnamed endpoint.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchLettersRows
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassC

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- **The class-C arm, at a seam's produced cells.**  The three calls, the copy's test and
the merge's step read the endpoint's cells and nothing else, so one theorem serves the four
leaves once their cells are built (`classCSeamCells_56True` … `…_58Else`). -/
theorem hcontArm_classC_of_cells {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
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

/-! ### The kind literal's three incommings

`if.then413.i`'s `phi` selects `%.sink372`, and the value it selects is the leaf's kind.
The five incommings are the block's own; these three are the class-C leaves'. -/

/-- The kind literal on `if.then403.i`'s edge: `10`. -/
theorem clsC_phi_then403 :
    phiIncoming "if.then403.i"
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] =
      some (.imm (.int 32 (BitVec.ofNat 32 10))) := by
  decide

/-- The kind literal on `if.else405.i`'s edge — `LeafBlock56`'s clear arm and
`LeafBlock58`'s: `0`. -/
theorem clsC_phi_else405 :
    phiIncoming "if.else405.i"
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] =
      some (.imm (.int 32 (BitVec.ofNat 32 0))) := by
  decide

/-- The kind literal on `LeafBlock58`'s own edge: `8`. -/
theorem clsC_phi_leaf58 :
    phiIncoming "LeafBlock58"
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] =
      some (.imm (.int 32 (BitVec.ofNat 32 8))) := by
  decide

/-- **A class-C seam's root word**, from the chain endpoint's: the span writes the kind
record and nothing else, so the slot's word is the chain's, read past the record's store. -/
theorem classCSeam_rootRead {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {sm ss : State} (hss : ss.mem = sm.mem) (cA rdv : BitVec 32)
    (hroot : readBytes sm.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)) :
    readBytes (writeBytes ss.mem (C.stage.tok + 16) (natToBytes cA.toNat 4))
      (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4) := by
  rw [hss, walkReadBytes_rootSlot_of_tokStore (C := C) (off := 16) (len := 4)
    (v := natToBytes cA.toNat 4) (by decide) (natToBytes_length _ _)]
  exact hroot

/-! #### `110`: `ClsS413T`, through `if.then403.i` -/

/-- The two test cells at `ClsS413T` are the chain endpoint's. -/
theorem clsS413T_env_cells (sm : State) (x : BitVec 8) (v : BitVec 32)
    (hee : lookupName sm.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)))
    (hcond : lookupName sm.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))) :
    lookupName (ClsS413T sm x).env "%ee.1.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) ∧
    lookupName (ClsS413T sm x).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  constructor <;>
    · simp only [ClsS413T, ClsS403, ClsS56, HeadS60, HeadS62, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      assumption

/-- **`110`'s seam's cells**, at its named state. -/
noncomputable def classCSeamCells_56True {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {x : BitVec 8} (ch : HcontHeadChain G C s x)
    (hInvS : WalkInv G ({ ClsC₄₀₃ ch.Cm with block := "if.then413.i" })
      (ClsS413T ch.sm x))
    (cA : BitVec 32) (hcA : cA = BitVec.ofNat 32 10) (rdv : BitVec 32)
    (hroot : readBytes ch.sm.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)) :
    HcontSeamCells ({ ClsC₄₀₃ ch.Cm with block := "if.then413.i" })
      (ClsS413T ch.sm x) cA rdv where
  p := "if.then403.i"
  op := .imm (.int 32 (BitVec.ofNat 32 10))
  hpre := by simp only [ClsS413T, ClsS403]
  hphi := clsC_phi_then403
  hop := by rw [hcA]; simp only [evalOperand, Const.toValue]
  hkind := hInvS.regs ("%kind404.i", .ptr (ch.Cm.stage.tok + 16))
    (by simp [walkStaticRegs])
  hrd := hInvS.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs])
  hc := hInvS.regs ("%c.i", .ptr (ch.Cm.stage.c)) (by simp [walkStaticRegs])
  ht := hInvS.regs ("%t352.i", .ptr (ch.Cm.stage.tok)) (by simp [walkStaticRegs])
  ho := hInvS.regs ("%z", .ptr (ch.Cm.stage.z)) (by simp [walkStaticRegs])
  hreadRoot := classCSeam_rootRead (C := ({ ClsC₄₀₃ ch.Cm with block := "if.then413.i" }))
    (sm := ch.sm) (ss := ClsS413T ch.sm x) (by rfl) cA rdv hroot
  cd := ch.v.toNat
  hei := (clsS413T_env_cells ch.sm x ch.v ch.hee ch.hcond).1
  hcd := (clsS413T_env_cells ch.sm x ch.v ch.hee ch.hcond).2
  hcd64 := by have := ch.v.isLt; omega

/-- **`110`'s continuing arm, at its rows.** -/
theorem hcontArm_classC_56True_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x (BitVec.ofNat 8 116) = 1)
    (h110eq : evalICmp .eq x (BitVec.ofNat 8 110) = 1)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x)
    (calls : HcontSeamCalls G ({ ClsC₄₀₃ ch.Cm with block := "if.then413.i" })
      (ClsS413T ch.sm x))
    (hcA : calls.cA = BitVec.ofNat 32 10)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hspan : Seg (stage2Calls stage2SubCalls) G ch.Cm ch.sm
      ({ ClsC₄₀₃ ch.Cm with block := "if.then413.i" }) (ClsS413T ch.sm x) 5 :=
    c56TrueSpan (calls := stage2Calls stage2SubCalls) (G := G) (C := ch.Cm) (s := ch.sm)
      ch.seg.inv' ch.hblock ch.h8 h110 h116 h110eq
  have hcells : HcontSeamCells ({ ClsC₄₀₃ ch.Cm with block := "if.then413.i" })
      (ClsS413T ch.sm x) calls.cA calls.rdv :=
    classCSeamCells_56True ch hspan.measure.inv' calls.cA hcA calls.rdv (ch.hroot hroot)
  exact hcontArm_classC_of_cells hInv hk h8 h110 h125 ch hspan rfl (by decide)
    (by show ch.Cm.k = C.k; exact ch.hk) calls hcells

/-- **`110`'s continuing dispatch, at its rows.** -/
theorem walkDispatch_at_classC_56True_of_rows {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x (BitVec.ofNat 8 116) = 1)
    (h110eq : evalICmp .eq x (BitVec.ofNat 8 110) = 1)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x)
    (calls : HcontSeamCalls G ({ ClsC₄₀₃ ch.Cm with block := "if.then413.i" })
      (ClsS413T ch.sm x))
    (hcA : calls.cA = BitVec.ofNat 32 10)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨arm⟩ :=
    hcontArm_classC_56True_of_rows hInv hk h8 h110 h116 h110eq h125 ch calls hcA hroot
  exact HcontArm.dispatch hInv hblock hk arm

/-! #### `111 … 115`: `ClsS413F`, through `if.else405.i` -/

/-- The two test cells at `ClsS413F` are the chain endpoint's. -/
theorem clsS413F_env_cells (sm : State) (x : BitVec 8) (v : BitVec 32)
    (hee : lookupName sm.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)))
    (hcond : lookupName sm.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))) :
    lookupName (ClsS413F sm x).env "%ee.1.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) ∧
    lookupName (ClsS413F sm x).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  constructor <;>
    · simp only [ClsS413F, ClsS405, ClsS56, HeadS60, HeadS62, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      assumption

/-- **`111 … 115`'s seam's cells**, at its named state. -/
noncomputable def classCSeamCells_56Else {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {x : BitVec 8} (ch : HcontHeadChain G C s x)
    (hInvS : WalkInv G (HeadC₄₁₃ (ClsC₄₀₅ ch.Cm)) (ClsS413F ch.sm x))
    (cA : BitVec 32) (hcA : cA = BitVec.ofNat 32 0) (rdv : BitVec 32)
    (hroot : readBytes ch.sm.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)) :
    HcontSeamCells (HeadC₄₁₃ (ClsC₄₀₅ ch.Cm)) (ClsS413F ch.sm x) cA rdv where
  p := "if.else405.i"
  op := .imm (.int 32 (BitVec.ofNat 32 0))
  hpre := by simp only [ClsS413F, ClsS405]
  hphi := clsC_phi_else405
  hop := by rw [hcA]; simp only [evalOperand, Const.toValue]
  hkind := hInvS.regs ("%kind404.i", .ptr (ch.Cm.stage.tok + 16))
    (by simp [walkStaticRegs])
  hrd := hInvS.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs])
  hc := hInvS.regs ("%c.i", .ptr (ch.Cm.stage.c)) (by simp [walkStaticRegs])
  ht := hInvS.regs ("%t352.i", .ptr (ch.Cm.stage.tok)) (by simp [walkStaticRegs])
  ho := hInvS.regs ("%z", .ptr (ch.Cm.stage.z)) (by simp [walkStaticRegs])
  hreadRoot := classCSeam_rootRead (C := (HeadC₄₁₃ (ClsC₄₀₅ ch.Cm)))
    (sm := ch.sm) (ss := ClsS413F ch.sm x) (by rfl) cA rdv hroot
  cd := ch.v.toNat
  hei := (clsS413F_env_cells ch.sm x ch.v ch.hee ch.hcond).1
  hcd := (clsS413F_env_cells ch.sm x ch.v ch.hee ch.hcond).2
  hcd64 := by have := ch.v.isLt; omega

/-- **`111 … 115`'s continuing arm, at its rows.** -/
theorem hcontArm_classC_56Else_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x (BitVec.ofNat 8 116) = 1)
    (h110eq : evalICmp .eq x (BitVec.ofNat 8 110) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x)
    (calls : HcontSeamCalls G (HeadC₄₁₃ (ClsC₄₀₅ ch.Cm)) (ClsS413F ch.sm x))
    (hcA : calls.cA = BitVec.ofNat 32 0)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hspan : Seg (stage2Calls stage2SubCalls) G ch.Cm ch.sm
      (HeadC₄₁₃ (ClsC₄₀₅ ch.Cm)) (ClsS413F ch.sm x) 5 :=
    c56ElseSpan (calls := stage2Calls stage2SubCalls) (G := G) (C := ch.Cm) (s := ch.sm)
      ch.seg.inv' ch.hblock ch.h8 h110 h116 h110eq
  have hcells : HcontSeamCells (HeadC₄₁₃ (ClsC₄₀₅ ch.Cm)) (ClsS413F ch.sm x)
      calls.cA calls.rdv :=
    classCSeamCells_56Else ch hspan.measure.inv' calls.cA hcA calls.rdv (ch.hroot hroot)
  exact hcontArm_classC_of_cells hInv hk h8 h110 h125 ch hspan rfl (by decide)
    (by show ch.Cm.k = C.k; exact ch.hk) calls hcells

/-- **`111 … 115`'s continuing dispatch, at its rows.** -/
theorem walkDispatch_at_classC_56Else_of_rows {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x (BitVec.ofNat 8 116) = 1)
    (h110eq : evalICmp .eq x (BitVec.ofNat 8 110) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x)
    (calls : HcontSeamCalls G (HeadC₄₁₃ (ClsC₄₀₅ ch.Cm)) (ClsS413F ch.sm x))
    (hcA : calls.cA = BitVec.ofNat 32 0)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨arm⟩ :=
    hcontArm_classC_56Else_of_rows hInv hk h8 h110 h116 h110eq h125 ch calls hcA hroot
  exact HcontArm.dispatch hInv hblock hk arm

/-! #### `116`: `ClsS58T`, through `LeafBlock58`'s own edge -/

/-- The two test cells at `ClsS58T` are the chain endpoint's. -/
theorem clsS58T_env_cells (sm : State) (x : BitVec 8) (v : BitVec 32)
    (hee : lookupName sm.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)))
    (hcond : lookupName sm.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))) :
    lookupName (ClsS58T sm x).env "%ee.1.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) ∧
    lookupName (ClsS58T sm x).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  constructor <;>
    · simp only [ClsS58T, HeadS58, HeadS60, HeadS62, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      assumption

/-- **`116`'s seam's cells**, at its named state. -/
noncomputable def classCSeamCells_58True {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {x : BitVec 8} (ch : HcontHeadChain G C s x)
    (hInvS : WalkInv G ({ HeadC₅₈ ch.Cm with block := "if.then413.i" })
      (ClsS58T ch.sm x))
    (cA : BitVec 32) (hcA : cA = BitVec.ofNat 32 8) (rdv : BitVec 32)
    (hroot : readBytes ch.sm.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)) :
    HcontSeamCells ({ HeadC₅₈ ch.Cm with block := "if.then413.i" })
      (ClsS58T ch.sm x) cA rdv where
  p := "LeafBlock58"
  op := .imm (.int 32 (BitVec.ofNat 32 8))
  hpre := by simp only [ClsS58T, HeadS58]
  hphi := clsC_phi_leaf58
  hop := by rw [hcA]; simp only [evalOperand, Const.toValue]
  hkind := hInvS.regs ("%kind404.i", .ptr (ch.Cm.stage.tok + 16))
    (by simp [walkStaticRegs])
  hrd := hInvS.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs])
  hc := hInvS.regs ("%c.i", .ptr (ch.Cm.stage.c)) (by simp [walkStaticRegs])
  ht := hInvS.regs ("%t352.i", .ptr (ch.Cm.stage.tok)) (by simp [walkStaticRegs])
  ho := hInvS.regs ("%z", .ptr (ch.Cm.stage.z)) (by simp [walkStaticRegs])
  hreadRoot := classCSeam_rootRead (C := ({ HeadC₅₈ ch.Cm with block := "if.then413.i" }))
    (sm := ch.sm) (ss := ClsS58T ch.sm x) (by rfl) cA rdv hroot
  cd := ch.v.toNat
  hei := (clsS58T_env_cells ch.sm x ch.v ch.hee ch.hcond).1
  hcd := (clsS58T_env_cells ch.sm x ch.v ch.hee ch.hcond).2
  hcd64 := by have := ch.v.isLt; omega

/-- **`116`'s continuing arm, at its rows.** -/
theorem hcontArm_classC_58True_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq x (BitVec.ofNat 8 116) = 1)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x)
    (calls : HcontSeamCalls G ({ HeadC₅₈ ch.Cm with block := "if.then413.i" })
      (ClsS58T ch.sm x))
    (hcA : calls.cA = BitVec.ofNat 32 8)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hspan : Seg (stage2Calls stage2SubCalls) G ch.Cm ch.sm
      ({ HeadC₅₈ ch.Cm with block := "if.then413.i" }) (ClsS58T ch.sm x) 4 :=
    c58TrueSpan (calls := stage2Calls stage2SubCalls) (G := G) (C := ch.Cm) (s := ch.sm)
      ch.seg.inv' ch.hblock ch.h8 h110 h116 h116eq
  have hcells : HcontSeamCells ({ HeadC₅₈ ch.Cm with block := "if.then413.i" })
      (ClsS58T ch.sm x) calls.cA calls.rdv :=
    classCSeamCells_58True ch hspan.measure.inv' calls.cA hcA calls.rdv (ch.hroot hroot)
  exact hcontArm_classC_of_cells hInv hk h8 h110 h125 ch hspan rfl (by decide)
    (by show ch.Cm.k = C.k; exact ch.hk) calls hcells

/-- **`116`'s continuing dispatch, at its rows.** -/
theorem walkDispatch_at_classC_58True_of_rows {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq x (BitVec.ofNat 8 116) = 1)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x)
    (calls : HcontSeamCalls G ({ HeadC₅₈ ch.Cm with block := "if.then413.i" })
      (ClsS58T ch.sm x))
    (hcA : calls.cA = BitVec.ofNat 32 8)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨arm⟩ :=
    hcontArm_classC_58True_of_rows hInv hk h8 h110 h116 h116eq h125 ch calls hcA hroot
  exact HcontArm.dispatch hInv hblock hk arm

/-! #### `117 … 125`: `HeadS413`, through `LeafBlock58`'s clear arm -/

/-- The two test cells at `HeadS413` are the chain endpoint's. -/
theorem headS413_env_cells (sm : State) (x : BitVec 8) (v : BitVec 32)
    (hee : lookupName sm.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)))
    (hcond : lookupName sm.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))) :
    lookupName (HeadS413 sm x).env "%ee.1.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) ∧
    lookupName (HeadS413 sm x).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  constructor <;>
    · simp only [HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      assumption

/-- **`117 … 125`'s seam's cells**, at its named state. -/
noncomputable def classCSeamCells_58Else {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {x : BitVec 8} (ch : HcontHeadChain G C s x)
    (hInvS : WalkInv G (HeadC₄₁₃ ch.Cm) (HeadS413 ch.sm x))
    (cA : BitVec 32) (hcA : cA = BitVec.ofNat 32 0) (rdv : BitVec 32)
    (hroot : readBytes ch.sm.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)) :
    HcontSeamCells (HeadC₄₁₃ ch.Cm) (HeadS413 ch.sm x) cA rdv where
  p := "if.else405.i"
  op := .imm (.int 32 (BitVec.ofNat 32 0))
  hpre := by simp only [HeadS413, HeadS405]
  hphi := clsC_phi_else405
  hop := by rw [hcA]; simp only [evalOperand, Const.toValue]
  hkind := hInvS.regs ("%kind404.i", .ptr (ch.Cm.stage.tok + 16))
    (by simp [walkStaticRegs])
  hrd := hInvS.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs])
  hc := hInvS.regs ("%c.i", .ptr (ch.Cm.stage.c)) (by simp [walkStaticRegs])
  ht := hInvS.regs ("%t352.i", .ptr (ch.Cm.stage.tok)) (by simp [walkStaticRegs])
  ho := hInvS.regs ("%z", .ptr (ch.Cm.stage.z)) (by simp [walkStaticRegs])
  hreadRoot := classCSeam_rootRead (C := (HeadC₄₁₃ ch.Cm))
    (sm := ch.sm) (ss := HeadS413 ch.sm x) (by rfl) cA rdv hroot
  cd := ch.v.toNat
  hei := (headS413_env_cells ch.sm x ch.v ch.hee ch.hcond).1
  hcd := (headS413_env_cells ch.sm x ch.v ch.hee ch.hcond).2
  hcd64 := by have := ch.v.isLt; omega

/-- **`117 … 125`'s continuing arm, at its rows.** -/
theorem hcontArm_classC_58Else_of_rows {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq x (BitVec.ofNat 8 116) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x)
    (calls : HcontSeamCalls G (HeadC₄₁₃ ch.Cm) (HeadS413 ch.sm x))
    (hcA : calls.cA = BitVec.ofNat 32 0)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hspan : Seg (stage2Calls stage2SubCalls) G ch.Cm ch.sm
      (HeadC₄₁₃ ch.Cm) (HeadS413 ch.sm x) 5 :=
    c58ElseSpan (calls := stage2Calls stage2SubCalls) (G := G) (C := ch.Cm) (s := ch.sm)
      ch.seg.inv' ch.hblock ch.h8 h110 h116 h116eq
  have hcells : HcontSeamCells (HeadC₄₁₃ ch.Cm) (HeadS413 ch.sm x) calls.cA calls.rdv :=
    classCSeamCells_58Else ch hspan.measure.inv' calls.cA hcA calls.rdv (ch.hroot hroot)
  exact hcontArm_classC_of_cells hInv hk h8 h110 h125 ch hspan rfl (by decide)
    (by show ch.Cm.k = C.k; exact ch.hk) calls hcells

/-- **`117 … 125`'s continuing dispatch, at its rows.** -/
theorem walkDispatch_at_classC_58Else_of_rows {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt x (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq x (BitVec.ofNat 8 116) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x)
    (calls : HcontSeamCalls G (HeadC₄₁₃ ch.Cm) (HeadS413 ch.sm x))
    (hcA : calls.cA = BitVec.ofNat 32 0)
    (hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨arm⟩ :=
    hcontArm_classC_58Else_of_rows hInv hk h8 h110 h116 h116eq h125 ch calls hcA hroot
  exact HcontArm.dispatch hInv hblock hk arm

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_classC_of_cells
#print axioms LeanLLVM.Refinement.WalkScope.clsC_phi_then403
#print axioms LeanLLVM.Refinement.WalkScope.clsC_phi_else405
#print axioms LeanLLVM.Refinement.WalkScope.clsC_phi_leaf58
#print axioms LeanLLVM.Refinement.WalkScope.classCSeam_rootRead
#print axioms LeanLLVM.Refinement.WalkScope.clsS413T_env_cells
#print axioms LeanLLVM.Refinement.WalkScope.classCSeamCells_56True
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_classC_56True_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_classC_56True_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.clsS413F_env_cells
#print axioms LeanLLVM.Refinement.WalkScope.classCSeamCells_56Else
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_classC_56Else_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_classC_56Else_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.clsS58T_env_cells
#print axioms LeanLLVM.Refinement.WalkScope.classCSeamCells_58True
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_classC_58True_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_classC_58True_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.headS413_env_cells
#print axioms LeanLLVM.Refinement.WalkScope.classCSeamCells_58Else
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_classC_58Else_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_classC_58Else_of_rows

end WalkScope
end LeanLLVM.Refinement
