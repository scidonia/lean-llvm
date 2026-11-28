/-
# The closing bracket's merge, at the term a caller can name

`closeBracketMerge_at` (`JsonStage2WalkDispatchClosers:1343`) concludes a
`WalkDispatchResult`, whose merge arm binds the carry and the depth operand
existentially.  A caller of `mergeCond_of_chain` cannot write the chain's last
carry equation, nor `hsp0_of_carry`'s tie, from that type: the constructed term
`closeCEnd (closeC₁₀b C) spz c8`, the selected depth `C.sp - 1`, the advanced
index `C.k + 1` and the post-call root word are visible only inside its proof.

This module restates the same argument with those conclusions exposed.  The proof
is the dispatch's own: every `have` is the one `closeBracketMerge_at` makes, and
the ending packages the same `hseg11`, `hsub8`, `L11` and the after-value post
instead of a `WalkDispatchResult`.

There is no `sorry`, `admit` or `native_decide`.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchClosers

set_option autoImplicit false

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR

/-- **The closing bracket's merge, exposed.**  The segment's carry is the term
`closeCEnd (closeC₁₀b C) (C.sp + 4294967295) 4`, the merge's selections are
`%sub.i = C.sp - 1` and `%inc.i = C.k + 1`, its `%nep` is the stream's count, and
the endpoint's root-done slot holds `1` (the depth-zero `s2_after_value` store).
`hsp1` is the caller's depth-one fact, which the `[1]` chain produces. -/
theorem closeBracketMerge_term {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)))
    (hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 93)
    (hsp : C.sp ≠ 0) (hsp1 : C.sp = 1)
    {b1 b2 : UInt8} (hmark : C.tyMap (C.sp - 1) = b1)
    (hstate : C.stMap (C.sp - 1) = b2)
    (hb1 : b1.toNat = 2) (hb2 : b2.toNat < 2)
    (hpreA : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next) :
    ∃ sd : State,
      WalkSegment (stage2Calls stage2SubCalls) G C s
        (closeCEnd (closeC₁₀b C)
          (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295) (BitVec.ofNat 8 4)) sd 11 ∧
      sd.pre = some "out_reserve.exit.i.i60" ∧
      evalOperand sd (.reg "%sub.i") =
        some (.int 32 (BitVec.ofNat 32 (C.sp - 1))) ∧
      evalOperand sd (.reg "%inc.i") =
        some (.int 64 (BitVec.ofNat 64 (C.k + 1))) ∧
      lookupName sd.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep)) ∧
      readBytes sd.mem (G.next0 + 8) 4 = some (natToBytes 1 4) := by
  have hseg5 := closePrefixBracketSeg (calls := stage2Calls stage2SubCalls) G C s hInv hhead
    hbe hsp
  have hInv5 := hseg5.inv'
  have hk5 : (closeC₂ C).k = C.k := rfl
  have h8₅ : lookupName (closeBracketS₅ s).env "%8" =
      some (.int 8 (BitVec.ofNat 8 93)) := by
    have h := hInv5.iter.reg8
    rw [hk5, hbe] at h
    exact h
  have f : CloseStackFacts G (closeC₂ C) (closeBracketS₅ s) :=
    closeStackFacts (G := G) (C := closeC₂ C) (s := closeBracketS₅ s) hInv5
      (by show (closeC₂ C).sp ≠ 0; exact hsp)
  have hmark5 : (closeC₂ C).tyMap ((closeC₂ C).sp - 1) = b1 := by
    simpa only [closeC₂] using hmark
  have hreadT : readBytes (closeBracketS₅ s).mem
      ((closeC₂ C).stage.ctype +
        (BitVec.ofNat 32 (closeC₂ C).sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [b1] := by
    rw [← hmark5]; exact f.tyread
  have L6 : WalkLink (stage2Calls stage2SubCalls) G (closeC₂ C) (closeBracketS₅ s)
      (closeC₃ C)
      (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
        (stackSelBit (BitVec.ofNat 8 93) b1)) :=
    mlStep₆c (calls := stage2Calls stage2SubCalls) G (closeC₂ C) (closeBracketS₅ s) hInv5
      rfl f.sp h8₅ f.ct f.q63 hreadT (closeAgree_93 hb1)
  have hidx : lookupName
      (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
        (stackSelBit (BitVec.ofNat 8 93) b1)).env "%idxprom65.i" =
      some (.int 64 (BitVec.ofNat 64
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat)) :=
    closeSel_idx _ _ _ _ _ _
  have hcmp : lookupName
      (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
        (stackSelBit (BitVec.ofNat 8 93) b1)).env "%cmp61.i" =
      some (.int 1 (walkSelBit (BitVec.ofNat 8 93))) :=
    closeSel_cmp _ _ _ _ _ _
  have hreadS : readBytes
      (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
        (stackSelBit (BitVec.ofNat 8 93) b1)).mem
      (C.stage.cst + (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [b2] := by
    have h := f.stread
    rw [hstate] at h
    exact h
  obtain ⟨s₇, L7, hs₇⟩ := walkIfEnd74_at (calls := stage2Calls stage2SubCalls) G
    (closeC₃ C) (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93)
      b1 (stackSelBit (BitVec.ofNat 8 93) b1)) L6.inv' rfl f.cs hidx f.q63 hreadS hcmp
  have hbit₇ : walkSelBit (BitVec.ofNat 8 93) = (0 : BitVec 1) := closeSelBit_93
  have hpc₇ : (if walkSelBit (BitVec.ofNat 8 93) = (1 : BitVec 1) then "cond.true.i"
      else "cond.end.i") = "cond.end.i" := by rw [hbit₇]; rfl
  have hs₇' : s₇ = ifEnd74Out (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype
      (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1)) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0 := by
    rw [hs₇, hbit₇]
  have L7' : WalkLink (stage2Calls stage2SubCalls) G (closeC₃ C)
      (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
        (stackSelBit (BitVec.ofNat 8 93) b1)) (closeC₄b C)
      (ifEnd74Out (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype
        (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1)) C.stage.cst
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0) := by
    rw [hpc₇] at L7
    rw [hs₇'] at L7
    exact L7
  have h15 : evalOperand (ifEnd74Out (stackSelOut (closeBracketS₅ s) C.sp C.stage.ctype
      (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1)) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0) (.reg "%15") =
      some (.int 8 (BitVec.ofNat 8 b2.toNat)) :=
    closeByte_val _ _ _ b2 0
  obtain ⟨s₈, L8, hs₈⟩ := WalkLink.cond_end_i_at (calls := stage2Calls stage2SubCalls) G
    (closeC₄b C) _ L7'.inv' rfl h15
  have hult : evalICmp .ult (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 2) = 1 :=
    closeUlt_one (show b2.toNat < 256 from UInt8.toNat_lt b2) (by decide) hb2
  have hbit₈ : (if evalICmp .ult (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 2) = 1 then
      "if.then109.i" else "cleanup104.i") = "if.then109.i" := by
    rw [hult]; rfl
  rw [hbit₈] at L8
  have hs₈' : s₈ = closeBracket109S (ifEnd74Out (stackSelOut (closeBracketS₅ s) C.sp
      C.stage.ctype (BitVec.ofNat 8 93) b1 (stackSelBit (BitVec.ofNat 8 93) b1))
      C.stage.cst (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 0) b2 := by
    rw [hs₈, hbit₈]
    rfl
  have hInv8 : WalkInv G (closeC₁₀b C) s₈ := L8.inv'
  have hpc8 : s₈.pc = "if.then109.i" := by rw [hs₈']; rfl
  have hpre8 : s₈.pre = some "cond.end.i" := by rw [hs₈']; rfl
  have hmem8 : s₈.mem = s.mem := by rw [hs₈']; rfl
  have hnext8 : s₈.next = s.next := by rw [hs₈']; rfl
  -- the after-value call resolves here
  have hspz : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat =
      C.sp - 1 := by
    rw [closeSub_eq (Nat.pos_of_ne_zero hsp) (depth_lt_32 hInv.depth_cap)]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have h := hInv.depth_cap
      simp only [stage2StackExtent] at h
      omega)]
  have hspzcap : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat ≤
      stage2StackExtent := by
    have h := hInv.depth_cap
    simp only [stage2StackExtent] at h ⊢
    omega
  have hpreA8 : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s₈.mem s₈.next := by
    rw [hmem8, hnext8]
    exact hpreA
  obtain ⟨r, hcall, hpost, hfr⟩ := s2AfterValueContract.resolves (next := s₈.next) hpreA8
  obtain ⟨m, hm, -, hmem, hrn⟩ := hpost
  have hbyte : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat - 1 + 1 ≤
      stage2StackExtent := by
    have h520 : stage2StackExtent = 520 := rfl
    rw [h520] at hspzcap ⊢
    omega
  have hread : readBytes r.mem (C.stage.z + 32) 4 = some (natToBytes 0 4) := by
    obtain h1 | ⟨b, h1⟩ := stage2AfterValue_form hm
    · rw [hmem, h1]
      rw [walkReadBytes_log_of_write (m := s₈.mem) (z := C.stage.z)
        (a := G.next0 + 8) (w := 4) (off := 32) (w' := 4) (bs := wordBytes 4 1)
        (by simp [wordBytes, natToBytes_length]) (by simpa using C.stage.rootSlot_log)
        (by decide)]
      exact L8.inv'.log_hash
    · rw [hmem, h1]
      rw [walkReadBytes_log_of_write (m := s₈.mem) (z := C.stage.z)
        (a := C.stage.cst + ((BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat - 1))
        (w := 1) (off := 32) (w' := 4) (bs := [b])
        (by simp) (walkCstByte_log_sep (C := closeC₁₀b C) (s := s₈) L8.inv' hbyte)
        (by decide)]
      exact L8.inv'.log_hash
  have hsub8 : lookupName s₈.env "%sub.i" = some (.int 32
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)) := by
    rw [hs₈']
    rw [closeBracket109S_other _ _ "%sub.i" (by decide),
      closeByte_other _ _ _ _ _ "%sub.i" (by decide)]
    exact closeSel_sub (closeBracketS₅ s) C.sp C.stage.ctype (BitVec.ofNat 8 93) b1
      (stackSelBit (BitVec.ofNat 8 93) b1)
  have hstep9 := closeIfThen109Term (C := closeC₁₀b C) (s := s₈) r (BitVec.ofNat 8 4)
    hpc8 (p := "cond.end.i") (op := .imm (.int 8 (BitVec.ofNat 8 4)))
    hpre8 (by decide) (by simp [evalOperand]) hsub8 hInv8.ptrs.2.2.2.1
    hInv8.ptrs.2.2.2.2.1
    (hInv8.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs]))
    hInv8.ptrs.2.2.2.2.2 hcall hread
  have hspw8 : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat = 0 ∨
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat - 1 <
        (closeC₁₀b C).wlen := by
    right
    have hw : (closeC₁₀b C).wlen = C.wlen := rfl
    rw [hw]
    have h := hInv.sp_le_wlen
    omega
  obtain ⟨s₉, L9⟩ := WalkLink.if_then109_i G (closeC₁₀b C) s₈ hInv8 rfl
    hpre8 (p := "cond.end.i") (op := .imm (.int 8 (BitVec.ofNat 8 4)))
    (c8 := BitVec.ofNat 8 4) (by decide) (by simp [evalOperand]) hsub8 hspzcap
    (hInv8.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs]))
    hpreA8 hspw8
  have hs₉ : s₉ = close109S s₈ r (BitVec.ofNat 8 4) :=
    Ctrl.jump.inj (L9.step.symm.trans hstep9)
  rw [hs₉] at L9
  -- `if.end.i.i55`
  have hklt : C.k < G.nep :=
    WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hhead)
  have hevclear : C.evlen + 1 ≤ G.evcap :=
    (walkEventReserve_clear L9.inv'
      (walkEmitC_of_not_contains (b := "if.end.i.i55") (by decide)) hklt).1
  have hev63 : C.evlen < 2 ^ 63 := by
    have h1 : C.evlen ≤ G.nev0 + stage2RecordBytes * G.n := L9.inv'.evlen_le
    have h2 := G.ev63
    omega
  have hev64len : C.evlen + 1 < 2 ^ 64 := by
    have h1 := G.evcapLt
    omega
  have hreadL : readBytes (close109S s₈ r (BitVec.ofNat 8 4)).mem
      (C.stage.z + 8) 8 = some (natToBytes (BitVec.ofNat 64 C.evlen).toNat 8) := by
    have h := L9.inv'.log_len
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : C.evlen < 2 ^ 64)]
    simpa only [wordBytes] using h
  have hreadC : readBytes (close109S s₈ r (BitVec.ofNat 8 4)).mem
      (C.stage.z + 16) 8 = some (natToBytes (BitVec.ofNat 64 G.evcap).toNat 8) := by
    have h := L9.inv'.log_cap
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt G.evcapLt]
    simpa only [wordBytes] using h
  have hguard : evalICmp .ugt (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1)
      (BitVec.ofNat 64 G.evcap) = 0 := by
    have hsum : BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1 =
        BitVec.ofNat 64 (C.evlen + 1) := BitVec.ofNat_add_ofNat _ _
    rw [hsum]
    exact walkEvalICmp_ugt_ofNat_zero hev64len G.evcapLt (by omega)
  obtain ⟨s₁₀, L10⟩ := WalkLink.if_end_i_i55 (calls := stage2Calls stage2SubCalls) G
    (closeAfter109 (closeC₁₀b C)
    (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
    (close109S s₈ r (BitVec.ofNat 8 4)) L9.inv' rfl
    (L9.inv'.regs ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs]))
    (L9.inv'.regs ("%cap", .ptr (C.stage.z + 16)) (by simp [walkStaticRegs]))
    hreadL hreadC
  have hbit₁₀ : (if evalICmp .ugt (BitVec.ofNat 64 C.evlen + BitVec.ofNat 64 1)
      (BitVec.ofNat 64 G.evcap) = 1 then "if.end.i.i.i64" else "out_reserve.exit.i.i60") =
      "out_reserve.exit.i.i60" := by rw [hguard]; rfl
  rw [hbit₁₀] at L10
  have hstep10 := closeEndIITerm (calls := stage2Calls stage2SubCalls) G
    (closeAfter109 (closeC₁₀b C)
    (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
    (close109S s₈ r (BitVec.ofNat 8 4)) rfl
    (L9.inv'.regs ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs]))
    (L9.inv'.regs ("%cap", .ptr (C.stage.z + 16)) (by simp [walkStaticRegs]))
    hreadL hreadC hguard
  have hs₁₀ : s₁₀ = closeEndIIS (closeAfter109 (closeC₁₀b C)
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
      (BitVec.ofNat 64 G.evcap) :=
    Ctrl.jump.inj (L10.step.symm.trans hstep10)
  rw [hs₁₀] at L10
  -- `out_reserve.exit.i.i60`
  have hst10 : lookupName (closeEndIIS (closeAfter109 (closeC₁₀b C)
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
      (BitVec.ofNat 64 G.evcap)).env "%add.i.i.i58" =
      some (.int 64 (BitVec.ofNat 64 (C.evlen + 1))) := by
    rw [closeEndIIS_add, BitVec.ofNat_add_ofNat]
  have hs10 : lookupName (closeEndIIS (closeAfter109 (closeC₁₀b C)
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
      (BitVec.ofNat 64 G.evcap)).env "%conv115.i" = some (.int 8 (BitVec.ofNat 8 4)) := by
    rw [closeEndIIS_other _ _ _ _ _ (by decide),
      close109S_conv115]
  have hc11 : (closeC₁₂ (closeC₁₀b C)
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)).events.length ≤
      (closeC₁₂ (closeC₁₀b C)
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)).k :=
    L10.inv'.events_le_of_tight
      (walkEmitC_of_not_contains (b := "out_reserve.exit.i.i60") (by decide))
  obtain ⟨s₁₁, L11⟩ := WalkLink.out_reserve_exit_i_i60 (calls := stage2Calls stage2SubCalls) G
    (closeC₁₂ (closeC₁₀b C) (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
    (closeEndIIS (closeAfter109 (closeC₁₀b C)
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
      (BitVec.ofNat 64 G.evcap)) L10.inv' rfl
    (L10.inv'.regs ("%z", .ptr C.stage.z) (by simp [walkStaticRegs]))
    L10.inv'.log_base G.evLt hs10
    (closeEndIIS_oval _ _ _ _)
    hst10
    (L10.inv'.regs ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs]))
    hev63 hev64len hc11 hklt
  have hstep11 := closeEmitTerm G
    (closeC₁₂ (closeC₁₀b C) (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
    (closeEndIIS (closeAfter109 (closeC₁₀b C)
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
      (BitVec.ofNat 64 G.evcap)) rfl
    (L10.inv'.regs ("%z", .ptr C.stage.z) (by simp [walkStaticRegs]))
    L10.inv'.log_base G.evLt hs10
    (closeEndIIS_oval _ _ _ _) hst10
    (L10.inv'.regs ("%len", .ptr (C.stage.z + 8)) (by simp [walkStaticRegs]))
    hev63 hev64len
  have hs₁₁ : s₁₁ = closeEmitS (closeC₁₂ (closeC₁₀b C)
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (closeEndIIS (closeAfter109 (closeC₁₀b C)
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
        (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
        (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 8 4) :=
    Ctrl.jump.inj (L11.step.symm.trans hstep11)
  rw [hs₁₁] at L11
  -- the composition, counted at eleven
  have hseg11 : WalkSegment (stage2Calls stage2SubCalls) G C s
      (closeCEnd (closeC₁₀b C) (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295)
        (BitVec.ofNat 8 4))
      (closeEmitS (closeC₁₂ (closeC₁₀b C)
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
        (closeEndIIS (closeAfter109 (closeC₁₀b C)
          (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
          (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 8 4)) 11 :=
    hseg5.trans (Seg.measure (Seg.tail L6 (Seg.tail L7' (Seg.tail L8 (Seg.tail L9
      (Seg.tail L10 (Seg.tail L11 (Seg.nil L11.inv'))))))))
  let sd : State := closeEmitS (closeC₁₂ (closeC₁₀b C)
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
    (closeEndIIS (closeAfter109 (closeC₁₀b C)
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
      (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
      (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 8 4)
  refine ⟨sd, hseg11, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [evalOperand]
    have hpeel : lookupName sd.env "%sub.i" = lookupName s₈.env "%sub.i" := by
      show lookupName (closeEmitS (closeC₁₂ (closeC₁₀b C)
          (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
        (closeEndIIS (closeAfter109 (closeC₁₀b C)
          (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
          (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
          (BitVec.ofNat 64 G.evcap)) (BitVec.ofNat 8 4)).env "%sub.i" = _
      rw [closeEmitS_other (C := closeC₁₂ (closeC₁₀b C)
            (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
          (s := closeEndIIS (closeAfter109 (closeC₁₀b C)
            (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
            (close109S s₈ r (BitVec.ofNat 8 4)) (BitVec.ofNat 64 C.evlen)
            (BitVec.ofNat 64 G.evcap)) (k := BitVec.ofNat 8 4) (n := "%sub.i")
          (by decide),
        closeEndIIS_other (C := closeC₁₂ (closeC₁₀b C)
            (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295))
          (s := close109S s₈ r (BitVec.ofNat 8 4))
          (nl := BitVec.ofNat 64 C.evlen) (nc := BitVec.ofNat 64 G.evcap)
          (n := "%sub.i") (by decide),
        close109S_other (s := s₈) (r := r) (c8 := BitVec.ofNat 8 4)
          (n := "%sub.i") (by decide)]
    rw [hpeel, hsub8,
      closeSub_eq (Nat.pos_of_ne_zero hsp) (depth_lt_32 hInv.depth_cap)]
  · exact LeanLLVM.evalOperand_reg_of L11.inv'.inc_reg
  · exact L11.inv'.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep))
      (by simp [walkStaticRegs])
  · -- the post-call root word: the depth-zero after-value store, outside both
    -- writes the finalisation makes
    have hmemR : sd.mem =
        writeBytes
          (writeBytes r.mem (G.ev + C.evlen) (natToBytes (BitVec.ofNat 8 4).toNat 1))
          (C.stage.z + 8) (wordBytes 8 (C.evlen + 1)) := rfl
    rw [hmemR]
    rw [walkReadBytes_writeBytes_outside (start := C.stage.z + 8)
          (v := wordBytes 8 (C.evlen + 1)) (by
            have hlen : (wordBytes 8 (C.evlen + 1)).length = 8 := by
              rw [wordBytes, natToBytes_length]
            rw [hlen]
            rcases C.stage.rootSlot_log with h | h
            · left; omega
            · right; simp only [stage2LogExtent] at h; omega),
        walkReadBytes_writeBytes_outside (start := G.ev + C.evlen)
          (v := natToBytes (BitVec.ofNat 8 4).toNat 1) (by
            rw [natToBytes_length]
            have hnev0 : G.nev0 ≤ C.evlen := by
              rw [hInv.evlen_eq]; omega
            rcases C.stage.rootSlot_ev with h | h
            · left; omega
            · right; omega)]
    have hspz0 : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat = 0 := by
      rw [hspz, hsp1]
    rw [hspz0] at hm
    have hm0 : stage2AfterValue s₈.mem 0 (G.next0 + 8) C.stage.ctype C.stage.cst =
        some (writeBytes s₈.mem (G.next0 + 8) (wordBytes 4 1)) := by
      simp [stage2AfterValue]
    have hm' : m = writeBytes s₈.mem (G.next0 + 8) (wordBytes 4 1) :=
      Option.some.inj (hm.symm.trans hm0)
    rw [hmem, hm']
    have hrootread : readBytes (writeBytes s₈.mem (G.next0 + 8) (wordBytes 4 1))
        (G.next0 + 8) 4 = some (wordBytes 4 1) := by
      simpa only [wordBytes, natToBytes_length] using
        (readBytes_writeBytes_same (m := s₈.mem) (addr := G.next0 + 8)
          (bs := wordBytes 4 1))
    simpa only [wordBytes] using hrootread

/-! ### Axiom footprints -/

#print axioms closeBracketMerge_term

end WalkScope
end LeanLLVM.Refinement
