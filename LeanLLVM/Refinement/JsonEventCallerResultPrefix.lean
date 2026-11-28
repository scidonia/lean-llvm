/-
# The `[1]` walk from the staged seed: the opener and the first loop pass

`evb_caller_result` (`JsonEventCallerResult`) takes the five counted segments of the
`[1]` walk from its caller.  This module starts the construction from the seed the
entry run hands the loop: `walkSeed G S` at a state carrying `WalkInv`, with `[1]`'s
document and entry stream.  The opener's nine links and the header's pass are
*produced* here — `bracketOpenSeg` and `headPassSeg` at the seed's own cells — and
the carry identifications are the segments' endpoints, not hypotheses:

* the opener's merge is `openC₉ (openHeadC (walkSeed G S)) 0x5B`, the term the
  opener's tail reaches, and its trace appends the bracket's tag;
* the first head pass reaches `headPassC C₁ 1 1`, the header's `%k.2.i`/`%sp.i.1`
  at the merge's own selections.

What is taken is the staging and the environment: the seed's invariant (which the
entry's run produces; `seededInv`/`walkSeedInvariant_geometry` are the producers)
and the root slot's staged word, the one memory cell `WalkInv` does not name
(`root_slot` is presence, not value).  No segment, carry equation or merge reading
is supplied.

There is no `sorry`, `admit` or `native_decide`.
-/
import LeanLLVM.Refinement.JsonEventPremisesOne
import LeanLLVM.Refinement.JsonStage2WalkMergeCond
import LeanLLVM.Refinement.JsonStage2WalkSpansChain

set_option autoImplicit false

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR

/-! ### The seed's cells at `[1]` -/

/-- `[1]`'s first entry byte, from the document's spelling. -/
theorem evbEntryByte_zero {m0 : Mem} {G : WalkGeom m0}
    (hbs : G.bs = evbDoc) (hent : G.ent = [0, 1, 2]) :
    entryByte G 0 = 0x5B := by
  simp only [entryByte, entryPos, hbs, hent, List.getD]
  rfl

/-- The seed's `%8` is the first entry's byte. -/
theorem evbSeed_reg8 {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {s : State}
    (hInv : WalkInv G (walkSeed G S) s)
    (hbs : G.bs = evbDoc) (hent : G.ent = [0, 1, 2]) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 0x5B)) := by
  have h := hInv.iter.reg8
  rw [show (walkSeed G S).k = 0 from rfl] at h
  rw [evbEntryByte_zero hbs hent] at h
  have hto : (0x5B : UInt8).toNat = 91 := by decide
  rw [hto] at h
  exact LeanLLVM.evalOperand_reg_of h

/-- The seed's `%8` names the entry's byte, which is the operand's literal. -/
theorem evbSeed_entryByte {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G}
    (hbs : G.bs = evbDoc) (hent : G.ent = [0, 1, 2]) :
    BitVec.ofNat 8 0x5B = BitVec.ofNat 8 (entryByte G (walkSeed G S).k).toNat := by
  rw [show (walkSeed G S).k = 0 from rfl, evbEntryByte_zero hbs hent]
  rfl

/-- The seed's depth and written mark are zero. -/
theorem evbSeed_sp {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    (walkSeed G S).sp = 0 := rfl

theorem evbSeed_wlen {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    (walkSeed G S).wlen = 0 := rfl

/-- The seed's `%nep` is the staged count. -/
theorem evbSeed_nep {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {s : State}
    (hInv : WalkInv G (walkSeed G S) s) :
    lookupName s.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep)) :=
  hInv.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs])

/-- The seed's `%inc.i` is its index's successor. -/
theorem evbSeed_inc {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {s : State}
    (hInv : WalkInv G (walkSeed G S) s) :
    lookupName s.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 ((walkSeed G S).k + 1))) :=
  hInv.inc_reg

/-- **The seed's value-position staging.**  At depth zero the precondition asks only
that its first argument's word is `0`, which it is. -/
theorem evbSeed_valuePos_pre {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {s : State}
    (_hInv : WalkInv G (walkSeed G S) s) (rd : BitVec 32) :
    s2ValuePosPre [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 rd,
      .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst] s.mem s.next := by
  refine ⟨BitVec.ofNat 32 (walkSeed G S).sp, rd,
    (walkSeed G S).stage.ctype, (walkSeed G S).stage.cst, rfl, ?_⟩
  left
  rw [evbSeed_sp]
  decide

/-- **The call at the seed answers `1`** when the root word is zero: `stage2ValuePos`
at depth zero reads only that word. -/
theorem evbSeed_valuePos_ret {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {s : State}
    (hInv : WalkInv G (walkSeed G S) s)
    {rd : BitVec 32} (hrd : rd.toNat = 0)
    {r : CallOutcome}
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 rd,
       .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst] s.mem s.next =
        some r) :
    r.ret = .int 32 (BitVec.ofNat 32 1) := by
  have hpre := evbSeed_valuePos_pre hInv rd
  obtain ⟨v, hv, hret, -, -⟩ :=
    s2ValuePos_sound (args := [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 rd,
      .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst])
      (mem := s.mem) (next := s.next) hpre hcall
  have hval : stage2ValuePos s.mem (BitVec.ofNat 32 (walkSeed G S).sp).toNat rd.toNat
      (walkSeed G S).stage.ctype (walkSeed G S).stage.cst = some 1 := by
    rw [show (BitVec.ofNat 32 (walkSeed G S).sp).toNat = 0 from by
      rw [evbSeed_sp]; decide, hrd]
    simp [stage2ValuePos]
  have hv1 : v = 1 := Option.some.inj (hv.symm.trans hval)
  rw [hret, hv1]

/-! ### The opener's nine links -/

/-- **The opener's segment and its carry, from the seed.**  The byte is the document's
first entry (`0x5B`), the root word is the staged zero (the environmental cell), and
the segment's endpoint is the term `openC₉ (openHeadC (walkSeed G S)) 0x5B`. -/
theorem evb_openSeg_from_seed {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {s₀ : State}
    (hInv₀ : WalkInv G (walkSeed G S) s₀)
    (hbs : G.bs = evbDoc) (hent : G.ent = [0, 1, 2])
    (hroot₀ : readBytes s₀.mem (G.next0 + 8) 4 =
      some (natToBytes (0 : BitVec 32).toNat 4)) :
    ∃ (r : CallOutcome) (rd : BitVec 32),
      rd.toNat = 0 ∧
      r.ret = .int 32 (BitVec.ofNat 32 1) ∧
      WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s₀
        (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B))
        (openS₉ (openHeadC (walkSeed G S)) (openBrS₄ s₀) r rd (BitVec.ofNat 8 0x5B)) 9 := by
  let b : BitVec 8 := BitVec.ofNat 8 0x5B
  have h8 : evalOperand s₀ (.reg "%8") = some (.int 8 b) := evbSeed_reg8 hInv₀ hbs hent
  have hbe : b = BitVec.ofNat 8 (entryByte G (walkSeed G S).k).toNat :=
    evbSeed_entryByte hbs hent
  have hsp519 : (walkSeed G S).sp ≤ 519 := by rw [evbSeed_sp]; omega
  let rd : BitVec 32 := 0
  have hrdval : rd.toNat = 0 := rfl
  have hread : readBytes s₀.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4) := by
    rw [hrdval]
    exact hroot₀
  have hpreV := evbSeed_valuePos_pre (G := G) (S := S) (s := s₀) hInv₀ rd
  obtain ⟨r, hcall⟩ :=
    s2ValuePos_answers (args := [.int 32 (BitVec.ofNat 32 (walkSeed G S).sp), .int 32 rd,
      .ptr (walkSeed G S).stage.ctype, .ptr (walkSeed G S).stage.cst])
      (mem := s₀.mem) (next := s₀.next) hpreV
  have hret := evbSeed_valuePos_ret (G := G) (S := S) hInv₀ hrdval hcall
  exact ⟨r, rd, hrdval, hret,
    bracketOpenSeg G (walkSeed G S) s₀ hInv₀ (walkSeed_block G S) h8
      (by rfl) hbe hsp519 hread hpreV r hcall hret⟩

/-! ### The first header's pass -/

/-- The opener's merge state is at the predecessor the closer of the tail names. -/
theorem openS₉_pre {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (r : CallOutcome) (rd : BitVec 32) (b : BitVec 8) :
    (openS₉ C s r rd b).pre = some "out_reserve.exit.i.i" := rfl

/-- `%inc.i` at the opener's merge is the head's own. -/
theorem openS₉_incAt {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (r : CallOutcome) (rd : BitVec 32) (b : BitVec 8) :
    lookupName (openS₉ C s r rd b).env "%inc.i" = lookupName s.env "%inc.i" :=
  openS₉_inc C s r rd b

/-- `%nep` at the opener's merge is the head's own. -/
theorem openS₉_nepAt {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (r : CallOutcome) (rd : BitVec 32) (b : BitVec 8) :
    lookupName (openS₉ C s r rd b).env "%nep" = lookupName s.env "%nep" :=
  openS₉_nep C s r rd b

/-- **The first head pass, from the opener's merge.**  The merge's `%sp.i.1` is
`%inc33.i` (`C.sp + 1`) and its `%k.2.i` is `%inc.i` (`C.k + 1`), so the header reaches
`headPassC C (C.k + 1) (C.sp + 1)`. -/
theorem evb_headPass_from_opener {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G}
    {s₀ : State} (hInv₀ : WalkInv G (walkSeed G S) s₀)
    (_hbs : G.bs = evbDoc) (_hent : G.ent = [0, 1, 2]) (hnep : G.nep = 3)
    {r : CallOutcome} {rd : BitVec 32}
    (hseg : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s₀
      (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B))
      (openS₉ (openHeadC (walkSeed G S)) (openBrS₄ s₀) r rd (BitVec.ofNat 8 0x5B)) 9) :
    ∃ s', WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s₀
      (headPassC (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B))
        ((walkSeed G S).k + 1) ((walkSeed G S).sp + 1)) s' 11 := by
  let C₁ : WalkCarry G := openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)
  let s₁ : State := openS₉ (openHeadC (walkSeed G S)) (openBrS₄ s₀) r rd
    (BitVec.ofNat 8 0x5B)
  have hblock : C₁.block = "cleanup478.i" := rfl
  have hpre : s₁.pre = some "out_reserve.exit.i.i" := openS₉_pre _ _ _ _ _
  have hsp : phiIncoming "out_reserve.exit.i.i" cleanupSpIncoming = some (.reg "%inc33.i") :=
    by decide
  have hspv : evalOperand s₁ (.reg "%inc33.i") =
      some (.int 32 (BitVec.ofNat 32 (C₁.sp + 1))) := by
    simp only [evalOperand]
    rw [openS₉_inc33]
  have hk : phiIncoming "out_reserve.exit.i.i" cleanupKIncoming = some (.reg "%inc.i") :=
    by decide
  have hkv : evalOperand s₁ (.reg "%inc.i") =
      some (.int 64 (BitVec.ofNat 64 (C₁.k + 1))) := by
    simp only [evalOperand]
    rw [openS₉_incAt]
    rw [openBrS₄_other _ _ (by decide) (by decide) (by decide) (by decide)]
    rw [evbSeed_inc hInv₀]
  have hnepv : lookupName s₁.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep)) := by
    rw [openS₉_nepAt]
    rw [openBrS₄_other _ _ (by decide) (by decide) (by decide) (by decide)]
    exact evbSeed_nep hInv₀
  have hnep_lt : G.nep < 2 ^ 64 := WalkGeom.nep_lt G
  have hguard : C₁.k + 1 < (BitVec.ofNat 64 G.nep).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnep_lt]
    simp only [C₁, openC₉, openHeadC]
    rw [show (walkSeed G S).k = 0 from rfl, hnep]
    omega
  have hcap : C₁.k + 1 < G.nep := by
    simp only [C₁, openC₉, openHeadC]
    rw [show (walkSeed G S).k = 0 from rfl, hnep]
    omega
  have hadvance : C₁.k < C₁.k + 1 := by omega
  have hspcap : C₁.sp + 1 ≤ stage2StackExtent := by
    simp only [C₁, openC₉, openHeadC, evbSeed_sp, stage2StackExtent]
    omega
  have hspw : C₁.sp + 1 ≤ C₁.wlen := by
    simp only [C₁, openC₉, openHeadC, evbSeed_sp, evbSeed_wlen]
    omega
  obtain ⟨s', hsegH⟩ :=
    headPassSeg G C₁ s₁ hseg.inv' hblock hpre hsp hspv hk hkv hnepv hguard hcap
      hadvance hspcap hspw
  exact ⟨s', hseg.trans hsegH⟩

/-! ### The carry's two computed numbers

`mergeCond_of_chain`'s extended carries differ from the segments' plain ones only in
`spm`/`root`.  At `[1]` the opener's push selects `C.sp + 1` and the header's pass
carries it, so the first loop head's depth is `1` and the merge's is the seed's zero
advanced by one.  Nothing here reads the segments. -/

/-- The opener's merge selects the push's own depth. -/
theorem evb_C₁_spm {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} :
    (openC₉M (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)).spm = 1 := by
  rw [openC₉M_spm, openHeadC_sp, evbSeed_sp]

/-- The first head pass carries the merge's depth, so the head's selected depth is
`1` and its index is `1`. -/
theorem evb_H₁_cells {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} :
    (headPassCM (openC₉M (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B))
        ((walkSeed G S).k + 1)).sp = 1 ∧
    (headPassCM (openC₉M (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B))
        ((walkSeed G S).k + 1)).k = (walkSeed G S).k + 1 := by
  refine ⟨?_, rfl⟩
  rw [headPassCM_sp, evb_C₁_spm]

/-- The bracket's tag is `3`, the trace's first record. -/
theorem evb_tag_bracket :
    (ifEnd24St (BitVec.ofNat 8 0x5B)).toNat = 3 := by decide

/-- **The opener's trace appends the bracket's tag.**  `openC₉`'s `events` field is
the source's plus `EventRecord.tag (ifEnd24St b).toNat`, and the bracket's tag is `3`. -/
theorem evb_open_trace {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} :
    (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)).events =
      (walkSeed G S).events ++ [EventRecord.tag 3] := by
  simp only [openC₉, openHeadC, evb_tag_bracket]

/-- **The opener's merge cells.**  The merge keeps the index and the depth, and it is
the block the header's pass starts from. -/
theorem evb_open_cells {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} :
    (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)).block = "cleanup478.i" ∧
    (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)).k = (walkSeed G S).k ∧
    (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)).sp = (walkSeed G S).sp :=
  ⟨rfl, rfl, rfl⟩

/-! ### Axiom footprints -/

#print axioms evbEntryByte_zero
#print axioms evbSeed_reg8
#print axioms evbSeed_valuePos_ret
#print axioms evb_openSeg_from_seed
#print axioms evb_headPass_from_opener
#print axioms evb_tag_bracket
#print axioms evb_C₁_spm
#print axioms evb_H₁_cells
#print axioms evb_open_trace
#print axioms evb_open_cells

end WalkScope
end LeanLLVM.Refinement
