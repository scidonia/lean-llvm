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
| `.stringOpener`, `C.sp = 0`, root word `0` | any | `hcontArm_twoEntry_of_payload` (the payload's lane and its two calls) |
| `.stringOpener`, `C.sp = 0`, root word nonzero | any | `hcontArm_stringOpenZeroRefuse_of_staging` (its refusal: the call answers `0`, the walk takes `if.then249.i`) |
| `.stringOpener`, `C.sp ≠ 0` | any | `hcontArm_stringOpenAboveZero_of_class` (the class's row `deep`) |
| `.comma`, `.colon`, `.closeBracket`, `.closeBrace` | any | `hcontArm_of_derivedClass` (the invariant's own cells) |
| `.openBracket`, `.openBrace` | any | the payload's `abi.openCall` and the opener producers |
| `.value` | `wsByte` | `hcontArm_scalarRun_of_class` (the class's `scalarRun` row) |
| `.value` | the three leaves | `hcontArm_value_of_lane` (the payload's default lane) |
| `.defaultValueHigh` | `wsByte` | `hcontArm_ws_of_rows` (the whitespace group, at the class's two clear bits — the guard the group's `run` field now carries) |
| `.defaultValueHigh` | the three leaves | `hcontArm_cleanup_of_class` (the class's `cleanup`/`cleanupRow`) |
| the six tag-clear default classes | any | **the refusal arm** (`HcontArm.badToken`, from `HcontClassRows.refuseSeg`): those bytes are never value bytes (`%8 < 44`, `59 … 90`, `92`, `94 … 122` minus the three literals, `124`), so the edge takes `if.then432.i` and refuses.  The three literal bytes inside `94 … 122` keep the run arm (`.defaultValueBracketHigh`'s `f`/`n`/`t` sub-branches) |
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
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessString
import LeanLLVM.Refinement.JsonStage2WalkDispatchHcontStringDeep

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The depth-zero string opener's refusal

`if.then219.i`'s call is `s2_value_pos` at the root slot's read, and at depth zero the
model answers `1` only when that word is `0`.  So a depth-zero opener whose root word is
nonzero is the *other* arm of the same byte: its call answers `0`, `if.end245.i`'s
`%or.cond523.i` is clear, the walk leaves for `if.then249.i` — the refusal word's store —
and reaches the copy at `if.then`.  This is the class's own route from the head, and the
split in `walkContinueArm_of_payload` is the root word's. -/

/-- **The value-position callee's reply at depth zero**: `1` only for a zero root word.
This module is upstream of `JsonStage2WalkDispatchAbiOfInv`, so the fact is restated here. -/
theorem stage2ValuePos_zero_at {mem : Mem} {rd : BitVec 32} {ct cs : Nat} :
    stage2ValuePos mem 0 rd.toNat ct cs = some (if rd.toNat = 0 then 1 else 0) := by
  simp [stage2ValuePos]

/-- **The depth-zero string opener's refusal, from the head.**  The byte `34`'s head chain
to `if.then219.i`, the zero answer and `if.end245.i`'s refusal, as one `WalkRefuseAt`.  The
answer is `0` because the lane's root word is nonzero (`stage2ValuePos` at depth zero), and
the price is inside the entry's own credit (`refusePrice_of_le`). -/
noncomputable def hcontStringOpenZeroRefuseRoute {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1)
    (hsp0 : C.sp = 0) (L : HcontStringLane G C s) (hrd : L.rd.toNat ≠ 0) :
    WalkRefuseAt (stage2Calls stage2SubCalls) G C s := by
  let q : Nat := bytesToNat L.bs
  have hq : q = entryPos G (C.k + 1) := by
    dsimp only [q]
    exact L.hq
  have hlt91 : evalICmp .slt (BitVec.ofNat 8 34) (BitVec.ofNat 8 91) = 1 := by decide
  have hlt44 : evalICmp .slt (BitVec.ofNat 8 34) (BitVec.ofNat 8 44) = 1 := by decide
  have heq34 : evalICmp .eq (BitVec.ofNat 8 34) (BitVec.ofNat 8 34) = 1 := by decide
  have hk63 : C.k + 1 < 2 ^ 63 := by
    have h1 := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hk64 : C.k + 2 < 2 ^ 64 := by
    have h1 := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  have hn64 : G.n < 2 ^ 64 := by
    have h := G.maxDoc
    simp only [stage2MaxDocument] at h
    omega
  have hcount : evalICmp .ult (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) = 1 :=
    cont_ult_one G C hk
  have h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 34)) := by
    rw [← eq_bit_value hclass]
    exact cont_reg8 hInv
  -- 1. `NodeBlock21`
  obtain ⟨s1, hl1, hs1⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hs1' : s1 = strS₁ s := by
    rw [hs1, hlt91, if_pos rfl]
    dsimp only [strS₁, State.bind]
  have hcarry1 : ({ C with
      block := (if evalICmp .slt (BitVec.ofNat 8 34) (BitVec.ofNat 8 91) = 1 then "NodeBlock5"
        else "NodeBlock19") } : WalkCarry G) = strC₁ C := by
    rw [hlt91, if_pos rfl]
  subst hs1'
  have hl1' : WalkLink (stage2Calls stage2SubCalls) G C s (strC₁ C) (strS₁ s) := by
    rw [← hcarry1]; exact hl1
  -- 2. `NodeBlock5`
  have h8₂ : evalOperand (strS₁ s) (.reg "%8") = some (.int 8 (BitVec.ofNat 8 34)) := by
    simp only [strS₁, State.bind, evalOperand,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s2, hl2, hs2⟩ :=
    WalkLink.NodeBlock5_at (calls := stage2Calls stage2SubCalls) G (strC₁ C) (strS₁ s)
      hl1'.inv' rfl h8₂
  have hs2' : s2 = strS₂ s := by
    rw [hs2, hlt44, if_pos rfl]
    dsimp only [strS₂, strS₁, State.bind]
  have hcarry2 : ({ strC₁ C with
      block := (if evalICmp .slt (BitVec.ofNat 8 34) (BitVec.ofNat 8 44) = 1 then "LeafBlock"
        else "NodeBlock") } : WalkCarry G) = strC₂ C := by
    rw [hlt44, if_pos rfl]
  subst hs2'
  have hl2' : WalkLink (stage2Calls stage2SubCalls) G (strC₁ C) (strS₁ s)
      (strC₂ C) (strS₂ s) := by
    rw [← hcarry2]; exact hl2
  -- 3. `LeafBlock`
  have h8₃ : evalOperand (strS₂ s) (.reg "%8") = some (.int 8 (BitVec.ofNat 8 34)) := by
    simp only [strS₂, strS₁, State.bind, evalOperand,
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  obtain ⟨s3, hl3, hs3⟩ :=
    WalkLink.LeafBlock_at (calls := stage2Calls stage2SubCalls) G (strC₂ C) (strS₂ s)
      hl2'.inv' rfl h8₃
  have hs3' : s3 = strS₃ s := by
    rw [hs3, heq34, if_pos rfl]
    dsimp only [strS₃, strS₂, strS₁, State.bind]
  have hcarry3 : ({ strC₂ C with
      block := (if evalICmp .eq (BitVec.ofNat 8 34) (BitVec.ofNat 8 34) = 1 then "sw.bb202.i"
        else "sw.default.i") } : WalkCarry G) = strC₃ C := by
    rw [heq34, if_pos rfl]
  subst hs3'
  have hl3' : WalkLink (stage2Calls stage2SubCalls) G (strC₂ C) (strS₂ s)
      (strC₃ C) (strS₃ s) := by
    rw [← hcarry3]; exact hl3
  -- 4. `sw.bb202.i`
  have hinc₄ : evalOperand (strS₃ s) (.reg "%inc.i") =
      some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := by
    simp only [strS₃, strS₂, strS₁, State.bind, evalOperand,
      lookupName_cons_ne (k := "%SwitchLeaf") (n := "%inc.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%inc.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%inc.i") _ _ (by decide)]
    exact LeanLLVM.evalOperand_reg_of hInv.inc_reg
  have hnep₄ : evalOperand (strS₃ s) (.reg "%nep") =
      some (.int 64 (BitVec.ofNat 64 G.nep)) := by
    simp only [strS₃, strS₂, strS₁, State.bind, evalOperand,
      lookupName_cons_ne (k := "%SwitchLeaf") (n := "%nep") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%nep") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%nep") _ _ (by decide)]
    exact LeanLLVM.evalOperand_reg_of
      (hInv.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs]))
  obtain ⟨s4, hl4, hs4⟩ :=
    WalkLink.sw_bb202_i_at (calls := stage2Calls stage2SubCalls) G (strC₃ C) (strS₃ s)
      hl3'.inv' rfl hinc₄ hnep₄
  have hs4' : s4 = strS₄ s := by
    rw [hs4, hcount, if_pos rfl]
    dsimp only [strS₄, strS₃, strS₂, strS₁, State.bind]
  have hcarry4 : ({ strC₃ C with
      block := (if evalICmp .ult (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) = 1
        then "if.end207.i" else "if.then205.i") } : WalkCarry G) = strC₄ C := by
    rw [hcount, if_pos rfl]
  subst hs4'
  have hl4' : WalkLink (stage2Calls stage2SubCalls) G (strC₃ C) (strS₃ s)
      (strC₄ C) (strS₄ s) := by
    rw [← hcarry4]; exact hl4
  -- 5. `if.end207.i`: the advance, the lane read and the cursor-record store
  have hinc₅ : lookupName (strS₄ s).env "%inc.i" =
      some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := by
    simp only [strS₄, strS₃, strS₂, strS₁, State.bind,
      lookupName_cons_ne (k := "%cmp203.not.i") (n := "%inc.i") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf") (n := "%inc.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%inc.i") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%inc.i") _ _ (by decide)]
    exact hInv.inc_reg
  have h4₅ : lookupName (strS₄ s).env "%4" =
      some (.int 64 (BitVec.ofNat 64 G.n)) := by
    simp only [strS₄, strS₃, strS₂, strS₁, State.bind,
      lookupName_cons_ne (k := "%cmp203.not.i") (n := "%4") _ _ (by decide),
      lookupName_cons_ne (k := "%SwitchLeaf") (n := "%4") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%4") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%4") _ _ (by decide)]
    exact hInv.regs ("%4", .int 64 (BitVec.ofNat 64 G.n)) (by simp [walkStaticRegs])
  have hread₅ : readBytes (strS₄ s).mem (G.ep + (C.k + 1) * 4) 4 = some L.bs := by
    simpa only [strS₄, strS₃, strS₂, strS₁, State.bind] using L.hreadLane
  have hqlt : q < G.n := by
    rw [hq]
    exact entryPos_lt G (by omega)
  have hbit₅ : evalICmp .ugt (BitVec.ofNat 64 G.n) (BitVec.ofNat 64 q) = 1 :=
    walkEvalICmp_ugt_ofNat hn64 (by omega) hqlt
  obtain ⟨s5, hl5, hs5⟩ :=
    WalkLink.if_end207_i (calls := stage2Calls stage2SubCalls) G (strC₄ C) (strS₄ s)
      hl4'.inv' rfl (q := q) hk63 hinc₅ h4₅ hread₅ (by rfl) hk64
  have hs5' : s5 = strS₅ G C q s := by
    rw [hs5, hbit₅, if_pos rfl]
    dsimp only [strS₅, strSetK₅, strS₄, strS₃, strS₂, strS₁, State.bind, stateAt, cells]
  have hcarry5 : ({ strC₄ C with
      block := (if evalICmp .ugt (BitVec.ofNat 64 G.n) (BitVec.ofNat 64 q) = 1
        then "if.then219.i" else "if.then214.i") } : WalkCarry G) = strC₅ C := by
    rw [hbit₅, if_pos rfl]
  subst hs5'
  have hl5' : WalkLink (stage2Calls stage2SubCalls) G (strC₄ C) (strS₄ s)
      (strC₅ C) (strS₅ G C q s) := by
    rw [← hcarry5]; exact hl5
  -- 6. `if.then219.i`: the value-position call at depth zero
  have hInv5 : WalkInv G (strC₅ C) (strS₅ G C q s) := hl5'.inv'
  have hroot5 : lookupName (strS₅ G C q s).env "%root_done.i"
      = some (.ptr (G.next0 + 8)) :=
    hInv5.regs ⟨"%root_done.i", .ptr (G.next0 + 8)⟩ (by simp [walkStaticRegs])
  have hread5 : readBytes (strS₅ G C q s).mem (G.next0 + 8) 4
      = some (natToBytes L.rd.toNat 4) := by
    have h := walkReadBytes_rootSlot_at (G := G) (C := C) (s := s) (k := C.k + 2)
      (rd := L.rd) L.hreadRoot
    simpa only [strS₅, strSetK₅, strS₄, strS₃, strS₂, strS₁, State.bind, stateAt] using h
  have hspv : (BitVec.ofNat 32 C.sp).toNat = 0 := by rw [hsp0]; decide
  have hpre5 : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 L.rd,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (strS₅ G C q s).mem (strS₅ G C q s).next :=
    ⟨BitVec.ofNat 32 C.sp, L.rd, C.stage.ctype, C.stage.cst, rfl, Or.inl hspv⟩
  have hx5 : ∀ r, stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 L.rd,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (strS₅ G C q s).mem (strS₅ G C q s).next = some r →
      r.ret = .int 32 (BitVec.ofNat 32 0) := by
    intro r hr
    rw [s2ValuePos_reply, hspv, stage2ValuePos_zero_at, ite_eq_right hrd] at hr
    have hsame : r = ⟨.int 32 (BitVec.ofNat 32 0),
      (strS₅ G C q s).mem, (strS₅ G C q s).next⟩ := (Option.some.inj hr).symm
    rw [hsame]
  obtain ⟨s6, hl6, hs6⟩ :=
    WalkLink.if_then219_i (G := G) (C := strC₅ C) (s := strS₅ G C q s) hInv5 rfl
      (root := G.next0 + 8) (rd := L.rd) (x := 0) hroot5 hread5 hpre5 hx5
  have hbit6 : evalICmp .eq (BitVec.ofNat 32 C.sp) (BitVec.ofNat 32 0) = 1 := by
    rw [hsp0]; decide
  have hs6' : s6 = strS₆ G C q L.rd 0 s := by
    rw [hs6, hbit6, if_pos rfl]
    rfl
  have hcarry6 : ({ strC₅ C with
      block := (if evalICmp .eq (BitVec.ofNat 32 C.sp) (BitVec.ofNat 32 0) = 1
        then "if.end245.i" else "land.lhs.true.i") } : WalkCarry G) = strC₆ C := by
    rw [hbit6, if_pos rfl]
  subst hs6'
  have hl6' : WalkLink (stage2Calls stage2SubCalls) G (strC₅ C) (strS₅ G C q s)
      (strC₆ C) (strS₆ G C q L.rd 0 s) := by
    rw [← hcarry6]; exact hl6
  -- 7. `if.end245.i`: the key's `0` and the answer's `0` select the refusal
  have hInv6 : WalkInv G (strC₆ C) (strS₆ G C q L.rd 0 s) := hl6'.inv'
  have hcall7 : lookupName (strS₆ G C q L.rd 0 s).env "%call222.i"
      = some (.int 32 0) := by
    simp [strS₆, strS₅, strS₄, strS₃, strS₂, strS₁, State.bind, stateAt, cells, lookupName]
  have hv7 : evalOperand (strS₆ G C q L.rd 0 s)
      (.imm (.int 1 (BitVec.ofNat 1 0))) = some (.int 1 0) := rfl
  have hbit7 : (if (0 : BitVec 1) = 1 then (1 : BitVec 1)
      else evalICmp .ne (0 : BitVec 32) (BitVec.ofNat 32 0)) = 0 := by
    rw [if_neg (by decide)]
    decide
  obtain ⟨s7, hl7, _hs7⟩ :=
    WalkLink.if_end245_i (G := G) (C := strC₆ C) (s := strS₆ G C q L.rd 0 s)
      hInv6 rfl (p := "if.then219.i") (op := .imm (.int 1 (BitVec.ofNat 1 0)))
      (k := 0) (x := 0) rfl if_end245_key_then219 hv7 hcall7
  have hcarry7 : ({ strC₆ C with
      block := (if (if (0 : BitVec 1) = 1 then (1 : BitVec 1)
        else evalICmp .ne (0 : BitVec 32) (BitVec.ofNat 32 0)) = 1
        then "if.end256.i" else "if.then249.i") } : WalkCarry G)
      = { strC₆ C with block := "if.then249.i" } := by
    rw [hbit7]
    rfl
  have hl7' : WalkLink (stage2Calls stage2SubCalls) G (strC₆ C)
      (strS₆ G C q L.rd 0 s) { strC₆ C with block := "if.then249.i" } s7 := by
    rw [← hcarry7]; exact hl7
  -- 8. `if.then249.i`: the refusal word's store
  have hidx : evalOperand s7 (.reg "%idxprom.i")
      = some (.int 64 (BitVec.ofNat 64 (entryPos G C.k))) :=
    LeanLLVM.evalOperand_reg_of hl7'.inv'.idx_reg
  have he : lookupName s7.env "%e" = some (.ptr C.stage.e) :=
    hl7'.inv'.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs])
  obtain ⟨s8, hl8, hs8⟩ :=
    WalkLink.if_then249_i_at (calls := stage2Calls stage2SubCalls) G
      { strC₆ C with block := "if.then249.i" } s7 hl7'.inv' rfl
      (j := entryPos G C.k) hidx he
      (le_of_lt (entryPos_lt G (by omega)))
      (entryPos_lt_64 G C.k)
  have hread8 : readBytes s8.mem (C.stage.e + 8) 8 =
      some (wordBytes 8 (entryPos G C.k)) := by
    rw [hs8]
    simpa only [State.bind] using
      refuseSegment_word_of_store (m := _) (e := C.stage.e) (v := entryPos G C.k)
  -- the composition
  have h1 : WalkSegment (stage2Calls stage2SubCalls) G C s (strC₁ C) (strS₁ s) 1 :=
    WalkSegment.of_link hl1'
  have h2 : WalkSegment (stage2Calls stage2SubCalls) G C s (strC₂ C) (strS₂ s) 2 :=
    h1.trans (WalkSegment.of_link hl2')
  have h3 : WalkSegment (stage2Calls stage2SubCalls) G C s (strC₃ C) (strS₃ s) 3 :=
    h2.trans (WalkSegment.of_link hl3')
  have h4 : WalkSegment (stage2Calls stage2SubCalls) G C s (strC₄ C) (strS₄ s) 4 :=
    h3.trans (WalkSegment.of_link hl4')
  have h5 : WalkSegment (stage2Calls stage2SubCalls) G C s (strC₅ C) (strS₅ G C q s) 5 :=
    h4.trans (WalkSegment.of_link hl5')
  have hseg6 : WalkSegment (stage2Calls stage2SubCalls) G C s (strC₆ C)
      (strS₆ G C q L.rd 0 s) 6 :=
    h5.trans (WalkSegment.of_link hl6')
  have hseg2 : WalkSegment (stage2Calls stage2SubCalls) G (strC₆ C)
      (strS₆ G C q L.rd 0 s)
      { strC₆ C with block := "if.then", eoff := entryPos G C.k, refusal := true } s8 2 :=
    (WalkSegment.of_link hl7').trans (WalkSegment.of_link hl8)
  refine ⟨_, s8, 8, ⟨hseg6.trans hseg2, rfl, ⟨entryPos G C.k, entryPos_le G C.k, hread8⟩⟩,
    hl8.inv'.eoff_le, ?_⟩
  exact refusePrice_of_le G C (p := 8) (by omega) (by omega)

/-- **The depth-zero string opener's refusal arm, from the staging.**  The class's own
facts plus the route: the root word's nonzero read is the split's other arm, and
`hcontStringOpenZeroRefuseRoute` composes the walk to the copy. -/
noncomputable def hcontArm_stringOpenZeroRefuse_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1)
    (hsp0 : C.sp = 0) (L : HcontStringLane G C s) (hrd : L.rd.toNat ≠ 0) :
    HcontArm (stage2Calls stage2SubCalls) G C s := by
  have hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 L.rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next :=
    ⟨BitVec.ofNat 32 C.sp, L.rd, C.stage.ctype, C.stage.cst, rfl,
      Or.inl (by rw [hsp0]; decide)⟩
  let r : CallOutcome := Classical.choose (s2ValuePos_answers hpreV)
  have hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 L.rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r :=
    Classical.choose_spec (s2ValuePos_answers hpreV)
  exact .stringOpenZeroRefuse
    (by rw [← eq_bit_value hclass]; exact cont_reg8 hInv)
    hsp0 L.hreadRoot hrd hpreV r hcall
    (hcontStringOpenZeroRefuseRoute hInv hblock hk hclass hsp0 L hrd)

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
      · -- the depth-zero opener splits on the root word the call reads
        let L : HcontStringLane G C s := hp.lane.string C s hInv hblock hk hsp
        by_cases hrd0 : L.rd.toNat = 0
        · have hroot0 : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4) := by
            rw [L.hreadRoot, hrd0]
          exact ⟨hcontArm_twoEntry_of_payload hInv hblock hk h34 hsp hroot0 hp⟩
        · exact ⟨hcontArm_stringOpenZeroRefuse_of_staging hInv hblock hk h34 hsp L hrd0⟩
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
  | otherValue h91 _ _ _ hbit =>
      -- the kind-`0` edge: the tag is clear and the byte is below the three pivots
      have hx91 : (hlastByte G C).toInt < 91 := by simpa using toInt_lt_of_slt_one h91
      exact hcontArm_badToken_of_row hc hInv hblock hk h8 hbit
        (eq_zero_of_toInt_ne (x := hlastByte G C) (c := BitVec.ofNat 8 102) (by
          simp only [toInt_8_102]
          omega))
        (eq_zero_of_toInt_ne (x := hlastByte G C) (c := BitVec.ofNat 8 110) (by
          simp only [toInt_8_110]
          omega))
        (eq_zero_of_toInt_ne (x := hlastByte G C) (c := BitVec.ofNat 8 116) (by
          simp only [toInt_8_116]
          omega))
  | defaultValueLow h91 h44 hne34 =>
      -- `%8 < 44`: the tag is clear by the bound
      have hx44 : (hlastByte G C).toInt < 44 := by simpa using toInt_lt_of_slt_one h44
      exact hcontArm_badToken_of_row hc hInv hblock hk h8
        (tag_zero_of_toInt_lt_44 hx44)
        (eq_zero_of_toInt_ne (x := hlastByte G C) (c := BitVec.ofNat 8 102) (by
          simp only [toInt_8_102]
          omega))
        (eq_zero_of_toInt_ne (x := hlastByte G C) (c := BitVec.ofNat 8 110) (by
          simp only [toInt_8_110]
          omega))
        (eq_zero_of_toInt_ne (x := hlastByte G C) (c := BitVec.ofNat 8 116) (by
          simp only [toInt_8_116]
          omega))
  | defaultValueMid h91 h44 h58 hne58 =>
      -- `58 < %8 < 91`
      have hx91 : (hlastByte G C).toInt < 91 := by simpa using toInt_lt_of_slt_one h91
      have hge58 : 58 ≤ (hlastByte G C).toInt := by simpa using toInt_ge_of_slt_zero h58
      exact hcontArm_badToken_of_row hc hInv hblock hk h8
        (tag_zero_of_toInt_ge_58 hge58)
        (eq_zero_of_toInt_ne (x := hlastByte G C) (c := BitVec.ofNat 8 102) (by
          simp only [toInt_8_102]
          omega))
        (eq_zero_of_toInt_ne (x := hlastByte G C) (c := BitVec.ofNat 8 110) (by
          simp only [toInt_8_110]
          omega))
        (eq_zero_of_toInt_ne (x := hlastByte G C) (c := BitVec.ofNat 8 116) (by
          simp only [toInt_8_116]
          omega))
  | defaultValueBracket h91 h123 h93 hne91 =>
      -- the byte is `92`
      have hge91 : 91 ≤ (hlastByte G C).toInt := by simpa using toInt_ge_of_slt_zero h91
      have hx93 : (hlastByte G C).toInt < 93 := by simpa using toInt_lt_of_slt_one h93
      exact hcontArm_badToken_of_row hc hInv hblock hk h8
        (tag_zero_of_toInt_ge_58 (by omega))
        (eq_zero_of_toInt_ne (x := hlastByte G C) (c := BitVec.ofNat 8 102) (by
          simp only [toInt_8_102]
          omega))
        (eq_zero_of_toInt_ne (x := hlastByte G C) (c := BitVec.ofNat 8 110) (by
          simp only [toInt_8_110]
          omega))
        (eq_zero_of_toInt_ne (x := hlastByte G C) (c := BitVec.ofNat 8 116) (by
          simp only [toInt_8_116]
          omega))
  | defaultValueBracketHigh h91 h123 h93 hne93 =>
      cases r.hclass with
      | wsByte hws =>
          -- Vacuous when the byte is on the kind-0 edge (`94 … 122` minus the three
          -- literals): that sub-branch is the refusal arm (`HcontArm.badToken`); the
          -- f/n/t sub-branches are the emit run, whose rows are `scanF`/`scan56True`/
          -- `scan58True`.
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
      -- the byte is `124`
      have hge123 : 123 ≤ (hlastByte G C).toInt := by simpa using toInt_ge_of_slt_zero h123
      have hx125 : (hlastByte G C).toInt < 125 := by simpa using toInt_lt_of_slt_one h125
      exact hcontArm_badToken_of_row hc hInv hblock hk h8
        (tag_zero_of_toInt_ge_58 (by omega))
        (eq_zero_of_toInt_ne (x := hlastByte G C) (c := BitVec.ofNat 8 102) (by
          simp only [toInt_8_102]
          omega))
        (eq_zero_of_toInt_ne (x := hlastByte G C) (c := BitVec.ofNat 8 110) (by
          simp only [toInt_8_110]
          omega))
        (eq_zero_of_toInt_ne (x := hlastByte G C) (c := BitVec.ofNat 8 116) (by
          simp only [toInt_8_116]
          omega))
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

#print axioms LeanLLVM.Refinement.WalkScope.stage2ValuePos_zero_at
#print axioms LeanLLVM.Refinement.WalkScope.hcontStringOpenZeroRefuseRoute
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_stringOpenZeroRefuse_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkContinueArm_of_payload
#print axioms LeanLLVM.Refinement.WalkScope.walkContinueFacts_of_payload

end WalkScope
end LeanLLVM.Refinement
