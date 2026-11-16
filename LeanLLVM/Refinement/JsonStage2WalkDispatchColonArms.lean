/-
The colon above depth zero: the marker's three sub-routes.

The colon's head is the switch's `NodeBlock21 → NodeBlock5 → NodeBlock → LeafBlock3 →
if.then173.i`; at a positive depth the block's test sends the run to `if.end179.i`,
which reads the type stack's byte at `%sp - 1`:

* `1` (a brace is open) — `lor.lhs.false.i`, which reads the *state* stack's byte at
  the same index: `1` sets it to `2` at `if.end195.i` and merges, anything else refuses
  at `if.then192.i`;
* anything else — `if.then192.i` refuses on the type stack's own byte
  (`stackMarkerRefuse_at`).

The merge keeps the depth (`cleanup478.i`'s `%sp.i.1` incoming is `%sp.i.0248`) and
advances the index by one; every refusal stores the entry's position at `%e + 8`.

`colonHeadSeg` is the shared six-link prefix to `if.end179.i`'s target, `colonLorSeg`
the marker's one link, and the route theorems add their last link.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchCommaArms
import LeanLLVM.Refinement.JsonStage2WalkDispatchDepthStores

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- The state after `if.then173.i` at a positive depth. -/
def colonOut (s : State) : State :=
  { s.bind "%cmp174.i" (.int 1 (0 : BitVec 1)) with
    pc := "if.end179.i", pre := some s.pc }

/-- `if.end179.i`'s target at the colon's depth and type-stack byte. -/
abbrev colonMarker {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (b1 : UInt8) : State :=
  smS₆ (colonOut (colS₄ (colS₃ (colS₂ (colS₁ s))))) C.sp C.stage.ctype b1

/-- The marker's branch bit: the type stack's byte is the brace's marker. -/
abbrev colonBit (b : UInt8) : BitVec 1 :=
  evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 1)

/-- **The colon's six-link prefix**: the switch's four pivots, the depth test's
non-refusal edge and `if.end179.i`'s marker read. -/
theorem colonHeadSeg {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)))
    (hsp : C.sp ≠ 0) {b1 : UInt8} (hmark : C.tyMap (C.sp - 1) = b1) :
    Seg calls G C s
      { C with block := (if colonBit b1 = 1 then "lor.lhs.false.i" else "if.then192.i") }
      (colonMarker C s b1) 6 := by
  have hpos : 0 < C.sp := Nat.pos_of_ne_zero hsp
  have hsp32 := depth_lt_32 hInv.depth_cap
  have hoff := pairOff_eq hpos hsp32
  have hq63 : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat < 2 ^ 63 := by
    rw [hoff]; omega
  have hlt : C.sp - 1 < C.wlen := by
    have h := hInv.sp_le_wlen; omega
  have hreadT : readBytes s.mem
      (C.stage.ctype + (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [b1] := by
    rw [hoff, JsonEntrySteps.readBytes_one, hInv.tyBytes (C.sp - 1) hlt, hmark]
    rfl
  have h8₁ : evalOperand (colS₁ s) (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)) := by
    simpa only [colS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₂ : evalOperand (colS₂ (colS₁ s)) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 58)) := by
    simpa only [colS₂, colS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₃ : evalOperand (colS₃ (colS₂ (colS₁ s))) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 58)) := by
    simpa only [colS₃, colS₂, colS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have hsp₄ : evalOperand (colS₄ (colS₃ (colS₂ (colS₁ s)))) (.reg "%sp.i.0248") =
      some (.int 32 (BitVec.ofNat 32 C.sp)) := by
    simpa only [colS₄, colS₃, colS₂, colS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%SwitchLeaf4") (n := "%sp.i.0248") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot") (n := "%sp.i.0248") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%sp.i.0248") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%sp.i.0248") _ _ (by decide)]
      using hInv.depth_reg
  have hbit : evalICmp .eq (BitVec.ofNat 32 C.sp) (BitVec.ofNat 32 0) = 0 :=
    depthEqZero_bit hpos hsp32
  have hct : lookupName (colS₄ (colS₃ (colS₂ (colS₁ s)))).env "%ctype.i" =
      some (.ptr C.stage.ctype) := hInv.ptrs.2.2.2.1
  have hsp₄' : lookupName (colS₄ (colS₃ (colS₂ (colS₁ s)))).env "%sp.i.0248" =
      some (.int 32 (BitVec.ofNat 32 C.sp)) := hsp₄
  have L₁ := colStep₁ (calls := calls) G C s hInv hhead h8
  have L₂ := colStep₂ (calls := calls) G { C with block := "NodeBlock5" } (colS₁ s)
    L₁.inv' rfl h8₁
  have L₃ := colStep₃ (calls := calls) G { C with block := "NodeBlock" } (colS₂ (colS₁ s))
    L₂.inv' rfl h8₂
  have L₄ := colStep₄ (calls := calls) G { C with block := "LeafBlock3" }
    (colS₃ (colS₂ (colS₁ s))) L₃.inv' rfl h8₃
  obtain ⟨s₅, hl₅, hs₅⟩ := WalkLink.if_then173_i_at (calls := calls) G
    { C with block := "if.then173.i" } (colS₄ (colS₃ (colS₂ (colS₁ s)))) L₄.inv' rfl
    (x1 := BitVec.ofNat 32 C.sp) hsp₄'
  have L₅ : WalkLink calls G { C with block := "if.then173.i" }
      (colS₄ (colS₃ (colS₂ (colS₁ s)))) { C with block := "if.end179.i" }
      (colonOut (colS₄ (colS₃ (colS₂ (colS₁ s))))) := by
    rw [hs₅] at hl₅
    have hne : ¬ (evalICmp .eq (BitVec.ofNat 32 C.sp) (BitVec.ofNat 32 0) = 1) := by
      rw [hbit]; decide
    rw [if_neg hne] at hl₅
    simp only [hbit] at hl₅
    simpa only [colonOut] using hl₅
  obtain ⟨s₆, hl₆, hs₆⟩ := walkIfEnd179_at (calls := calls) G
    { C with block := "if.end179.i" } (colonOut (colS₄ (colS₃ (colS₂ (colS₁ s)))))
    L₅.inv' rfl hsp₄' hct hq63
    (by simpa only [colonOut, State.bind, colS₄, colS₃, colS₂, colS₁] using hreadT)
  rw [show colonMarker C s b1 = s₆ from hs₆.symm]
  exact Seg.tail L₁ (Seg.tail L₂ (Seg.tail L₃ (Seg.tail L₄ (Seg.tail L₅
    (Seg.tail hl₆ (Seg.nil hl₆.inv'))))))

/-! ### The marker's own link -/

/-- The target's `%idxprom182.i`: the depth less one. -/
theorem colonMarker_idx {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (b1 : UInt8) :
    lookupName (colonMarker C s b1).env "%idxprom182.i" =
      some (.int 64 (BitVec.ofNat 64
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat)) := by
  simp only [colonMarker, smS₆, stateAt, walkMarkerEnv, cells,
    lookupName_cons_ne (k := "%cmp185.not.i") (n := "%idxprom182.i") _ _ (by decide),
    lookupName_cons_ne (k := "%23") (n := "%idxprom182.i") _ _ (by decide),
    lookupName_cons_ne (k := "%arrayidx183.i") (n := "%idxprom182.i") _ _ (by decide),
    lookupName_cons_ne (k := "%sub181.i") (n := "%idxprom182.i") _ _ (by decide),
    lookupName_cons_self]

/-- The target's `%cst.i` survives the prefix. -/
theorem colonMarker_cst {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (b1 : UInt8) :
    lookupName (colonMarker C s b1).env "%cst.i" = lookupName s.env "%cst.i" := by
  simp only [colonMarker, smS₆, colonOut, stateAt, walkMarkerEnv, cells, State.bind,
    colS₄, colS₃, colS₂, colS₁,
    lookupName_cons_ne (k := "%cmp185.not.i") (n := "%cst.i") _ _ (by decide),
    lookupName_cons_ne (k := "%23") (n := "%cst.i") _ _ (by decide),
    lookupName_cons_ne (k := "%arrayidx183.i") (n := "%cst.i") _ _ (by decide),
    lookupName_cons_ne (k := "%idxprom182.i") (n := "%cst.i") _ _ (by decide),
    lookupName_cons_ne (k := "%sub181.i") (n := "%cst.i") _ _ (by decide),
    lookupName_cons_ne (k := "%cmp174.i") (n := "%cst.i") _ _ (by decide),
    lookupName_cons_ne (k := "%SwitchLeaf4") (n := "%cst.i") _ _ (by decide),
    lookupName_cons_ne (k := "%Pivot") (n := "%cst.i") _ _ (by decide),
    lookupName_cons_ne (k := "%Pivot6") (n := "%cst.i") _ _ (by decide),
    lookupName_cons_ne (k := "%Pivot22") (n := "%cst.i") _ _ (by decide)]

/-- **The marker's one link**: from the brace's marker to `lor.lhs.false.i`'s target.
The invariant is the prefix's *own* target, as the state-stack refusals compose. -/
theorem colonLorSeg {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) {b1 b2 : UInt8} (hsp : C.sp ≠ 0)
    (hInv : WalkInv G { C with block := "lor.lhs.false.i" } (colonMarker C s b1))
    (hstate : C.stMap (C.sp - 1) = b2) :
    Seg calls G { C with block := "lor.lhs.false.i" } (colonMarker C s b1)
      { C with block := (if evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 1) = 1
          then "if.end195.i" else "if.then192.i") }
      (lorNext (colonMarker C s b1) C.stage.cst
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2) 1 := by
  have hpos : 0 < C.sp := Nat.pos_of_ne_zero hsp
  have hsp32 := depth_lt_32 hInv.depth_cap
  have hoff := pairOff_eq hpos hsp32
  have hlt : C.sp - 1 < C.wlen := by
    have h : C.sp ≤ C.wlen := hInv.sp_le_wlen
    omega
  have hq63 : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat < 2 ^ 63 := by
    rw [hoff]; omega
  have hidx := colonMarker_idx C s b1
  have hread : readBytes (colonMarker C s b1).mem
      (C.stage.cst + (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [b2] := by
    rw [hoff, JsonEntrySteps.readBytes_one, hInv.stBytes (C.sp - 1) hlt, hstate]
    rfl
  obtain ⟨s', hl, hs⟩ := WalkLink.lor_lhs_false_at (calls := calls) G
    { C with block := "lor.lhs.false.i" } (colonMarker C s b1) hInv rfl
    (by rw [colonMarker_cst]; exact hInv.ptrs.2.2.2.2.1) hidx hq63 hread
  rw [show lorNext (colonMarker C s b1) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2 = s' from hs.symm]
  exact Seg.tail hl (Seg.nil hl.inv')

/-! ### The three sub-routes -/

/-- The marker's `%arrayidx188.i`: the state stack's byte address. -/
theorem lorOut_ap (s : State) (cs q : Nat) (b : UInt8) :
    lookupName (lorOut s cs q b).env "%arrayidx188.i" = some (.ptr (cs + q)) := by
  simp only [lorOut, stateAt, cells,
    lookupName_cons_ne (k := "%cmp190.not.i") (n := "%arrayidx188.i") _ _ (by decide),
    lookupName_cons_ne (k := "%24") (n := "%arrayidx188.i") _ _ (by decide),
    lookupName_cons_self]

/-- The marker's `%arrayidx188.i` at its target. -/
theorem lorNext_ap (s : State) (cs q : Nat) (b : UInt8) :
    lookupName (lorNext s cs q b).env "%arrayidx188.i" = some (.ptr (cs + q)) :=
  lorOut_ap s cs q b

/-- The colon's seven links at the brace's marker, with the type stack's bit folded
in: the prefix and the marker's state-stack read. -/
theorem colonBraceSeg {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)))
    (hsp : C.sp ≠ 0) {b1 b2 : UInt8} (hmark : C.tyMap (C.sp - 1) = b1)
    (hstate : C.stMap (C.sp - 1) = b2) (hbit1 : colonBit b1 = 1) :
    WalkSegment calls G C s
      { C with block := (if evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 1) = 1
          then "if.end195.i" else "if.then192.i") }
      (lorNext (colonMarker C s b1) C.stage.cst
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2) 7 := by
  have hseg6 := colonHeadSeg (calls := calls) G C s hInv hhead h8 hsp hmark
  have hseg6' : Seg calls G C s { C with block := "lor.lhs.false.i" }
      (colonMarker C s b1) 6 := by
    rw [hbit1] at hseg6
    rw [if_pos (show (1 : BitVec 1) = 1 from rfl)] at hseg6
    exact hseg6
  have hlor := colonLorSeg (calls := calls) G C s hsp hseg6'.measure.inv' hstate
  exact hseg6'.measure.trans hlor.measure

/-- **The colon's brace merge**: the type stack's byte is `1` and the state stack's
`1`, so `if.end195.i` sets the state byte to `2` and the run merges. -/
theorem colonBraceMerge_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)))
    (hsp : C.sp ≠ 0) {b1 b2 : UInt8} (hmark : C.tyMap (C.sp - 1) = b1)
    (hstate : C.stMap (C.sp - 1) = b2) (hbit1 : colonBit b1 = 1)
    (hb2 : evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 1) = 1) :
    WalkDispatchResult calls G C s := by
  have hseg7 := colonBraceSeg (calls := calls) G C s hInv hhead h8 hsp hmark hstate hbit1
  have hseg7' : WalkSegment calls G C s { C with block := "if.end195.i" }
      (lorNext (colonMarker C s b1) C.stage.cst
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2) 7 := by
    rw [hb2] at hseg7
    rw [if_pos (show (1 : BitVec 1) = 1 from rfl)] at hseg7
    exact hseg7
  have hp : lookupName (lorNext (colonMarker C s b1) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2).env
      "%arrayidx188.i" =
      some (.ptr (C.stage.cst +
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat)) :=
    lorNext_ap _ _ _ _
  have hq : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat <
      stage2StackExtent := by
    rw [pairOff_eq (Nat.pos_of_ne_zero hsp) (depth_lt_32 hInv.depth_cap)]
    exact commaOff_lt hInv.depth_cap
  obtain ⟨s₈, hl₈, hs₈⟩ := WalkLink.if_end195_at (calls := calls) G
    { C with block := "if.end195.i" } (lorNext (colonMarker C s b1) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2) hseg7'.inv' rfl hp hq
  have hseg8 := hseg7'.trans (Seg.tail hl₈ (Seg.nil hl₈.inv')).measure
  have hklt : C.k < G.nep := WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hhead)
  refine WalkDispatchResult.merge _ _ 8 C.sp (C.k + 1) "if.end195.i"
    (.reg "%sp.i.0248") (.reg "%inc.i") (BitVec.ofNat 64 G.nep) hseg8 rfl rfl ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hs₈, stackStoreOut_pre]
    simp only [lorNext, ite_eq_left hb2]
  · show phiIncoming "if.end195.i" cleanupSpIncoming = some (.reg "%sp.i.0248")
    decide
  · simpa only [evalOperand] using hseg8.inv'.depth_reg
  · show phiIncoming "if.end195.i" cleanupKIncoming = some (.reg "%inc.i")
    decide
  · simpa only [evalOperand] using hseg8.inv'.inc_reg
  · exact hseg8.inv'.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs])
  · omega
  · exact commaCap G hklt
  · exact hseg8.inv'.depth_cap
  · exact hseg8.inv'.sp_le_wlen
  · exact commaPrice G

/-- **The colon's brace refusal**: the type stack's byte is `1` and the state stack's
is not `1`, so `if.then192.i` refuses at the entry's position. -/
theorem colonBraceRefuse_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)))
    (hsp : C.sp ≠ 0) {b1 b2 : UInt8} (hmark : C.tyMap (C.sp - 1) = b1)
    (hstate : C.stMap (C.sp - 1) = b2) (hbit1 : colonBit b1 = 1)
    (hb2 : evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 1) = 0) :
    WalkDispatchResult calls G C s := by
  have hklt : C.k < G.nep := WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hhead)
  have hseg7 := colonBraceSeg (calls := calls) G C s hInv hhead h8 hsp hmark hstate hbit1
  have hseg7' : WalkSegment calls G C s { C with block := "if.then192.i" }
      (lorNext (colonMarker C s b1) C.stage.cst
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2) 7 := by
    rw [hb2] at hseg7
    rw [ite_eq_right (show ¬ ((0 : BitVec 1) = 1) from by decide)] at hseg7
    exact hseg7
  have hidx := lorOut_idx (colonMarker C s b1) C.stage.cst
    (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2
  have hv : evalOperand (lorNext (colonMarker C s b1) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2) (.reg "%idxprom.i") =
      some (.int 64 (BitVec.ofNat 64 (entryPos G C.k))) := by
    have h := hseg7'.inv'.idx_reg
    simpa only [evalOperand] using h
  have he : lookupName (lorNext (colonMarker C s b1) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2).env "%e" =
      some (.ptr C.stage.e) := by
    have h := hseg7'.inv'.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs])
    exact h
  obtain ⟨s₈, hl₈, hs₈⟩ := WalkLink.if_then192_i_at (calls := calls) G
    { C with block := "if.then192.i" } (lorNext (colonMarker C s b1) C.stage.cst
      (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2) hseg7'.inv' rfl
    hv he (le_of_lt (entryPos_lt G hklt))
    (by have := entryPos_lt G hklt; have := WalkGeom.n_lt G; omega)
  have hseg8 := hseg7'.trans (Seg.tail hl₈ (Seg.nil hl₈.inv')).measure
  have hread : readBytes s₈.mem (C.stage.e + 8) 8 =
      some (wordBytes 8 (entryPos G C.k)) := by
    rw [hs₈]
    simpa only [State.bind] using
      refuseSegment_word_of_store (m := (lorNext (colonMarker C s b1) C.stage.cst
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat b2).mem)
        (e := C.stage.e) (v := entryPos G C.k)
  exact commaRefuseAt G C s hInv hhead hseg8 rfl hread
    (le_of_lt (entryPos_lt G hklt)) hl₈.inv'.eoff_le

/-- **The colon's marker refusal**: the type stack's byte is not `1`, so the run
refuses at `if.then192.i` on the type stack's own byte (`stackMarkerRefuse_at`). -/
theorem colonMarkerRefuse_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 58)))
    (hsp : C.sp ≠ 0) {b1 : UInt8} (hmark : C.tyMap (C.sp - 1) = b1)
    (hbit1 : colonBit b1 = 0) :
    WalkDispatchResult calls G C s := by
  have hklt : C.k < G.nep := WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hhead)
  have hq1 : (C.tyMap (C.sp - 1)).toNat ≠ 1 := by
    have hval : b1.toNat ≠ 1 := by
      intro h
      have : colonBit b1 = 1 := by
        simp only [colonBit, BitVec.ofNat, h]
        rfl
      rw [hbit1] at this
      exact absurd this (by decide)
    rwa [hmark]
  have hv : evalOperand s (.reg "%idxprom.i") =
      some (.int 64 (BitVec.ofNat 64 (entryPos G C.k))) := by
    simpa only [evalOperand] using hInv.idx_reg
  have he : lookupName s.env "%e" = some (.ptr C.stage.e) :=
    hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs])
  obtain ⟨Cd, sd, p, hseg, herr, hprice⟩ :=
    stackMarkerRefuse_at G C s hInv hhead h8 hsp hq1 hv he
      (le_of_lt (entryPos_lt G hklt))
      (by have := entryPos_lt G hklt; have := WalkGeom.n_lt G; omega) hklt
  exact WalkDispatchResult.refuse Cd sd p hseg.seg hseg.block hseg.word herr hprice

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.colonHeadSeg
#print axioms LeanLLVM.Refinement.WalkScope.colonBraceMerge_at
#print axioms LeanLLVM.Refinement.WalkScope.colonBraceRefuse_at
#print axioms LeanLLVM.Refinement.WalkScope.colonMarkerRefuse_at

end WalkScope
end LeanLLVM.Refinement
