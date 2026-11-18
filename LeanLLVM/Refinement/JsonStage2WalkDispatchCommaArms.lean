/-
The comma above depth zero: the container pair's four sub-routes.

The comma's head is the switch's `NodeBlock21 → NodeBlock5 → NodeBlock → LeafBlock1 →
if.then127.i`; at a positive depth the block's test sends the run to `if.end133.i`,
which reads both container stacks at `%sp - 1` and branches on the type stack's byte:

| type | state | block | outcome |
|---|---|---|---|
| `1` (brace) | `3` | `if.end150.i` | stores `4`, merges |
| `1` | other | `if.then147.i` | refuses |
| other (bracket) | `1` | `if.end162.i` | stores `2`, merges |
| other | other | `if.then159.i` | refuses |

The two merges keep the depth (`cleanup478.i`'s `%sp.i.1` incoming is
`%sp.i.0248`) and advance the index by one; the two refusals store the entry's
position at `%e + 8`.

`commaPairSeg` is the shared six-link prefix to the pair's target; the four route
theorems each add their two links and build the merge or the refusal.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchOpeners
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessState
import LeanLLVM.Refinement.JsonStage2WalkDispatchDepthStores
import LeanLLVM.Refinement.JsonStage2WalkDispatchPair
import LeanLLVM.Refinement.JsonStage2WalkSteps

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The depth test's non-refusal edge

`if.then127.i` compares the depth with zero; at a positive depth the bit is `0` and
the edge is `if.end133.i`. -/

/-- The state after `if.then127.i` at a positive depth. -/
def commaOut (s : State) : State :=
  { s.bind "%cmp128.i" (.int 1 (0 : BitVec 1)) with
    pc := "if.end133.i", pre := some s.pc }

/-- A positive depth's zero test is `0`. -/
theorem depthEqZero_bit {sp : Nat} (hpos : 0 < sp) (hsp32 : sp < 2 ^ 32) :
    evalICmp .eq (BitVec.ofNat 32 sp) (BitVec.ofNat 32 0) = 0 := by
  refine refuseICmp_eq_zero (fun h => ?_)
  have hz : (BitVec.ofNat 32 sp).toNat = 0 := by rw [h]; rfl
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsp32] at hz
  omega

/-- A depth inside the stacks is a 32-bit word's worth. -/
theorem depth_lt_32 {sp : Nat} (h : sp ≤ stage2StackExtent) : sp < 2 ^ 32 := by
  have h520 : stage2StackExtent = 520 := rfl
  omega

/-! ### The shared prefix: the head, the depth test and the pair -/

/-- The prefix's target: the pair's successor at the switch's six links. -/
abbrev commaTarget {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (b1 b2 : UInt8) : State :=
  pairNext (commaOut (comS₄ (comS₃ (comS₂ (comS₁ s))))) C.sp C.stage.ctype C.stage.cst b1 b2

/-- **The comma's six-link prefix**: the switch's four pivots, the depth test's
non-refusal edge and `if.end133.i`'s pair. -/
theorem commaPairSeg {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)))
    (hsp : C.sp ≠ 0) {b1 b2 : UInt8}
    (hmark : C.tyMap (C.sp - 1) = b1) (hstate : C.stMap (C.sp - 1) = b2) :
    Seg calls G C s
      { C with block := (if pairBit (BitVec.ofNat 8 b1.toNat) = 1 then "if.then141.i"
          else "if.else153.i") }
      (pairNext (commaOut (comS₄ (comS₃ (comS₂ (comS₁ s))))) C.sp C.stage.ctype
        C.stage.cst b1 b2) 6 := by
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
  have hreadS : readBytes s.mem
      (C.stage.cst + (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat) 1 =
      some [b2] := by
    rw [hoff, JsonEntrySteps.readBytes_one, hInv.stBytes (C.sp - 1) hlt, hstate]
    rfl
  have h8₁ : evalOperand (comS₁ s) (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)) := by
    simpa only [comS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₂ : evalOperand (comS₂ (comS₁ s)) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 44)) := by
    simpa only [comS₂, comS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have h8₃ : evalOperand (comS₃ (comS₂ (comS₁ s))) (.reg "%8") =
      some (.int 8 (BitVec.ofNat 8 44)) := by
    simpa only [comS₃, comS₂, comS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  have hsp₄ : evalOperand (comS₄ (comS₃ (comS₂ (comS₁ s)))) (.reg "%sp.i.0248") =
      some (.int 32 (BitVec.ofNat 32 C.sp)) := by
    have hd := LeanLLVM.evalOperand_reg_of hInv.depth_reg
    simpa only [comS₄, comS₃, comS₂, comS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%SwitchLeaf2") (n := "%sp.i.0248") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot") (n := "%sp.i.0248") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot6") (n := "%sp.i.0248") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%sp.i.0248") _ _ (by decide)]
      using hd
  have hbit : evalICmp .eq (BitVec.ofNat 32 C.sp) (BitVec.ofNat 32 0) = 0 :=
    depthEqZero_bit hpos hsp32
  have hct : lookupName (comS₄ (comS₃ (comS₂ (comS₁ s)))).env "%ctype.i" =
      some (.ptr C.stage.ctype) :=
    hInv.ptrs.2.2.2.1
  have hcs : lookupName (comS₄ (comS₃ (comS₂ (comS₁ s)))).env "%cst.i" =
      some (.ptr C.stage.cst) :=
    hInv.ptrs.2.2.2.2.1
  have hsp₄' : lookupName (comS₄ (comS₃ (comS₂ (comS₁ s)))).env "%sp.i.0248" =
      some (.int 32 (BitVec.ofNat 32 C.sp)) := lookupName_of_evalOperand_reg hsp₄
  have L₁ := comStep₁ (calls := calls) G C s hInv hhead h8
  have L₂ := comStep₂ (calls := calls) G { C with block := "NodeBlock5" } (comS₁ s)
    L₁.inv' rfl h8₁
  have L₃ := comStep₃ (calls := calls) G { C with block := "NodeBlock" } (comS₂ (comS₁ s))
    L₂.inv' rfl h8₂
  have L₄ := comStep₄ (calls := calls) G { C with block := "LeafBlock1" }
    (comS₃ (comS₂ (comS₁ s))) L₃.inv' rfl h8₃
  obtain ⟨s₅, hl₅, hs₅⟩ := WalkLink.if_then127_i_at (calls := calls) G
    { C with block := "if.then127.i" } (comS₄ (comS₃ (comS₂ (comS₁ s)))) L₄.inv' rfl
    (x1 := BitVec.ofNat 32 C.sp) hsp₄
  have L₅ : WalkLink calls G { C with block := "if.then127.i" }
      (comS₄ (comS₃ (comS₂ (comS₁ s)))) { C with block := "if.end133.i" }
      (commaOut (comS₄ (comS₃ (comS₂ (comS₁ s))))) := by
    rw [hs₅] at hl₅
    have hne : ¬ (evalICmp .eq (BitVec.ofNat 32 C.sp) (BitVec.ofNat 32 0) = 1) := by
      rw [hbit]; decide
    rw [if_neg hne] at hl₅
    simp only [hbit] at hl₅
    simpa only [commaOut] using hl₅
  obtain ⟨s₆, hl₆, hs₆⟩ := WalkLink.if_end133_at (calls := calls) G
    { C with block := "if.end133.i" } (commaOut (comS₄ (comS₃ (comS₂ (comS₁ s)))))
    L₅.inv' rfl hsp₄' hct hcs hq63
    (by simpa only [commaOut, State.bind, comS₄, comS₃, comS₂, comS₁] using hreadT)
    (by simpa only [commaOut, State.bind, comS₄, comS₃, comS₂, comS₁] using hreadS)
  have htarget : s₆ = pairNext (commaOut (comS₄ (comS₃ (comS₂ (comS₁ s)))))
      C.sp C.stage.ctype C.stage.cst b1 b2 := hs₆
  rw [← htarget]
  exact Seg.tail L₁ (Seg.tail L₂ (Seg.tail L₃ (Seg.tail L₄ (Seg.tail L₅
    (Seg.tail hl₆ (Seg.nil hl₆.inv'))))))

/-! ### The prefix at each marker

The pair's branch bit is decided by the type stack's byte: `1` takes `if.then141.i`,
anything else `if.else153.i`.  The two facts the routes read are the prefix at each
marker, with the branch bit folded out. -/

/-- The comma's six links at the brace's marker. -/
theorem commaBraceSeg {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)))
    (hsp : C.sp ≠ 0) {b2 : UInt8} (hmark : C.tyMap (C.sp - 1) = 1)
    (hstate : C.stMap (C.sp - 1) = b2) :
    Seg calls G C s { C with block := "if.then141.i" } (commaTarget C s 1 b2) 6 := by
  have h := commaPairSeg (calls := calls) G C s hInv hhead h8 hsp hmark hstate
  have h1 : pairBit (BitVec.ofNat 8 (UInt8.toNat 1)) = 1 := by decide
  simp only [h1, if_true, commaTarget] at h ⊢
  exact h

/-- The comma's six links at a non-brace marker. -/
theorem commaBracketSeg {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)))
    (hsp : C.sp ≠ 0) {b1 b2 : UInt8} (hmark : C.tyMap (C.sp - 1) = b1)
    (hstate : C.stMap (C.sp - 1) = b2)
    (hbit : pairBit (BitVec.ofNat 8 b1.toNat) = 0) :
    Seg calls G C s { C with block := "if.else153.i" } (commaTarget C s b1 b2) 6 := by
  have h := commaPairSeg (calls := calls) G C s hInv hhead h8 hsp hmark hstate
  rw [hbit] at h
  have hne : ¬ ((0 : BitVec 1) = 1) := by decide
  rw [if_neg hne] at h
  simpa only [commaTarget] using h

/-- The prefix's `%22` at a marker. -/
theorem commaTarget_22 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (b1 b2 : UInt8) :
    lookupName (commaTarget C s b1 b2).env "%22" =
      some (.int 8 (BitVec.ofNat 8 b2.toNat)) := pairOut_22 s C.sp C.stage.ctype C.stage.cst b1 b2

/-- The prefix's `%arrayidx143.i` at a marker. -/
theorem commaTarget_ap2 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (b1 b2 : UInt8) :
    lookupName (commaTarget C s b1 b2).env "%arrayidx143.i" =
      some (.ptr (C.stage.cst +
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat)) :=
  pairOut_ap2 s C.sp C.stage.ctype C.stage.cst b1 b2

/-! ### The two merges

The store blocks set the state stack's byte and jump to the merge; the merge's depth
incoming is `%sp.i.0248` and its index incoming `%inc.i`, so the depth is unchanged
and the index advances by one. -/

/-- The offset is inside the stacks. -/
theorem commaOff_lt {sp : Nat} (h : sp ≤ stage2StackExtent) : sp - 1 < stage2StackExtent := by
  have h520 : stage2StackExtent = 520 := rfl
  omega

/-- The merge's index bound at one step. -/
theorem commaCap {m0 : Mem} (G : WalkGeom m0) {k : Nat} (hk : k < G.nep) :
    k + 1 ≤ (BitVec.ofNat 64 G.nep).toNat := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (openNep_lt G)]
  omega

/-- The merge's price at one step. -/
theorem commaPrice {m0 : Mem} (G : WalkGeom m0) {k : Nat} :
    8 + 2 ≤ stage2EntryAllowance * (k + 1 - k) +
      stage2ByteAllowance * (entryPos G (k + 1) - entryPos G k) := by
  have h1 : k + 1 - k = 1 := by omega
  simp only [stage2EntryAllowance, stage2ByteAllowance, h1]
  omega

/-- **The comma's brace merge**: the type stack's byte is `1` and the state stack's
`3`, so `if.end150.i` sets the state byte to `4` and the run merges. -/
theorem commaBraceMerge_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)))
    (hsp : C.sp ≠ 0) {b2 : UInt8} (hmark : C.tyMap (C.sp - 1) = 1)
    (hstate : C.stMap (C.sp - 1) = b2)
    (hb2 : evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 1) :
    WalkDispatchResult calls G C s := by
  have hseg := commaBraceSeg (calls := calls) G C s hInv hhead h8 hsp hmark hstate
  have h22 : evalOperand (commaTarget C s 1 b2) (.reg "%22") =
      some (.int 8 (BitVec.ofNat 8 b2.toNat)) := by
    walk_read using commaTarget_22 C s 1 b2
  obtain ⟨s₆, hl₆, hs₆⟩ := WalkLink.if_then141_i_at (calls := calls) G
    { C with block := "if.then141.i" } (commaTarget C s 1 b2) hseg.measure.inv' rfl
    (x1 := BitVec.ofNat 8 b2.toNat) h22
  have hl₆' : WalkLink calls G { C with block := "if.then141.i" } (commaTarget C s 1 b2)
      { C with block := "if.end150.i" } s₆ := by
    rw [if_pos hb2] at hl₆
    exact hl₆
  have hoff : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat = C.sp - 1 :=
    pairOff_eq (Nat.pos_of_ne_zero hsp) (depth_lt_32 hInv.depth_cap)
  have hp : lookupName s₆.env "%arrayidx143.i" =
      some (.ptr (C.stage.cst + (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat)) := by
    rw [hs₆]
    simpa only [State.bind,
      lookupName_cons_ne (k := "%cmp145.not.i") (n := "%arrayidx143.i") _ _ (by decide)]
      using commaTarget_ap2 C s 1 b2
  have hq : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat < stage2StackExtent := by
    rw [hoff]; exact commaOff_lt hInv.depth_cap
  obtain ⟨s₇, hl₇, hs₇⟩ := WalkLink.if_end150_at (calls := calls) G
    { C with block := "if.end150.i" } s₆ hl₆'.inv' rfl hp hq
  have h₂ : Seg calls G { C with block := "if.then141.i" } (commaTarget C s 1 b2)
      { C with
        block := "cleanup478.i",
        stMap := fun i => if i = (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat
          then (natToBytes (BitVec.ofNat 8 4).toNat 1).getD 0 0 else C.stMap i }
      (stackStoreOut { C with block := "if.end150.i" } (BitVec.ofNat 8 4)
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat s₆) 2 := by
    rw [← hs₇]
    exact Seg.tail hl₆' (Seg.tail hl₇ (Seg.nil hl₇.inv'))
  have hseg8 := hseg.measure.trans h₂.measure
  have hklt : C.k < G.nep := WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hhead)
  refine WalkDispatchResult.merge _ _ 8 C.sp (C.k + 1) "if.end150.i"
    (.reg "%sp.i.0248") (.reg "%inc.i") (BitVec.ofNat 64 G.nep) hseg8 rfl rfl ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stackStoreOut_pre, hs₆]
    simp only [if_pos hb2]
  · show phiIncoming "if.end150.i" cleanupSpIncoming = some (.reg "%sp.i.0248")
    decide
  · walk_read using hseg8.inv'.depth_reg
  · show phiIncoming "if.end150.i" cleanupKIncoming = some (.reg "%inc.i")
    decide
  · walk_read using hseg8.inv'.inc_reg
  · exact hseg8.inv'.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs])
  · omega
  · exact commaCap G hklt
  · exact hseg8.inv'.depth_cap
  · exact hseg8.inv'.sp_le_wlen
  · exact commaPrice G

/-! ### The two refusals

The refusal stores write the entry's position at `%e + 8` and reach `if.then`; the
refusal's word is that store's read-back, and the price is `refusePrice_of_le`'s. -/

/-- A refusal's five fields from the eight-link run. -/
theorem commaRefuseAt {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    {Cd : WalkCarry G} {sd : State} {j : Nat}
    (hseg : WalkSegment calls G C s Cd sd 8) (hblk : Cd.block = "if.then")
    (hread : readBytes sd.mem (Cd.stage.e + 8) 8 = some (wordBytes 8 j))
    (hj : j ≤ G.n) (hjj : Cd.eoff ≤ G.n) :
    WalkDispatchResult calls G C s := by
  have hklt : C.k < G.nep := WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hhead)
  exact WalkDispatchResult.refuse Cd sd 8 hseg hblk ⟨j, hj, hread⟩ hjj
    (refusePrice_of_le G C (by omega) hklt)

/-- **The comma's brace refusal**: the type stack's byte is `1` and the state stack's
is not `3`, so `if.then147.i` refuses at the entry's position. -/
theorem commaBraceRefuse_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)))
    (hsp : C.sp ≠ 0) {b2 : UInt8} (hmark : C.tyMap (C.sp - 1) = 1)
    (hstate : C.stMap (C.sp - 1) = b2)
    (hb2 : evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 3) = 0) :
    WalkDispatchResult calls G C s := by
  have hklt : C.k < G.nep := WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hhead)
  have hseg := commaBraceSeg (calls := calls) G C s hInv hhead h8 hsp hmark hstate
  have hInvSeg := hseg.measure.inv'
  have h22 : evalOperand (commaTarget C s 1 b2) (.reg "%22") =
      some (.int 8 (BitVec.ofNat 8 b2.toNat)) := by
    walk_read using commaTarget_22 C s 1 b2
  obtain ⟨s₆, hl₆, hs₆⟩ := WalkLink.if_then141_i_at (calls := calls) G
    { C with block := "if.then141.i" } (commaTarget C s 1 b2) hInvSeg rfl
    (x1 := BitVec.ofNat 8 b2.toNat) h22
  have hl₆' : WalkLink calls G { C with block := "if.then141.i" } (commaTarget C s 1 b2)
      { C with block := "if.then147.i" } s₆ := by
    rw [if_neg (by rw [hb2]; decide)] at hl₆
    exact hl₆
  have hv₆ : evalOperand s₆ (.reg "%idxprom.i") =
      some (.int 64 (BitVec.ofNat 64 (entryPos G C.k))) := by
    rw [hs₆]
    have hd := LeanLLVM.evalOperand_reg_of hInvSeg.idx_reg
    simpa only [State.bind, evalOperand,
      lookupName_cons_ne (k := "%cmp145.not.i") (n := "%idxprom.i") _ _ (by decide)]
      using hd
  have he₆ : lookupName s₆.env "%e" = some (.ptr C.stage.e) := by
    rw [hs₆]
    simpa only [State.bind,
      lookupName_cons_ne (k := "%cmp145.not.i") (n := "%e") _ _ (by decide)]
      using hInvSeg.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs])
  obtain ⟨s₇, hl₇, hs₇⟩ := WalkLink.if_then147_i_at (calls := calls) G
    { C with block := "if.then147.i" } s₆ hl₆'.inv' rfl hv₆ he₆
    (le_of_lt (entryPos_lt G hklt))
    (by have := entryPos_lt G hklt; have := WalkGeom.n_lt G; omega)
  have h₂ : Seg calls G { C with block := "if.then141.i" } (commaTarget C s 1 b2)
      { C with block := "if.then", eoff := entryPos G C.k, refusal := true } s₇ 2 :=
    Seg.tail hl₆' (Seg.tail hl₇ (Seg.nil hl₇.inv'))
  have hread : readBytes s₇.mem (C.stage.e + 8) 8 =
      some (wordBytes 8 (entryPos G C.k)) := by
    rw [hs₇]
    simpa only [State.bind] using
      refuseSegment_word_of_store (m := s₆.mem) (e := C.stage.e) (v := entryPos G C.k)
  exact commaRefuseAt G C s hInv hhead (hseg.measure.trans h₂.measure) rfl hread
    (le_of_lt (entryPos_lt G hklt)) hl₇.inv'.eoff_le

/-- **The comma's bracket merge**: the type stack's byte is not `1` and the state
stack's is `1`, so `if.end162.i` sets the state byte to `2` and the run merges. -/
theorem commaBracketMerge_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)))
    (hsp : C.sp ≠ 0) {b1 b2 : UInt8} (hmark : C.tyMap (C.sp - 1) = b1)
    (hstate : C.stMap (C.sp - 1) = b2)
    (hbit : pairBit (BitVec.ofNat 8 b1.toNat) = 0)
    (hb2 : evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 1) = 1) :
    WalkDispatchResult calls G C s := by
  have hseg := commaBracketSeg (calls := calls) G C s hInv hhead h8 hsp hmark hstate hbit
  have h22 : evalOperand (commaTarget C s b1 b2) (.reg "%22") =
      some (.int 8 (BitVec.ofNat 8 b2.toNat)) := by
    walk_read using commaTarget_22 C s b1 b2
  obtain ⟨s₆, hl₆, hs₆⟩ := WalkLink.if_else153_i_at (calls := calls) G
    { C with block := "if.else153.i" } (commaTarget C s b1 b2) hseg.measure.inv' rfl
    (x1 := BitVec.ofNat 8 b2.toNat) h22
  have hl₆' : WalkLink calls G { C with block := "if.else153.i" } (commaTarget C s b1 b2)
      { C with block := "if.end162.i" } s₆ := by
    rw [if_pos hb2] at hl₆
    exact hl₆
  have hoff : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat = C.sp - 1 :=
    pairOff_eq (Nat.pos_of_ne_zero hsp) (depth_lt_32 hInv.depth_cap)
  have hp : lookupName s₆.env "%arrayidx143.i" =
      some (.ptr (C.stage.cst + (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat)) := by
    rw [hs₆]
    simpa only [State.bind,
      lookupName_cons_ne (k := "%cmp157.not.i") (n := "%arrayidx143.i") _ _ (by decide)]
      using commaTarget_ap2 C s b1 b2
  have hq : (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat < stage2StackExtent := by
    rw [hoff]; exact commaOff_lt hInv.depth_cap
  obtain ⟨s₇, hl₇, hs₇⟩ := WalkLink.if_end162_at (calls := calls) G
    { C with block := "if.end162.i" } s₆ hl₆'.inv' rfl hp hq
  have h₂ : Seg calls G { C with block := "if.else153.i" } (commaTarget C s b1 b2)
      { C with
        block := "cleanup478.i",
        stMap := fun i => if i = (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat
          then (natToBytes (BitVec.ofNat 8 2).toNat 1).getD 0 0 else C.stMap i }
      (stackStoreOut { C with block := "if.end162.i" } (BitVec.ofNat 8 2)
        (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295).toNat s₆) 2 := by
    rw [← hs₇]
    exact Seg.tail hl₆' (Seg.tail hl₇ (Seg.nil hl₇.inv'))
  have hseg8 := hseg.measure.trans h₂.measure
  have hklt : C.k < G.nep := WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hhead)
  refine WalkDispatchResult.merge _ _ 8 C.sp (C.k + 1) "if.end162.i"
    (.reg "%sp.i.0248") (.reg "%inc.i") (BitVec.ofNat 64 G.nep) hseg8 rfl rfl ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stackStoreOut_pre, hs₆]
    simp only [if_pos hb2]
  · show phiIncoming "if.end162.i" cleanupSpIncoming = some (.reg "%sp.i.0248")
    decide
  · walk_read using hseg8.inv'.depth_reg
  · show phiIncoming "if.end162.i" cleanupKIncoming = some (.reg "%inc.i")
    decide
  · walk_read using hseg8.inv'.inc_reg
  · exact hseg8.inv'.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs])
  · omega
  · exact commaCap G hklt
  · exact hseg8.inv'.depth_cap
  · exact hseg8.inv'.sp_le_wlen
  · exact commaPrice G

/-- **The comma's bracket refusal**: the type stack's byte is not `1` and the state
stack's is not `1`, so `if.then159.i` refuses at the entry's position. -/
theorem commaBracketRefuse_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 44)))
    (hsp : C.sp ≠ 0) {b1 b2 : UInt8} (hmark : C.tyMap (C.sp - 1) = b1)
    (hstate : C.stMap (C.sp - 1) = b2)
    (hbit : pairBit (BitVec.ofNat 8 b1.toNat) = 0)
    (hb2 : evalICmp .eq (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 1) = 0) :
    WalkDispatchResult calls G C s := by
  have hklt : C.k < G.nep := WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hhead)
  have hseg := commaBracketSeg (calls := calls) G C s hInv hhead h8 hsp hmark hstate hbit
  have hInvSeg := hseg.measure.inv'
  have h22 : evalOperand (commaTarget C s b1 b2) (.reg "%22") =
      some (.int 8 (BitVec.ofNat 8 b2.toNat)) := by
    walk_read using commaTarget_22 C s b1 b2
  obtain ⟨s₆, hl₆, hs₆⟩ := WalkLink.if_else153_i_at (calls := calls) G
    { C with block := "if.else153.i" } (commaTarget C s b1 b2) hInvSeg rfl
    (x1 := BitVec.ofNat 8 b2.toNat) h22
  have hl₆' : WalkLink calls G { C with block := "if.else153.i" } (commaTarget C s b1 b2)
      { C with block := "if.then159.i" } s₆ := by
    rw [if_neg (by rw [hb2]; decide)] at hl₆
    exact hl₆
  have hv₆ : evalOperand s₆ (.reg "%idxprom.i") =
      some (.int 64 (BitVec.ofNat 64 (entryPos G C.k))) := by
    rw [hs₆]
    have hd := LeanLLVM.evalOperand_reg_of hInvSeg.idx_reg
    simpa only [State.bind, evalOperand,
      lookupName_cons_ne (k := "%cmp157.not.i") (n := "%idxprom.i") _ _ (by decide)]
      using hd
  have he₆ : lookupName s₆.env "%e" = some (.ptr C.stage.e) := by
    rw [hs₆]
    simpa only [State.bind,
      lookupName_cons_ne (k := "%cmp157.not.i") (n := "%e") _ _ (by decide)]
      using hInvSeg.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs])
  obtain ⟨s₇, hl₇, hs₇⟩ := WalkLink.if_then159_i_at (calls := calls) G
    { C with block := "if.then159.i" } s₆ hl₆'.inv' rfl hv₆ he₆
    (le_of_lt (entryPos_lt G hklt))
    (by have := entryPos_lt G hklt; have := WalkGeom.n_lt G; omega)
  have h₂ : Seg calls G { C with block := "if.else153.i" } (commaTarget C s b1 b2)
      { C with block := "if.then", eoff := entryPos G C.k, refusal := true } s₇ 2 :=
    Seg.tail hl₆' (Seg.tail hl₇ (Seg.nil hl₇.inv'))
  have hread : readBytes s₇.mem (C.stage.e + 8) 8 =
      some (wordBytes 8 (entryPos G C.k)) := by
    rw [hs₇]
    simpa only [State.bind] using
      refuseSegment_word_of_store (m := s₆.mem) (e := C.stage.e) (v := entryPos G C.k)
  exact commaRefuseAt G C s hInv hhead (hseg.measure.trans h₂.measure) rfl hread
    (le_of_lt (entryPos_lt G hklt)) hl₇.inv'.eoff_le

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.commaPairSeg
#print axioms LeanLLVM.Refinement.WalkScope.commaBraceMerge_at
#print axioms LeanLLVM.Refinement.WalkScope.commaBraceRefuse_at
#print axioms LeanLLVM.Refinement.WalkScope.commaBracketMerge_at
#print axioms LeanLLVM.Refinement.WalkScope.commaBracketRefuse_at

end WalkScope
end LeanLLVM.Refinement

