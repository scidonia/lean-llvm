/-
# The leaf document bytes: the two routes the byte's class opens below `if.else387.i`

`HcontDefaultRow.hclass` classifies the byte before the next entry's end four ways.  The
scan-free class (`14 ≤ %35 < 32`, `%35 ≠ 13`) reaches the token's end through
`NodeBlock41 → NodeBlock39 → LeafBlock35`, and the six head-switch classes' chains are
stated at it.  The two remaining non-whitespace classes take different leaves:

* `.lowLeaf` — `%35 < 13` and `%35 ∉ {9, 10}` — takes `NodeBlock41`'s first arm to
  `LeafBlock33`, whose offset test `ule (%35 + 247), 1` clears to `if.end372.i`;
* `.highLeaf` — `32 ≤ %35` and `%35 ≠ 32` — takes `NodeBlock39`'s second arm to
  `LeafBlock37`, whose equality test `eq %35, 32` clears to `if.end372.i`.

Both leaves store the same token end as `LeafBlock35` (`if.end372.i`'s `phi` takes
`%cond350.i` from each of the three), so the seam's cells, its memory and its root-slot
transport are the scan-free endpoint's, one link shorter on the low class.

## What is factored here

The byte's three pivots are stated once, as a counted chain from **any** state at
`NodeBlock41` whose carry is a `NodeBlock41` carry: the route enters as the state term,
not as a hypothesis about it.  The six default classes' chains and the high-byte route's
differ only in how they reach that state, so each composes the same theorem with its own
prefix — `contSwToLandSeg` for the continuing default arm, `contPrefixLand` for the
high-byte route.

`HcontByteRoute` is the class as the byte itself carries it: the three routes' bits on
`cont35 b35`, with no `G` or `v` baked in, so the last entry's own byte can take them too.
`HcontHeadByte.toRoute` is the row's class at the document's byte.

`contSeamByte` names the endpoint as a function of the class: a `State` cannot be a
`Prop` disjunction, and each leaf binds its own comparison cell, so the seam term must
depend on which leaf was taken.  The three routes' endpoints carry the same `%8`,
`%ee.1.i`, `%cond350.i` and memory, which is what the arm above them reads.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchLettersHead
import LeanLLVM.Refinement.JsonStage2WalkDispatchSupply

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The row's class, at the document's byte

`HcontByteRoute` and the states its three routes reach live in
`JsonStage2WalkRevolutionPrefix`, above every bundle that names them; this module keeps the
conversion from the row's class and the chains that consume it. -/

/-- **The row's class, at the document's byte.**  The three routes' bits are the same
statement at `cont35 (contB35 G v)`, so the conversion is the equality of the two
spellings. -/
def HcontHeadByte.toRoute {m0 : Mem} {G : WalkGeom m0} {v : BitVec 32} {b : UInt8}
    (hb35 : b = contB35 G v) (hb : HcontHeadByte G v) :
    HcontByteRoute (cont35 b) :=
  match hb with
  | .scanFree f =>
      .scanFree (by rw [hb35]; exact f.hb13) (by rw [hb35]; exact f.hb32)
        (by rw [hb35]; exact f.hbne13)
  | .lowLeaf h1 h2 => .lowLeaf (by rw [hb35]; exact h1) (by rw [hb35]; exact h2)
  | .highLeaf h1 h2 h3 =>
      .highLeaf (by rw [hb35]; exact h1) (by rw [hb35]; exact h2)
        (by rw [hb35]; exact h3)

/-! ### The byte's leaf arms, at the byte's class

`contP41Low`, `contP33Out`, `contP39High`, `contP37Out`, the three pivot endpoints
(`contP35Any`, `contP33Any`, `contP37Any`) and `contSeamByte` are
`JsonStage2WalkRevolutionPrefix`'s, as are their cell peels and the byte's three counted
route segments (`contByteSegScanFree`, `contByteSegLow`, `contByteSegHigh`): the bundles a
class's chain is stated at name them, so they sit above `JsonStage2WalkRevolution`. -/

/-! ### The cells at the `NodeBlock41` state, from the class's own

The default arm's `NodeBlock41` state is `contLandOut (contMidS ...)`.  `%cond350.i` is
`cond.end349.i`'s cell and `%8`/`%end.i` are the class's, read through the two binds. -/

/-- `%cond350.i` at `contLandOut`'s state. -/
theorem contLandOut_cond {m0 : Mem} {G : WalkGeom m0} (s : State) (v : Nat) (b35 : UInt8) :
    lookupName (contLandOut (G := G) s v b35).env "%cond350.i" =
      lookupName s.env "%cond350.i" := by
  simp only [contLandOut, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%8` at `contLandOut`'s state. -/
theorem contLandOut_env8 {m0 : Mem} {G : WalkGeom m0} (s : State) (v : Nat) (b35 : UInt8) :
    lookupName (contLandOut (G := G) s v b35).env "%8" = lookupName s.env "%8" := by
  simp only [contLandOut, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%end.i` at `contLandOut`'s state. -/
theorem contLandOut_envEnd {m0 : Mem} {G : WalkGeom m0} (s : State) (v : Nat)
    (b35 : UInt8) :
    lookupName (contLandOut (G := G) s v b35).env "%end.i" = lookupName s.env "%end.i" := by
  simp only [contLandOut, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%8` at `contMidS`'s state: the count test's and the bound's binds are fresh. -/
theorem contMidS_env8 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (qs : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) :
    lookupName (contMidS C qs inc nep ep v ix).env "%8" = lookupName qs.env "%8" := by
  simp only [contMidS, contSwOut, cte345OutAt, condEnd349OutAt, stateAt, cells,
    State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%end.i` at `contMidS`'s state: no bind of the count test, the lane or the bound
rebinds it. -/
theorem contMidS_envEnd {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (qs : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) :
    lookupName (contMidS C qs inc nep ep v ix).env "%end.i" = lookupName qs.env "%end.i" := by
  simp only [contMidS, contSwOut, cte345OutAt, condEnd349OutAt, stateAt, cells,
    State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%cond350.i` at the default arm's `NodeBlock41` state: `cond.end349.i` bound it and
the binds between are fresh. -/
theorem contMidLand_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (qs : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8) :
    lookupName (contLandOut (G := G) (contMidS C qs inc nep ep v ix) v.toNat b35).env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  rw [contLandOut_cond, contMidS_cond]

/-- `%8` at the default arm's `NodeBlock41` state, from the class's own cell. -/
theorem contMidLand_env8 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (qs : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8)
    {x : BitVec 8} (h : lookupName qs.env "%8" = some (.int 8 x)) :
    lookupName (contLandOut (G := G) (contMidS C qs inc nep ep v ix) v.toNat b35).env
      "%8" = some (.int 8 x) := by
  rw [contLandOut_env8, contMidS_env8]
  exact h

/-- `%end.i` at the default arm's `NodeBlock41` state, from the class's own cell. -/
theorem contMidLand_envEnd {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (qs : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8)
    (h : lookupName qs.env "%end.i" = some (.ptr (C.stage.tok + 8))) :
    lookupName (contLandOut (G := G) (contMidS C qs inc nep ep v ix) v.toNat b35).env
      "%end.i" = some (.ptr (C.stage.tok + 8)) := by
  rw [contLandOut_envEnd, contMidS_envEnd]
  exact h

/-! ### The continuing head's chain, per head-switch class and per byte class

Each class's prefix to `sw.default.i` is a counted chain of its own (`contLowToDefault` …
`contBrcToDefault`), and the suffix from `sw.default.i` to the seam is the shared four
(`contSwToLandSeg`) plus the byte's pivots (`contByteSeg`).  So the count is the class's
(three or four) plus four plus the byte's (three or four), i.e. at most twelve. -/

/-- The default arm's bound state's memory: the head's with the token record's two
stores (`cond.end349.i`'s position and gap). -/
theorem contMidS_mem {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q5 : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) :
    (contMidS C q5 inc nep ep v ix).mem =
      writeBytes (writeBytes q5.mem C.stage.tok (natToBytes ix.toNat 8))
        (C.stage.tok + 20) (natToBytes (BitVec.ofNat 32 1).toNat 4) := by
  simp only [contMidS, condEnd349OutAt, cte345OutAt, contSwOut, stateAt, cells, State.bind]

/-- **The root slot's word crosses `cond.end349.i`'s two stores.**  Both are inside the
token record, whose extent ends at or below the root slot, so the word the copy call's
argument list carries is the head's. -/
theorem contMidS_rootRead {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} (q5 : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) {rdv : BitVec 32}
    (hroot : readBytes q5.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)) :
    readBytes (contMidS C q5 inc nep ep v ix).mem (G.next0 + 8) 4 =
      some (natToBytes rdv.toNat 4) := by
  rw [contMidS_mem]
  change readBytes
    (writeBytes (writeBytes q5.mem (C.stage.tok + 0) (natToBytes ix.toNat 8))
      (C.stage.tok + 20) (natToBytes (BitVec.ofNat 32 1).toNat 4))
    (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)
  rw [walkReadBytes_rootSlot_of_tokStore (C := C) (off := 20) (len := 4)
    (v := natToBytes (BitVec.ofNat 32 1).toNat 4) (by decide) (natToBytes_length _ _)]
  rw [walkReadBytes_rootSlot_of_tokStore (C := C) (off := 0) (len := 8)
    (v := natToBytes ix.toNat 8) (by decide) (natToBytes_length _ _)]
  exact hroot

/-- **The default arm's head chain, from a class's `sw.default.i` state.**  The shared
four links, the `NodeBlock41` state's cells and the byte's pivots, ending at the class's
seam.  The caller supplies its own prefix. -/
noncomputable def contSwHeadLeafSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (q5 : State) (k : Nat)
    (hpre : Seg (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) q5 k)
    (hk : k ≤ 4) (hmem : q5.mem = s.mem)
    {x : BitVec 8} (h8end5 : lookupName q5.env "%8" = some (.int 8 x))
    (hend5 : lookupName q5.env "%end.i" = some (.ptr (C.stage.tok + 8)))
    {inc nep : BitVec 64}
    (hinc : evalOperand q5 (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand q5 (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    {ep : Nat} {v : BitVec 32}
    (h5 : lookupName (contSwOut q5 inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contSwOut q5 inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx : lookupName (contSwOut q5 inc nep).env "%idxprom.i" = some (.int 64 ix))
    (htok : lookupName (contSwOut q5 inc nep).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap : lookupName (contSwOut q5 inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contMidS C q5 inc nep ep v ix).mem
      ((G.b - 1) + v.toNat) 1 = some [b35])
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (hb : HcontByteRoute (cont35 b35)) :
    HcontHeadChain G C s x := by
  have hseg4 : WalkSegment (stage2Calls stage2SubCalls) G (HeadAC₄ C) q5 (ContAC₄ C)
      (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35) 4 :=
    contSwToLandSeg G C q5 (Seg.measure hpre).inv' rfl hinc hnep hnext h5 hi63 hread hidx htok hgap
      hugt hread35
  have hcond4 : lookupName (contLandOut (G := G) (contMidS C q5 inc nep ep v ix)
      v.toNat b35).env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) :=
    contMidLand_cond C q5 inc nep ep v ix b35
  have hend4 : lookupName (contLandOut (G := G) (contMidS C q5 inc nep ep v ix)
      v.toNat b35).env "%end.i" = some (.ptr (C.stage.tok + 8)) :=
    contMidLand_envEnd C q5 inc nep ep v ix b35 hend5
  have h8q4 : lookupName (contLandOut (G := G) (contMidS C q5 inc nep ep v ix)
      v.toNat b35).env "%8" = some (.int 8 x) :=
    contMidLand_env8 C q5 inc nep ep v ix b35 h8end5
  have h35 : evalOperand (contLandOut (G := G) (contMidS C q5 inc nep ep v ix)
      v.toNat b35) (.reg "%35") = some (.int 8 (cont35 b35)) := by
    exact LeanLLVM.evalOperand_reg_of
      (contLandOut_35 (G := G) (s := contMidS C q5 inc nep ep v ix) (v := v.toNat) b35)
  let q4 : State := contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35
  rcases hb with ⟨hb13, hb32, hbne13⟩ | ⟨hb13, hbns⟩ | ⟨hb13, hb32, hbne32⟩
  · have hsegB : Seg (stage2Calls stage2SubCalls) G (ContAC₄ C) q4
        { ContAC₄ C with block := "if.else387.i" }
        (contSeamByte q4 v.toNat (ContAC₄ C).stage.tok b35 x
          (.scanFree hb13 hb32 hbne13)) 4 :=
      contByteSegScanFree (ContAC₄ C) q4 hseg4.inv' rfl h35 hcond4 hend4 h8q4 hbit hb13 hb32
        hbne13
    refine
      { nH := k + (4 + 4)
        hnH := by omega
        Cm := ContSeamC C
        sm := contSeamByte q4 v.toNat (ContAC₄ C).stage.tok b35 x
          (.scanFree hb13 hb32 hbne13)
        seg := (Seg.measure hpre).trans (hseg4.trans (Seg.measure hsegB))
        hblock := rfl
        hk := rfl
        h8 := ?_
        v := v
        hee := contSeamByte_ee q4 v.toNat (ContAC₄ C).stage.tok b35 x
          (.scanFree hb13 hb32 hbne13)
        hcond := ?_
        hroot := ?_ }
    · have hlk : lookupName (contSeamByte q4 v.toNat (ContAC₄ C).stage.tok b35 x
        (.scanFree hb13 hb32 hbne13)).env "%8" = some (.int 8 x) := by
        rw [contSeamByte_env8]
        exact h8q4
      exact LeanLLVM.evalOperand_reg_of hlk
    · show lookupName (contSeamByte q4 v.toNat (ContAC₄ C).stage.tok b35 x
        (.scanFree hb13 hb32 hbne13)).env "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 v.toNat))
      rw [contSeamByte_cond]
      exact hcond4
    · intro rdv hroot
      exact contSeamByte_rootRead (C := ContAC₄ C) q4 v.toNat b35 x
        (.scanFree hb13 hb32 hbne13)
        (contMidS_rootRead (C := C) q5 inc nep ep v ix (by rw [hmem]; exact hroot))
  · have hsegB : Seg (stage2Calls stage2SubCalls) G (ContAC₄ C) q4
        { ContAC₄ C with block := "if.else387.i" }
        (contSeamByte q4 v.toNat (ContAC₄ C).stage.tok b35 x (.lowLeaf hb13 hbns)) 3 :=
      contByteSegLow (ContAC₄ C) q4 hseg4.inv' rfl h35 hcond4 hend4 h8q4 hbit hb13 hbns
    refine
      { nH := k + (4 + 3)
        hnH := by omega
        Cm := ContSeamC C
        sm := contSeamByte q4 v.toNat (ContAC₄ C).stage.tok b35 x (.lowLeaf hb13 hbns)
        seg := (Seg.measure hpre).trans (hseg4.trans (Seg.measure hsegB))
        hblock := rfl
        hk := rfl
        h8 := ?_
        v := v
        hee := contSeamByte_ee q4 v.toNat (ContAC₄ C).stage.tok b35 x (.lowLeaf hb13 hbns)
        hcond := ?_
        hroot := ?_ }
    · have hlk : lookupName (contSeamByte q4 v.toNat (ContAC₄ C).stage.tok b35 x
        (.lowLeaf hb13 hbns)).env "%8" = some (.int 8 x) := by
        rw [contSeamByte_env8]
        exact h8q4
      exact LeanLLVM.evalOperand_reg_of hlk
    · show lookupName (contSeamByte q4 v.toNat (ContAC₄ C).stage.tok b35 x
        (.lowLeaf hb13 hbns)).env "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 v.toNat))
      rw [contSeamByte_cond]
      exact hcond4
    · intro rdv hroot
      exact contSeamByte_rootRead (C := ContAC₄ C) q4 v.toNat b35 x (.lowLeaf hb13 hbns)
        (contMidS_rootRead (C := C) q5 inc nep ep v ix (by rw [hmem]; exact hroot))
  · have hsegB : Seg (stage2Calls stage2SubCalls) G (ContAC₄ C) q4
        { ContAC₄ C with block := "if.else387.i" }
        (contSeamByte q4 v.toNat (ContAC₄ C).stage.tok b35 x
          (.highLeaf hb13 hb32 hbne32)) 4 :=
      contByteSegHigh (ContAC₄ C) q4 hseg4.inv' rfl h35 hcond4 hend4 h8q4 hbit hb13 hb32
        hbne32
    refine
      { nH := k + (4 + 4)
        hnH := by omega
        Cm := ContSeamC C
        sm := contSeamByte q4 v.toNat (ContAC₄ C).stage.tok b35 x
          (.highLeaf hb13 hb32 hbne32)
        seg := (Seg.measure hpre).trans (hseg4.trans (Seg.measure hsegB))
        hblock := rfl
        hk := rfl
        h8 := ?_
        v := v
        hee := contSeamByte_ee q4 v.toNat (ContAC₄ C).stage.tok b35 x
          (.highLeaf hb13 hb32 hbne32)
        hcond := ?_
        hroot := ?_ }
    · have hlk : lookupName (contSeamByte q4 v.toNat (ContAC₄ C).stage.tok b35 x
        (.highLeaf hb13 hb32 hbne32)).env "%8" = some (.int 8 x) := by
        rw [contSeamByte_env8]
        exact h8q4
      exact LeanLLVM.evalOperand_reg_of hlk
    · show lookupName (contSeamByte q4 v.toNat (ContAC₄ C).stage.tok b35 x
        (.highLeaf hb13 hb32 hbne32)).env "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 v.toNat))
      rw [contSeamByte_cond]
      exact hcond4
    · intro rdv hroot
      exact contSeamByte_rootRead (C := ContAC₄ C) q4 v.toNat b35 x
        (.highLeaf hb13 hb32 hbne32)
        (contMidS_rootRead (C := C) q5 inc nep ep v ix (by rw [hmem]; exact hroot))

/-- **The `.defaultValueLow` class's head chain**, at its three-link prefix. -/
noncomputable def contLowHeadLeafSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 1)
    (hne34 : evalICmp .eq x (BitVec.ofNat 8 34) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (lowS₃ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (lowS₃ s x) (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    {ep : Nat} {v : BitVec 32}
    (h5 : lookupName (contSwOut (lowS₃ s x) inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contSwOut (lowS₃ s x) inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx : lookupName (contSwOut (lowS₃ s x) inc nep).env "%idxprom.i" =
      some (.int 64 ix))
    (htok : lookupName (contSwOut (lowS₃ s x) inc nep).env "%t352.i" =
      some (.ptr C.stage.tok))
    (hgap : lookupName (contSwOut (lowS₃ s x) inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contMidS C (lowS₃ s x) inc nep ep v ix).mem
      ((G.b - 1) + v.toNat) 1 = some [b35])
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (hb : HcontByteRoute (cont35 b35))
    (hend5 : lookupName (lowS₃ s x).env "%end.i" = some (.ptr (C.stage.tok + 8)))
    (h8end5 : lookupName (lowS₃ s x).env "%8" = some (.int 8 x)) :
    HcontHeadChain G C s x :=
  contSwHeadLeafSeg G C s (lowS₃ s x) 3
    (contLowToDefault G C s hInv hblock h8 h91 h44 hne34) (by omega) rfl h8end5 hend5
    hinc hnep hnext h5 hi63 hread hidx htok hgap hugt hread35 hbit hb

/-- **The `.defaultValueMid` class's head chain**, at its four-link prefix. -/
noncomputable def contMidHeadLeafSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 0)
    (hne58 : evalICmp .eq x (BitVec.ofNat 8 58) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (midS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (midS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    {ep : Nat} {v : BitVec 32}
    (h5 : lookupName (contSwOut (midS₄ s x) inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contSwOut (midS₄ s x) inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx : lookupName (contSwOut (midS₄ s x) inc nep).env "%idxprom.i" =
      some (.int 64 ix))
    (htok : lookupName (contSwOut (midS₄ s x) inc nep).env "%t352.i" =
      some (.ptr C.stage.tok))
    (hgap : lookupName (contSwOut (midS₄ s x) inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contMidS C (midS₄ s x) inc nep ep v ix).mem
      ((G.b - 1) + v.toNat) 1 = some [b35])
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (hb : HcontByteRoute (cont35 b35))
    (hend5 : lookupName (midS₄ s x).env "%end.i" = some (.ptr (C.stage.tok + 8)))
    (h8end5 : lookupName (midS₄ s x).env "%8" = some (.int 8 x)) :
    HcontHeadChain G C s x :=
  contSwHeadLeafSeg G C s (midS₄ s x) 4
    (contMidToDefault G C s hInv hblock h8 h91 h44 h58 hne58) (by omega) rfl h8end5 hend5
    hinc hnep hnext h5 hi63 hread hidx htok hgap hugt hread35 hbit hb

/-- **The `.otherValue` class's head chain**, at its four-link prefix. -/
noncomputable def contOthHeadLeafSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
    (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (othS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (othS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    {ep : Nat} {v : BitVec 32}
    (h5 : lookupName (contSwOut (othS₄ s x) inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contSwOut (othS₄ s x) inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx : lookupName (contSwOut (othS₄ s x) inc nep).env "%idxprom.i" =
      some (.int 64 ix))
    (htok : lookupName (contSwOut (othS₄ s x) inc nep).env "%t352.i" =
      some (.ptr C.stage.tok))
    (hgap : lookupName (contSwOut (othS₄ s x) inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contMidS C (othS₄ s x) inc nep ep v ix).mem
      ((G.b - 1) + v.toNat) 1 = some [b35])
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (hb : HcontByteRoute (cont35 b35))
    (hend5 : lookupName (othS₄ s x).env "%end.i" = some (.ptr (C.stage.tok + 8)))
    (h8end5 : lookupName (othS₄ s x).env "%8" = some (.int 8 x)) :
    HcontHeadChain G C s x :=
  contSwHeadLeafSeg G C s (othS₄ s x) 4
    (contOthToDefault G C s hInv hblock h8 h91 h44 h58 hne44) (by omega) rfl h8end5 hend5
    hinc hnep hnext h5 hi63 hread hidx htok hgap hugt hread35 hbit hb

/-- **The `.defaultValueBracket` class's head chain**, at its four-link prefix. -/
noncomputable def contBrkHeadLeafSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
    (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 1)
    (hne91 : evalICmp .eq x (BitVec.ofNat 8 91) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (brkS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (brkS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    {ep : Nat} {v : BitVec 32}
    (h5 : lookupName (contSwOut (brkS₄ s x) inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contSwOut (brkS₄ s x) inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx : lookupName (contSwOut (brkS₄ s x) inc nep).env "%idxprom.i" =
      some (.int 64 ix))
    (htok : lookupName (contSwOut (brkS₄ s x) inc nep).env "%t352.i" =
      some (.ptr C.stage.tok))
    (hgap : lookupName (contSwOut (brkS₄ s x) inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contMidS C (brkS₄ s x) inc nep ep v ix).mem
      ((G.b - 1) + v.toNat) 1 = some [b35])
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (hb : HcontByteRoute (cont35 b35))
    (hend5 : lookupName (brkS₄ s x).env "%end.i" = some (.ptr (C.stage.tok + 8)))
    (h8end5 : lookupName (brkS₄ s x).env "%8" = some (.int 8 x)) :
    HcontHeadChain G C s x :=
  contSwHeadLeafSeg G C s (brkS₄ s x) 4
    (contBrkToDefault G C s hInv hblock h8 h91 h123 h93 hne91) (by omega) rfl h8end5 hend5
    hinc hnep hnext h5 hi63 hread hidx htok hgap hugt hread35 hbit hb

/-- **The `.defaultValueBracketHigh` class's head chain**, at its four-link prefix. -/
noncomputable def contBhHeadLeafSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
    (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 0)
    (hne93 : evalICmp .eq x (BitVec.ofNat 8 93) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (bhS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (bhS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    {ep : Nat} {v : BitVec 32}
    (h5 : lookupName (contSwOut (bhS₄ s x) inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contSwOut (bhS₄ s x) inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx : lookupName (contSwOut (bhS₄ s x) inc nep).env "%idxprom.i" =
      some (.int 64 ix))
    (htok : lookupName (contSwOut (bhS₄ s x) inc nep).env "%t352.i" =
      some (.ptr C.stage.tok))
    (hgap : lookupName (contSwOut (bhS₄ s x) inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contMidS C (bhS₄ s x) inc nep ep v ix).mem
      ((G.b - 1) + v.toNat) 1 = some [b35])
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (hb : HcontByteRoute (cont35 b35))
    (hend5 : lookupName (bhS₄ s x).env "%end.i" = some (.ptr (C.stage.tok + 8)))
    (h8end5 : lookupName (bhS₄ s x).env "%8" = some (.int 8 x)) :
    HcontHeadChain G C s x :=
  contSwHeadLeafSeg G C s (bhS₄ s x) 4
    (contBhToDefault G C s hInv hblock h8 h91 h123 h93 hne93) (by omega) rfl h8end5 hend5
    hinc hnep hnext h5 hi63 hread hidx htok hgap hugt hread35 hbit hb

/-- **The `.defaultValueBrace` class's head chain**, at its four-link prefix. -/
noncomputable def contBrcHeadLeafSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1)
    (hne123 : evalICmp .eq x (BitVec.ofNat 8 123) = 0)
    {inc nep : BitVec 64}
    (hinc : evalOperand (brcS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (brcS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    {ep : Nat} {v : BitVec 32}
    (h5 : lookupName (contSwOut (brcS₄ s x) inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contSwOut (brcS₄ s x) inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx : lookupName (contSwOut (brcS₄ s x) inc nep).env "%idxprom.i" =
      some (.int 64 ix))
    (htok : lookupName (contSwOut (brcS₄ s x) inc nep).env "%t352.i" =
      some (.ptr C.stage.tok))
    (hgap : lookupName (contSwOut (brcS₄ s x) inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contMidS C (brcS₄ s x) inc nep ep v ix).mem
      ((G.b - 1) + v.toNat) 1 = some [b35])
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (hb : HcontByteRoute (cont35 b35))
    (hend5 : lookupName (brcS₄ s x).env "%end.i" = some (.ptr (C.stage.tok + 8)))
    (h8end5 : lookupName (brcS₄ s x).env "%8" = some (.int 8 x)) :
    HcontHeadChain G C s x :=
  contSwHeadLeafSeg G C s (brcS₄ s x) 4
    (contBrcToDefault G C s hInv hblock h8 h91 h123 h125 hne123) (by omega) rfl h8end5 hend5
    hinc hnep hnext h5 hi63 hread hidx htok hgap hugt hread35 hbit hb

/-! ### The high-byte route's leaf chains

The head byte `126`/`127` reaches `NodeBlock41` through `contPrefixLand`'s eight links
(the four high-byte pivots, the count test's succeeding arm, the bound's `phi` and the
whitespace check), so the byte's pivots are appended to those. -/

/-- **The high-byte route's chain to the seam, at the byte's class.**  Eight links to
`NodeBlock41` plus the byte's three or four, i.e. at most twelve. -/
theorem hcontHeadLeafSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (hlt123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
    (hlt125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq x (BitVec.ofNat 8 125) = 0)
    {inc nep : BitVec 64} {ep : Nat} {v : BitVec 32}
    (hinc : evalOperand (headAS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (headAS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    (h5 : lookupName (contAS₅ s x inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contAS₅ s x inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx5 : lookupName (contAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix))
    (htok5 : lookupName (contAS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap5 : lookupName (contAS₅ s x inc nep).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contEndS C s x inc nep ep v ix).mem
      ((G.b - 1) + v.toNat) 1 = some [b35])
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (hb : HcontByteRoute (cont35 b35)) :
    ∃ n : Nat, n ≤ 12 ∧
      WalkSegment (stage2Calls stage2SubCalls) G C s (ContSeamC C)
        (contSeamByte (contLandS C s x inc nep ep v ix b35) v.toNat (ContAC₄ C).stage.tok
          b35 x hb) n := by
  have hseg8 : WalkSegment (stage2Calls stage2SubCalls) G C s (ContAC₄ C)
      (contLandS C s x inc nep ep v ix b35) 8 :=
    contPrefixLand G C s hInv hblock h8 hlt91 hlt123 hlt125 hne125 hinc hnep hnext h5 hi63 hread
      hidx5 htok5 hgap5 hugt hread35
  have hcond4 : lookupName (contLandS C s x inc nep ep v ix b35).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) :=
    contLandS_cond C s x inc nep ep v ix b35
  have hend4 : lookupName (contLandS C s x inc nep ep v ix b35).env "%end.i" =
      some (.ptr ((ContAC₄ C).stage.tok + 8)) := by
    simp only [contLandS, contEndS, condEnd349OutAt, cte345OutAt, stateAt, cells,
      State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%end.i", .ptr (C.stage.tok + 8)) (by simp [walkStaticRegs])
  have h8q4 : lookupName (contLandS C s x inc nep ep v ix b35).env "%8" =
      some (.int 8 x) := by
    have hcell : lookupName (contLandS C s x inc nep ep v ix b35).env "%8" =
        lookupName s.env "%8" := by
      simp only [contLandS, contEndS, condEnd349OutAt, cte345OutAt, contAS₅, headAS₄,
        headAS₃, headAS₂, headAS₁, stateAt, cells, State.bind]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
    rw [hcell]
    walk_read using h8
  have h35 : evalOperand (contLandS C s x inc nep ep v ix b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
    simp only [evalOperand]
    exact contLandS_35 C s x inc nep ep v ix b35
  rcases hb with ⟨hb13, hb32, hbne13⟩ | ⟨hb13, hbns⟩ | ⟨hb13, hb32, hbne32⟩
  · refine ⟨8 + 4, by omega, ?_⟩
    exact hseg8.trans (Seg.measure (contByteSegScanFree (ContAC₄ C)
      (contLandS C s x inc nep ep v ix b35) hseg8.inv' rfl h35 hcond4 hend4 h8q4 hbit hb13
      hb32 hbne13))
  · refine ⟨8 + 3, by omega, ?_⟩
    exact hseg8.trans (Seg.measure (contByteSegLow (ContAC₄ C)
      (contLandS C s x inc nep ep v ix b35) hseg8.inv' rfl h35 hcond4 hend4 h8q4 hbit hb13
      hbns))
  · refine ⟨8 + 4, by omega, ?_⟩
    exact hseg8.trans (Seg.measure (contByteSegHigh (ContAC₄ C)
      (contLandS C s x inc nep ep v ix b35) hseg8.inv' rfl h35 hcond4 hend4 h8q4 hbit hb13
      hb32 hbne32))

/-- The `NodeBlock41`-based carries' `if.else387.i` update is the seam's own carry. -/
theorem contCarryIf_eq {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) :
    ({ ContAC₄ C with block := "if.else387.i" } : WalkCarry G) = ContSeamC C := rfl

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.contByteSegScanFree
#print axioms LeanLLVM.Refinement.WalkScope.contByteSegLow
#print axioms LeanLLVM.Refinement.WalkScope.contByteSegHigh
#print axioms LeanLLVM.Refinement.WalkScope.contLowHeadLeafSeg
#print axioms LeanLLVM.Refinement.WalkScope.contMidHeadLeafSeg
#print axioms LeanLLVM.Refinement.WalkScope.contOthHeadLeafSeg
#print axioms LeanLLVM.Refinement.WalkScope.contBrkHeadLeafSeg
#print axioms LeanLLVM.Refinement.WalkScope.contBhHeadLeafSeg
#print axioms LeanLLVM.Refinement.WalkScope.contBrcHeadLeafSeg
#print axioms LeanLLVM.Refinement.WalkScope.hcontHeadLeafSeg

end WalkScope
end LeanLLVM.Refinement
