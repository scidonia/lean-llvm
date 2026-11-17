/-
# The default arm's head chain, from the payload's document row

`HcontLane.defaultLane` (`JsonStage2WalkDispatchSupply`) carries the default arm's document
facts: the next entry's position word and the read that fetches it, the bound's compare,
and the byte before the entry's end with its class (`HcontByteClass`).  The class is a
disjunction; this module consumes its three non-whitespace disjuncts (`HcontHeadByte`) and
turns the row into the arm's head chain at each head-switch class the default arm admits.
The `.wsByte` disjunct is the run class's, consumed by `JsonStage2WalkDispatchSeams`' seam
group.

## The chain is the class's prefix plus the shared suffix

`JsonStage2WalkDispatchLettersHead` factors the chain into a prefix per head-switch class —
`.defaultValueLow`'s three links, the four-pivot classes' four — and the shared four to
`NodeBlock41` (`contSwToLandSeg`).  The byte's pivots then take one of three routes, stated
once in `JsonStage2WalkDispatchLeafBytes` (`contByteSegScanFree`/`Low`/`High`): the
scan-free class's four links, the low leaf's three and the high leaf's four.  The prefix's
binds are the only difference between the classes' states, and no block of either part
touches the document's memory, so the payload's single document row feeds all six.

The other cells the chain reads are the invariant's: `%inc.i` and `%nep` are `WalkInv`'s
count cells, `%5` is `WalkPtrs`'s positions table, `%idxprom.i` is `WalkInv.idx_reg`, and
`%t352.i`, `%gap.i` and `%end.i` are `walkStaticRegs`'s.  Each is peeled through the class's
prefix and the suffix's first bind; none is supplied.

## The byte before the entry's end

The payload's read is at the head state's memory, and the suffix writes the token record
before the whitespace check reads.  `contMidS_docByte` is the transport: the two stores are
outside the document's staged region (`stage2StagedWrites_against`), so the same document
byte is read at the suffix's state.  That lemma is the `contMidS` twin of
`contEndS_docByte`.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchSupply
import LeanLLVM.Refinement.JsonStage2WalkDispatchLettersHead
import LeanLLVM.Refinement.JsonStage2WalkDispatchLeafBytes
import LeanLLVM.Refinement.JsonStage2WalkHcontFactsOfStaging

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The document's byte, at the suffix's own memory -/

/-- **The document's byte read at the default suffix's state.**  `contMidS` is
`cond.end349.i`'s two token-record stores after the count test's bind: the stores are
outside the document's staged region, so a read of the document at the head state is the
same read here.  The proof is `contEndS_docByte`'s with the head switch's binds abstracted
to an arbitrary source state whose memory is the head's. -/
theorem contMidS_docByte {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s q : State)
    (hInv : WalkInv G C s) (hmem : q.mem = s.mem) (inc nep : BitVec 64) (ep : Nat)
    (v : BitVec 32) (ix : BitVec 64) {idx : Nat} (hidx : idx < G.n) :
    readBytes (contMidS C q inc nep ep v ix).mem (G.b + idx) 1 =
      some [G.bs.getD idx 0] := by
  have hsep := stage2StagedWrites_against C.stage.separate (a := G.b)
    (m := G.n + stage2ReadTail) (by simp [stage2Regions])
    (r := (C.stage.tok, stage2TokenExtent)) (by simp [stage2StagedWrites])
  have htok : stage2TokenExtent = 24 := rfl
  rw [htok] at hsep
  have h4 : (natToBytes (BitVec.ofNat 32 1).toNat 4).length = 4 := natToBytes_length ..
  have h8 : (natToBytes ix.toNat 8).length = 8 := natToBytes_length ..
  simp only [contMidS, condEnd349OutAt, cte345OutAt, contSwOut, stateAt, cells, State.bind]
  rw [hmem]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok + 20)
    (v := natToBytes (BitVec.ofNat 32 1).toNat 4) (by rw [h4]; rcases hsep with h | h <;> omega)]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok)
    (v := natToBytes ix.toNat 8) (by rw [h8]; rcases hsep with h | h <;> omega)]
  exact walkDoc_byte G C s hInv (by have h := hInv.alen_le; omega)
    (le_trans hInv.evlen_le G.evRoom) hidx

/-! ### `.defaultValueLow`: three links, then the shared eight -/

/-- **`NodeBlock5 → LeafBlock → sw.default.i` plus the suffix, from the payload's row.**
The class's three pivots, the suffix's eight, and the document row for the cell every
default chain reads: eleven links in all, and the endpoint is the class-C span's entry. -/
noncomputable def lowHeadChain_of_lane {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 1)
    (hne34 : evalICmp .eq x (BitVec.ofNat 8 34) = 0)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (r : HcontDefaultRow G C s) (hb : HcontHeadByte G r.v) :
    HcontHeadChain G C s x := by
  obtain ⟨v, hread0, _hv1, hvle, hugt, _hclass⟩ := r
  -- the head's byte and the invariant's cells at the class's prefix state
  have h8q : lookupName (lowS₃ s x).env "%8" = some (.int 8 x) := by
    simp only [lowS₃, lowS₂, lowS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [evalOperand] using h8
  have hincq : evalOperand (lowS₃ s x) (.reg "%inc.i") =
      some (.int 64 (hlastIncV C)) := by
    simp only [evalOperand, lowS₃, lowS₂, lowS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [hlastIncV] using hInv.inc_reg
  have hnepq : evalOperand (lowS₃ s x) (.reg "%nep") =
      some (.int 64 (hlastNepV G)) := by
    simp only [evalOperand, lowS₃, lowS₂, lowS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [hlastNepV] using
      hInv.regs ("%nep", .int 64 (hlastNepV G)) (by simp [walkStaticRegs])
  have h5q : lookupName (lowS₃ s x).env "%5" = some (.ptr G.ep) := by
    simp only [lowS₃, lowS₂, lowS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.ptrs.2.1
  have hidxq : lookupName (lowS₃ s x).env "%idxprom.i" =
      some (.int 64 (contIx G C)) := by
    simp only [lowS₃, lowS₂, lowS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [contIx] using hInv.idx_reg
  have htokq : lookupName (lowS₃ s x).env "%t352.i" = some (.ptr C.stage.tok) := by
    simp only [lowS₃, lowS₂, lowS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%t352.i", .ptr C.stage.tok) (by simp [walkStaticRegs])
  have hgapq : lookupName (lowS₃ s x).env "%gap.i" = some (.ptr (C.stage.tok + 20)) := by
    simp only [lowS₃, lowS₂, lowS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%gap.i", .ptr (C.stage.tok + 20)) (by simp [walkStaticRegs])
  have hendq : lookupName (lowS₃ s x).env "%end.i" = some (.ptr (C.stage.tok + 8)) := by
    simp only [lowS₃, lowS₂, lowS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%end.i", .ptr (C.stage.tok + 8)) (by simp [walkStaticRegs])
  -- the suffix's first bind leaves them alone
  have h5 : lookupName (contSwOut (lowS₃ s x) (hlastIncV C) (hlastNepV G)).env "%5" =
      some (.ptr G.ep) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%5") _ _ (by decide)]
    exact h5q
  have hidx : lookupName (contSwOut (lowS₃ s x) (hlastIncV C) (hlastNepV G)).env
      "%idxprom.i" = some (.int 64 (contIx G C)) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%idxprom.i") _ _ (by decide)]
    exact hidxq
  have htok : lookupName (contSwOut (lowS₃ s x) (hlastIncV C) (hlastNepV G)).env
      "%t352.i" = some (.ptr C.stage.tok) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%t352.i") _ _ (by decide)]
    exact htokq
  have hgap : lookupName (contSwOut (lowS₃ s x) (hlastIncV C) (hlastNepV G)).env
      "%gap.i" = some (.ptr (C.stage.tok + 20)) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%gap.i") _ _ (by decide)]
    exact hgapq
  -- the document row, at the suffix's memory
  have hincTo : (hlastIncV C).toNat = C.k + 1 := cont_inc_toNat G C hk
  have hread : readBytes (contSwOut (lowS₃ s x) (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4) := by
    rw [hincTo]
    simpa only [contSwOut, State.bind, lowS₃, lowS₂, lowS₁] using hread0
  have hread35 : readBytes (contMidS C (lowS₃ s x) (hlastIncV C) (hlastNepV G) G.ep v
      (contIx G C)).mem ((G.b - 1) + v.toNat) 1 = some [contB35 G v] := by
    have hq : v.toNat - 1 < G.n := by
      have hpos := entryPos_lt G hk
      omega
    have hmid := contMidS_docByte G C s (lowS₃ s x) hInv rfl (hlastIncV C) (hlastNepV G)
      G.ep v (contIx G C) hq
    have hb : 1 ≤ G.b := G.bPos
    rw [show (G.b - 1) + v.toNat = G.b + (v.toNat - 1) from by omega]
    simpa only [contB35] using hmid
  exact contLowHeadLeafSeg G C s hInv hblock h8 h91 h44 hne34 hincq hnepq
    (cont_ult_one G C hk) h5 (cont_hi63 G C hk) hread hidx htok hgap hugt hread35 hbit
    (HcontHeadByte.toRoute rfl hb) hendq h8q

/-! ### The four-pivot classes: four links, then the shared eight -/

/-- **`NodeBlock5 → NodeBlock → LeafBlock3 → sw.default.i` plus the suffix.**  The mid
class's four pivots, the suffix's eight, and the payload's document row: twelve links. -/
noncomputable def midHeadChain_of_lane {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 0)
    (hne58 : evalICmp .eq x (BitVec.ofNat 8 58) = 0)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (r : HcontDefaultRow G C s) (hb : HcontHeadByte G r.v) :
    HcontHeadChain G C s x := by
  obtain ⟨v, hread0, _hv1, hvle, hugt, _hclass⟩ := r
  have h8q : lookupName (midS₄ s x).env "%8" = some (.int 8 x) := by
    simp only [midS₄, midS₃, midS₂, midS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [evalOperand] using h8
  have hincq : evalOperand (midS₄ s x) (.reg "%inc.i") =
      some (.int 64 (hlastIncV C)) := by
    simp only [evalOperand, midS₄, midS₃, midS₂, midS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [hlastIncV] using hInv.inc_reg
  have hnepq : evalOperand (midS₄ s x) (.reg "%nep") =
      some (.int 64 (hlastNepV G)) := by
    simp only [evalOperand, midS₄, midS₃, midS₂, midS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [hlastNepV] using
      hInv.regs ("%nep", .int 64 (hlastNepV G)) (by simp [walkStaticRegs])
  have h5q : lookupName (midS₄ s x).env "%5" = some (.ptr G.ep) := by
    simp only [midS₄, midS₃, midS₂, midS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.ptrs.2.1
  have hidxq : lookupName (midS₄ s x).env "%idxprom.i" =
      some (.int 64 (contIx G C)) := by
    simp only [midS₄, midS₃, midS₂, midS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [contIx] using hInv.idx_reg
  have htokq : lookupName (midS₄ s x).env "%t352.i" = some (.ptr C.stage.tok) := by
    simp only [midS₄, midS₃, midS₂, midS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%t352.i", .ptr C.stage.tok) (by simp [walkStaticRegs])
  have hgapq : lookupName (midS₄ s x).env "%gap.i" = some (.ptr (C.stage.tok + 20)) := by
    simp only [midS₄, midS₃, midS₂, midS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%gap.i", .ptr (C.stage.tok + 20)) (by simp [walkStaticRegs])
  have hendq : lookupName (midS₄ s x).env "%end.i" = some (.ptr (C.stage.tok + 8)) := by
    simp only [midS₄, midS₃, midS₂, midS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%end.i", .ptr (C.stage.tok + 8)) (by simp [walkStaticRegs])
  have h5 : lookupName (contSwOut (midS₄ s x) (hlastIncV C) (hlastNepV G)).env "%5" =
      some (.ptr G.ep) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%5") _ _ (by decide)]
    exact h5q
  have hidx : lookupName (contSwOut (midS₄ s x) (hlastIncV C) (hlastNepV G)).env
      "%idxprom.i" = some (.int 64 (contIx G C)) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%idxprom.i") _ _ (by decide)]
    exact hidxq
  have htok : lookupName (contSwOut (midS₄ s x) (hlastIncV C) (hlastNepV G)).env
      "%t352.i" = some (.ptr C.stage.tok) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%t352.i") _ _ (by decide)]
    exact htokq
  have hgap : lookupName (contSwOut (midS₄ s x) (hlastIncV C) (hlastNepV G)).env
      "%gap.i" = some (.ptr (C.stage.tok + 20)) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%gap.i") _ _ (by decide)]
    exact hgapq
  have hincTo : (hlastIncV C).toNat = C.k + 1 := cont_inc_toNat G C hk
  have hread : readBytes (contSwOut (midS₄ s x) (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4) := by
    rw [hincTo]
    simpa only [contSwOut, State.bind, midS₄, midS₃, midS₂, midS₁] using hread0
  have hread35 : readBytes (contMidS C (midS₄ s x) (hlastIncV C) (hlastNepV G) G.ep v
      (contIx G C)).mem ((G.b - 1) + v.toNat) 1 = some [contB35 G v] := by
    have hq : v.toNat - 1 < G.n := by
      have hpos := entryPos_lt G hk
      omega
    have hmid := contMidS_docByte G C s (midS₄ s x) hInv rfl (hlastIncV C) (hlastNepV G)
      G.ep v (contIx G C) hq
    have hb : 1 ≤ G.b := G.bPos
    rw [show (G.b - 1) + v.toNat = G.b + (v.toNat - 1) from by omega]
    simpa only [contB35] using hmid
  exact contMidHeadLeafSeg G C s hInv hblock h8 h91 h44 h58 hne58 hincq hnepq
    (cont_ult_one G C hk) h5 (cont_hi63 G C hk) hread hidx htok hgap hugt hread35 hbit
    (HcontHeadByte.toRoute rfl hb) hendq h8q

/-- **`NodeBlock5 → NodeBlock → LeafBlock1 → sw.default.i` plus the suffix.**  The
`.otherValue` class's four pivots and the payload's document row: twelve links. -/
noncomputable def othHeadChain_of_lane {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
    (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (r : HcontDefaultRow G C s) (hb : HcontHeadByte G r.v) :
    HcontHeadChain G C s x := by
  obtain ⟨v, hread0, _hv1, hvle, hugt, _hclass⟩ := r
  have h8q : lookupName (othS₄ s x).env "%8" = some (.int 8 x) := by
    simp only [othS₄, othS₃, othS₂, othS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [evalOperand] using h8
  have hincq : evalOperand (othS₄ s x) (.reg "%inc.i") =
      some (.int 64 (hlastIncV C)) := by
    simp only [evalOperand, othS₄, othS₃, othS₂, othS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [hlastIncV] using hInv.inc_reg
  have hnepq : evalOperand (othS₄ s x) (.reg "%nep") =
      some (.int 64 (hlastNepV G)) := by
    simp only [evalOperand, othS₄, othS₃, othS₂, othS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [hlastNepV] using
      hInv.regs ("%nep", .int 64 (hlastNepV G)) (by simp [walkStaticRegs])
  have h5q : lookupName (othS₄ s x).env "%5" = some (.ptr G.ep) := by
    simp only [othS₄, othS₃, othS₂, othS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.ptrs.2.1
  have hidxq : lookupName (othS₄ s x).env "%idxprom.i" =
      some (.int 64 (contIx G C)) := by
    simp only [othS₄, othS₃, othS₂, othS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [contIx] using hInv.idx_reg
  have htokq : lookupName (othS₄ s x).env "%t352.i" = some (.ptr C.stage.tok) := by
    simp only [othS₄, othS₃, othS₂, othS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%t352.i", .ptr C.stage.tok) (by simp [walkStaticRegs])
  have hgapq : lookupName (othS₄ s x).env "%gap.i" = some (.ptr (C.stage.tok + 20)) := by
    simp only [othS₄, othS₃, othS₂, othS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%gap.i", .ptr (C.stage.tok + 20)) (by simp [walkStaticRegs])
  have hendq : lookupName (othS₄ s x).env "%end.i" = some (.ptr (C.stage.tok + 8)) := by
    simp only [othS₄, othS₃, othS₂, othS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%end.i", .ptr (C.stage.tok + 8)) (by simp [walkStaticRegs])
  have h5 : lookupName (contSwOut (othS₄ s x) (hlastIncV C) (hlastNepV G)).env "%5" =
      some (.ptr G.ep) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%5") _ _ (by decide)]
    exact h5q
  have hidx : lookupName (contSwOut (othS₄ s x) (hlastIncV C) (hlastNepV G)).env
      "%idxprom.i" = some (.int 64 (contIx G C)) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%idxprom.i") _ _ (by decide)]
    exact hidxq
  have htok : lookupName (contSwOut (othS₄ s x) (hlastIncV C) (hlastNepV G)).env
      "%t352.i" = some (.ptr C.stage.tok) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%t352.i") _ _ (by decide)]
    exact htokq
  have hgap : lookupName (contSwOut (othS₄ s x) (hlastIncV C) (hlastNepV G)).env
      "%gap.i" = some (.ptr (C.stage.tok + 20)) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%gap.i") _ _ (by decide)]
    exact hgapq
  have hincTo : (hlastIncV C).toNat = C.k + 1 := cont_inc_toNat G C hk
  have hread : readBytes (contSwOut (othS₄ s x) (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4) := by
    rw [hincTo]
    simpa only [contSwOut, State.bind, othS₄, othS₃, othS₂, othS₁] using hread0
  have hread35 : readBytes (contMidS C (othS₄ s x) (hlastIncV C) (hlastNepV G) G.ep v
      (contIx G C)).mem ((G.b - 1) + v.toNat) 1 = some [contB35 G v] := by
    have hq : v.toNat - 1 < G.n := by
      have hpos := entryPos_lt G hk
      omega
    have hmid := contMidS_docByte G C s (othS₄ s x) hInv rfl (hlastIncV C) (hlastNepV G)
      G.ep v (contIx G C) hq
    have hb : 1 ≤ G.b := G.bPos
    rw [show (G.b - 1) + v.toNat = G.b + (v.toNat - 1) from by omega]
    simpa only [contB35] using hmid
  exact contOthHeadLeafSeg G C s hInv hblock h8 h91 h44 h58 hne44 hincq hnepq
    (cont_ult_one G C hk) h5 (cont_hi63 G C hk) hread hidx htok hgap hugt hread35 hbit
    (HcontHeadByte.toRoute rfl hb) hendq h8q

/-- **`NodeBlock19 → NodeBlock11 → LeafBlock7 → sw.default.i` plus the suffix.**  The
`.defaultValueBracket` class's four pivots and the payload's document row: twelve links. -/
noncomputable def brkHeadChain_of_lane {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
    (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 1)
    (hne91 : evalICmp .eq x (BitVec.ofNat 8 91) = 0)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (r : HcontDefaultRow G C s) (hb : HcontHeadByte G r.v) :
    HcontHeadChain G C s x := by
  obtain ⟨v, hread0, _hv1, hvle, hugt, _hclass⟩ := r
  have h8q : lookupName (brkS₄ s x).env "%8" = some (.int 8 x) := by
    simp only [brkS₄, brkS₃, brkS₂, brkS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [evalOperand] using h8
  have hincq : evalOperand (brkS₄ s x) (.reg "%inc.i") =
      some (.int 64 (hlastIncV C)) := by
    simp only [evalOperand, brkS₄, brkS₃, brkS₂, brkS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [hlastIncV] using hInv.inc_reg
  have hnepq : evalOperand (brkS₄ s x) (.reg "%nep") =
      some (.int 64 (hlastNepV G)) := by
    simp only [evalOperand, brkS₄, brkS₃, brkS₂, brkS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [hlastNepV] using
      hInv.regs ("%nep", .int 64 (hlastNepV G)) (by simp [walkStaticRegs])
  have h5q : lookupName (brkS₄ s x).env "%5" = some (.ptr G.ep) := by
    simp only [brkS₄, brkS₃, brkS₂, brkS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.ptrs.2.1
  have hidxq : lookupName (brkS₄ s x).env "%idxprom.i" =
      some (.int 64 (contIx G C)) := by
    simp only [brkS₄, brkS₃, brkS₂, brkS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [contIx] using hInv.idx_reg
  have htokq : lookupName (brkS₄ s x).env "%t352.i" = some (.ptr C.stage.tok) := by
    simp only [brkS₄, brkS₃, brkS₂, brkS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%t352.i", .ptr C.stage.tok) (by simp [walkStaticRegs])
  have hgapq : lookupName (brkS₄ s x).env "%gap.i" = some (.ptr (C.stage.tok + 20)) := by
    simp only [brkS₄, brkS₃, brkS₂, brkS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%gap.i", .ptr (C.stage.tok + 20)) (by simp [walkStaticRegs])
  have hendq : lookupName (brkS₄ s x).env "%end.i" = some (.ptr (C.stage.tok + 8)) := by
    simp only [brkS₄, brkS₃, brkS₂, brkS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%end.i", .ptr (C.stage.tok + 8)) (by simp [walkStaticRegs])
  have h5 : lookupName (contSwOut (brkS₄ s x) (hlastIncV C) (hlastNepV G)).env "%5" =
      some (.ptr G.ep) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%5") _ _ (by decide)]
    exact h5q
  have hidx : lookupName (contSwOut (brkS₄ s x) (hlastIncV C) (hlastNepV G)).env
      "%idxprom.i" = some (.int 64 (contIx G C)) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%idxprom.i") _ _ (by decide)]
    exact hidxq
  have htok : lookupName (contSwOut (brkS₄ s x) (hlastIncV C) (hlastNepV G)).env
      "%t352.i" = some (.ptr C.stage.tok) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%t352.i") _ _ (by decide)]
    exact htokq
  have hgap : lookupName (contSwOut (brkS₄ s x) (hlastIncV C) (hlastNepV G)).env
      "%gap.i" = some (.ptr (C.stage.tok + 20)) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%gap.i") _ _ (by decide)]
    exact hgapq
  have hincTo : (hlastIncV C).toNat = C.k + 1 := cont_inc_toNat G C hk
  have hread : readBytes (contSwOut (brkS₄ s x) (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4) := by
    rw [hincTo]
    simpa only [contSwOut, State.bind, brkS₄, brkS₃, brkS₂, brkS₁] using hread0
  have hread35 : readBytes (contMidS C (brkS₄ s x) (hlastIncV C) (hlastNepV G) G.ep v
      (contIx G C)).mem ((G.b - 1) + v.toNat) 1 = some [contB35 G v] := by
    have hq : v.toNat - 1 < G.n := by
      have hpos := entryPos_lt G hk
      omega
    have hmid := contMidS_docByte G C s (brkS₄ s x) hInv rfl (hlastIncV C) (hlastNepV G)
      G.ep v (contIx G C) hq
    have hb : 1 ≤ G.b := G.bPos
    rw [show (G.b - 1) + v.toNat = G.b + (v.toNat - 1) from by omega]
    simpa only [contB35] using hmid
  exact contBrkHeadLeafSeg G C s hInv hblock h8 h91 h123 h93 hne91 hincq hnepq
    (cont_ult_one G C hk) h5 (cont_hi63 G C hk) hread hidx htok hgap hugt hread35 hbit
    (HcontHeadByte.toRoute rfl hb) hendq h8q

/-- **`NodeBlock19 → NodeBlock11 → LeafBlock9 → sw.default.i` plus the suffix.**  The
`.defaultValueBracketHigh` class's four pivots and the payload's document row: twelve
links.  This is the letters route's `'a'` class. -/
noncomputable def bhHeadChain_of_lane {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
    (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 0)
    (hne93 : evalICmp .eq x (BitVec.ofNat 8 93) = 0)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (r : HcontDefaultRow G C s) (hb : HcontHeadByte G r.v) :
    HcontHeadChain G C s x := by
  obtain ⟨v, hread0, _hv1, hvle, hugt, _hclass⟩ := r
  have h8q : lookupName (bhS₄ s x).env "%8" = some (.int 8 x) := by
    simp only [bhS₄, bhS₃, bhS₂, bhS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [evalOperand] using h8
  have hincq : evalOperand (bhS₄ s x) (.reg "%inc.i") =
      some (.int 64 (hlastIncV C)) := by
    simp only [evalOperand, bhS₄, bhS₃, bhS₂, bhS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [hlastIncV] using hInv.inc_reg
  have hnepq : evalOperand (bhS₄ s x) (.reg "%nep") =
      some (.int 64 (hlastNepV G)) := by
    simp only [evalOperand, bhS₄, bhS₃, bhS₂, bhS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [hlastNepV] using
      hInv.regs ("%nep", .int 64 (hlastNepV G)) (by simp [walkStaticRegs])
  have h5q : lookupName (bhS₄ s x).env "%5" = some (.ptr G.ep) := by
    simp only [bhS₄, bhS₃, bhS₂, bhS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.ptrs.2.1
  have hidxq : lookupName (bhS₄ s x).env "%idxprom.i" =
      some (.int 64 (contIx G C)) := by
    simp only [bhS₄, bhS₃, bhS₂, bhS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [contIx] using hInv.idx_reg
  have htokq : lookupName (bhS₄ s x).env "%t352.i" = some (.ptr C.stage.tok) := by
    simp only [bhS₄, bhS₃, bhS₂, bhS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%t352.i", .ptr C.stage.tok) (by simp [walkStaticRegs])
  have hgapq : lookupName (bhS₄ s x).env "%gap.i" = some (.ptr (C.stage.tok + 20)) := by
    simp only [bhS₄, bhS₃, bhS₂, bhS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%gap.i", .ptr (C.stage.tok + 20)) (by simp [walkStaticRegs])
  have hendq : lookupName (bhS₄ s x).env "%end.i" = some (.ptr (C.stage.tok + 8)) := by
    simp only [bhS₄, bhS₃, bhS₂, bhS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%end.i", .ptr (C.stage.tok + 8)) (by simp [walkStaticRegs])
  have h5 : lookupName (contSwOut (bhS₄ s x) (hlastIncV C) (hlastNepV G)).env "%5" =
      some (.ptr G.ep) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%5") _ _ (by decide)]
    exact h5q
  have hidx : lookupName (contSwOut (bhS₄ s x) (hlastIncV C) (hlastNepV G)).env
      "%idxprom.i" = some (.int 64 (contIx G C)) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%idxprom.i") _ _ (by decide)]
    exact hidxq
  have htok : lookupName (contSwOut (bhS₄ s x) (hlastIncV C) (hlastNepV G)).env
      "%t352.i" = some (.ptr C.stage.tok) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%t352.i") _ _ (by decide)]
    exact htokq
  have hgap : lookupName (contSwOut (bhS₄ s x) (hlastIncV C) (hlastNepV G)).env
      "%gap.i" = some (.ptr (C.stage.tok + 20)) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%gap.i") _ _ (by decide)]
    exact hgapq
  have hincTo : (hlastIncV C).toNat = C.k + 1 := cont_inc_toNat G C hk
  have hread : readBytes (contSwOut (bhS₄ s x) (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4) := by
    rw [hincTo]
    simpa only [contSwOut, State.bind, bhS₄, bhS₃, bhS₂, bhS₁] using hread0
  have hread35 : readBytes (contMidS C (bhS₄ s x) (hlastIncV C) (hlastNepV G) G.ep v
      (contIx G C)).mem ((G.b - 1) + v.toNat) 1 = some [contB35 G v] := by
    have hq : v.toNat - 1 < G.n := by
      have hpos := entryPos_lt G hk
      omega
    have hmid := contMidS_docByte G C s (bhS₄ s x) hInv rfl (hlastIncV C) (hlastNepV G)
      G.ep v (contIx G C) hq
    have hb : 1 ≤ G.b := G.bPos
    rw [show (G.b - 1) + v.toNat = G.b + (v.toNat - 1) from by omega]
    simpa only [contB35] using hmid
  exact contBhHeadLeafSeg G C s hInv hblock h8 h91 h123 h93 hne93 hincq hnepq
    (cont_ult_one G C hk) h5 (cont_hi63 G C hk) hread hidx htok hgap hugt hread35 hbit
    (HcontHeadByte.toRoute rfl hb) hendq h8q

/-- **`NodeBlock19 → NodeBlock17 → LeafBlock13 → sw.default.i` plus the suffix.**  The
`.defaultValueBrace` class's four pivots — the byte `124` — and the payload's document row:
twelve links.  This is the brace class's chain, at `contBrcHeadSeg`; it was the one
head-switch class of the default arm whose chain had no `_of_lane` wrapper. -/
noncomputable def brcHeadChain_of_lane {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1)
    (hne123 : evalICmp .eq x (BitVec.ofNat 8 123) = 0)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (r : HcontDefaultRow G C s) (hb : HcontHeadByte G r.v) :
    HcontHeadChain G C s x := by
  obtain ⟨v, hread0, _hv1, hvle, hugt, _hclass⟩ := r
  have h8q : lookupName (brcS₄ s x).env "%8" = some (.int 8 x) := by
    simp only [brcS₄, brcS₃, brcS₂, brcS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [evalOperand] using h8
  have hincq : evalOperand (brcS₄ s x) (.reg "%inc.i") =
      some (.int 64 (hlastIncV C)) := by
    simp only [evalOperand, brcS₄, brcS₃, brcS₂, brcS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [hlastIncV] using hInv.inc_reg
  have hnepq : evalOperand (brcS₄ s x) (.reg "%nep") =
      some (.int 64 (hlastNepV G)) := by
    simp only [evalOperand, brcS₄, brcS₃, brcS₂, brcS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [hlastNepV] using
      hInv.regs ("%nep", .int 64 (hlastNepV G)) (by simp [walkStaticRegs])
  have h5q : lookupName (brcS₄ s x).env "%5" = some (.ptr G.ep) := by
    simp only [brcS₄, brcS₃, brcS₂, brcS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.ptrs.2.1
  have hidxq : lookupName (brcS₄ s x).env "%idxprom.i" =
      some (.int 64 (contIx G C)) := by
    simp only [brcS₄, brcS₃, brcS₂, brcS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    simpa only [contIx] using hInv.idx_reg
  have htokq : lookupName (brcS₄ s x).env "%t352.i" = some (.ptr C.stage.tok) := by
    simp only [brcS₄, brcS₃, brcS₂, brcS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%t352.i", .ptr C.stage.tok) (by simp [walkStaticRegs])
  have hgapq : lookupName (brcS₄ s x).env "%gap.i" = some (.ptr (C.stage.tok + 20)) := by
    simp only [brcS₄, brcS₃, brcS₂, brcS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%gap.i", .ptr (C.stage.tok + 20)) (by simp [walkStaticRegs])
  have hendq : lookupName (brcS₄ s x).env "%end.i" = some (.ptr (C.stage.tok + 8)) := by
    simp only [brcS₄, brcS₃, brcS₂, brcS₁, State.bind]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hInv.regs ("%end.i", .ptr (C.stage.tok + 8)) (by simp [walkStaticRegs])
  have h5 : lookupName (contSwOut (brcS₄ s x) (hlastIncV C) (hlastNepV G)).env "%5" =
      some (.ptr G.ep) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%5") _ _ (by decide)]
    exact h5q
  have hidx : lookupName (contSwOut (brcS₄ s x) (hlastIncV C) (hlastNepV G)).env
      "%idxprom.i" = some (.int 64 (contIx G C)) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%idxprom.i") _ _ (by decide)]
    exact hidxq
  have htok : lookupName (contSwOut (brcS₄ s x) (hlastIncV C) (hlastNepV G)).env
      "%t352.i" = some (.ptr C.stage.tok) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%t352.i") _ _ (by decide)]
    exact htokq
  have hgap : lookupName (contSwOut (brcS₄ s x) (hlastIncV C) (hlastNepV G)).env
      "%gap.i" = some (.ptr (C.stage.tok + 20)) := by
    simp only [contSwOut, State.bind]
    rw [lookupName_cons_ne (k := "%cmp343.i") (n := "%gap.i") _ _ (by decide)]
    exact hgapq
  have hincTo : (hlastIncV C).toNat = C.k + 1 := cont_inc_toNat G C hk
  have hread : readBytes (contSwOut (brcS₄ s x) (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4) := by
    rw [hincTo]
    simpa only [contSwOut, State.bind, brcS₄, brcS₃, brcS₂, brcS₁] using hread0
  have hread35 : readBytes (contMidS C (brcS₄ s x) (hlastIncV C) (hlastNepV G) G.ep v
      (contIx G C)).mem ((G.b - 1) + v.toNat) 1 = some [contB35 G v] := by
    have hq : v.toNat - 1 < G.n := by
      have hpos := entryPos_lt G hk
      omega
    have hmid := contMidS_docByte G C s (brcS₄ s x) hInv rfl (hlastIncV C) (hlastNepV G)
      G.ep v (contIx G C) hq
    have hb : 1 ≤ G.b := G.bPos
    rw [show (G.b - 1) + v.toNat = G.b + (v.toNat - 1) from by omega]
    simpa only [contB35] using hmid
  exact contBrcHeadLeafSeg G C s hInv hblock h8 h91 h123 h125 hne123 hincq hnepq
    (cont_ult_one G C hk) h5 (cont_hi63 G C hk) hread hidx htok hgap hugt hread35 hbit
    (HcontHeadByte.toRoute rfl hb) hendq h8q

/-! ### The arms, at the chain the payload's row produced

Three arms share the default arm's document row: the scan-free letters route, its `'f'`
leaf, and the class-C span whose bytes are `110 … 125`.  Each takes the chain the producers
above return and a three-link tail at the seam it names, and each runs the real
`.dispatch`.  So the payload's `lane` group now reaches the default arm's head chain.  The
tails themselves are `JsonStage2WalkDispatchLettersRows`': the chain carries the seam's
pair and the root word's transport, so the letters and `'f'` arms are handed the callee
rows in place of a tail, and the class-C arm the span's endpoint's cells beside the rows.
-/

/-- **The letters arm, from the payload's chain.** -/
noncomputable def hcontArm_letters_of_lane {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0)
    (ch : HcontHeadChain G C s x)
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ ch.Cm))
      (LetS413 ch.sm x) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  hcontArm_letters_of_staging C s hInv (hlastByte_of_reg8 hInv h8) hbit h110 hne102
    ch.seg ch.hnH ch.hblock ch.hk ch.h8 hTail ht htk htok

/-- **The `'f'` arm, from the payload's chain.** -/
noncomputable def hcontArm_fLetter_of_lane {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (h102 : evalICmp .eq x (BitVec.ofNat 8 102) = 1)
    (ch : HcontHeadChain G C s x)
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (FC₄₁₃ ch.Cm)
      (FS413 ch.sm x) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  hcontArm_fLetter_of_staging C s hInv (hlastByte_of_reg8 hInv h8) hbit h110 h102
    ch.seg ch.hnH ch.hblock ch.hk ch.h8 hTail ht htk htok

/-- **The class-C arm, from the payload's chain** and the byte's own span. -/
noncomputable def hcontArm_classC_of_lane {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1)
    (ch : HcontHeadChain G C s x)
    {Cs : WalkCarry G} {ss : State} {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G ch.Cm ch.sm Cs ss nS)
    (hs : Cs.block = "if.then413.i") (hnS : nS ≤ 5)
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  hcontArm_classC_of_staging C s hInv (hlastByte_of_reg8 hInv h8) h110 h125
    ch.seg ch.hnH ch.hblock ch.hk ch.h8 hSpan hs hnS hTail ht htk htok

/-- **The letters dispatch, from the payload's chain.** -/
theorem walkDispatch_at_letters_of_lane {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0)
    (ch : HcontHeadChain G C s x)
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ ch.Cm))
      (LetS413 ch.sm x) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_letters_of_lane hInv h8 hbit h110 hne102 ch hTail ht htk htok)

/-- **The `'f'` dispatch, from the payload's chain.** -/
theorem walkDispatch_at_fLetter_of_lane {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1)
    (h102 : evalICmp .eq x (BitVec.ofNat 8 102) = 1)
    (ch : HcontHeadChain G C s x)
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (FC₄₁₃ ch.Cm)
      (FS413 ch.sm x) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_fLetter_of_lane hInv h8 hbit h110 h102 ch hTail ht htk htok)

/-- **The class-C dispatch, from the payload's chain and the byte's span.** -/
theorem walkDispatch_at_classC_of_lane {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
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
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = C.k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_classC_of_lane hInv h8 h110 h125 ch hSpan hs hnS hTail ht htk htok)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.contMidS_docByte
#print axioms LeanLLVM.Refinement.WalkScope.lowHeadChain_of_lane
#print axioms LeanLLVM.Refinement.WalkScope.midHeadChain_of_lane
#print axioms LeanLLVM.Refinement.WalkScope.othHeadChain_of_lane
#print axioms LeanLLVM.Refinement.WalkScope.brkHeadChain_of_lane
#print axioms LeanLLVM.Refinement.WalkScope.bhHeadChain_of_lane
#print axioms LeanLLVM.Refinement.WalkScope.brcHeadChain_of_lane
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_letters_of_lane
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_fLetter_of_lane
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_classC_of_lane
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_letters_of_lane
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_fLetter_of_lane
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_classC_of_lane

end WalkScope
end LeanLLVM.Refinement
