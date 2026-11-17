/-
# The plain-value class, from the staging

`HcontArm.scalar` (`JsonStage2WalkDispatchHcontArms`) and `LastEntryArm.scalar`
(`JsonStage2WalkDispatchArms`) are the head switch's plain-value arm: the four pivots
`NodeBlock5 → NodeBlock → LeafBlock1 → sw.default.i`, the count test's succeeding arm at
a continuing entry and its failing one at the last, the whitespace check's no-run class,
and the tag test's *true* arm — a digit or `-`, so `if.end372.i` leaves for
`if.then413.i` with kind `7` and the scan-free tail follows.  The continuing composition
is `walkRevolutionMergeSegScalar` (`JsonStage2WalkHcontScalar`), its bundle
`HcontScalarFacts`; the terminal composition is `scalarMerge_at`
(`JsonStage2WalkDispatchScalar`) at the prefix `scalarPrefixSeg`
(`JsonStage2WalkDispatchScalarPrefix`).

This module produces both arms at every state that carries the invariant.

## What is derived, and what is taken

The head byte's class is four bits on the document's byte, and the byte itself is the
invariant's: `WalkInv.iter.reg8` names `%8` at `hlastByte G C`, so once the class fixes
which byte it is, the cell follows (`cont_reg8_at`).  The remaining rows are the walk's
own: the counts, the count test, the lane's pointer, the entry's index, the token
record's two cells and the byte before the entry's end with its read.  All of those are
*derived*, and the two bundles' tables name each one.

| row | continuing scalar | last-entry scalar |
|---|---|---|
| `h8` | `cont_reg8_at` at the class's byte | the same |
| `h91` | `slt_one_of_toInt_le` from `h58`: the order passes 58 before 91 | the same |
| `hinc`, `hnep` | `WalkInv.inc_reg` and `%nep`'s `walkStaticRegs` row, peeled through `scS₄` | derived by the arm's own prefix (`scalarHeadSeg`) |
| `hnext` | `cont_ult_one` from the consumer's guard | — (the last entry fails the test, and the prefix derives it) |
| `h5`, `hi63` | `WalkPtrs` and `cont_hi63` | — |
| `ix`, `hidx5` | `WalkInv.idx_reg`, peeled through `scS₅` | — |
| `htok5`, `hgap5` | `WalkInv.regs`'s two rows, peeled through `scS₅` | — |
| `b35`, `hread35` | `contB35 G v` and `cont_hread35` (the scalar route's bound state has the high-byte route's memory, `sEnd_mem`) | `G.bs.getD (G.n - 1) 0` and `scalarEndS_docByte` |
| `hzread` | — | `WalkInv.log_base` across the token record's four stores (`token_log_sep`) |
| `hev64` | — | `WalkGeom.evLt` |

The document's content is taken, each with what supplies it:

| premise | what supplies it |
|---|---|
| `hx` | **the head byte**: the class's witness is `hlastByte G C`; a caller holding a literal byte has `hlastByte_of_reg8` |
| `h44`, `h58`, `hne44` | **the class's three bits**: `44 ≤ %8`, `%8 < 58` and `%8 ≠ 44`, the left-open interval a digit or `-` stands in |
| `hbit` | **the tag test**: `%8 = 45` or `%8 + 208 <u 10`, so `.` and `/` are excluded |
| `v`, `hread`, `hspan` | **the next entry's lane word and its order** (continuing only): `%5`'s pointer is the invariant's, the word is `G.ent`'s |
| `hugt` | **the entry's non-emptiness** (continuing only) |
| `hb13`, `hb32`, `hbne32` | **the byte before the entry's end and its no-run class**: the document's content |
| the three calls, their pre/postconditions and answers | **the tail's callees** at the argument lists the walk stages |
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchLaneOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchSpansOfStaging
import LeanLLVM.Refinement.JsonStage2WalkHcontScalar
import LeanLLVM.Refinement.JsonStage2WalkDispatchArms
import LeanLLVM.Refinement.JsonStage2WalkDispatchHcontArms
import LeanLLVM.Refinement.JsonStage2WalkDispatchScalar

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The cells the scalar prefix reads

Each is a peel: the four pivots and the count test's cell bind their own names, and none
of them is a carrier the invariant or the staging fixes. -/

/-- `%inc.i` at the count test's block is the loop head's. -/
theorem scS4_envInc (s : State)
    (x : BitVec 8) (inc : BitVec 64)
    (h : lookupName s.env "%inc.i" = some (.int 64 inc)) :
    lookupName (scS₄ s x).env "%inc.i" = some (.int 64 inc) := by
  simp only [scS₄, scS₃, scS₂, scS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- `%nep` at the count test's block is the loop head's. -/
theorem scS4_envNep (s : State) (x : BitVec 8) (nep : BitVec 64)
    (h : lookupName s.env "%nep" = some (.int 64 nep)) :
    lookupName (scS₄ s x).env "%nep" = some (.int 64 nep) := by
  simp only [scS₄, scS₃, scS₂, scS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- `%5` at the bound's `phi` is the invariant's positions table. -/
theorem scS5_env5 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (hInv : WalkInv G C s) :
    lookupName (scS₅ s x inc nep).env "%5" = some (.ptr G.ep) := by
  simp only [scS₅, scS₄, scS₃, scS₂, scS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact hInv.ptrs.2.1

/-- `%idxprom.i` at the bound's `phi` is the loop head's. -/
theorem scS5_envIdx (s : State) (x : BitVec 8) (inc nep : BitVec 64) (ix : BitVec 64)
    (h : lookupName s.env "%idxprom.i" = some (.int 64 ix)) :
    lookupName (scS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix) := by
  simp only [scS₅, scS₄, scS₃, scS₂, scS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- `%t352.i` at the bound's `phi` is the loop head's token record. -/
theorem scS5_envTok {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64)
    (h : lookupName s.env "%t352.i" = some (.ptr C.stage.tok)) :
    lookupName (scS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok) := by
  simp only [scS₅, scS₄, scS₃, scS₂, scS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- `%gap.i` at the bound's `phi` is the loop head's. -/
theorem scS5_envGap {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64)
    (h : lookupName s.env "%gap.i" = some (.ptr (C.stage.tok + 20))) :
    lookupName (scS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20)) := by
  simp only [scS₅, scS₄, scS₃, scS₂, scS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-! ### The continuing plain-value bundle

The bundle's rows are the class's four bits and the document's byte; everything else is
this module's.  `sEnd_mem` is what lets the byte before the entry's end be read at the
scalar route's own bound state: the route's two token stores are the high-byte route's,
at the same addresses. -/

/-- **The plain-value prefix's cells**: the document's class at the head's byte, the lane's
word, and the head state's own cells at the four pivots, the count test and the byte before
the entry's end.  It is the bundle's half above the tail — a row group, not a bundle: no
call outcome, no event and no segment. -/
structure HcontScalarPrefix {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  x : BitVec 8
  h8 : evalOperand s (.reg "%8") = some (.int 8 x)
  hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1
  h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0
  h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1
  hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0
  hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
    evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1
  inc : BitVec 64
  nep : BitVec 64
  hinc : evalOperand (scS₄ s x) (.reg "%inc.i") = some (.int 64 inc)
  hnep : evalOperand (scS₄ s x) (.reg "%nep") = some (.int 64 nep)
  hnext : evalICmp .ult inc nep = 1
  ep : Nat
  v : BitVec 32
  h5 : lookupName (scS₅ s x inc nep).env "%5" = some (.ptr ep)
  hi63 : inc.toNat < 2 ^ 63
  hread : readBytes (scS₅ s x inc nep).mem (ep + inc.toNat * 4) 4 =
    some (natToBytes v.toNat 4)
  ix : BitVec 64
  hidx5 : lookupName (scS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix)
  htok5 : lookupName (scS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok)
  hgap5 : lookupName (scS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20))
  hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1
  b35 : UInt8
  hread35 : readBytes (sEnd C s x inc nep ep v ix).mem ((G.b - 1) + v.toNat) 1 =
    some [b35]
  hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0
  hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0
  hbne32 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 0

/-- **The prefix's cells, from the entry's evidence.**  The class's four bits and the
entry's lane are the document's; `h8`, `hlt91`, the counts, the pointer, the index, the
token's two cells and the byte before the entry's end are the head invariant's.
`sEnd_mem` is what lets that byte be read at the scalar route's own bound state: the
route's two token stores are the high-byte route's, at the same addresses. -/
def hcontScalarPrefix_of_inv {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (hx : x = hlastByte G C)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
    (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1)
    {v : BitVec 32}
    (hread : readBytes (scS₅ s x (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4))
    (hspan : v.toNat ≤ entryPos G (C.k + 1))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat)
      (BitVec.ofNat 64 (entryPos G C.k)) = 1)
    (hb13 : evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 32) = 0)
    (hbne32 : evalICmp .eq (cont35 (contB35 G v)) (BitVec.ofNat 8 32) = 0) :
    HcontScalarPrefix G C s := by
  -- the lane is above the entry's index, so the byte before the entry's end is inside
  have hgt : entryPos G C.k < v.toNat := contLane_gt G C hk hugt
  have hv1 : 1 ≤ v.toNat := by omega
  -- the document's byte, across the route's own two token stores (`sEnd_mem`)
  have hread35 : readBytes (sEnd C s x (hlastIncV C) (hlastNepV G) G.ep v (contIx G C)).mem
      ((G.b - 1) + v.toNat) 1 = some [contB35 G v] := by
    rw [sEnd_mem]
    exact cont_hread35 (G := G) (C := C) (s := s) hInv hk (v := v) (k := v.toNat - 1)
      hspan (by omega)
  exact
    { x := x
      h8 := cont_reg8_at hInv hx
      hlt91 := slt_one_of_toInt_le (by decide) h58
      h44 := h44
      h58 := h58
      hne44 := hne44
      hbit := hbit
      inc := hlastIncV C
      nep := hlastNepV G
      hinc := by
        show evalOperand (scS₄ s x) (.reg "%inc.i") = some (.int 64 (hlastIncV C))
        simp only [evalOperand]
        exact scS4_envInc s x (hlastIncV C) hInv.inc_reg
      hnep := by
        show evalOperand (scS₄ s x) (.reg "%nep") = some (.int 64 (hlastNepV G))
        simp only [evalOperand]
        exact scS4_envNep s x (hlastNepV G)
          (hInv.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs]))
      hnext := cont_ult_one G C hk
      ep := G.ep
      v := v
      h5 := scS5_env5 C s x (hlastIncV C) (hlastNepV G) hInv
      hi63 := cont_hi63 G C hk
      hread := hread
      ix := contIx G C
      hidx5 := scS5_envIdx s x (hlastIncV C) (hlastNepV G) (contIx G C) hInv.idx_reg
      htok5 := scS5_envTok C s x (hlastIncV C) (hlastNepV G) (cont_static_tok hInv)
      hgap5 := scS5_envGap C s x (hlastIncV C) (hlastNepV G)
        (hInv.regs ("%gap.i", .ptr (C.stage.tok + 20)) (by simp [walkStaticRegs]))
      hugt := hugt
      b35 := contB35 G v
      hread35 := hread35
      hb13 := hb13
      hb32 := hb32
      hbne32 := hbne32 }

/-- **The plain-value continuing bundle, from the prefix and the tail.** -/
def hcontScalarFacts_of_staging {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (pre : HcontScalarPrefix G C s)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) {cA rdv xA : BitVec 32}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (ContAC₇ C))
      (scSeamS C s pre.x pre.inc pre.nep pre.ep pre.v pre.ix pre.b35)
      (TailCarryEnd (HeadC₄₁₃ (ContAC₇ C)) ev)
      (scEnd C s pre.x pre.inc pre.nep pre.ep pre.v pre.ix pre.b35 r₁ r₂ r₃
        cA rdv xA) 3) :
    HcontScalarFacts G C s :=
  { x := pre.x
    h8 := pre.h8
    hlt91 := pre.hlt91
    h44 := pre.h44
    h58 := pre.h58
    hne44 := pre.hne44
    hbit := pre.hbit
    inc := pre.inc
    nep := pre.nep
    hinc := pre.hinc
    hnep := pre.hnep
    hnext := pre.hnext
    ep := pre.ep
    v := pre.v
    h5 := pre.h5
    hi63 := pre.hi63
    hread := pre.hread
    ix := pre.ix
    hidx5 := pre.hidx5
    htok5 := pre.htok5
    hgap5 := pre.hgap5
    hugt := pre.hugt
    b35 := pre.b35
    hread35 := pre.hread35
    hb13 := pre.hb13
    hb32 := pre.hb32
    hbne32 := pre.hbne32
    r₁ := r₁
    r₂ := r₂
    r₃ := r₃
    ev := ev
    cA := cA
    rdv := rdv
    xA := xA
    hTail := hTail }

/-- **The plain-value continuing arm, from the staging.** -/
def hcontArm_scalar_of_staging {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (hx : x = hlastByte G C)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
    (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1)
    {v : BitVec 32}
    (hread : readBytes (scS₅ s x (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4))
    (hspan : v.toNat ≤ entryPos G (C.k + 1))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat)
      (BitVec.ofNat 64 (entryPos G C.k)) = 1)
    (hb13 : evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 32) = 0)
    (hbne32 : evalICmp .eq (cont35 (contB35 G v)) (BitVec.ofNat 8 32) = 0)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) {cA rdv xA : BitVec 32}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (ContAC₇ C))
      (scSeamS C s x (hlastIncV C) (hlastNepV G) G.ep v (contIx G C) (contB35 G v))
      (TailCarryEnd (HeadC₄₁₃ (ContAC₇ C)) ev)
      (scEnd C s x (hlastIncV C) (hlastNepV G) G.ep v (contIx G C) (contB35 G v) r₁ r₂ r₃
        cA rdv xA) 3) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .scalar (hcontScalarFacts_of_staging G C s
    (hcontScalarPrefix_of_inv G C s hInv hk hx h44 h58 hne44 hbit hread hspan hugt hb13 hb32
      hbne32) r₁ r₂ r₃ ev (cA := cA) (rdv := rdv) (xA := xA) hTail)

/-- **The plain-value continuing dispatch, from the staging.** -/
theorem walkDispatch_at_scalar_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    {x : BitVec 8} (hx : x = hlastByte G C)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
    (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1)
    {v : BitVec 32}
    (hread : readBytes (scS₅ s x (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4))
    (hspan : v.toNat ≤ entryPos G (C.k + 1))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat)
      (BitVec.ofNat 64 (entryPos G C.k)) = 1)
    (hb13 : evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 32) = 0)
    (hbne32 : evalICmp .eq (cont35 (contB35 G v)) (BitVec.ofNat 8 32) = 0)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) {cA rdv xA : BitVec 32}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (ContAC₇ C))
      (scSeamS C s x (hlastIncV C) (hlastNepV G) G.ep v (contIx G C) (contB35 G v))
      (TailCarryEnd (HeadC₄₁₃ (ContAC₇ C)) ev)
      (scEnd C s x (hlastIncV C) (hlastNepV G) G.ep v (contIx G C) (contB35 G v) r₁ r₂ r₃
        cA rdv xA) 3) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_scalar_of_staging G C s hInv hk hx h44 h58 hne44 hbit hread hspan hugt hb13
      hb32 hbne32 r₁ r₂ r₃ ev (cA := cA) (rdv := rdv) (xA := xA) hTail)

/-! ### The terminal plain-value arm

The last entry's scalar arm carries its rows directly (`LastEntryArm.scalar`), so its
producer supplies the arm rather than a bundle.  Two of its rows are the model's: the
document's last byte across the prefix's token stores, and the log's base word across the
kind store.  The first is `scalarEndS_docByte`; the second is `WalkInv.log_base` and the
staged objects' separation, since the token record and the log are two entries of the
seven the caller stages apart. -/

/-- **The document reads as itself at the terminal bound state.**  `cond.end349.i`'s two
stores are inside the token record, whose staged extent is disjoint from the document's
region, so the memory `scalarEndS` leaves holds the document's bytes. -/
theorem scalarEndS_docByte {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) {x : BitVec 8} {inc nep : BitVec 64} {v : Nat}
    {ix : BitVec 64} {q : Nat} (hq : q < G.n) :
    readBytes (scalarEndS C s x inc nep v ix).mem
      (G.b + q) 1 = some [G.bs.getD q 0] := by
  have hsep := stage2StagedWrites_against C.stage.separate (a := G.b)
    (m := G.n + stage2ReadTail) (by simp [stage2Regions])
    (r := (C.stage.tok, stage2TokenExtent)) (by simp [stage2StagedWrites])
  have htok : stage2TokenExtent = 24 := rfl
  rw [htok] at hsep
  have h4 : (natToBytes (BitVec.ofNat 32 1).toNat 4).length = 4 := natToBytes_length ..
  have h8 : (natToBytes ix.toNat 8).length = 8 := natToBytes_length ..
  simp only [scalarEndS, condEnd349OutAt, scalarS₅, scalarS₄, scalarS₃, scalarS₂, scalarS₁,
    State.bind]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok + 20)
    (v := natToBytes (BitVec.ofNat 32 1).toNat 4) (by rw [h4]; rcases hsep with h | h <;> omega)]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok)
    (v := natToBytes ix.toNat 8) (by rw [h8]; rcases hsep with h | h <;> omega)]
  exact walkDoc_byte G C s hInv (by have h := hInv.alen_le; omega)
    (le_trans hInv.evlen_le G.evRoom) hq

/-- **The token record and the log are separate objects**: both are entries of the seven
the caller stages, at their own extents. -/
theorem token_log_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} :
    C.stage.tok + stage2TokenExtent ≤ C.stage.z ∨
      C.stage.z + stage2LogExtent ≤ C.stage.tok := by
  have h := stagedWrites_sep C.stage.writes_separate (i := 3) (j := 5)
    (by decide) (by decide) (by decide)
  simpa only [stage2StagedWrites, List.getElem_cons_zero, List.getElem_cons_succ]
    using h

/-- **The log's base word survives the terminal prefix's token stores.**  The prefix
writes the token's position and gap (`cond.end349.i`), the token's end (`seamFin`) and the
literal's kind; all four are inside the token record, which is disjoint from the log at
its staged extent, so the word at `%z` is `WalkInv.log_base`'s. -/
theorem scalarSeam_logBase {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) {x : BitVec 8} {inc nep : BitVec 64} {v : Nat}
    {ix : BitVec 64} {b35 : UInt8} :
    readBytes
      (writeBytes (scalarSeam C s x inc nep v ix b35).mem
        (C.stage.tok + 16) (natToBytes (7 : Nat) 4)) C.stage.z 8 =
      some (wordBytes 8 G.ev) := by
  have hsep := token_log_sep (G := G) (C := C)
  have htok : stage2TokenExtent = 24 := rfl
  have hlog : stage2LogExtent = 64 := rfl
  have h4 : (natToBytes (7 : Nat) 4).length = 4 := natToBytes_length ..
  have h8i : (natToBytes ix.toNat 8).length = 8 := natToBytes_length ..
  have h8v : (natToBytes (BitVec.ofNat 64 v).toNat 8).length = 8 :=
    natToBytes_length ..
  have h4g : (natToBytes (BitVec.ofNat 32 1).toNat 4).length = 4 := natToBytes_length ..
  simp only [scalarSeam, seamFin, scalarP37, scalarP39, scalarP41, scalarLand, scalarEndS,
    condEnd349OutAt, scalarS₅, scalarS₄, scalarS₃, scalarS₂, scalarS₁, stateAt, cells,
    State.bind]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok + 16)
    (v := natToBytes (7 : Nat) 4) (by rw [h4]; rcases hsep with h | h <;> omega)]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok + 8)
    (v := natToBytes (BitVec.ofNat 64 v).toNat 8)
    (by rw [h8v]; rcases hsep with h | h <;> omega)]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok + 20)
    (v := natToBytes (BitVec.ofNat 32 1).toNat 4)
    (by rw [h4g]; rcases hsep with h | h <;> omega)]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok)
    (v := natToBytes ix.toNat 8) (by rw [h8i]; rcases hsep with h | h <;> omega)]
  exact hInv.log_base

/-- **The terminal plain-value arm, from the entry's evidence.**  The class's three bits
and its tag test are the document's; `h8`, the byte before the entry's end with its read,
the log's base word and the stream's width are derived. -/
def lastEntryArm_scalar_of_staging {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hnot : ¬ (C.k + 1 < G.nep))
    {x : BitVec 8} (hx : x = hlastByte G C)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
    (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
    (hb13 : evalICmp .slt (head35 (G.bs.getD (G.n - 1) 0)) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (head35 (G.bs.getD (G.n - 1) 0)) (BitVec.ofNat 8 32) = 0)
    (hbne32 : evalICmp .eq (head35 (G.bs.getD (G.n - 1) 0)) (BitVec.ofNat 8 32) = 0)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1)
    (r₁ r₂ r₃ : CallOutcome) {rdv : BitVec 32} {xA : BitVec 32}
    (hreadT : readBytes
      (writeBytes (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
        G.n (BitVec.ofNat 64 (entryPos G C.k))
        (G.bs.getD (G.n - 1) 0)).mem (C.stage.tok + 16) (natToBytes (7 : Nat) 4))
      (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpre₁ : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .int 32 rdv,
       .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst]
      (writeBytes (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
        G.n (BitVec.ofNat 64 (entryPos G C.k))
        (G.bs.getD (G.n - 1) 0)).mem (C.stage.tok + 16) (natToBytes (7 : Nat) 4))
      (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
        G.n (BitVec.ofNat 64 (entryPos G C.k))
        (G.bs.getD (G.n - 1) 0)).next)
    (hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .int 32 rdv,
       .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst]
      (writeBytes (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
        G.n (BitVec.ofNat 64 (entryPos G C.k))
        (G.bs.getD (G.n - 1) 0)).mem (C.stage.tok + 16) (natToBytes (7 : Nat) 4))
      (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
        G.n (BitVec.ofNat 64 (entryPos G C.k))
        (G.bs.getD (G.n - 1) 0)).next = some r₁)
    (hret₁ : r₁.ret = .int 32 xA)
    (hbit0T : evalICmp .eq xA (BitVec.ofNat 32 0) = 0)
    (hpre₂ : s2ScalarValuePre
      [.ptr (TailCarry₂ (ScalarC₁₁ C)).stage.c,
       .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.tok,
       .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.z] r₁.mem r₁.next)
    (hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr (TailCarry₂ (ScalarC₁₁ C)).stage.c,
       .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.tok,
       .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.z] r₁.mem r₁.next = some r₂)
    (hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1))
    (hpre₃ : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .ptr (G.next0 + 8),
       .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst] r₂.mem r₂.next)
    (hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .ptr (G.next0 + 8),
       .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst] r₂.mem r₂.next =
      some r₃) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s := by
  -- the last entry's index, and the document's last byte inside it
  have hk1 : C.k < G.nep := WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)
  have hlast : C.k + 1 = G.nep := by have := hInv.k_le; omega
  have hnep1 : 1 ≤ G.nep := by omega
  have hn1 : 1 ≤ G.n := le_trans hnep1 G.nep_le
  have hread35 :
      readBytes (scalarEndS C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
        G.n (BitVec.ofNat 64 (entryPos G C.k))).mem
        ((G.b - 1) + G.n) 1 = some [G.bs.getD (G.n - 1) 0] := by
    have hq : G.n - 1 < G.n := by omega
    have hb : 1 ≤ G.b := G.bPos
    rw [show (G.b - 1) + G.n = G.b + (G.n - 1) from by omega]
    exact scalarEndS_docByte G C s hInv (x := x) (q := G.n - 1) hq
  exact
    .scalar (cont_reg8_at hInv hx) (slt_one_of_toInt_le (by decide) h58) h44 h58 hne44
      hread35 hb13 hb32 hbne32 hbit r₁ r₂ r₃ hreadT hpre₁ hcall₁ hret₁ hbit0T
      (scalarSeam_logBase G C s hInv (x := x)) hpre₂ hcall₂ hret₂ G.evLt hpre₃ hcall₃

/-- **The terminal plain-value dispatch, from the staging.**  The arm's producer and
`LastEntryArm.dispatch` at its composition. -/
theorem walkDispatch_at_scalar_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    {x : BitVec 8} (hx : x = hlastByte G C)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
    (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
    (hb13 : evalICmp .slt (head35 (G.bs.getD (G.n - 1) 0)) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (head35 (G.bs.getD (G.n - 1) 0)) (BitVec.ofNat 8 32) = 0)
    (hbne32 : evalICmp .eq (head35 (G.bs.getD (G.n - 1) 0)) (BitVec.ofNat 8 32) = 0)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1)
    (r₁ r₂ r₃ : CallOutcome) {rdv : BitVec 32} {xA : BitVec 32}
    (hreadT : readBytes
      (writeBytes (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
        G.n (BitVec.ofNat 64 (entryPos G C.k))
        (G.bs.getD (G.n - 1) 0)).mem (C.stage.tok + 16) (natToBytes (7 : Nat) 4))
      (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpre₁ : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .int 32 rdv,
       .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst]
      (writeBytes (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
        G.n (BitVec.ofNat 64 (entryPos G C.k))
        (G.bs.getD (G.n - 1) 0)).mem (C.stage.tok + 16) (natToBytes (7 : Nat) 4))
      (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
        G.n (BitVec.ofNat 64 (entryPos G C.k))
        (G.bs.getD (G.n - 1) 0)).next)
    (hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .int 32 rdv,
       .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst]
      (writeBytes (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
        G.n (BitVec.ofNat 64 (entryPos G C.k))
        (G.bs.getD (G.n - 1) 0)).mem (C.stage.tok + 16) (natToBytes (7 : Nat) 4))
      (scalarSeam C s x (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
        G.n (BitVec.ofNat 64 (entryPos G C.k))
        (G.bs.getD (G.n - 1) 0)).next = some r₁)
    (hret₁ : r₁.ret = .int 32 xA)
    (hbit0T : evalICmp .eq xA (BitVec.ofNat 32 0) = 0)
    (hpre₂ : s2ScalarValuePre
      [.ptr (TailCarry₂ (ScalarC₁₁ C)).stage.c,
       .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.tok,
       .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.z] r₁.mem r₁.next)
    (hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr (TailCarry₂ (ScalarC₁₁ C)).stage.c,
       .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.tok,
       .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.z] r₁.mem r₁.next = some r₂)
    (hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1))
    (hpre₃ : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .ptr (G.next0 + 8),
       .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst] r₂.mem r₂.next)
    (hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .ptr (G.next0 + 8),
       .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst] r₂.mem r₂.next =
      some r₃) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_scalar_of_staging G C s hInv hblock hnot hx h44 h58 hne44 hb13 hb32 hbne32
      hbit r₁ r₂ r₃ (rdv := rdv) (xA := xA) hreadT hpre₁ hcall₁ hret₁ hbit0T hpre₂ hcall₂
      hret₂ hpre₃ hcall₃)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.scS4_envInc
#print axioms LeanLLVM.Refinement.WalkScope.scS5_env5
#print axioms LeanLLVM.Refinement.WalkScope.hcontScalarPrefix_of_inv
#print axioms LeanLLVM.Refinement.WalkScope.hcontScalarFacts_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_scalar_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_scalar_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.scalarEndS_docByte
#print axioms LeanLLVM.Refinement.WalkScope.token_log_sep
#print axioms LeanLLVM.Refinement.WalkScope.scalarSeam_logBase
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_scalar_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_scalar_last_of_staging

end WalkScope
end LeanLLVM.Refinement
