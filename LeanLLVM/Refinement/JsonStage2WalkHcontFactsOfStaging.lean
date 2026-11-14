/-
# The continuing entry's facts, from the staging

`WalkContinueFacts` (`JsonStage2WalkPremisesOfStaging`) is the continuing entry's
obstruction: `HcontFacts` at every head state with an entry left.  `HcontFacts`
(`JsonStage2WalkRevolution`) is the bundle `walkRevolution_seg` consumes, field for field;
the path it describes is `hcontPrefixSeg`'s (`JsonStage2WalkRevolutionPrefix`) — the four
high-byte pivots, `sw.default.i`'s *succeeding* arm, the bound's `phi`, the whitespace
check at the entry's end and the token's end — and this module is the twin of
`hlastFacts_of_staging`: the same three sources (the invariant's clauses, the document's
content and the staging's addresses) producing the continuing bundle instead of the last
entry's.

## The twin's shape

`hlastFacts_of_staging` is a `def`, because the bundle is a `Type`: its first member of
each group is a *witness* the later fields are stated at.  This is a `def` for the same
reason, and it takes the evidence the recomposed prefix takes.  Three differences, each a
consequence of the bundles' statements rather than a choice made here:

* **There is no `hblock`.**  The last entry's producer read the block once, for the
  refill's `walkLoopHead_inner_pos` — the `1 ≤ C.inner` its `hinner` field needed.  The
  continuing bundle carries no inner budget, so no field of it reads the block, and the
  premise is dropped rather than bound and discarded.
* **`hk` is taken, and it is load-bearing.**  `C.k + 1 < G.nep` is what makes `hnext`
  provable (see below) and what bounds the lane's index (`hi63`).  It is *not* a premise
  the bundle's fields discard: two of them read it.
* **The scan's traversal is not part of the prefix group.**  `HcontFacts` states
  `walkScanRounds457`'s three hypotheses (`hround`, `hguard`, `hbyte`) and the token's
  register at its exit (`htok`) instead, because the continuing entry's scan runs over the
  entry's span; they arrive as premises, and `htok` is the one obstruction no staging
  evidence closes.

## `hnext` is the first field of this bundle that is derived, not supplied

The field used to be `hge : evalICmp .ult inc nep = 0`, and it was the old bundle's one
obstruction: at a real head state `%inc.i = C.k + 1` and `%nep = G.nep`
(`WalkInv.blockIndex` and the header's store), so `= 0` is `¬ (C.k + 1 < G.nep)` while the
consumer's hypothesis is that inequality — the bundle was uninhabited and
`walkRevolution_seg` vacuous.  The recomposition states the field at the value a continuing
entry has, `= 1`, and that value is **arithmetic on the consumer's own hypothesis**:
`hinc`/`hnep` pin the counts to `ofNat 64 (C.k + 1)` and `ofNat 64 G.nep`, and `hk` says
the first is below the second, so the test's word is `1` (`cont_ult_one`).  The old
producer could not supply this field's *false* value from any staging evidence; the new one
derives its true value from `hk`.  It is the first field of either bundle that is derived
from a consumer hypothesis rather than read off the input.

## The map, per group

Produced · reduced to a named premise · premised correctly (the model cannot supply it) ·
supplied as a named premise.

| group | status |
|---|---|
| the head's byte (`x`, `h8`) | **produced**: `hInv.iter.reg8` is the field, and the witness is `hlastByte G C` |
| the four pivot bits (`hlt91`, `hlt123`, `hlt125`, `hne125`) | **premised correctly: the document's.**  Four of the eight class bits on the head's byte |
| the entry counts' witnesses and their head facts (`inc`, `nep`, `hinc`, `hnep`) | **produced**: the witnesses are the loop's values (`hlastIncV C`, `hlastNepV G`) and the cells are the loop head's own, peeled down to `headAS₄` (`headAS4_envInc`, `headAS4_envNep`) |
| the count test's value (`hnext`) | **produced**: `cont_ult_one` from `hk` — the first derived-not-supplied field of this bundle; see the section above |
| the next entry's lane (`ep`, `v`, `hread`) | **premised correctly: the document's.**  The positions table's address is the invariant's (`%5` is `WalkPtrs`'s `some (.ptr G.ep)`), but the word at the next entry's index and the read that fetches it are the document's |
| the lane index's width (`hi63`) | **produced**: `cont_hi63`, arithmetic on `hk` and `G.nep_le`'s `G.nep ≤ 2 ^ 32` |
| the default arm's remaining cells (`ix`, `hidx5`, `htok5`, `hgap5`) | **produced**: `%idxprom.i` and `%t352.i` are the staging's at the loop head (`hidxS`, `htokS`) and `%gap.i` is `regs`'s, peeled to the succeeding arm's state (`contAS5_envIdx`, `contAS5_envTok`, `contAS5_envGap`) |
| the entry's non-emptiness (`hugt`) | **premised correctly: the document's.**  The next entry's position against this entry's index is a relation between the lane's word and the entry stream; neither the invariant nor the staging fixes it |
| the byte before the entry's end (`b35`, `hread35`) | **premised correctly: the document's.**  `land.lhs.true357.i` reads the document at `%cond350.i - 1`; the staging fixes the address, not the byte |
| that byte's three pivot bits (`hb13`, `hb32`, `hbne13`) | **premised correctly: the document's**, and they are the class the price's longest path names: no whitespace run, so the token's end is reached directly |
| the seam's cells (`b8`, `hend`, `h8end`) | **produced**: `%8` is the loop head's (`hInv.iter.reg8`) and `%end.i` is `regs`'s, each peeled from `contP35S` down to `s` (`contP35S_env8`, `contP35S_envEnd`) |
| the seam's byte test (`hbit`) | **premised correctly: the document's** — the fifth of the eight class bits on the head's byte on this path |
| the second byte's class (`x1`, `h8c`) | **produced**: `if.end372.i`'s else arm binds five cells and none is `%8`, so `contSeamS_env8` peels the seam to the token's end and `h8c` *is* `h8end` |
| the second byte's three class bits (`hc110`, `hc116`, `hceq116`) | **premised correctly: the document's** — the remaining three of the eight; `%8` is not rebound, so all eight are one byte |
| the tail's counted segment (`hTail`, `ei`, `cA`, `rdv`, `xA`) and its start state's invariant (`hInvT`) | **supplied: a named premise, and the reason is the finding below.**  `consumerTailSegAt` composes the segment from the three calls' contracts, but its `hei` cell is `%ee.1.i`'s value at the tail's start, and on the class `contSeamS` builds that value is `ofNat 64 v.toNat` (the seam stores `%cond350.i` on the `LeafBlock35` edge).  A segment at `ei` therefore needs `ei = v.toNat`, which the bundle's `heicd` forbids.  The start state's invariant rides with it: `WalkSegment` records only its target's, so a producer cannot read the source's |
| the scan's landing (`a`, `q`, `bs`, `src`, `sel`, `hpreS`, `hincS`, `h3S`, `hbsS`, `hloc105`, `x47`, `h47`, `hloc96`) | **produced**: `contEntry_pre` is the entry's own construction and `hlastEntry_phiSel` a closed `phi`; `%3` peels to the tail's start and is `ptrs`'s document base (`contEntry_env3`), so `a = G.b`; `%47` is `landRhs457OutAt`'s own cell (`contEntry_env47`), `q` is the byte read's value (`hbsS` is `rfl`), and `hloc105`/`hloc96` hold because neither block is a `WalkLocal` scan block |
| the landing's selection (`hopS`) | **supplied: a named premise.**  The operand `hincS` selects is `%ee.1.i`, and its value at `contTailStart` is `ofNat 64 v.toNat` (`contTailStart_ee`), so the field asserts `ei = v.toNat` — the same cell the tail's segment needs.  It is supplied for the same reason and is the second half of the finding below |
| the landing's byte read and its two tests (`hpos`, `hreadS`, `hbit47`, `hws47`) | **premised correctly: the document's.**  The byte at `G.b + ei`, the bound its extraction needs and the two tests on it are properties of `G.bs` at the entry's own index |
| the latch's local (`hlatch`) | **reduced to a named premise**: `WalkLocal` at `while.body462.i` *is* the `ScanCount` the latch's own state writes.  The latch's bound is *not* a field: `%cond350.i` is `cond.end349.i`'s `phi` cell, and `contLatch_cond` is the peel that reads it as the lane's word |
| the span's two numbers and the scan's non-emptiness (`hspan`, `hstart`, `heicd`) | **premised correctly: the document's.**  `v.toNat` is at or before the next entry's position, `ei` this entry's or after it, and `ei < v.toNat` the scan's non-emptiness — the entry stream's numbers, which the staging does not fix |
| the traversal's three hypotheses (`hround`, `hguard`, `hbyte`) | **supplied: a named premise.**  `walkScanRounds457`'s own, unweakened — the round at a byte, the latch's guard, and the input's totality at every index the scan visits.  A `WalkSegment` cannot carry them: the segment records a run and an invariant, not the per-visit obligations an induction consumes |
| the token's register at the scan's exit (`htok`) | **supplied: a named premise, and it is not derivable.**  A traversal whose final state is existential has no named term to state a register at, and the layer has no preservation lemma for registers.  The lemma that would close it is *the extra-token scan preserves a register it does not bind* |

**The map's counted shape, per row: 8 produced, 1 reduced to a named premise, 9 premised
correctly, 4 supplied as named premises** — twenty-two rows in all, so **8 of 22
produced.**  Against the pre-recomposition bundle's `8 of 18`, the produced *count* is
unchanged while the bundle grew by four groups, and the movement inside it is the trade the
finding forced: `hnext` moved from supplied to **produced** (its value is now the one a
continuing entry has, so `hk` gives it), while the tail's segment and `hopS` moved from
produced to **supplied** (the seam cell both need is `ofNat 64 v.toNat` on this class).

## What producing the bundle found

**`hopS` and `heicd` cannot both hold in the class the recomposed prefix supplies**, and
this is a contradiction between two of the bundle's own fields — the same defect class the
pre-recomposition bundle carried, in the same place.  The arithmetic:

* `contSeamS` stores `%cond350.i` in the seam (`seamFin`'s `%ee.1.i` cell), and on this
  class `%cond350.i` is the lane's word, so at `contTailStart`
  `%ee.1.i = ofNat 64 v.toNat` — `contTailStart_ee` below is that peel, and the fixture's
  `%ee.1.i` `phi` says the same (`[%cond350.i, LeafBlock35]`);
* `hopS` asserts the landing's selection is `ofNat 64 ei`, and `hincS` selects `%ee.1.i`
  on the `if.then447.i` edge — so `hopS` says `ei = v.toNat`;
* `heicd` says `ei < v.toNat`.

The consumer reads `heicd` (`walkRevolution_seg` hands it to `contScanRounds`), so the
bundle is uninhabited at this class, and so is `walkRevolution_seg` at it.  **The prefix's
class is the no-whitespace-run one, where the extra-token scan is empty** — the run classes,
whose `%ee.1.i` is the run's stop `%ee.0.i238`, are the ones `heicd` describes and the
prefix module's header names as still to write.  So the repair is not a field of this
bundle: either the bundle is stated for a run class (a prefix whose seam carries the run's
stop), or `heicd` becomes the emptiness this class actually has.  Producing `hopS` or
`hTail` here would require *choosing* `ei = v.toNat`, which `heicd` forbids, so both are
supplied and the contradiction is reported rather than papered over.

This was invisible for the reason the earlier bundle's defect was invisible: the fields were
each checked against the path they were read from, and nothing in the bundle's own module
reads two of them against each other.  A producer reads them together.

## Which lemmas this file reuses

`hlastEntry_phiSel` (a closed `phi` fact, the same list), `hlastLoc105` and `hlastLoc96`
(generic in the scan's states), `hlast_nep_toNat`, and the invariant's own clauses
(`WalkInv.iter.reg8`, `WalkInv.regs`, `WalkInv.ptrs`).  The peels are new because the
recomposed prefix's states are new: `headAS4_envInc`/`headAS4_envNep`, the four at
`contAS₅`, `contP35S_env8`/`contP35S_envEnd`, `contSeamS_env8`, `contEntry_pre`,
`contEntry_env3`, `contEntry_env47`, `contTailStart_ee`, and the two arithmetic lemmas
`cont_ult_one`/`cont_hi63`.
-/

import LeanLLVM.Refinement.JsonStage2WalkRevolution

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The cells the recomposed path reads

Each is a peel: the blocks between the state and the loop head bind their own cells, and
none of them rebinds the name the lemma is about. -/

/-- `%inc.i` at `sw.default.i`'s entry is `%inc.i` at the loop head. -/
theorem headAS4_envInc (s : State) (x : BitVec 8) :
    lookupName (headAS₄ s x).env "%inc.i" = lookupName s.env "%inc.i" := by
  simp only [headAS₄, headAS₃, headAS₂, headAS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%nep` at `sw.default.i`'s entry is `%nep` at the loop head: no block writes it. -/
theorem headAS4_envNep (s : State) (x : BitVec 8) :
    lookupName (headAS₄ s x).env "%nep" = lookupName s.env "%nep" := by
  simp only [headAS₄, headAS₃, headAS₂, headAS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%5` at the succeeding arm is the invariant's positions table: `WalkPtrs`'s second
pointer, and the head chain rebinds no pointer register. -/
theorem contAS5_env5 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (hInv : WalkInv G C s) :
    lookupName (contAS₅ s x inc nep).env "%5" = some (.ptr G.ep) := by
  simp only [contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact hInv.ptrs.2.1

/-- `%idxprom.i` at the succeeding arm is the loop head's. -/
theorem contAS5_envIdx (s : State) (x : BitVec 8) (inc nep : BitVec 64) (ix : BitVec 64)
    (h : lookupName s.env "%idxprom.i" = some (.int 64 ix)) :
    lookupName (contAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix) := by
  simp only [contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- `%t352.i` at the succeeding arm is the loop head's token record. -/
theorem contAS5_envTok {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64)
    (h : lookupName s.env "%t352.i" = some (.ptr C.stage.tok)) :
    lookupName (contAS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok) := by
  simp only [contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- `%gap.i` at the succeeding arm is the loop head's: it is one of `walkStaticRegs`'s
twenty-four. -/
theorem contAS5_envGap {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64)
    (h : lookupName s.env "%gap.i" = some (.ptr (C.stage.tok + 20))) :
    lookupName (contAS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20)) := by
  simp only [contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- `%8` at the byte's leaf is the loop head's byte: the lane, the bound's `phi`, the
whitespace check and the three pivots bind their own cells and none of them is `%8`. -/
theorem contP35S_env8 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (contP35S C s x inc nep ep v ix b35).env "%8" = lookupName s.env "%8" := by
  simp only [contP35S, contP39S, contP41S, contLandS, contEndS, cte345OutAt,
    condEnd349OutAt, contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%end.i` at the byte's leaf is the loop head's: it is `walkStaticRegs`'s token slot. -/
theorem contP35S_envEnd {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (contP35S C s x inc nep ep v ix b35).env "%end.i" =
      lookupName s.env "%end.i" := by
  simp only [contP35S, contP39S, contP41S, contLandS, contEndS, cte345OutAt,
    condEnd349OutAt, contAS₅, headAS₄, headAS₃, headAS₂, headAS₁, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%8` at the seam is its value at the byte's leaf: the seam binds four literal cells and
`%ee.1.i`, and none of them is `%8`. -/
theorem contSeamS_env8 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) :
    lookupName (contSeamS C s x inc nep ep v ix b35 b8).env "%8" =
      lookupName (contP35S C s x inc nep ep v ix b35).env "%8" := by
  simp only [contSeamS, seamS, seamFin, stateAt]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- **The seam's `%ee.1.i` cell**, and the reason the two supplied fields cannot be
produced: `cond.end349.i`'s `phi` selects `%cond350.i` on the leaf edge, so the seam stores
the entry's end, not its start. -/
theorem contTailStart_ee {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8) :
    lookupName (contTailStart C s x inc nep ep v ix b35 b8 x1).env "%ee.1.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [contTailStart, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, contSeamS, seamS,
    seamFin, stateAt, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- The scan's entry's `pre` is `if.then447.i` — the seam of the extra-token scan, by
construction. -/
theorem contEntry_pre {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8) (r₁ r₂ r₃ : CallOutcome) (ei : Nat)
    (cA rdv xA : BitVec 32) :
    (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA).pre =
      some "if.then447.i" := by
  simp only [contEntry, ScanEntry, TailS₃, stateAt]

/-- `%3` at the scan's entry is the document's base: the tail binds none of the six pointer
registers, so the tail's start invariant supplies it. -/
theorem contEntry_env3 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8) (r₁ r₂ r₃ : CallOutcome) (ei : Nat)
    (cA rdv xA : BitVec 32)
    (hInvT : WalkInv G (ContTailStartC C) (contTailStart C s x inc nep ep v ix b35 b8 x1)) :
    lookupName (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA).env "%3" =
      some (.ptr G.b) := by
  simp only [contEntry, ScanEntry, TailS₃, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact hInvT.ptrs.1

/-- **`%47` at the landing is the scanned byte**: `landRhs457OutAt` binds it to
`ofNat 8 q`. -/
theorem contEntry_env47 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8) (r₁ r₂ r₃ : CallOutcome) (ei : Nat)
    (cA rdv xA : BitVec 32) (idx : BitVec 64) (a q : Nat) :
    evalOperand
      (landRhs457OutAt
        (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA) idx a q)
      (.reg "%47") = some (.int 8 (BitVec.ofNat 8 q)) := by
  simp only [landRhs457OutAt, stateAt, cells, evalOperand]
  rw [lookupName_cons_self]

/-! ### The count test's value, and the lane index's width

`hk` is the consumer's hypothesis; these two are the arithmetic that reads the bundle's
counts at it. -/

/-- **A continuing entry passes the count test.**  The counts are the loop's words, so the
test is `C.k + 1 < G.nep` at `Nat` level, and that is `hk`. -/
theorem cont_ult_one {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (hk : C.k + 1 < G.nep) : evalICmp .ult (hlastIncV C) (hlastNepV G) = 1 := by
  have h64 : C.k + 1 < 2 ^ 64 := by
    have h1 := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  simp only [evalICmp, hlastIncV]
  rw [BitVec.ult_eq_decide, BitVec.toNat_ofNat, hlast_nep_toNat, Nat.mod_eq_of_lt h64]
  simp [BitVec.ofBool]
  omega

/-- The lane's index reads back as its `Nat`: it is the header's increment. -/
theorem cont_inc_toNat {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (hk : C.k + 1 < G.nep) : (hlastIncV C).toNat = C.k + 1 := by
  have h64 : C.k + 1 < 2 ^ 64 := by
    have h1 := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  simp only [hlastIncV, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]

/-- The lane's index is a document position, so its `signExtend 64` reading is itself
below `2 ^ 63`. -/
theorem cont_hi63 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (hk : C.k + 1 < G.nep) : (hlastIncV C).toNat < 2 ^ 63 := by
  have h := cont_inc_toNat G C hk
  have h1 := G.nep_le
  have h2 := G.maxDoc
  simp only [stage2MaxDocument] at h2
  omega

/-! ### The producer

`HcontFacts` from the entry's evidence: the prefix's inputs, the scan's traversal supplied,
and the two fields the seam's `%ee.1.i` cell makes unproducible at this class supplied with
the reason recorded above.
-/

/-- **The bundle, from the entry's evidence.**  The prefix group is `hcontPrefixSeg`'s
input list — the head's byte and its class bits, the counts and the test's value, the next
entry's lane, the bound's relation, the byte before the end and its class, the seam's byte,
the tail's segment and the scan's landing — plus the span's two numbers, the traversal's
three hypotheses and the token's register.

`hnext` is derived from `hk`; `hTail` and `hopS` are supplied, because the seam's
`%ee.1.i` cell is `ofNat 64 v.toNat` on this class and both fields assert `ofNat 64 ei`. -/
def hcontFacts_of_staging {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    (hlt91 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 91) = 0)
    (hlt123 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 123) = 0)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hincL : lookupName s.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 1))))
    (hnepL : lookupName s.env "%nep" = some (.int 64 (hlastNepV G)))
    {v : BitVec 32}
    (hread : readBytes (contAS₅ s (hlastByte G C) (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidxS : lookupName s.env "%idxprom.i" = some (.int 64 ix))
    (htokS : lookupName s.env "%t352.i" = some (.ptr C.stage.tok))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes
      (contEndS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix).mem
      ((G.b - 1) + v.toNat) 1 = some [b35])
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (hc110 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 0)
    (hc116 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 116) = 0)
    (hceq116 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 116) = 0)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) {cA rdv : BitVec 32} {xA : BitVec 32}
    {ei : Nat}
    (hInvT : WalkInv G (ContTailStartC C)
      (contTailStart C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35
        (hlastByte G C) (hlastByte G C)))
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
      (contTailStart C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35
        (hlastByte G C) (hlastByte G C))
      (TailCarryScan (ContTailStartC C) ev)
      (contEntry C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35
        (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ ei cA rdv xA) 3)
    (hopS : evalOperand (stateAt
      (contEntry C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35
        (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ ei cA rdv xA).env
      (contEntry C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35
        (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ ei cA rdv xA)) (.reg "%ee.1.i") =
      some (.int 64 (BitVec.ofNat 64 ei)))
    {bs : List UInt8}
    (hpos : ((BitVec.ofNat 64 ei).signExtend 64).toNat < 2 ^ 63)
    (hreadS : readBytes
      (contEntry C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35
        (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ ei cA rdv xA).mem
      (G.b + ((BitVec.ofNat 64 ei).signExtend 64).toNat) 1 = some bs)
    (hbit47 : evalICmp .slt (BitVec.ofNat 8 (bytesToNat bs)) (BitVec.ofNat 8 13) = 1)
    (hws47 : evalICmp .ule (BitVec.ofNat 8 (bytesToNat bs) + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 1)
    (hlatch : WalkLocal { TailCarryScan (ContTailStartC C) ev with block := "while.body462.i" }
      (contLatch C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35
        (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ ei cA rdv xA
        (BitVec.ofNat 64 ei) G.b (bytesToNat bs) (BitVec.ofNat 8 (bytesToNat bs))))
    (hspan : v.toNat ≤ entryPos G (C.k + 1))
    (hstart : entryPos G C.k ≤ ei)
    (heicd : ei < v.toNat)
    (hround : ∀ (C' : WalkCarry G) (s' : State) (p a : Nat) (bs : List UInt8) (q : Nat)
      (x : BitVec 8), WalkInv G C' s' → C'.block = "while.body462.i" →
      lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
      lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) →
      p + 1 < v.toNat → p + 1 < 2 ^ 63 →
      lookupName (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
        "land.rhs457.i").env "%3" = some (.ptr a) →
      readBytes s'.mem (a + (p + 1)) 1 = some bs → bytesToNat bs = q →
      evalOperand (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
        "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) →
      evalICmp .slt x (BitVec.ofNat 8 13) = 1 →
      evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 →
      WalkLocal (ScanC₁₀₅ (ScanCLand C'))
        (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
          "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) →
      WalkLocal (ScanC₉₆ (ScanCLand C'))
        (ScanS₉₆ (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x) →
      WalkLocal { ScanCLand C' with block := "while.body462.i" }
        (Latch462S (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x) →
      ∃ (C'' : WalkCarry G) (s'' : State) (j : Nat),
        WalkSegment (stage2Calls stage2SubCalls) G C' s' C'' s'' j ∧
        WalkInv G C'' s'' ∧ C''.block = "while.body462.i" ∧ j ≤ stage2ByteAllowance ∧
        lookupName s''.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (p + 1))) ∧
        lookupName s''.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)))
    (hguard : ∀ (C' : WalkCarry G) (s' : State), WalkInv G C' s' →
      C'.block = "while.body462.i" → ScanGuard s' "%q.0.i246" "%cond350.i" C'.inner)
    (hbyte : ∀ (C' : WalkCarry G) (s' : State) (p : Nat), WalkInv G C' s' →
      C'.block = "while.body462.i" → p + 1 < v.toNat →
      lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
      lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) →
      ∃ (a : Nat) (bs : List UInt8) (q : Nat) (x : BitVec 8),
        lookupName (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
          "land.rhs457.i").env "%3" = some (.ptr a) ∧
        readBytes s'.mem (a + (p + 1)) 1 = some bs ∧ bytesToNat bs = q ∧
        evalOperand (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
          "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) ∧
        evalICmp .slt x (BitVec.ofNat 8 13) = 1 ∧
        evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 ∧
        WalkLocal (ScanC₁₀₅ (ScanCLand C'))
          (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
            "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) ∧
        WalkLocal (ScanC₉₆ (ScanCLand C'))
          (ScanS₉₆ (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
            (BitVec.ofNat 64 (p + 1)) a q x) ∧
        WalkLocal { ScanCLand C' with block := "while.body462.i" }
          (Latch462S (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
            "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q x))
    (htok : ∀ (C' : WalkCarry G) (s' : State), WalkInv G C' s' →
      C'.block = "while.body462.i" → ∃ tok : Nat, lookupName s'.env "%t352.i" = some (.ptr tok))
    :
    HcontFacts G C s :=
  { x := hlastByte G C
    h8 := by
      show evalOperand s (.reg "%8") = some (.int 8 (hlastByte G C))
      simp only [evalOperand]
      exact hInv.iter.reg8
    hlt91 := hlt91
    hlt123 := hlt123
    hlt125 := hlt125
    hne125 := hne125
    inc := hlastIncV C
    nep := hlastNepV G
    hinc := by
      show evalOperand (headAS₄ s (hlastByte G C)) (.reg "%inc.i") =
        some (.int 64 (hlastIncV C))
      simp only [evalOperand]
      rw [headAS4_envInc s (hlastByte G C)]
      exact hincL
    hnep := by
      show evalOperand (headAS₄ s (hlastByte G C)) (.reg "%nep") =
        some (.int 64 (hlastNepV G))
      simp only [evalOperand]
      rw [headAS4_envNep s (hlastByte G C)]
      exact hnepL
    hnext := cont_ult_one G C hk
    ep := G.ep
    v := v
    h5 := contAS5_env5 C s (hlastByte G C) (hlastIncV C) (hlastNepV G) hInv
    hi63 := cont_hi63 G C hk
    hread := hread
    ix := ix
    hidx5 := contAS5_envIdx s (hlastByte G C) (hlastIncV C) (hlastNepV G) ix hidxS
    htok5 := contAS5_envTok C s (hlastByte G C) (hlastIncV C) (hlastNepV G) htokS
    hgap5 := contAS5_envGap C s (hlastByte G C) (hlastIncV C) (hlastNepV G)
      (hInv.regs ("%gap.i", .ptr (C.stage.tok + 20)) (by simp [walkStaticRegs]))
    hugt := hugt
    b35 := b35
    hread35 := hread35
    hb13 := hb13
    hb32 := hb32
    hbne13 := hbne13
    b8 := hlastByte G C
    hend := by
      rw [contP35S_envEnd C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35]
      exact hInv.regs ("%end.i", .ptr (C.stage.tok + 8)) (by simp [walkStaticRegs])
    h8end := by
      rw [contP35S_env8 C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35]
      exact hInv.iter.reg8
    hbit := hbit
    x1 := hlastByte G C
    h8c := by
      simp only [evalOperand]
      rw [contSeamS_env8 C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35
          (hlastByte G C),
        contP35S_env8 C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35]
      exact hInv.iter.reg8
    hc110 := hc110
    hc116 := hc116
    hceq116 := hceq116
    r₁ := r₁
    r₂ := r₂
    r₃ := r₃
    ev := ev
    cA := cA
    rdv := rdv
    xA := xA
    ei := ei
    hTail := hTail
    heicd := heicd
    a := G.b
    q := bytesToNat bs
    bs := bs
    src := "if.then447.i"
    sel := .reg "%ee.1.i"
    hpreS := contEntry_pre C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35
      (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ ei cA rdv xA
    hincS := hlastEntry_phiSel
    hopS := hopS
    h3S := contEntry_env3 C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35
      (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ ei cA rdv xA hInvT
    hpos := hpos
    hreadS := hreadS
    hbsS := rfl
    hloc105 := hlastLoc105 (ContTailStartC C) ev
      (contEntry C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35
        (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ ei cA rdv xA)
      (BitVec.ofNat 64 ei) G.b (bytesToNat bs)
    x47 := BitVec.ofNat 8 (bytesToNat bs)
    h47 := contEntry_env47 C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35
      (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ ei cA rdv xA (BitVec.ofNat 64 ei) G.b
      (bytesToNat bs)
    hbit47 := hbit47
    hws47 := hws47
    hloc96 := hlastLoc96 (ContTailStartC C) ev
      (contEntry C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35
        (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ ei cA rdv xA)
      (BitVec.ofNat 64 ei) G.b (bytesToNat bs) (BitVec.ofNat 8 (bytesToNat bs))
    hlatch := hlatch
    hspan := hspan
    hstart := hstart
    hround := hround
    hguard := hguard
    hbyte := hbyte
    htok := htok }

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.contTailStart_ee
#print axioms LeanLLVM.Refinement.WalkScope.cont_ult_one
#print axioms LeanLLVM.Refinement.WalkScope.cont_hi63
#print axioms LeanLLVM.Refinement.WalkScope.hcontFacts_of_staging

end WalkScope
end LeanLLVM.Refinement
