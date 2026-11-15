/-
# The continuing entry's facts, from the staging

`WalkContinueFacts` (`JsonStage2WalkPremisesOfStaging`) is the continuing entry's premise:
one bundle per class at every head state with an entry left.  This module produces the
**whitespace** class's — `HcontFacts` (`JsonStage2WalkRevolution`), the bundle
`walkRevolutionMergeSegWs` consumes field for field.  The path it describes is the run
class's: the four high-byte pivots, `sw.default.i`'s *succeeding* arm, the bound's `phi`,
the whitespace check at the entry's end, the skip to the run's stop `k`, the token's end
`if.end372.i`, the class-C span, the tail and the scan — and the module is the twin of
`hlastFacts_of_staging`: the same three sources (the invariant's clauses, the document's
content and the staging's addresses) producing the continuing bundle instead of the last
entry's.

The scan-free class's bundle is `HcontCleanupFacts`, and its producer is not here: its
segment needs no scan, no tail budget and no traversal, so it is `walkRevolutionMergeSeg`'s
evidence assembled at the staging's own states.

## The twin's shape

`hlastFacts_of_staging` is a `def`, because the bundle is a `Type`: its first member of
each group is a *witness* the later fields are stated at.  This is a `def` for the same
reason, and it takes the evidence the run class's states take.  Three differences, each a
consequence of the bundles' statements rather than a choice made here:

* **There is no `hblock`.**  Neither producer reads the block: neither bundle carries an
  inner budget at the head state, so no field reads the block, and the last entry's path
  enters no scan at all, so it needs no refill lemma either.  The premise is dropped rather
  than bound and discarded in both.
* **`hk` is taken, and it is load-bearing.**  `C.k + 1 < G.nep` is what makes `hnext`
  provable (see below) and what bounds the lane's index (`hi63`).  It is *not* a premise
  the bundle's fields discard: two of them read it.
* **The scan's traversal is not part of the run group.**  `HcontFacts` states
  `walkScanRounds457`'s three hypotheses (`hround`, `hguard`, `hbyte`) and the token's
  register at its exit (`htok`) instead, because the continuing entry's scan runs over the
  entry's span; they arrive as premises, and `htok` is the one obstruction no staging
  evidence closes.  The run's own segment (`hRun`) is supplied for the same structural
  reason, one segment out; its bound (`hcond_sl`) is the one cell of its endpoint the
  invariant does not carry, while `%inc.i` and `%nep` are read off the segment's target
  invariant (`contWsSeamS_inc`, `contWsSeamS_nep`).

## `hnext` is the first field of this bundle that is derived, not supplied

The field used to be `hge : evalICmp .ult inc nep = 0`, and it was the old bundle's one
obstruction: at a real head state `%inc.i = C.k + 1` and `%nep = G.nep`
(`WalkInv.blockIndex` and the header's store), so `= 0` is `¬ (C.k + 1 < G.nep)` while the
consumer's hypothesis is that inequality — the bundle was uninhabited and every consumer at
that class vacuous.  The recomposition states the field at the value a continuing
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
| the entry counts' witnesses and their head facts (`inc`, `nep`, `hinc`, `hnep`) | **produced, from no supplied fact**: the witnesses are the loop's values (`hlastIncV C`, `hlastNepV G`) and the cells are the invariant's own — `WalkInv.inc_reg` and `%nep`'s `walkStaticRegs` row — peeled down to `headAS₄` (`headAS4_envInc`, `headAS4_envNep`) |
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
| the tail's counted segment (`hTail`, `cA`, `rdv`, `xA`) | **supplied: a named premise.**  `consumerTailSegAt` composes the segment from the three calls' contracts, but the third link needs the copy's span bound (`v.toNat - k ≤ C.inner`), which is the entry's inner budget — a value no clause of `WalkInv` fixes at the tail's start.  The scan-free arm's twin needs no budget (`consumerTailSegEmptyAt`), because its two cells are the same word |
| the whitespace run (`sl`, `k`, `n`, `b8`, `hRun`, `hnRun`) | **supplied: a named premise, and its producer is named.**  `contWsRun`: the skip's per-visit dispatch and the latch's own step — four links a continuing byte at `LeafBlock43`'s class and five at `46`/`48`'s, four or five at the exit (the per-visit lemmas are `JsonStage2WalkRevolution`'s `wsContinue43`/`46`/`48` and `wsExit43`/`46`/`48`) — with the per-index document `∀` as the traversal's premise.  The count is a bound, because the classes differ in cost; the segment's endpoint is its own term, so the bundle reads `hRun.inv'` for the span; `hnRun` is the price the bundle states, `n + 8·(v - 1 - k) ≤ 8·ΔA + 5` |
| the scan's landing (`a`, `q`, `bs`, `h3S`, `hpos`, `hreadS`, `hbsS`, `hloc105`, `x47`, `h47`, `hloc96`) | **premised correctly: the document's and the staging's.**  `%3` is the staging's document base and the byte at `G.b + k` is the input's; the two locals hold because neither block is a `WalkLocal` scan block.  `src`/`sel`/`hpreS`/`hincS` are *not* fields any more: they are closed (`contWsEntry_pre`, `hlastEntry_phiSel`) |
| the landing's selection (`hopS`) | **produced** (`contWsEntry_hopS`): the operand is `%ee.1.i` and the seam stored the run's stop `k` in it (`contWsEntry_ee`), so the landing's index *is* the run's stop.  This is the field that used to be supplied and that contradicted the stopper — the finding below |
| the run endpoint's two registers (`hinc_sl`, `hnep_sl`) | **retired: proved, not supplied.**  `%inc.i` is `WalkInv.inc_reg` and `%nep` is one of `walkStaticRegs`' pairs, and the seam binds neither (`seamS_env_inc`, `seamS_env_nep`), so the segment's target invariant reads both at `sl` (`contWsSeamS_inc`, `contWsSeamS_nep`).  A `WalkSegment` carries the invariant at its target, and the run's target is the seam's source |
| the run endpoint's bound (`hcond_sl`) | **supplied: a named premise.**  No `WalkInv` clause names `%cond350.i` at an arbitrary state, and a `WalkSegment` records a run and its target's invariant, not the blocks the run passed.  The lemma that would close it is *the whitespace skip preserves the bound it does not bind* |
| the span's two numbers and the run's stop (`hspan`, `hstart`, `heicd`) | **premised correctly: the document's.**  `v.toNat` is at or before the next entry's position, the run's stop at or after this entry's, and `k < v.toNat` the scan's non-emptiness — the entry stream's numbers, which the staging does not fix |
| the traversal's three hypotheses (`hround`, `hguard`, `hbyte`) | **supplied: a named premise.**  `walkScanRounds457`'s own, unweakened — the round at a byte, the latch's guard, and the input's totality at every index the scan visits.  A `WalkSegment` cannot carry them: the segment records a run and an invariant, not the per-visit obligations an induction consumes |
| the token's register at the scan's exit (`htok`) | **supplied: a named premise, and it is not derivable.**  A traversal whose final state is existential has no named term to state a register at, and the layer has no preservation lemma for registers.  The lemma that would close it is *the extra-token scan preserves a register it does not bind* |

**The map's shape.**  *Produced* from the invariant and the staging: the head's byte
(`hlastByte G C`), the two counts and their cells, the count test's value, the default
arm's four cells, the run's arithmetic (`hi63`) and `hnext`.  *Produced from another
field's cell*: `hopS` (`contWsEntry_hopS`).  *Named premises*, each with its producer or
its reason: the document's bytes and classes, the whitespace run (`contWsRun`, planned), the
tail's segment (the inner budget), the landing's byte and locals, the traversal's three
hypotheses, the token register at the scan's exit, and the run endpoint's bound.  No row is a
field weakened to make a proof close, and the two that were supplied *because* the seam's cell
contradicted the stopper — `hopS` and the tail — are now either produced or supplied for a
reason that survives the class split.

## What producing the bundle found

**`hopS` and `heicd` could not both hold at the states the older prefix supplied**, and
this is the defect the split repairs.  The arithmetic, kept because it is the instrument:

* `contSeamS` stores `%cond350.i` in the seam (`seamFin`'s `%ee.1.i` cell), and on that
  class `%cond350.i` is the lane's word, so at `contTailStart`
  `%ee.1.i = ofNat 64 v.toNat` — `contTailStart_ee` is that peel;
* `hopS` asserts the landing's selection is `ofNat 64 ei`, and `hincS` selects `%ee.1.i`
  on the `if.then447.i` edge — so `hopS` says `ei = v.toNat`;
* `heicd` says `ei < v.toNat`.

A consumer reads both (`contScanRounds` takes the stopper, the landing takes the index), so
the bundle *was* uninhabited at that class.  **The prefix's class is the no-whitespace-run
one, where the extra-token scan is empty** — the run class, whose `%ee.1.i` is the run's
stop `%ee.0.i238`, is the one `heicd` describes.

**The repair is the split, and it is in the tree.**  `HcontFacts` is now the whitespace
arm, stated at the run class's states (`contWsSeamS`, `contWsTailStart`, `contWsEntry`,
`contWsLatch`): its seam stores the run's stop `k`, `hopS` is *produced*
(`contWsEntry_hopS`, from `contWsEntry_ee`), and `heicd` says `k < v.toNat`, which is the
scan's actual span.  The no-whitespace class's bundle is `HcontCleanupFacts`
(`JsonStage2WalkRevolution`), whose seam stores the entry's end and whose walk reaches
`if.end473.i` without a scan — so the class that made the fields contradict carries
neither of them.  `HcontCase` (`JsonStage2WalkDispatchWitnessString`) has one arm per class,
and the loop's step takes each arm's own composition.

**The method step this file's earlier version named is what found it**: the fields were each
checked against the path they were read from, and nothing in the bundle's own module reads
two of them against each other — a producer reads them together.  An elaborating structure
literal and an inhabited bundle are different claims, and only the second is what a
refinement statement consumes.

## Which lemmas this file reuses

`hlastEntry_phiSel` (a closed `phi` fact, the same list), `hlastLoc105` and `hlastLoc96`
(generic in the scan's states), `hlast_nep_toNat`, and the invariant's own clauses
(`WalkInv.iter.reg8`, `WalkInv.regs`, `WalkInv.ptrs`).  `headAS4_envInc`/`headAS4_envNep`
are the other module's (the two carries' shared head peel), and the rest are new because
the states are new: the four at `contAS₅`, `contP35S_env8`/`contP35S_envEnd`,
`contSeamS_env8`, `contEntry_pre`, `contEntry_env3`, `contEntry_env47`,
`contTailStart_ee`, and the two arithmetic lemmas `cont_ult_one`/`cont_hi63`.
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

`HcontFacts` from the entry's evidence.  The groups the invariant and the staging fix are
*derived* — the head's byte, the two counts and their cells, the count test's value, the
default arm's four cells — and the rest is supplied, each with the reason the layer cannot
produce it: the document's bytes and their classes, the whitespace run's segment (its
producer is `contWsRun`, planned), the tail's three calls, the scan's landing and its
traversal's three hypotheses, the token record at the scan's exit, the run endpoint's two
registers and the scan's bound at it.
-/

/-- **The bundle, from the entry's evidence.**  Produced at the loop's own values: the head's
byte is `hlastByte G C`, the counts are `hlastIncV C`/`hlastNepV G`, the position table is
`G.ep`, and the classes are read on `hlastByte G C`.  `hnext` is derived from `hk`
(`cont_ult_one`), `hi63` from `hk` and the stream's size (`cont_hi63`), and the default
arm's four cells are the invariant's peels at `contAS₅` — so only the document's facts, the
run, the tail, the traversal and the run endpoint's bound enter as premises.

`hopS` is **not** a premise any more: at `contWsEntry` the seam stored the run's stop
(`contWsEntry_ee`), so the landing's index follows from the cell rather than being asserted
against a stopper.  That is the repair this producer's earlier shape recorded as impossible
— see this module's header. -/
def hcontFacts_of_staging {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    (hlt91 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 91) = 0)
    (hlt123 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 123) = 0)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
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
    {sl : State} {k n : Nat} {b8 : BitVec 8}
    (hRun : WalkSegment (stage2Calls stage2SubCalls) G (ContAC₄ C)
      (contLandS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35)
      (ContSeamC C) (contWsSeamS C sl k b8) n)
    (hnRun : n + stage2ByteAllowance * (v.toNat - 1 - k) ≤
      stage2ByteAllowance * (entryPos G (C.k + 1) - entryPos G C.k) + 5)
    (heicd : k < v.toNat)
    (h8c : evalOperand (contWsSeamS C sl k b8) (.reg "%8") =
      some (.int 8 (hlastByte G C)))
    (hc110 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 0)
    (hc116 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 116) = 0)
    (hceq116 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 116) = 0)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) {cA rdv xA : BitVec 32}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
      (contWsTailStart C sl k b8 (hlastByte G C))
      (TailCarryScan (ContTailStartC C) ev)
      (contWsEntry C sl k b8 (hlastByte G C) r₁ r₂ r₃ k v cA rdv xA) 3)
    {a q : Nat} {bs : List UInt8} {x47 : BitVec 8}
    (h3S : lookupName (contWsEntry C sl k b8 (hlastByte G C) r₁ r₂ r₃ k v cA rdv xA).env
      "%3" = some (.ptr a))
    (hpos : ((BitVec.ofNat 64 k).signExtend 64).toNat < 2 ^ 63)
    (hreadS : readBytes
      (contWsEntry C sl k b8 (hlastByte G C) r₁ r₂ r₃ k v cA rdv xA).mem
      (a + ((BitVec.ofNat 64 k).signExtend 64).toNat) 1 = some bs)
    (hbsS : bytesToNat bs = q)
    (hloc105 : WalkLocal (ScanC₁₀₅ (TailCarryScan (ContTailStartC C) ev))
      (landRhs457OutAt (contWsEntry C sl k b8 (hlastByte G C) r₁ r₂ r₃ k v cA rdv xA)
        (BitVec.ofNat 64 k) a q))
    (h47 : evalOperand
      (landRhs457OutAt (contWsEntry C sl k b8 (hlastByte G C) r₁ r₂ r₃ k v cA rdv xA)
        (BitVec.ofNat 64 k) a q) (.reg "%47") = some (.int 8 x47))
    (hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1)
    (hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1)
    (hloc96 : WalkLocal (ScanC₉₆ (TailCarryScan (ContTailStartC C) ev))
      (ScanS₉₆ (contWsEntry C sl k b8 (hlastByte G C) r₁ r₂ r₃ k v cA rdv xA)
        (BitVec.ofNat 64 k) a q x47))
    (hlatch : WalkLocal { TailCarryScan (ContTailStartC C) ev with block := "while.body462.i" }
      (contWsLatch C sl k b8 (hlastByte G C) r₁ r₂ r₃ k v cA rdv xA
        (BitVec.ofNat 64 k) a q x47))
    (hspan : v.toNat ≤ entryPos G (C.k + 1))
    (hstart : entryPos G C.k ≤ k)
    (hcond_sl : lookupName sl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)))
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
      exact hInv.inc_reg
    hnep := by
      show evalOperand (headAS₄ s (hlastByte G C)) (.reg "%nep") =
        some (.int 64 (hlastNepV G))
      simp only [evalOperand]
      rw [headAS4_envNep s (hlastByte G C)]
      exact hInv.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs])
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
    sl := sl
    k := k
    n := n
    b8 := b8
    hRun := hRun
    hnRun := hnRun
    heicd := heicd
    x1 := hlastByte G C
    h8c := h8c
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
    hTail := hTail
    a := a
    q := q
    bs := bs
    h3S := h3S
    hpos := hpos
    hreadS := hreadS
    hbsS := hbsS
    hloc105 := hloc105
    x47 := x47
    h47 := h47
    hbit47 := hbit47
    hws47 := hws47
    hloc96 := hloc96
    hlatch := hlatch
    hspan := hspan
    hstart := hstart
    hcond_sl := hcond_sl
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
