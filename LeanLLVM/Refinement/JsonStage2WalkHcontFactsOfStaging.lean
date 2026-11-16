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
  entry's span; the three hypotheses arrive as premises, and `htok` is **no longer one**:
  `%t352.i` is one of `walkStaticRegs`, so `WalkInv.regs` carries it at every state that
  holds the invariant (`cont_static_tok`) and the field is a theorem of the bundle's own
  quantified states.  The run itself is **not** a premise: the bundle carries the class
  (`hClass`) and `contWsRunF` derives the segment, its count bound and the stop's
  `%cond350.i` cell from it, while `%inc.i` and `%nep` are read off the segment's target
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
| the head's byte's two naming bits (`hlt125`, `hne125`) | **premised correctly: the document's.**  Both clear leave the byte at `ofNat 8 126` or `127` in the signed order, and that is the whole class: the other six bits (`hlt91`, `hlt123`, `hc110`, `hc116`, `hceq116`, and the seam's test) are `decide`d there (`hlast_slt_zero_of_toInt_le`, `hlast_eq_zero_of_slt_zero`, `hlast_bit6_of_class`) |
| the entry counts' witnesses and their head facts (`inc`, `nep`, `hinc`, `hnep`) | **produced, from no supplied fact**: the witnesses are the loop's values (`hlastIncV C`, `hlastNepV G`) and the cells are the invariant's own — `WalkInv.inc_reg` and `%nep`'s `walkStaticRegs` row — peeled down to `headAS₄` (`headAS4_envInc`, `headAS4_envNep`) |
| the count test's value (`hnext`) | **produced**: `cont_ult_one` from `hk` — the first derived-not-supplied field of this bundle; see the section above |
| the next entry's lane (`ep`, `v`, `hread`) | **premised correctly: the document's.**  The positions table's address is the invariant's (`%5` is `WalkPtrs`'s `some (.ptr G.ep)`), but the word at the next entry's index and the read that fetches it are the document's |
| the lane index's width (`hi63`) | **produced**: `cont_hi63`, arithmetic on `hk` and `G.nep_le`'s `G.nep ≤ 2 ^ 32` |
| the default arm's remaining cells (`ix`, `hidx5`, `htok5`, `hgap5`) | **produced, from no supplied fact**: `%idxprom.i` is `WalkInv.idx_reg`'s cell at the pinned witness `contIx G C` and `%t352.i` is `WalkInv.regs`'s (`cont_static_tok`); `%gap.i` is `regs`'s, each peeled to the succeeding arm's state (`contAS5_envIdx`, `contAS5_envTok`, `contAS5_envGap`) |
| the entry's non-emptiness (`hugt`) | **premised correctly: the document's.**  The next entry's position against this entry's index is a relation between the lane's word and the entry stream; neither the invariant nor the staging fixes it |
| the byte before the entry's end (`b35`, `hread35`) | **the read is produced, the byte's value is the document's.**  `land.lhs.true357.i` reads the document at `%cond350.i - 1`; `contEndS`'s two token-record stores are disjoint from the document's staged region, so `contEndS_docByte` yields `walkDoc_byte`'s byte at that index.  The witness is therefore the document's own term, `contB35 G v = G.bs.getD (v - 1) 0`, and no memory fact is supplied |
| that byte's three pivot bits (`hb13`, `hb32`, `hbne13`) | **premised correctly: the document's**, and they are the class the price's longest path names: no whitespace run, so the token's end is reached directly |
| the seam's cells (`b8`, `hend`, `h8end`) | **produced**: `%8` is the loop head's (`hInv.iter.reg8`) and `%end.i` is `regs`'s, each peeled from `contP35S` down to `s` (`contP35S_env8`, `contP35S_envEnd`) |
| the seam's byte test (`hbit`) | **premised correctly: the document's** — the fifth of the eight class bits on the head's byte on this path |
| the second byte's class (`x1`, `h8c`) | **produced**: `if.end372.i`'s else arm binds five cells and none is `%8`, so `contSeamS_env8` peels the seam to the token's end and `h8c` *is* `h8end` |
| the second byte's three class bits (`hc110`, `hc116`, `hceq116`) | **produced** from the class's two: the same byte, whose signed order already clears `110` and `116` and excludes `116` (`hlast_slt_zero_of_toInt_le`, `hlast_eq_zero_of_slt_zero`) |
| the tail's counted segment (`hTail`, `cA`, `rdv`, `xA`) | **supplied: a named premise, and now with a reachable producer.**  `consumerTailSegAt` composes the segment from the three calls' contracts.  Its third link's span bound (`v.toNat - k ≤ C.inner`) used to be the obstruction; it is now derived — `k < v.toNat` is `cont_heicd` and `v.toNat - ix.toNat ≤ C.inner` plus `ix.toNat < k` gives it.  What remains between this field and `consumerTailSegAt` is the three callees' own preconditions and answers, which are the staging's and no clause of `WalkInv` fixes at the callee's argument list (the same survivors `hlastTail_of_calls`'s map names).  So the field stays the named premise and its producer is `consumerTailSegAt` at the seam's landing |
| the whitespace run (`k`, `x1`, `hClass`) | **the class is supplied, the run is derived.**  `hClass` is the one premise that makes the segment total: `%35` is one of the four whitespace bytes, so the leaf the pivots reach takes its true arm, the per-index `∀` continues the token to `k` and the stop is at `k`.  Its last two conjuncts are the inner budget the first visit's `ScanEntered` needs — the refill's, so supplied — and `entryPos C.k ≤ ix.toNat`, which is now `le_rfl` at the pinned `contIx G C`.  `contWsRunF` (`JsonStage2WalkRevolution`) derives the segment, its count `N ≤ 5·(k - i) + 10` and the stop's `%cond350.i` cell; `contWsPriceF` derives `N + 8·(v - 1 - k) ≤ 8·ΔA + 5` |
| the scan's landing (`q`, `bs`, `hreadS`, `hbsS`, `x47`, `h47`) | **premised correctly: the document's.**  The address is derived — `%3` at `contWsEntry` is `WalkPtrs`'s `some (.ptr G.b)`, which is the tail segment's own target invariant (`hTail.inv'.ptrs.1`), so `a := G.b`; and `hpos`, `hloc105`, `hloc96` are derived (`cont_hpos`, and the two `hlastLoc*` lemmas, which are generic in the state).  What stays supplied is the byte at `G.b + k` and its class — the input's — and the two index cells `q`/`x47` that name it |
| the landing's selection (`hopS`) | **produced** (`contWsEntry_hopS`): the operand is `%ee.1.i` and the seam stored the run's stop `k` in it (`contWsEntry_ee`), so the landing's index *is* the run's stop.  This is the field that used to be supplied and that contradicted the stopper — the finding below |
| the run endpoint's two registers (`hinc_sl`, `hnep_sl`) | **retired: proved, not supplied.**  `%inc.i` is `WalkInv.inc_reg` and `%nep` is one of `walkStaticRegs`' pairs, and the seam binds neither (`seamS_env_inc`, `seamS_env_nep`), so the segment's target invariant reads both at the endpoint (`contWsSeamS_inc`, `contWsSeamS_nep`).  A `WalkSegment` carries the invariant at its target, and the run's target is the seam's source |
| the run endpoint's bound (`hcond_sl`) | **retired: derived, not supplied.**  No `WalkInv` clause names `%cond350.i` at an arbitrary state, and a `WalkSegment` records a run and its target's invariant, not the blocks the run passed — so `contWsRunF` returns the cell as its third conjunct, carried through the arms' latch induction, and the bundle names it no longer.  The seam's `%end.i` cell is derived the same way: `wsSlS_envEnd` transports it from the head state's `WalkInv.regs` |
| the span's two numbers and the run's stop (`hspan`, `hstart`, `heicd`) | **`hspan` is the document's; `hstart` and `heicd` are derived.**  `v.toNat ≤ entryPos G (C.k + 1)` is the entry stream's number, which the staging does not fix.  `hstart` is `entryPos C.k ≤ k`, i.e. the run's own `ix < k` at the pinned index; `heicd` is `k < v.toNat`, and it is the field that decides the bundle's inhabitation: the class disjunct is `wsStop G (v - 1)`, the per-index conjunct makes every index in `[ix, k)` a continuing byte, and `hugt` puts `v - 1` above `ix` — so `v - 1` below `k` would be both (`cont_heicd`, `wsCont_not_wsStop`) |
| the traversal's three hypotheses (`hround`, `hguard`, `hbyte`) | **supplied: a named premise each, with its source named.**  `hround` is the visit's own step — the latch at `while.body462.i` and its three leaves — so the **staging's** (the pinned body's `step`); it is the `∀`-form of a `WalkLink`, which a `WalkSegment` cannot substitute because a segment records a run and an invariant, not a per-visit obligation.  `hguard` is `ScanGuard` at the latch, the **staging's measure**: the invariant's local clause there is `ScanCount` (`∃ i c, c - i ≤ inner ∧ i < c ∧ …`), and the `∀` form quantifies over representations (`ofNat 64 i`), which the clause does not bound in width.  `hbyte` is **both**: its read is the **document's** — `walkDoc_byte` yields the byte at `G.b + p` at any invariant state, so no frame premise is needed — while its two class bits (`slt 13 = 1`, `ule … = 1`) are the visited byte's **content**, the input's, and its two locals and `%47` binding are `decide`-able.  So of the three, only the document half of `hbyte` is derivable from this layer's evidence; the rest is the pinned body's and the input's |
| the token's register at the scan's exit (`htok`) | **derived.**  `%t352.i` is one of `walkStaticRegs`'s thirty-two, and `WalkInv.regs` carries them at every state, so `cont_static_tok` proves the field's `∀` outright — no preservation lemma is needed, and the earlier reading (that a traversal's existential endpoint leaves no term to state a register at) applied to the *scan's own* endpoint, not to the invariant-carrying states the field quantifies over |

**The map's shape.**  *Produced* from the invariant and the staging: the head's byte
(`hlastByte G C`), its seven class bits from two, the two counts and their cells, the count
test's value, the entry's index, the default arm's four cells, the byte before the entry's
end and the read that fetches it, the landing's address and its two locals, the landing
index's width, `hstart` and `heicd`.  *Produced from another field's cell*: `hopS`
(`contWsEntry_hopS`).  *Named premises*, each with its producer or its reason: the two class
bits on the head's byte, the entry's word (`hread`) and its order (`hugt`), the whitespace
class (`hClass`) — which is the document's content and the refill's budget — the tail's
segment (the three callees' own preconditions), the landing's byte and its class, and the
traversal's three hypotheses.  The run, its count, its price, its endpoint's two cells and
the token register at its exit are no longer premises: `contWsRunF`, `contWsPriceF`,
`wsSlS_envEnd` and `cont_static_tok` derive them.  No row is a field weakened to make a
proof close, and the two that were supplied *because* the seam's cell contradicted the
stopper — `hopS` and the tail — are now either produced or supplied for a reason that
survives the class split.

## This round: the count, and the question it leaves

**The count, measured.**  The producer's signature named **53 binders** before this round
and **35** after it (`awk` over the `def`'s top-level `( … )`/`{ … }` groups, splitting each
at its first `:`, so a group such as `(r₁ r₂ r₃ : CallOutcome)` is three arguments).  Setting
the five fixed ones (`m0`, `G`, `C`, `s`, `hInv`) and the consumer's `hk` aside, that is
**47 supplied arguments before and 29 after** — eighteen derived, nothing added.  The
eighteen: `hlt91`, `hlt123`, `hc110`, `hc116`, `hceq116`, `hpos`, `h3S`/`a`, `b35`,
`hread35`, `heicd`, `hstart`, `hloc105`, `hloc96`, `htok`, `htokS`, `hidxS`/`ix`.

**The acceptance question — is the bundle producible at every reachable whitespace head
state?**  Yes, and the field that decides it is `hClass`'s *inner budget* conjunct,
`v.toNat - entryPos C.k ≤ C.inner`.  Everything else is either a theorem of the head state
(the index, the counts, the class bits, the token cell, `heicd`, `hstart`, `hpos`) or a
document fact true at a state of this class (the two naming bits, the byte before the
entry's end and its class, the per-index run, the landing's byte).  The budget is the one
conjunct `WalkInv` cannot supply: `inner_cap` bounds `C.inner` **above** (`≤ walkInnerCap G`),
and the walk asserts the invariant at mid-scan states where the component is being spent
down.  At the loop head it is true because the head refills: `walkSeed` and the back edge's
carry both set `inner := walkInnerCap G`, so `C.inner = walkInnerCap G = 4 * G.n + 5` there,
and `v.toNat - entryPos C.k ≤ G.n` by the stream's order — which is the positivity
`walkLoopHead_inner_pos` states, given that equality.  It stays an argument to the producer
because it is the *refill's* fact, not the invariant's; that is a `WalkInv` question (a lower
bound valid only at the head), not a producer one.
`hTail` is the second-placed dependency: its producer is `consumerTailSegAt`, and what it
still needs is the three callees' preconditions, which the staging supplies at the seam's
landing and `WalkInv` does not carry at the callee's argument list.

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
neither of them.  The continuing premise is `HcontArm` (`JsonStage2WalkDispatchHcontArms`),
one constructor per head-switch class; `HcontCase` (`JsonStage2WalkDispatchWitnessString`)
is the sub-union of its three token bundles, and the loop's step takes each arm's own
composition.

**The class split is now a census, not a pair of bits.**  `HcontFacts`'s head fields still
clear the two high-byte pivots, because that is the route this bundle's composition proves
(`contPrefixLand`'s eight links); the plain-value route's class is `HcontScalarFacts`
(`JsonStage2WalkHcontScalar`), composed at sixteen links, and the old split's failure at an
ordinary numeral is `JsonStage2WalkHcontDomain`'s regression.  So the high-byte restriction
here is one arm's, stated on that arm, and not the continuing entry's shape.

**The method step this file's earlier version named is what found it**: the fields were each
checked against the path they were read from, and nothing in the bundle's own module reads
two of them against each other — a producer reads them together.  An elaborating structure
literal and an inhabited bundle are different claims, and only the second is what a
refinement statement consumes.

## Which lemmas this file reuses

`hlastEntry_phiSel` (a closed `phi` fact, the same list), `hlastLoc105` and `hlastLoc96`
(generic in the scan's states), `hlast_nep_toNat`, the class arithmetic the last entry's
producer established (`hlast_slt_zero_of_toInt_le`, `hlast_eq_zero_of_slt_zero`), the
document's byte (`walkDoc_byte`), and the invariant's own clauses (`WalkInv.iter.reg8`,
`WalkInv.regs`, `WalkInv.idx_reg`, `WalkInv.ptrs`).  `headAS4_envInc`/`headAS4_envNep`
are the other module's (the two carries' shared head peel), and the rest are new because
the states are new: the four at `contAS₅`, `contP35S_env8`/`contP35S_envEnd`,
`contSeamS_env8`, `contEntry_pre`, `contEntry_env3`, `contEntry_env47`,
`contTailStart_ee`, the two arithmetic lemmas `cont_ult_one`/`cont_hi63`, and this round's
`cont_static_tok`, `contEndS_docByte`, `wsCont_not_wsStop`, `cont_heicd`,
`contIx_toNat`/`cont_heicd_of`/`cont_hpos`/`cont_hread35`.
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

/-! ### The cells the model delivers

Four of the bundle's supplied groups are the model's rather than the input's content, and
each has a producer that was already in the tree when this round began:

* **the token record's register.**  `%t352.i` is one of `walkStaticRegs`'s thirty-two, so
  `WalkInv.regs` carries it at every state — `cont_static_tok`.  This is the fact the
  header used to call *not derivable*: no preservation lemma is needed once the bundle
  states the register at a state that carries the invariant, which the traversal's
  endpoint (`contWsLatch`/`revExitS`) does.
* **the byte before the entry's end.**  `cond.end349.i` writes the index and the gap marker
  inside the token record, and the token's staged extent is disjoint from the document's
  region, so the memory `contEndS` leaves holds the document's bytes: `contEndS_docByte`,
  `walkDoc_byte`'s own byte.  The *value* stays the caller's — `WalkGeom.doc` fixes the
  byte's term, not its class — but the read, the address and the index bound do not.
* **the entry's index.**  `%idxprom.i` is `WalkInv.idx_reg`'s cell, so `ix` is
  `ofNat 64 (entryPos G C.k)` and the bundle's `entryPos G C.k ≤ ix.toNat` conjunct is
  `le_rfl` at it.
* **the byte's class.**  `%35` is `cont35 b35`, whose three arms are exactly `wsStop`'s
  three, so the class disjunct *is* `wsStop G (v.toNat - 1)` and — with the per-index
  `wsCont` conjunct the bundle already carries — it bounds the run's stop
  (`cont_heicd`).  The class of the head byte is two premises, not seven: `hlt125` and
  `hne125` leave it at `126` or `127`, and the other five bits are `decide`d there. -/

/-- **The token record's register**, at every state that carries the invariant: `%t352.i` is
one of `walkStaticRegs`'s thirty-two, and `WalkInv.regs` carries them all. -/
theorem cont_static_tok {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) :
    lookupName s.env "%t352.i" = some (.ptr C.stage.tok) :=
  hInv.regs ("%t352.i", .ptr C.stage.tok) (by simp [walkStaticRegs])

/-- **The byte before the entry's end is the document's.**  `cond.end349.i` stores the
index and the gap marker inside the token record, whose staged extent is disjoint from the
document's region, so the memory `contEndS` leaves holds the document's bytes; the byte is
`walkDoc_byte`'s, at an index inside the document. -/
theorem contEndS_docByte {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) {x : BitVec 8} {inc nep : BitVec 64} {ep : Nat} {v : BitVec 32}
    {ix : BitVec 64} {q : Nat} (hq : q < G.n) :
    readBytes (contEndS C s x inc nep ep v ix).mem (G.b + q) 1 = some [G.bs.getD q 0] := by
  have hsep := stage2StagedWrites_against C.stage.separate (a := G.b)
    (m := G.n + stage2ReadTail) (by simp [stage2Regions])
    (r := (C.stage.tok, stage2TokenExtent)) (by simp [stage2StagedWrites])
  have htok : stage2TokenExtent = 24 := rfl
  rw [htok] at hsep
  have h4 : (natToBytes (BitVec.ofNat 32 1).toNat 4).length = 4 := natToBytes_length ..
  have h8 : (natToBytes ix.toNat 8).length = 8 := natToBytes_length ..
  simp only [contEndS, cte345OutAt, contAS₅, headAS₄, headAS₃, headAS₂, headAS₁,
    condEnd349OutAt, stateAt, cells, State.bind]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok + 20)
    (v := natToBytes (BitVec.ofNat 32 1).toNat 4) (by rw [h4]; rcases hsep with h | h <;> omega)]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok)
    (v := natToBytes ix.toNat 8) (by rw [h8]; rcases hsep with h | h <;> omega)]
  exact walkDoc_byte G C s hInv (by have h := hInv.alen_le; omega)
    (le_trans hInv.evlen_le G.evRoom) hq

/-- **A continuing byte and a stopping byte are different bytes.**  The two predicates are
the same three tests with the leaf's stop bit read the other way, so no byte satisfies both:
each arm of `wsCont` contradicts each arm of `wsStop` on one of the two bits the arms share. -/
theorem wsCont_not_wsStop {m0 : Mem} (G : WalkGeom m0) {q : Nat}
    (hc : wsCont G q) (hs : wsStop G q) : False := by
  unfold wsCont at hc
  unfold wsStop at hs
  rcases hc with hC | hC | hC
  · rcases hs with hS | hS | hS
    · exact absurd (hC.2.symm.trans hS.2) (by decide)
    · exact absurd (hC.1.symm.trans hS.1) (by decide)
    · exact absurd (hC.1.symm.trans hS.1) (by decide)
  · rcases hs with hS | hS | hS
    · exact absurd (hC.1.symm.trans hS.1) (by decide)
    · exact absurd (hC.2.2.symm.trans hS.2.2) (by decide)
    · exact absurd (hC.2.1.symm.trans hS.2.1) (by decide)
  · rcases hs with hS | hS | hS
    · exact absurd (hC.1.symm.trans hS.1) (by decide)
    · exact absurd (hC.2.1.symm.trans hS.2.1) (by decide)
    · exact absurd (hC.2.2.symm.trans hS.2.2) (by decide)

/-- **The stop is inside the entry's end**, from the class the whitespace check read.  The
byte before the entry's end is whitespace (`wsStop`), the run's stop is the *first* byte the
run does not continue, and the entry is non-empty (`ix < v`), so `v - 1` cannot lie below
the stop: if it did, the per-index conjunct would make it a continuing byte.  This is the
field that used to be supplied, and it is the one that decides the bundle's inhabitation —
its earlier form (`ei < cd` with `ei = cd`) is what made the other class's bundle vacuous. -/
theorem cont_heicd {m0 : Mem} (G : WalkGeom m0) {ix k v : Nat}
    (hstop : wsStop G (v - 1)) (hcont : ∀ p, ix ≤ p → p < k → wsCont G p)
    (hik : ix < k) (hixv : ix < v) : k < v := by
  by_contra h
  have hvk : v ≤ k := by omega
  have h1 : ix ≤ v - 1 := by omega
  have h2 : v - 1 < k := by omega
  exact wsCont_not_wsStop G (hcont (v - 1) h1 h2) hstop

/-- **The entry's index**, as the invariant carries it: `%idxprom.i` is
`WalkInv.idx_reg`'s cell, so the bundle's `ix` is this term at every head state. -/
abbrev contIx {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : BitVec 64 :=
  BitVec.ofNat 64 (entryPos G C.k)

/-- **The byte before the entry's end**, as the document holds it.  The read is
`contEndS_docByte`'s; this is the term the bundle's `b35` witness takes. -/
abbrev contB35 {m0 : Mem} (G : WalkGeom m0) (v : BitVec 32) : UInt8 :=
  G.bs.getD (v.toNat - 1) 0

/-- `contIx` reads back as the entry's position: it is below `2 ^ 64` and the entry is in
the document. -/
theorem contIx_toNat {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (hk : C.k + 1 < G.nep) : (contIx G C).toNat = entryPos G C.k := by
  have hk1 : C.k < G.nep := by omega
  have h1 := entryPos_lt G hk1
  have h2 := G.maxDoc
  simp only [stage2MaxDocument] at h2
  have he64 : entryPos G C.k < 2 ^ 64 := by omega
  simp only [contIx, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt he64]

/-- **The stop's bound, from the class the price already reads.**  `cont_heicd` at the
entry's index: `hugt` is the entry stream's order (`%cond350.i > %idxprom.i`), and the
class disjunct is the byte before the entry's end. -/
theorem cont_heicd_of {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {v : BitVec 32}
    {k : Nat} (hk : C.k + 1 < G.nep)
    (hws : wsStop G (v.toNat - 1))
    (hcont : ∀ q, entryPos G C.k ≤ q → q < k → wsCont G q)
    (hik : entryPos G C.k < k)
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat)
      (BitVec.ofNat 64 (entryPos G C.k)) = 1) :
    k < v.toNat := by
  have hk1 : C.k < G.nep := by omega
  have he := entryPos_lt G hk1
  have h2 := G.maxDoc
  simp only [stage2MaxDocument] at h2
  have he64 : entryPos G C.k < 2 ^ 64 := by omega
  have hv64 : v.toNat < 2 ^ 64 := by have := v.isLt; omega
  have hixv : entryPos G C.k < v.toNat := by
    have h := (evalICmp_ugt_one_iff_toNat (BitVec.ofNat 64 v.toNat)
      (BitVec.ofNat 64 (entryPos G C.k))).1 hugt
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64,
      Nat.mod_eq_of_lt hv64] at h
  exact cont_heicd G hws hcont hik hixv

/-- **The landing's index is a document position**, so its sign-extended reading is itself
below `2 ^ 63`: the stop is inside the entry's end, and the end is inside the document. -/
theorem cont_hpos {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {v : BitVec 32}
    {k : Nat} (hk : C.k + 1 < G.nep) (hspan : v.toNat ≤ entryPos G (C.k + 1))
    (hkv : k < v.toNat) :
    ((BitVec.ofNat 64 k).signExtend 64).toNat < 2 ^ 63 := by
  have hnext := entryPos_lt G hk
  have h2 := G.maxDoc
  simp only [stage2MaxDocument] at h2
  have hv : v.toNat ≤ G.n := le_trans hspan (le_of_lt hnext)
  have hk64 : k < 2 ^ 64 := by omega
  simp only [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  omega

/-- **The byte before the entry's end, read at `contEndS`**: the address is the document's
own `G.b + (v - 1)` and the byte is `walkDoc_byte`'s across the two token-record stores
(`contEndS_docByte`). -/
theorem cont_hread35 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep) {v : BitVec 32} {k : Nat}
    (hspan : v.toNat ≤ entryPos G (C.k + 1)) (hkv : k < v.toNat) :
    readBytes (contEndS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v
      (contIx G C)).mem ((G.b - 1) + v.toNat) 1 = some [contB35 G v] := by
  have hnext := entryPos_lt G hk
  have hv : v.toNat ≤ G.n := le_trans hspan (le_of_lt hnext)
  have hq : v.toNat - 1 < G.n := by omega
  have hv1 : 1 ≤ v.toNat := by omega
  have hb : 1 ≤ G.b := G.bPos
  rw [show (G.b - 1) + v.toNat = G.b + (v.toNat - 1) from by omega]
  exact contEndS_docByte G C s hInv (x := hlastByte G C) (inc := hlastIncV C)
    (nep := hlastNepV G) (ep := G.ep) (v := v) (ix := contIx G C) hq

/-- **The tail's three numeric hypotheses, from the bundle's class field.**  `consumerTailSegAt`
takes `cd - ei ≤ C.inner`, `ei < cd` and `cd < 2 ^ 64` at the scan's entry; on this arm
`ei = k` and `cd = v.toNat`.  The middle is `heicd`, the last is the lane word's width, and
the first — the one this file's map used to call unobtainable — follows from the class's
budget (`v.toNat - entryPos C.k ≤ C.inner`) and the stop's position (`entryPos C.k < k`).
So the tail's segment is exactly `consumerTailSegAt`'s at the seam's landing; what it still
needs is that lemma's callee premises, not a span. -/
theorem cont_wsTailSpan {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {v : BitVec 32}
    {k : Nat} (hik : entryPos G C.k < k) (hkv : k < v.toNat)
    (hbudget : v.toNat - entryPos G C.k ≤ C.inner) :
    v.toNat - k ≤ C.inner ∧ k < v.toNat ∧ v.toNat < 2 ^ 64 := by
  refine ⟨by omega, hkv, ?_⟩
  have hv := v.isLt
  omega

/-! ### The producer

`HcontFacts` from the entry's evidence.  The groups the invariant and the staging fix are
*derived* — the head's byte and its seven class bits (two premises), the two counts and their
cells, the count test's value, the entry's index, the default arm's four cells, the byte
before the entry's end and the stop's bound — and the rest is supplied, each with the reason
the layer cannot produce it: the entry's word, the whitespace class, the tail's three calls,
the scan's landing and its traversal's three hypotheses.  The run is no longer supplied:
`contWsRunF` (`JsonStage2WalkRevolution`) derives it from the class, and this module names its
endpoint as the total function `contWsSlStaging`. -/

/-- **The bundle's stop term at the staging's own values**: the total function of the
byte, the lane's word and the run's stop. -/
abbrev contWsSlStaging {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8) (k : Nat) : State :=
  wsSlS G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v ix b35 k

/-- **The bundle, from the entry's evidence.**  Produced at the loop's own values: the head's
byte is `hlastByte G C`, the counts are `hlastIncV C`/`hlastNepV G`, the position table is
`G.ep`, and the classes are read on `hlastByte G C`.  `hnext` is derived from `hk`
(`cont_ult_one`), `hi63` from `hk` and the stream's size (`cont_hi63`), and the default
arm's four cells are the invariant's peels at `contAS₅` — so only the class, the document's
facts, the tail and the traversal enter as premises.  The class is `hClass`, and it is what
makes the run derivable: the segment, its count and its price come from `contWsRunF` and
`contWsPriceF`, and the seam's `%end.i` from `wsSlS_envEnd`.

`hopS` is **not** a premise any more: at `contWsEntry` the seam stored the run's stop
(`contWsEntry_ee`), so the landing's index follows from the cell rather than being asserted
against a stopper.  That is the repair this producer's earlier shape recorded as impossible
— see this module's header. -/
def hcontFacts_of_staging {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    {v : BitVec 32}
    (hread : readBytes (contAS₅ s (hlastByte G C) (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat)
      (BitVec.ofNat 64 (entryPos G C.k)) = 1)
    {k : Nat}
    (hClass' :
      wsStop G (v.toNat - 1) ∧
        (∀ q, entryPos G C.k ≤ q → q < k → wsCont G q) ∧ wsStop G k ∧
        entryPos G C.k < k ∧ v.toNat - entryPos G C.k ≤ C.inner)
    (h8c : evalOperand (contWsSeamS C (contWsSlStaging G C s v (contIx G C) (contB35 G v) k) k
      (hlastByte G C)) (.reg "%8") = some (.int 8 (hlastByte G C)))
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) {cA rdv xA : BitVec 32}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
      (contWsTailStart C (contWsSlStaging G C s v (contIx G C) (contB35 G v) k) k (hlastByte G C)
        (hlastByte G C))
      (TailCarryScan (ContTailStartC C) ev)
      (contWsEntry C (contWsSlStaging G C s v (contIx G C) (contB35 G v) k) k (hlastByte G C)
        (hlastByte G C) r₁ r₂ r₃ k v cA rdv xA) 3)
    {q : Nat} {bs : List UInt8} {x47 : BitVec 8}
    (hreadS : readBytes
      (contWsEntry C (contWsSlStaging G C s v (contIx G C) (contB35 G v) k) k (hlastByte G C)
        (hlastByte G C) r₁ r₂ r₃ k v cA rdv xA).mem
      (G.b + ((BitVec.ofNat 64 k).signExtend 64).toNat) 1 = some bs)
    (hbsS : bytesToNat bs = q)
    (h47 : evalOperand
      (landRhs457OutAt (contWsEntry C (contWsSlStaging G C s v (contIx G C) (contB35 G v) k) k (hlastByte G C)
        (hlastByte G C) r₁ r₂ r₃ k v cA rdv xA) (BitVec.ofNat 64 k) G.b q)
      (.reg "%47") = some (.int 8 x47))
    (hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1)
    (hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1)
    (hlatch : WalkLocal { TailCarryScan (ContTailStartC C) ev with block := "while.body462.i" }
      (contWsLatch C (contWsSlStaging G C s v (contIx G C) (contB35 G v) k) k (hlastByte G C) (hlastByte G C)
        r₁ r₂ r₃ k v cA rdv xA (BitVec.ofNat 64 k) G.b q x47))
    (hspan : v.toNat ≤ entryPos G (C.k + 1))
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
    :
    HcontFacts G C s :=
  let hkv : k < v.toNat :=
    cont_heicd_of G C hk hClass'.1 hClass'.2.1 hClass'.2.2.2.1 hugt
  { x := hlastByte G C
    h8 := by
      show evalOperand s (.reg "%8") = some (.int 8 (hlastByte G C))
      simp only [evalOperand]
      exact hInv.iter.reg8
    hlt91 := hlast_slt_zero_of_toInt_le (by decide) hlt125
    hlt123 := hlast_slt_zero_of_toInt_le (by decide) hlt125
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
    ix := contIx G C
    hidx5 := contAS5_envIdx s (hlastByte G C) (hlastIncV C) (hlastNepV G) (contIx G C)
      hInv.idx_reg
    htok5 := contAS5_envTok C s (hlastByte G C) (hlastIncV C) (hlastNepV G)
      (cont_static_tok hInv)
    hgap5 := contAS5_envGap C s (hlastByte G C) (hlastIncV C) (hlastNepV G)
      (hInv.regs ("%gap.i", .ptr (C.stage.tok + 20)) (by simp [walkStaticRegs]))
    hugt := hugt
    b35 := contB35 G v
    hread35 := cont_hread35 G C s hInv hk hspan hkv
    k := k
    x1 := hlastByte G C
    hClass := by
      have hix_toNat : (contIx G C).toNat = entryPos G C.k := contIx_toNat G C hk
      refine ⟨?_, ?_, hClass'.2.2.1, ?_, ?_, ?_⟩
      · simpa only [cont35, contB35, wsStop, wsX, wsByte] using hClass'.1
      · intro q h1 h2
        exact hClass'.2.1 q (by rw [hix_toNat] at h1; exact h1) h2
      · rw [hix_toNat]; exact hClass'.2.2.2.1
      · rw [hix_toNat]; exact hClass'.2.2.2.2
      · rw [hix_toNat]
    heicd := hkv
    h8c := h8c
    hc110 := hlast_slt_zero_of_toInt_le (by decide) hlt125
    hc116 := hlast_slt_zero_of_toInt_le (by decide) hlt125
    hceq116 := hlast_eq_zero_of_slt_zero (by decide) hlt125
    r₁ := r₁
    r₂ := r₂
    r₃ := r₃
    ev := ev
    cA := cA
    rdv := rdv
    xA := xA
    hTail := hTail
    a := G.b
    q := q
    bs := bs
    h3S := hTail.inv'.ptrs.1
    hpos := cont_hpos G C hk hspan hkv
    hreadS := hreadS
    hbsS := hbsS
    hloc105 := hlastLoc105 (ContTailStartC C) ev
      (contWsEntry C (contWsSlStaging G C s v (contIx G C) (contB35 G v) k) k
        (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ k v cA rdv xA)
      (BitVec.ofNat 64 k) G.b q
    x47 := x47
    h47 := h47
    hbit47 := hbit47
    hws47 := hws47
    hloc96 := hlastLoc96 (ContTailStartC C) ev
      (contWsEntry C (contWsSlStaging G C s v (contIx G C) (contB35 G v) k) k
        (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ k v cA rdv xA)
      (BitVec.ofNat 64 k) G.b q x47
    hlatch := hlatch
    hspan := hspan
    hstart := le_of_lt hClass'.2.2.2.1
    hround := hround
    hguard := hguard
    hbyte := hbyte
    htok := fun C' s' hInv' _ => ⟨C'.stage.tok, cont_static_tok hInv'⟩ }

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.contTailStart_ee
#print axioms LeanLLVM.Refinement.WalkScope.cont_ult_one
#print axioms LeanLLVM.Refinement.WalkScope.cont_hi63
#print axioms LeanLLVM.Refinement.WalkScope.cont_static_tok
#print axioms LeanLLVM.Refinement.WalkScope.contEndS_docByte
#print axioms LeanLLVM.Refinement.WalkScope.wsCont_not_wsStop
#print axioms LeanLLVM.Refinement.WalkScope.cont_heicd
#print axioms LeanLLVM.Refinement.WalkScope.cont_heicd_of
#print axioms LeanLLVM.Refinement.WalkScope.cont_hpos
#print axioms LeanLLVM.Refinement.WalkScope.cont_hread35
#print axioms LeanLLVM.Refinement.WalkScope.cont_wsTailSpan
#print axioms LeanLLVM.Refinement.WalkScope.hcontFacts_of_staging

end WalkScope
end LeanLLVM.Refinement
