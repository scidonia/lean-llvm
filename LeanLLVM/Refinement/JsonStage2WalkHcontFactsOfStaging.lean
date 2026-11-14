/-
# The continuing entry's facts, from the staging

`WalkContinueFacts` (`JsonStage2WalkPremisesOfStaging`) is the continuing entry's
obstruction: `HcontFacts` at every head state with an entry left, and it has no producer
in the tree.  `HcontFacts` (`JsonStage2WalkRevolution`) is the bundle `walkRevolution_seg`
consumes, field for field; its prefix group is `HlastFacts`' (`JsonStage2WalkDispatchWitnessHlast`),
because it is the same path to the same latch.  This module is the twin of
`hlastFacts_of_staging`: the same three sources — the invariant's clauses, the document's
content and the staging's addresses — read at the same states, producing the continuing
bundle instead of the last entry's.

## The twin's shape

`hlastFacts_of_staging` is a `def`, because the bundle is a `Type`: its first member of
each group is a *witness* the later fields are stated at.  This is a `def` for the same
reason, and it takes the same evidence.  Three differences, each a consequence of the two
bundles' statements rather than a choice made here:

* **There is no `hk`.**  The last entry's producer takes `C.k + 1 = G.nep` because its
  counts are the loop's own values and its price is arithmetic on that equation.  The
  continuing bundle carries `hspan`/`hstart` (the scan's span against the entry's own
  positions) and no equation between the counts and the stream's length, so nothing in
  `HcontFacts`' field types reads the consumer's `C.k + 1 < G.nep`.  A producer stated
  without it applies at the consumer's states unchanged, and the absence is stated here
  rather than left as an unused binder.
* **There is no `hblock` either.**  The last entry's producer reads the block once, for the
  refill's `walkLoopHead_inner_pos` — the `1 ≤ C.inner` its `hinner` field needs.  The
  continuing bundle carries no inner budget, so no field of it reads the block, and the
  premise is dropped rather than bound and discarded: a caller applies this `def` at the
  head state it holds.
* **The scan's traversal is not part of the prefix group any more.**  `HlastFacts` used
  the last entry's scan (`qi`, `cw`, `hq`, `hqc`, `hexit`, `htokL`, `hinner`), whose bound
  is the tail's own `cd` and whose last visit is `cd - 1`.  `HcontFacts` states the
  traversal's three hypotheses (`hround`, `hguard`, `hbyte`) and the token's register at
  its exit (`htok`) instead, because the continuing entry's scan runs over the entry's
  span; they arrive as premises and the last group is the one obstruction no staging
  evidence closes.

## What producing the bundle found

The producer's one obstruction is not a missing lemma.  It is a contradiction between two of
the bundle's own field groups, and it is recorded at the structure (`HcontFacts`' doc
comment, `JsonStage2WalkRevolution`) as well as here:

> `hge` is `¬ (C.k + 1 < G.nep)` at a real head state, because `%inc.i = C.k + 1` and
> `%nep = G.nep` there; the consumer's `hk` is `C.k + 1 < G.nep`; so the bundle is
> uninhabited at every continuing entry — `walkRevolution_seg` is vacuous, and the prefix it
> composes (`hlastPrefixSeg`, the `cond.end349.i` arm) is the wrong arm for a continuing
> entry, which runs through `cond.true345.i`.

It was invisible until now because **the bundle was constructed before any consumer existed,
and the contradiction is between two of its own fields** — `hge` against `hinc`/`hnep` — not
between a field and the walk: each field is true of the path it was read from, and nothing in
the bundle's own module reads the two groups against each other or against a consumer's
hypothesis.  A producer reads them together, which is what this file does, and that is why
the obstruction surfaces here as a supplied premise rather than as a failed proof.

So the map below describes the bundle as stated, and its figure is the honest strength of
that statement — not of the revolution, which the finding above leaves vacuous.  Two
premises the last entry's producer carries are absent here, and each is one both ends
discard: no `hk`, because no field reads `C.k + 1 < G.nep`, and no `hblock`, because the
block was read only for the refill the missing `hinner` field needed.  *A premise both ends
discard is not a premise*, so neither is carried.

## The map, per group

Produced · reduced to a named premise · premised correctly (the model cannot supply it).
The classes are the ones `hlastFacts_of_staging`'s header carries, so the two maps can be
read against each other.

| group | status |
|---|---|
| the head's byte (`x`, `h8`) | **produced**: `hInv.iter.reg8` is the field, and the witness is the name `hlastByte G C = ofNat 8 (entryByte G C.k).toNat` — the same term the last entry's producer uses, because it is the same loop head |
| the four pivot bits (`hlt91`, `hlt123`, `hlt125`, `hne125`) and the seam's byte test (`hbit6`) | **premised correctly: the document's.**  Five of the eight class bits on the head's byte are decisions about `entryByte G C.k` |
| the second byte's three class bits (`hc110`, `hc116`, `hceq116`) | **premised correctly: the document's**, the other three of the eight; `%8` is not rebound between the head and the seam, so all eight are one byte |
| the entry counts' witnesses and their head facts (`inc`, `nep`, `hinc`, `hnep`) | **produced**: the witnesses are the loop's values (`hlastIncV C`, `hlastNepV G`) and the two cells are the staging's loop-head registers (`hincL`, `hnepL`) peeled from `s` down to `headAS₄` (`headAS4_envInc`, `headAS4_envNep`) |
| the count test's resolution (`hge`) | **premised correctly: the stream's** — the row that resisted, and the one the finding above is about.  `sw.default.i`'s test is `ult (%inc.i, %nep)`, so `hge` says the head path leaves on the failing arm; with the counts pinned to the loop's values it is `¬ (C.k + 1 < G.nep)`, the last entry's equation, which is exactly the one fact `HcontFacts`' consumer does *not* imply (`C.k + 1 < G.nep` is its hypothesis).  **The bundle therefore carries the count test's value as the caller's**: it is a property of the entry stream (`%nep` against `%inc.i`), not of the invariant, and the only route the layer has to a *value* of that test is `hlast_ult_self` at `inc = nep`.  Producing it at a continuing entry needs the head path through `cond.true345.i`, which `hlastPrefixSeg` does not state; that arm is new work in the prefix, not a residue here |
| the default arm's cells (`reg`, `c`, `ix`, `hpre5`, `hav5`, `hidx5`, `htok5`, `hgap5`) | **produced**: `hlast_pre5` is a closed `phi` computation; `%4` and `%gap.i` peel from the default arm to `s` (`hlastAS5_envFour`, `hlastAS5_envGap`) and `%idxprom.i`/`%t352.i` are the staging's at the head (`hlastAS5_envIdx`, `hlastAS5_envTok`), so `c = ofNat 64 v` is the staging's `h4L` |
| the token position's relation (`hugt`) | **premised correctly: the document's.**  The token's position against the entry's index relates `%4`'s word to the entry stream, and neither the invariant nor the staging fixes it |
| the seam's cells (`p`, `op`, `e`, `b8`, `hpre6`, `hin6`, `hv6`, `hend6`, `h8end`) | **produced**: `hlast_pre6` is the state's own predecessor and `hlast_phi6` a closed `phi`; `%8`/`%end.i`/`%idxprom.i` peel from the token's end to the loop head (`hlastEndS_env8`, `hlastEndS_envEnd`, `hlastEndS_envIdx`), so `e = ix`, `%end.i` is `regs`'s and `pre` is `cond.end349.i`'s |
| the second byte's class name (`x1`, `h8c`) | **produced**: `if.end372.i` binds five cells and none is `%8`, so `hlastSeam_env8` peels the seam to the token's end and `h8c` *is* `h8end` — the first byte's cell |
| the tail's three call outcomes and the trace's record (`r₁`, `r₂`, `r₃`, `ev`, `cA`, `rdv`, `xA`) | **produced**: the three contracts applied at their three staged argument lists (`s2ValuePosContract`, `s2ScalarValueContract`, `s2AfterValueContract`) |
| the appended record's name (`happ₂`) | **premised correctly:** `s2ScalarValuePost` concludes the append existentially in the record while the bundle's `ev` is the trace's, so naming it is the emission's step — the row the last entry's producer carries for the same reason |
| the tail's counted segment (`hTail`, `ei`, `cd`) | **produced**: `hlastTail_of_calls` — the three contracts composed by `consumerTailSegAt` at count `3` — with `ei`/`cd` the seed's words (`heiT`, `hcdT`) and the three facts the composition needs (`hinnerT`, `hlt2T`, `hcd64T`) |
| the scan's landing (`a`, `q`, `bs`, `src`, `sel`, `hpreS`, `hincS`, `hopS`, `h3S`, `hbsS`, `hloc105`, `hloc96`) | **produced**: `hlastEntry_pre` and `hlastEntry_phiSel` are the entry's own construction; `%ee.1.i` and `%3` peel to the tail's start (`hlastEntry_envEe`, `hlastEntry_env3`), so the selection is `%ee.1.i`, `hopS` is `heiT` and `a = G.b`; `%47` is `landRhs457OutAt`'s own cell (`x47 = ofNat 8 q`) with `q` the byte read's value (`hbsS` is `rfl`), and `hloc105`/`hloc96` hold because neither block is a `WalkLocal` scan block (`hlastLoc105`, `hlastLoc96`) |
| the landing's byte read and its two tests (`hpos`, `hreadS`, `hbit47`, `hws47`) | **premised correctly: the document's.**  The byte at `G.b + ei`, the bound its extraction needs and the two tests on it are properties of `G.bs` at the entry's own index; the staging fixes addresses and extents, not values |
| the latch's local and its bound (`hlatch`, `hcwL`) | **reduced to a named premise.**  `WalkLocal` at `while.body462.i` *is* the `ScanCount` the latch's own state writes, and `%cond350.i` is `cond.end349.i`'s `phi` cell: it peels from the latch through the scan's entry to the tail's start and is `hcdT` there (`contEntry_envCond350`, `latch_cond`) |
| the span's two numbers and the scan's non-emptiness (`hspan`, `hstart`, `heicd`) | **premised correctly: the document's.**  `cd` is the next entry's position or before it, `ei` this entry's or after it, and `ei < cd` the entry's non-emptiness — the entry stream's numbers, which the staging does not fix |
| the traversal's three hypotheses (`hround`, `hguard`, `hbyte`) | **supplied: a named premise.**  `walkScanRounds457`'s own, unweakened — the round at a byte, the latch's guard, and the input's totality at every index the scan visits (the model branches on a byte it does not store).  A `WalkSegment` cannot carry them: the segment records a run and an invariant, not the per-visit obligations a traversal's induction consumes |
| the token's register at the scan's exit (`htok`) | **supplied: a named premise, and it is not derivable.**  A traversal whose final state is existential has no named term to state a register at, and the layer has no preservation lemma for registers.  The lemma that would close it is *the extra-token scan preserves a register it does not bind*; that statement needs the visit's target state, which `walkScanRounds457`'s conclusion does not expose |

**The map's counted shape, per row: 8 produced, 1 reduced to a named premise, 7 premised
correctly, 2 supplied as named premises** — eighteen rows in all, so **8 of 18 produced.**
The seven correctly-premised are the document's five (its eight class bits, its position
relation, its scanned byte and its two tests on it, its span's two numbers, and the scan's
non-emptiness — one row each where the bundle states them apart), the record the callee
does not name, and the count test; each names the clause, list or contract that *cannot*
supply it.  The two
supplied rows are the traversal's hypotheses and the token's register, and each names the
lemma the layer does not have.  The count test's row is the one that would be produced at a
last entry and is not at a continuing one, and its reason is written there rather than
here.

## Which of the last entry's lemmas this file reuses

The prefix and the landing are the same path, so the producer's body is
`hlastFacts_of_staging`'s for those groups, lemma for lemma:

* the default arm: `hlast_pre5`, `hlastAS5_envFour`, `hlastAS5_envIdx`, `hlastAS5_envTok`,
  `hlastAS5_envGap`;
* the seam: `hlast_pre6`, `hlast_phi6`, `hlastEndS_envIdx`, `hlastEndS_envEnd`,
  `hlastEndS_env8`, and `hlastSeam_env8` for the second byte's class;
* the tail: `hlastTail_of_calls`, at `hlastTailAt` the last entry's producer uses;
* the landing: `hlastEntry_pre`, `hlastEntry_phiSel`, `hlastEntry_envEe`,
  `hlastEntry_env3`, `landRhs457OutAt_env47`, `hlastLoc105`, `hlastLoc96`;
* the invariant's own: `WalkInv.iter.reg8`, `WalkInv.regs` (`%gap.i`, `%end.i`).

Three things are new and each is a *statement at the continuing bundle's own field type*
rather than a re-derivation: the two head peels (`headAS4_envInc`, `headAS4_envNep`), the
count's peel from the scan's entry to the tail's start (`contEntry_envCond350`), and the
latch's bound read off it (`latch_cond`, which `JsonStage2WalkRevolution` already states).
No lemma in the last entry's file states a `%inc.i`/`%nep`/`%cond350.i` peel at the loop
head or at the latch, because that bundle took those cells as arguments; the twins are the
same `simp`-and-`lookupName_cons_ne` peels the file's own register lemmas use.
-/

import LeanLLVM.Refinement.JsonStage2WalkRevolution

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The peels the continuing bundle needs that the last entry's file states nowhere

The last entry's bundle takes `%inc.i`, `%nep` and `%cond350.i` as arguments, so its file
has no lemma for them: the counts were fixed by `C.k + 1 = G.nep` and the latch's bound by
`qi + 1 = cw`.  The continuing bundle fixes neither, so the three cells are produced here —
each by the same peel its neighbours already use. -/

/-- `%inc.i` at `sw.default.i`'s entry is `%inc.i` at the loop head: the head chain's five
arms bind their own pivot cells and none rebinds it. -/
theorem headAS4_envInc (s : State) (x : BitVec 8) :
    lookupName (headAS₄ s x).env "%inc.i" = lookupName s.env "%inc.i" := by
  simp only [headAS₄, headAS₃, headAS₂, headAS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%nep` at `sw.default.i`'s entry is `%nep` at the loop head.  `%nep` is an argument
the walk never writes, so the two readings are one cell. -/
theorem headAS4_envNep (s : State) (x : BitVec 8) :
    lookupName (headAS₄ s x).env "%nep" = lookupName s.env "%nep" := by
  simp only [headAS₄, headAS₃, headAS₂, headAS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%cond350.i` at the scan's entry is its cell at the tail's start: the scan's entry
binds the three calls' answers and the copy's two words, and `cond.end349.i`'s `phi` cell
is none of them. -/
theorem contEntry_envCond350 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (c ix : BitVec 64) (e : BitVec 64) (b8 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ei cd : Nat) (cA rdv xA : BitVec 32) :
    lookupName (hlastEntryAt C s x c ix e b8 b8 r₁ r₂ r₃ ei cd cA rdv xA).env "%cond350.i" =
      lookupName (hlastTailS C s x c ix e b8).env "%cond350.i" := by
  simp only [hlastEntryAt, hlastEntry, hlastTailS, ScanEntry, TailS₃, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-! ### The producer

`HcontFacts` from the entry's evidence: the three sources the last entry's producer reads,
with the scan's traversal supplied rather than derived.
-/

/-- **The bundle, from the entry's evidence.**  The prefix group is `hlastFacts_of_staging`'s,
lemma for lemma — the head path, the default arm's cells, the seam's, the second byte's
class, the tail's counted segment and the scan's landing — because it is the same path to
the same latch.  What changes is the scan: the continuing entry's traversal is stated as
`walkScanRounds457`'s three hypotheses, and the token's register at its exit is supplied.

The count test's resolution (`hge`) is the caller's: with the counts the loop's values it
is `¬ (C.k + 1 < G.nep)`, so it is not a consequence of `WalkInv` and it is not implied by
the consumer's `C.k + 1 < G.nep`.  See the group's row above. -/
def hcontFacts_of_staging {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s)
    (hlt91 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 91) = 0)
    (hlt123 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 123) = 0)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    {v : Nat}
    (hincL : lookupName s.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 1))))
    (hnepL : lookupName s.env "%nep" = some (.int 64 (hlastNepV G)))
    (hge : evalICmp .ult (hlastIncV C) (hlastNepV G) = 0)
    (h4L : lookupName s.env "%4" = some (.int 64 (BitVec.ofNat 64 v)))
    {ix : BitVec 64}
    (hidxS : lookupName s.env "%idxprom.i" = some (.int 64 ix))
    (htokS : lookupName s.env "%t352.i" = some (.ptr C.stage.tok))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v) ix = 0)
    (hbit6 : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (hc110 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 0)
    (hc116 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 116) = 0)
    (hceq116 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 116) = 0)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) {cA rdv : BitVec 32} {xA : BitVec 32}
    (ei cd : Nat)
    (hInvT : WalkInv G (TailStartC C) (hlastTailAt C s v ix))
    {pT : String} {opT : Operand} {regT : String}
    (hpreT : (hlastTailAt C s v ix).pre = some pT)
    (hincT : phiIncoming pT
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some opT)
    (hopT : evalOperand (stateAt (hlastTailAt C s v ix).env
      (hlastTailAt C s v ix)) opT = some (.int 32 cA))
    (hkindT : lookupName (hlastTailAt C s v ix).env "%kind404.i" =
      some (.ptr (C.stage.tok + 16)))
    (hrdT : lookupName (hlastTailAt C s v ix).env "%root_done.i" =
      some (.ptr (G.next0 + 8)))
    (hreadT : readBytes
      (writeBytes (hlastTailAt C s v ix).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpre₁ : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .int 32 rdv,
       .ptr (TailStartC C).stage.ctype, .ptr (TailStartC C).stage.cst]
      (writeBytes (hlastTailAt C s v ix).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (hlastTailAt C s v ix).next)
    (hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .int 32 rdv,
       .ptr (TailStartC C).stage.ctype, .ptr (TailStartC C).stage.cst]
      (writeBytes (hlastTailAt C s v ix).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (hlastTailAt C s v ix).next = some r₁)
    (hret₁ : r₁.ret = .int 32 xA)
    (hbit0T : evalICmp .eq xA (BitVec.ofNat 32 0) = 0)
    (hzread : readBytes
      (writeBytes (hlastTailAt C s v ix).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) C.stage.z 8 = some (wordBytes 8 G.ev))
    (hcT : lookupName (hlastTailAt C s v ix).env "%c.i" =
      some (.ptr (TailCarry₂ (TailStartC C)).stage.c))
    (htT : lookupName (hlastTailAt C s v ix).env "%t352.i" =
      some (.ptr (TailCarry₂ (TailStartC C)).stage.tok))
    (hoT : lookupName (hlastTailAt C s v ix).env "%z" =
      some (.ptr (TailCarry₂ (TailStartC C)).stage.z))
    (hpre₂ : s2ScalarValuePre
      [.ptr (TailCarry₂ (TailStartC C)).stage.c, .ptr (TailCarry₂ (TailStartC C)).stage.tok,
       .ptr (TailCarry₂ (TailStartC C)).stage.z] r₁.mem r₁.next)
    (hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr (TailCarry₂ (TailStartC C)).stage.c, .ptr (TailCarry₂ (TailStartC C)).stage.tok,
       .ptr (TailCarry₂ (TailStartC C)).stage.z] r₁.mem r₁.next = some r₂)
    (happ₂ : s2ScalarValueAppend r₁.mem r₂.mem
      (TailCarry₂ (TailStartC C)).stage.z ev.encodedBytes)
    (hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1))
    (hev64 : G.ev < 2 ^ 64) (hevlen64 : C.evlen < 2 ^ 64)
    (hltT : C.events.length < C.k)
    (hpre₃ : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .ptr (G.next0 + 8),
       .ptr (TailCarry₃ (TailStartC C) ev).stage.ctype,
       .ptr (TailCarry₃ (TailStartC C) ev).stage.cst] r₂.mem r₂.next)
    (hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .ptr (G.next0 + 8),
       .ptr (TailCarry₃ (TailStartC C) ev).stage.ctype,
       .ptr (TailCarry₃ (TailStartC C) ev).stage.cst] r₂.mem r₂.next = some r₃)
    (heiT : lookupName (hlastTailAt C s v ix).env "%ee.1.i" =
      some (.int 64 (BitVec.ofNat 64 ei)))
    (hcdT : lookupName (hlastTailAt C s v ix).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 cd)))
    (hinnerT : cd - ei ≤ (TailStartC C).inner) (hlt2T : ei < cd) (hcd64T : cd < 2 ^ 64)
    {bs : List UInt8}
    (hpos : ((BitVec.ofNat 64 ei).signExtend 64).toNat < 2 ^ 63)
    (hreadS : readBytes
      (hlastEntryAt C s (hlastByte G C) (BitVec.ofNat 64 v) ix ix (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ ei cd cA rdv xA).mem
      (G.b + ((BitVec.ofNat 64 ei).signExtend 64).toNat) 1 = some bs)
    (hbit47 : evalICmp .slt (BitVec.ofNat 8 (bytesToNat bs)) (BitVec.ofNat 8 13) = 1)
    (hws47 : evalICmp .ule (BitVec.ofNat 8 (bytesToNat bs) + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 1)
    (hlatch : WalkLocal { TailCarryScan (TailStartC C) ev with block := "while.body462.i" }
      (hlastLatchAt C s (hlastByte G C) (BitVec.ofNat 64 v) ix ix (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ ei cd cA rdv xA
        (BitVec.ofNat 64 ei) G.b (bytesToNat bs) (BitVec.ofNat 8 (bytesToNat bs))))
    (hspan : cd ≤ entryPos G (C.k + 1))
    (hstart : entryPos G C.k ≤ ei)
    (heicd : ei < cd)
    (hround : ∀ (C' : WalkCarry G) (s' : State) (p a : Nat) (bs : List UInt8) (q : Nat)
      (x : BitVec 8), WalkInv G C' s' → C'.block = "while.body462.i" →
      lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
      lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd)) →
      p + 1 < cd → p + 1 < 2 ^ 63 →
      lookupName (scanLatchOut s' "%inc463.i" "%exitcond298.not" p cd "land.rhs457.i").env
        "%3" = some (.ptr a) →
      readBytes s'.mem (a + (p + 1)) 1 = some bs → bytesToNat bs = q →
      evalOperand (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p cd
        "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) →
      evalICmp .slt x (BitVec.ofNat 8 13) = 1 →
      evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 →
      WalkLocal (ScanC₁₀₅ (ScanCLand C'))
        (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p cd "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q) →
      WalkLocal (ScanC₉₆ (ScanCLand C'))
        (ScanS₉₆ (scanLatchOut s' "%inc463.i" "%exitcond298.not" p cd "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x) →
      WalkLocal { ScanCLand C' with block := "while.body462.i" }
        (Latch462S (scanLatchOut s' "%inc463.i" "%exitcond298.not" p cd "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x) →
      ∃ (C'' : WalkCarry G) (s'' : State) (j : Nat),
        WalkSegment (stage2Calls stage2SubCalls) G C' s' C'' s'' j ∧
        WalkInv G C'' s'' ∧ C''.block = "while.body462.i" ∧ j ≤ stage2ByteAllowance ∧
        lookupName s''.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (p + 1))) ∧
        lookupName s''.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd)))
    (hguard : ∀ (C' : WalkCarry G) (s' : State), WalkInv G C' s' →
      C'.block = "while.body462.i" → ScanGuard s' "%q.0.i246" "%cond350.i" C'.inner)
    (hbyte : ∀ (C' : WalkCarry G) (s' : State) (p : Nat), WalkInv G C' s' →
      C'.block = "while.body462.i" → p + 1 < cd →
      lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
      lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd)) →
      ∃ (a : Nat) (bs : List UInt8) (q : Nat) (x : BitVec 8),
        lookupName (scanLatchOut s' "%inc463.i" "%exitcond298.not" p cd "land.rhs457.i").env
          "%3" = some (.ptr a) ∧
        readBytes s'.mem (a + (p + 1)) 1 = some bs ∧ bytesToNat bs = q ∧
        evalOperand (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p cd
          "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) ∧
        evalICmp .slt x (BitVec.ofNat 8 13) = 1 ∧
        evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 ∧
        WalkLocal (ScanC₁₀₅ (ScanCLand C'))
          (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p cd "land.rhs457.i")
            (BitVec.ofNat 64 (p + 1)) a q) ∧
        WalkLocal (ScanC₉₆ (ScanCLand C'))
          (ScanS₉₆ (scanLatchOut s' "%inc463.i" "%exitcond298.not" p cd "land.rhs457.i")
            (BitVec.ofNat 64 (p + 1)) a q x) ∧
        WalkLocal { ScanCLand C' with block := "while.body462.i" }
          (Latch462S (scanLatchOut s' "%inc463.i" "%exitcond298.not" p cd "land.rhs457.i")
            (BitVec.ofNat 64 (p + 1)) a q x))
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
    hge := hge
    reg := "%4"
    c := BitVec.ofNat 64 v
    ix := ix
    hpre5 := hlast_pre5
    hav5 := hlastAS5_envFour s (hlastByte G C) (hlastIncV C) (hlastNepV G)
      (BitVec.ofNat 64 v) h4L
    hidx5 := hlastAS5_envIdx s (hlastByte G C) (hlastIncV C) (hlastNepV G) ix hidxS
    htok5 := hlastAS5_envTok C s (hlastByte G C) (hlastIncV C) (hlastNepV G) htokS
    hgap5 := hlastAS5_envGap C s (hlastByte G C) (hlastIncV C) (hlastNepV G)
      (hInv.regs ("%gap.i", .ptr (C.stage.tok + 20)) (by simp [walkStaticRegs]))
    hugt := hugt
    p := "cond.end349.i"
    op := .reg "%idxprom.i"
    e := ix
    b8 := hlastByte G C
    hpre6 := hlast_pre6 C s (hlastByte G C) (hlastIncV C) (hlastNepV G)
      (BitVec.ofNat 64 v) ix
    hin6 := hlast_phi6
    hv6 := by
      simp only [evalOperand]
      rw [hlastEndS_envIdx C s (hlastByte G C) (hlastIncV C) (hlastNepV G)
        (BitVec.ofNat 64 v) ix]
      exact hidxS
    hend6 := by
      rw [hlastEndS_envEnd C s (hlastByte G C) (hlastIncV C) (hlastNepV G)
        (BitVec.ofNat 64 v) ix]
      exact hInv.regs ("%end.i", .ptr (C.stage.tok + 8)) (by simp [walkStaticRegs])
    h8end := by
      rw [hlastEndS_env8 C s (hlastByte G C) (hlastIncV C) (hlastNepV G)
        (BitVec.ofNat 64 v) ix]
      exact hInv.iter.reg8
    hbit6 := hbit6
    x1 := hlastByte G C
    h8c := by
      simp only [evalOperand]
      rw [hlastSeam_env8 C s (hlastByte G C) (BitVec.ofNat 64 v) ix ix (hlastByte G C),
        hlastEndS_env8 C s (hlastByte G C) (hlastIncV C) (hlastNepV G) (BitVec.ofNat 64 v) ix]
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
    cd := cd
    hTail := hlastTail_of_calls G C s (hlastByte G C) (BitVec.ofNat 64 v) ix ix (hlastByte G C) r₁ r₂ r₃ ev ei cd
      hInvT rfl (pT := pT) (opT := opT) (regT := regT) hpreT hincT hopT hkindT hrdT
      hreadT hpre₁ hcall₁ hret₁ hbit0T hzread hcT htT hoT hpre₂ hcall₂ happ₂ hret₂
      hev64 hevlen64 hltT hpre₃ hcall₃ heiT hcdT hinnerT hlt2T hcd64T
    heicd := heicd
    a := G.b
    q := bytesToNat bs
    bs := bs
    src := "if.then447.i"
    sel := .reg "%ee.1.i"
    hpreS := hlastEntry_pre C s (hlastByte G C) (BitVec.ofNat 64 v) ix ix (hlastByte G C) r₁ r₂ r₃ ei cd cA rdv xA
    hincS := hlastEntry_phiSel
    hopS := by
      show evalOperand (stateAt
        (hlastEntryAt C s (hlastByte G C) (BitVec.ofNat 64 v) ix ix (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ ei cd cA rdv xA).env
        (hlastEntryAt C s (hlastByte G C) (BitVec.ofNat 64 v) ix ix (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ ei cd cA rdv xA))
        (.reg "%ee.1.i") = some (.int 64 (BitVec.ofNat 64 ei))
      simp only [evalOperand, stateAt]
      rw [hlastEntry_envEe C s (hlastByte G C) (BitVec.ofNat 64 v) ix ix (hlastByte G C) r₁ r₂ r₃ ei cd cA rdv xA]
      exact heiT
    h3S := hlastEntry_env3 C s (hlastByte G C) (BitVec.ofNat 64 v) ix ix (hlastByte G C) r₁ r₂ r₃ ei cd cA rdv xA hInvT
    hpos := hpos
    hreadS := hreadS
    hbsS := rfl
    hloc105 := hlastLoc105 (TailStartC C) ev
      (hlastEntryAt C s (hlastByte G C) (BitVec.ofNat 64 v) ix ix (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ ei cd cA rdv xA)
      (BitVec.ofNat 64 ei) G.b (bytesToNat bs)
    x47 := BitVec.ofNat 8 (bytesToNat bs)
    h47 := landRhs457OutAt_env47 C s (hlastByte G C) (BitVec.ofNat 64 v) ix ix (hlastByte G C) r₁ r₂ r₃ ei cd cA rdv xA
      (BitVec.ofNat 64 ei) G.b (bytesToNat bs)
    hbit47 := hbit47
    hws47 := hws47
    hloc96 := hlastLoc96 (TailStartC C) ev
      (hlastEntryAt C s (hlastByte G C) (BitVec.ofNat 64 v) ix ix (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ ei cd cA rdv xA)
      (BitVec.ofNat 64 ei) G.b (bytesToNat bs) (BitVec.ofNat 8 (bytesToNat bs))
    hlatch := hlatch
    hcwL := by
      have hEntry : lookupName
          (hlastEntryAt C s (hlastByte G C) (BitVec.ofNat 64 v) ix ix (hlastByte G C)
            (hlastByte G C) r₁ r₂ r₃ ei cd cA rdv xA).env "%cond350.i" =
          some (.int 64 (BitVec.ofNat 64 cd)) := by
        rw [contEntry_envCond350 C s (hlastByte G C) (BitVec.ofNat 64 v) ix ix
          (hlastByte G C) r₁ r₂ r₃ ei cd cA rdv xA]
        exact hcdT
      exact latch_cond
        (hlastEntryAt C s (hlastByte G C) (BitVec.ofNat 64 v) ix ix (hlastByte G C)
          (hlastByte G C) r₁ r₂ r₃ ei cd cA rdv xA)
        (BitVec.ofNat 64 ei) G.b (bytesToNat bs) (BitVec.ofNat 8 (bytesToNat bs)) hEntry
    hspan := hspan
    hstart := hstart
    hround := hround
    hguard := hguard
    hbyte := hbyte
    htok := htok }

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.headAS4_envInc
#print axioms LeanLLVM.Refinement.WalkScope.headAS4_envNep
#print axioms LeanLLVM.Refinement.WalkScope.contEntry_envCond350
#print axioms LeanLLVM.Refinement.WalkScope.hcontFacts_of_staging

end WalkScope
end LeanLLVM.Refinement
