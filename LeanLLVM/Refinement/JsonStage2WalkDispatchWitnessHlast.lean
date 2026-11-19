/-
The walk's last entry: the scan-free segment to the merge, and the refusal arm.

## The premise both ends read

The bundle's guard and the head prefix's premise are the **same fact** — the last
entry's `%inc ≥ %nep`, which the prefix takes as `hge` and the bundle's producer takes as
`¬ (C.k + 1 < G.nep)` (`hlastFacts_of_staging`'s `hnot`, and the dispatch's own
`WalkLoopEnd.dispatch`).  That is
why the composition is not four applications over unrelated lemmas: it is **one premise,
read at both ends**.  The last entry cannot continue because its increments have reached
the entry count, and the prefix cannot run down the continuing arm for the same reason.

## The path: the byte test's `1` arm, and a scan that does not run

`%inc.i` has reached the count, so `sw.default.i` sends the walk to `cond.end349.i`
without reading a next entry's lane, and the bound's `phi` takes `%4`'s word.  At a last
entry that word is the **stream's end**, above the entry's own index, so `cond.end349.i`
takes `land.lhs.true357.i`: the walk reads the document at `%cond350.i - 1`, takes the
class with no whitespace run (`NodeBlock41 → NodeBlock39 → LeafBlock35`), and reaches
`if.end372.i` with `%ee.1.i = %cond350.i`.

Two consequences, and they are the whole reason this file was re-stated:

* the token's end *is* the entry's end, so `if.then447.i`'s target tests
  `ult (%ee.1.i) (%cond350.i)` on two cells that are the same word — `0`.  The walk
  leaves for `if.end473.i` and **the extra-token scan is never entered**;
* so the bundle's tail is the scan-free one (`WalkLink.if_then447_i_empty`,
  `consumerTailSegEmptyAt`): no `%ee.1.i` stopper, no landing, no latch, no traversal
  premises, and no inner budget.  There is no visit to afford.

The path is the assembly's own longest one — 20 links from `NodeBlock21` to
`cleanup478.i` — and its price is `20 + 2 ≤ 32 · Δk + 8 · Δbytes`, which at `Δk = 1` and
`entryPos G G.nep = 0` is `22 ≤ 32`: the byte term is zero because the last entry's
token ends where the stream does.

## The inventory

| piece | lemma | span |
|---|---|---|
| prefix | `hlastPrefixSeg` | `NodeBlock21 → if.end473.i` (19) |
| merge step | `walkIfEnd473_at` | `if.end473.i → cleanup478.i` (1) |
| finish | `walkFinishMerge_at`, `walkFinishRun` | the merge and the accept run |
| refusal | `walkFinishPath3` | the refusal copy's blocks |

## The earlier statement, and why it was wrong

The prefix this file composed was `walkHeadChainToScan`'s — the **last** entry's head with
the byte test on its *failing* arm (`hugt = 0`, the direct edge `cond.end349.i →
if.end372.i`) and the extra-token scan entered from it.  Both halves named a continuation
no last entry reaches, and they refuted each other:

* `hugt = 0` says `%cond350.i ≤ %idxprom.i`, i.e. the direct seam edge, which makes
  `%ee.1.i` the `%idxprom.i` word;
* the scan's entry (`hlt2T` with `hcdT`/`h4L`/`heiT`) says `%idxprom.i < %cond350.i`.

So `HlastFacts` was **uninhabited at a real last entry**, and the consumer that took it
universally (`WalkLoopEnd.hlast`) was vacuous.  The two halves are now the path the model
takes: the head is
the `1` arm (with `%cond350.i` the `%4` word, so the entry's end is the stream's) and the
tail is the scan-free segment.  Nothing was weakened to get there; two wrong fields were
replaced by the arm's own values.

## The bundle

`HlastFacts` is the input's facts at the last entry, grouped by subject.  It is a `Type`
rather than a `Prop` because its first member of each group is a *witness* — the byte, the
counts, `%4`'s word, the last byte before the end — that the later fields' statements are
stated at; a `Prop`-valued structure admits proof fields only, and the alternative — every
witness passed beside the bundle — is the 34-binder statement this bundle exists to avoid.
`WalkGeom` and `WalkStage` are the same shape for the same reason.

Three decisions worth keeping:

* **`%cond350.i` is one number, not two.**  On this arm the bound's `phi` takes `%4`'s
  word, so the bundle carries that word (`v`) and writes it wherever the bound appears —
  the head's byte test, the whitespace check's address, the seam's stored end, the tail's
  two cells.  A separate witness for the end would be the same fact written twice, and the
  scan-free test `ult v v` would then need an equation to be `0` instead of being one.
* **`x` is one byte, not three.**  `%8` is not rebound between the loop head and the
  class-C span, so the seam's own test and the span's three pivots are about the *head's*
  byte; the bundle carries one witness and states all eight class bits on it.  The
  producer takes **two** of the eight as premises — `hlt125` and `hne125`, the pair that
  names the class (the byte is `ofNat 8 126` or `ofNat 8 127`) — and derives the other six
  (`hlast_slt_zero_of_toInt_le`, `hlast_eq_zero_of_slt_zero`, `hlast_bit6_of_class`).
* **The depth's polarity is not a field.**  The exit tail's test is `%sp.i.1 = 0`, so the
  last entry's outcome is `finish` at depth zero and the refusal otherwise: a field `≠ 0`
  would make the bundle uninhabited exactly at the depth-zero inputs, where `hlast_finish`
  is the true outcome.  It is an argument of the two lemmas that read it (`hlast_refuse`,
  `hlast`), not a bundle field.

## Why the bundle cannot be named in the assembly

`HlastFacts`' field types name states defined above `JsonStage2WalkAssembly` —
`headAS₄`/`headAS₅` (`JsonStage2WalkHeadChainA`), `headEndS` (`JsonStage2WalkHeadChainScan`)
and the whitespace-check and tail states (`JsonStage2WalkPrefixCount`) — while the assembly
is the walk layer's *base*: `JsonStage2WalkSteps` and `JsonStage2WalkStepsPath` import it.
Importing this module into the assembly would close a cycle, which the build rejects.

So the bundle is named outside the assembly and enters at the consumer.
`walkLoopStep_of_staging` (`JsonStage2WalkPremisesOfStaging`) is where the input's bundle
becomes a `WalkDispatchResult`; both arms are stated at `stage2Calls stage2SubCalls` — a
segment's `calls` is the program's, not a variable.
-/

import LeanLLVM.Refinement.JsonStage2WalkHeadChainScan
import LeanLLVM.Refinement.JsonStage2WalkFinishPath
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessFinish
import LeanLLVM.Refinement.JsonStage2WalkPrefixCount
import LeanLLVM.Refinement.JsonStage2WalkDispatchSeamRow

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- `%inc.i`'s value at the last entry, as the bundle's `inc`. -/
abbrev hlastIncV {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : BitVec 64 :=
  BitVec.ofNat 64 (C.k + 1)

/-- `%nep`'s value, as the bundle's `nep`. -/
abbrev hlastNepV {m0 : Mem} (G : WalkGeom m0) : BitVec 64 :=
  BitVec.ofNat 64 G.nep

/-- The head's byte, as the invariant names it: `WalkInv.iter.reg8` is this term. -/
abbrev hlastByte {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : BitVec 8 :=
  BitVec.ofNat 8 (entryByte G C.k).toNat

/-- The entry stream's position past its last entry: the totalisation's own value, which
is what makes the finish's byte term vanish. -/
theorem entryPos_nep {m0 : Mem} (G : WalkGeom m0) : entryPos G G.nep = 0 := by
  have hlen : G.ent.length = G.nep := by
    rw [← readLanes32_length m0 G.ep G.nep G.ent G.entries]
  simp only [entryPos, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl

/-- `%inc.i` at `sw.default.i`'s entry is `%inc.i` at the loop head: the four pivots bind
their own cells and none of them is the header's increment. -/
theorem headAS4_envInc (s : State) (x : BitVec 8) :
    lookupName (headAS₄ s x).env "%inc.i" = lookupName s.env "%inc.i" := by
  simp only [headAS₄, headAS₃, headAS₂, headAS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%nep` at `sw.default.i`'s entry is `%nep` at the loop head: no block of the head path
binds the entry count. -/
theorem headAS4_envNep (s : State) (x : BitVec 8) :
    lookupName (headAS₄ s x).env "%nep" = lookupName s.env "%nep" := by
  simp only [headAS₄, headAS₃, headAS₂, headAS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%t352.i` at `sw.default.i`'s entry is the loop head's: the four pivots bind their own
cells and none of them is the token record's register. -/
theorem headAS5_envTokEq (s : State) (x : BitVec 8) (inc nep : BitVec 64) :
    lookupName (headAS₅ s x inc nep).env "%t352.i" = lookupName s.env "%t352.i" := by
  simp only [headAS₅, headAS₄, headAS₃, headAS₂, headAS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-! ### The bundle

`hlastEntry` is `TailS₃` built with the same Nat at both cells, so its `if` is the else
arm and its block is the merge's entry; `hlastMerge` is `walkIfEnd473_at`'s target at it.
The three `abbrev`s take the structure so a lemma's statement stays the length of the
field types rather than of the argument lists. -/

/-- The bundle's witnesses, at the tail's start. -/
abbrev hlastTailAt {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (v : Nat)
    (ix : BitVec 64) (b35 : UInt8) : State :=
  hlastTail C s (hlastByte G C) (hlastIncV C) (hlastNepV G) v ix b35

/-- The tail's start at the staging's own three witnesses: `%4`'s word the stream's end,
`%idxprom.i`'s the entry's position, and the byte before the end the document's last.  The
caller's premises about the tail's start are stated at this name, so the signature does not
have to spell the three terms out. -/
abbrev hlastTailNat {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) : State :=
  hlastTail C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.n
    (BitVec.ofNat 64 (entryPos G C.k)) (G.bs.getD (G.n - 1) 0)

/-- **The tail's start at the byte's route.**  The last byte's route is a document fact
(`hb`), and the seam the route reaches is the tail's source: this is `hlastTailAt` at the
class the byte selects, which is what the tail's calls and the merge's cells are read at. -/
abbrev hlastTailAtByte {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (v : Nat)
    (ix : BitVec 64) (b35 : UInt8) (hb : HcontByteRoute (head35 b35)) : State :=
  hlastTailByte C s (hlastByte G C) (hlastIncV C) (hlastNepV G) v ix b35 hb

/-- The tail's start at the staging's own witnesses, at the byte's route. -/
abbrev hlastTailRoute {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0))) : State :=
  hlastTailAtByte C s G.n (BitVec.ofNat 64 (entryPos G C.k)) (G.bs.getD (G.n - 1) 0) hb

/-! ### The structure -/

/-- **The input's facts, bundled.**  The statement that needs them is the last entry's two
outcomes; this is the single argument it takes, and each group is a subject the prefix or
the merge reads.

The head group is the arm the path takes: `hge = 0` (the count test fails at a last entry)
and `hugt = 1` (the stream's end is above the entry's index), so the walk reads the byte
before the end and the token's end is that end.  The fields the old bundle carried for the
scan — its entry, its landing, its latch and the inner budget its last visit cost — are
gone with the scan: `if.then447.i`'s target tests two cells that are the same word. -/
structure HlastFacts {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Type where
  /-- The head's byte. -/
  x : BitVec 8
  h8 : evalOperand s (.reg "%8") = some (.int 8 x)
  hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0
  hlt123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0
  hlt125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0
  hne125 : evalICmp .eq x (BitVec.ofNat 8 125) = 0
  /-- The entry counts, read at the default arm: the entry's index and the stream's
  count, and the test the last entry fails. -/
  inc : BitVec 64
  nep : BitVec 64
  hinc : evalOperand (headAS₄ s x) (.reg "%inc.i") = some (.int 64 inc)
  hnep : evalOperand (headAS₄ s x) (.reg "%nep") = some (.int 64 nep)
  hge : evalICmp .ult inc nep = 0
  /-- **`%4`'s word — the stream's end — and the entry's index.**  The bound's `phi`
  selects `%4` on the arm the count test's failure takes, so this word *is*
  `%cond350.i`: the token's end, the whitespace check's address and the tail's two cells
  are all stated at it. -/
  v : Nat
  hav5 : lookupName (headAS₅ s x inc nep).env "%4" = some (.int 64 (BitVec.ofNat 64 v))
  ix : BitVec 64
  hidx5 : lookupName (headAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix)
  htok5 : lookupName (headAS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok)
  hgap5 : lookupName (headAS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20))
  /-- **The byte test's value — the arm a last entry takes.**  `%cond350.i` is the
  stream's end and `%idxprom.i` this entry's position, so `ugt` is `1`:
  `cond.end349.i` goes to `land.lhs.true357.i`, and the walk reads the byte before the
  token's end.  The continuing bundle's `hugt` (`HcontFacts`) is `= 1` on the *lane's*
  word instead; the two agree on the arm and differ in what the word is. -/
  hugt : evalICmp .ugt (BitVec.ofNat 64 v) ix = 1
  /-- The byte before the token's end, its width and the read.  `land.lhs.true357.i` reads
  the document at `%cond350.i - 1`; the staging fixes the address, the document the byte. -/
  b35 : UInt8
  hread35 : readBytes (headEndS C s x inc nep (BitVec.ofNat 64 v) ix).mem
    ((G.b - 1) + v) 1 = some [b35]
  /-- **The bound's width, and why the bundle states it.**  `land.lhs.true357.i`'s `gep`
  sign-extends the bound (`(idx.signExtend 64).toNat`), so the step needs it *below*
  `2 ^ 63` — `v < 2 ^ 64` does not give that, which is why the field is not the weaker
  bound.

  **It is inhabitable**, and that matters for a field that strengthens a hypothesis: the
  word is the document's length in the geometry the staging describes, and
  `WalkGeom.maxDoc` gives `G.n ≤ stage2MaxDocument = 2 ^ 32 < 2 ^ 63`.  It is a premise
  rather than a derived fact because neither `WalkInv` nor `h4L` alone fixes the word's
  value: the staging fixes the address and the register, not the number. -/
  hv63 : v < 2 ^ 63
  /-- **That byte's route**: the class its three pivots select.  All three non-whitespace
  leaves reach `if.end372.i` without a run, so the class is what the prefix's chain and the
  tail's source are stated at — `HcontByteRoute`, the same type the continuing side names,
  read at this level's own byte. -/
  hb : HcontByteRoute (head35 b35)
  /-- The seam's own byte test on `%8` — the entry's first byte, which the walk leaves the
  token's end's `phi` on. -/
  hbit6 : (evalICmp .eq x (BitVec.ofNat 8 45) |||
    evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0
  /-- The class-C span's three pivots, on the same byte: `%8` is not rebound between the
  loop head and the span. -/
  hc110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0
  hc116 : evalICmp .slt x (BitVec.ofNat 8 116) = 0
  hceq116 : evalICmp .eq x (BitVec.ofNat 8 116) = 0
  /-- The tail's own: its three call outcomes, the event it emits, the seed's words and
  its segment at the byte's route — `if.then447.i`'s target on its `ult v v` arm. -/
  r₁ : CallOutcome
  r₂ : CallOutcome
  r₃ : CallOutcome
  ev : EventRecord
  cA : BitVec 32
  rdv : BitVec 32
  xA : BitVec 32
  hTail : WalkSegment (stage2Calls stage2SubCalls) G (TailStartC C)
    (hlastTailByte C s x inc nep v ix b35 hb)
    (TailCarryEnd (TailStartC C) ev)
    (hlastEntryByte C s x inc nep v ix b35 hb r₁ r₂ r₃ cA rdv xA) 3
  /-- The merge's cells: the index `%inc.i` the `phi` selects, the entry count `%nep`,
  the depth `%sp.i.0248` the exit tail's test reads, and the two staging words. -/
  k2 : Nat
  nepv : BitVec 64
  spv : Nat
  hk2 : evalOperand (hlastMergeByte C s x inc nep v ix b35 hb r₁ r₂ r₃ cA rdv xA)
    (.reg "%inc.i") = some (.int 64 (BitVec.ofNat 64 k2))
  hnepM : lookupName (hlastMergeByte C s x inc nep v ix b35 hb r₁ r₂ r₃ cA rdv xA).env
    "%nep" = some (.int 64 nepv)
  hterm : k2 = nepv.toNat
  hk2nep : k2 = G.nep
  hspvM : evalOperand (hlastMergeByte C s x inc nep v ix b35 hb r₁ r₂ r₃ cA rdv xA)
    (.reg "%sp.i.0248") = some (.int 32 (BitVec.ofNat 32 spv))
  heM : lookupName (hlastMergeByte C s x inc nep v ix b35 hb r₁ r₂ r₃ cA rdv xA).env
    "%e" = some (.ptr C.stage.e)
  h4M : lookupName (hlastMergeByte C s x inc nep v ix b35 hb r₁ r₂ r₃ cA rdv xA).env
    "%4" = some (.int 64 (BitVec.ofNat 64 v))
  /-- **The entry is the stream's last.**  The carry's index plus one is the count, which
  is what makes the path's count — `20` steps at the longest class — fit the entry's credit
  (`stage2EntryAllowance = 32`).  The path's count is a `Nat` (`hlastPrefixSegByte`), so the
  price is arithmetic on this. -/
  hlastK : C.k + 1 = G.nep

/-! ### The bundle's states, at their own argument lists

An `abbrev` taking the structure keeps the lemmas' statements short: the fields are the
`def`s' arguments in order, so a lemma's `hlastMergeF f` is the same term the bundle's
field types spell out. -/

abbrev hlastEntryF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HlastFacts G C s) : State :=
  hlastEntryByte C s f.x f.inc f.nep f.v f.ix f.b35 f.hb f.r₁ f.r₂ f.r₃ f.cA f.rdv f.xA

/-- The merge's carry: the route's tail's target carry, at the merge's own block. -/
abbrev hlastMergeC {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord) :
    WalkCarry G :=
  { TailCarryEnd (TailStartC C) ev with block := "cleanup478.i" }

abbrev hlastMergeCF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HlastFacts G C s) : WalkCarry G :=
  hlastMergeC C f.ev

abbrev hlastMergeAt {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (v : Nat)
    (ix : BitVec 64) (b35 : UInt8) (hb : HcontByteRoute (head35 b35))
    (r₁ r₂ r₃ : CallOutcome) (cA rdv xA : BitVec 32) : State :=
  hlastMergeByte C s (hlastByte G C) (hlastIncV C) (hlastNepV G) v ix b35 hb
    r₁ r₂ r₃ cA rdv xA

abbrev hlastMergeF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HlastFacts G C s) : State :=
  hlastMergeByte C s f.x f.inc f.nep f.v f.ix f.b35 f.hb f.r₁ f.r₂ f.r₃ f.cA f.rdv f.xA

/-- The merge's target: `%cmp.i`, `%k.2.i` and `%sp.i.1`, at the exit tail's first block. -/
def hlastThen {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (hb : HcontByteRoute (head35 b35))
    (r₁ r₂ r₃ : CallOutcome) (cA rdv xA : BitVec 32) (k2 spv : Nat) : State :=
  { hlastMergeByte C s x inc nep v ix b35 hb r₁ r₂ r₃ cA rdv xA with
    env := cells [("%cmp.i", .int 1 (0 : BitVec 1)),
      ("%k.2.i", .int 64 (BitVec.ofNat 64 k2)),
      ("%sp.i.1", .int 32 (BitVec.ofNat 32 spv))]
      (hlastMergeByte C s x inc nep v ix b35 hb r₁ r₂ r₃ cA rdv xA).env
    pc := "if.then485.i", pre := some "cleanup478.i" }

abbrev hlastThenF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HlastFacts G C s) : State :=
  hlastThen C s f.x f.inc f.nep f.v f.ix f.b35 f.hb f.r₁ f.r₂ f.r₃ f.cA f.rdv f.xA
    f.k2 f.spv

/-- The exit tail's carry: `if.then485.i`'s block, over the merge's. -/
abbrev hlastThenC {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HlastFacts G C s) : WalkCarry G :=
  { hlastMergeCF f with block := "if.then485.i" }

/-! ### The last entry's path to the merge

`hlastPrefixSegByte` is the segment to the merge's entry at the byte's route — `12 +
hlastByteCount hb` links to the tail's start and the tail's three — and the merge's own
step (`walkIfEnd473_at`, one link) follows it.  The merge's target state is
`hlastMergeByte`, whose `pre` is the block it left — that is the literal the merge's `phi`
reads, and it is the tail's target's own `pc` only because `TailS₃`'s `if` is the else arm
(`hlastEntryByte_pc`); the link leaves `some s.pc`, so the equation is rewritten into the
segment's endpoint before it is composed. -/

/-- **The last entry's path to the merge, at the byte's route.**  The prefix (the head, the
whitespace check, the byte's route, the class-C span and the tail) as one segment at its own
count, then the merge's step, with the merge's invariant. -/
theorem hlast_toMerge {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (f : HlastFacts G C s) :
    WalkSegment (stage2Calls stage2SubCalls) G C s (hlastMergeCF f) (hlastMergeF f)
        (((12 + hlastByteCount f.hb) + 3) + 1) ∧
      WalkInv G (hlastMergeCF f) (hlastMergeF f) := by
  -- the prefix: the route's count to the merge's entry
  have hpre : WalkSegment (stage2Calls stage2SubCalls) G C s
      (TailCarryEnd (TailStartC C) f.ev) (hlastEntryF f)
      ((12 + hlastByteCount f.hb) + 3) :=
    hlastPrefixSegByte (G := G) (C := C) (s := s) hInv hblock f.h8 f.hlt91 f.hlt123
      f.hlt125 f.hne125 f.hinc f.hnep f.hge f.hav5 f.hidx5 f.htok5 f.hgap5 f.hugt
      f.hread35 f.hv63 f.hb f.hbit6 f.hc110 f.hc116 f.hceq116 f.r₁ f.r₂ f.r₃ f.ev f.hTail
  -- `%t352.i` at the merge's entry is the loop head's token record
  have htokE : lookupName (hlastEntryF f).env "%t352.i" = some (.ptr C.stage.tok) := by
    rw [hlastEntryByte_envTok C s f.x f.inc f.nep f.v f.ix f.b35 f.hb f.r₁ f.r₂ f.r₃ f.cA
        f.rdv f.xA,
      hlastEndS_envTok C s f.x f.inc f.nep (BitVec.ofNat 64 f.v) f.ix]
    exact (headAS5_envTokEq s f.x f.inc f.nep).symm
      |>.trans f.htok5
  -- the merge's step, one link
  obtain ⟨s₆, hl₆, hs₆⟩ :=
    walkIfEnd473_at (sub := stage2SubCalls) (G := G) (C := TailCarryEnd (TailStartC C) f.ev)
      (s := hlastEntryF f) hpre.inv' rfl (tok := C.stage.tok) htokE
  -- the tail's `if` is the else arm, so the block it leaves is the merge's entry
  have hpc : (hlastEntryF f).pc = "if.end473.i" :=
    hlastEntryByte_pc C s f.x f.inc f.nep f.v f.ix f.b35 f.hb f.r₁ f.r₂ f.r₃ f.cA f.rdv f.xA
  rw [hpc] at hs₆
  rw [hs₆] at hl₆
  have hlink : WalkLink (stage2Calls stage2SubCalls) G (TailCarryEnd (TailStartC C) f.ev)
      (hlastEntryF f) (hlastMergeCF f) (hlastMergeF f) := hl₆
  exact ⟨hpre.trans (WalkSegment.of_link hlink), hlink.inv'⟩

/-! ### The two outcomes -/

/-- **The finish disjunct.**  The last entry's path reaches `cleanup478.i` at the terminal
index: the segment is `hlast_toMerge`'s, the merge's index is the `phi`'s selection
`%inc.i`, and the entry count is the state's `%nep`.  The price is arithmetic: the path is
at most `20` links (`hlastByteCount_le`), `hlastK` makes `Δk = 1`, and `entryPos G G.nep = 0`
kills the byte term, so `22 ≤ 32`. -/
theorem hlast_finish {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (f : HlastFacts G C s) :
    ∃ (Cd : WalkCarry G) (sd : State) (p k2 : Nat) (prev : String) (kOp : Operand)
      (nepv : BitVec 64),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p ∧ Cd.block = "cleanup478.i" ∧
      sd.pre = some prev ∧ phiIncoming prev cleanupKIncoming = some kOp ∧
      evalOperand sd kOp = some (.int 64 (BitVec.ofNat 64 k2)) ∧
      lookupName sd.env "%nep" = some (.int 64 nepv) ∧ k2 = nepv.toNat ∧
      p + 2 ≤ stage2EntryAllowance * (k2 - C.k) +
        stage2ByteAllowance * (entryPos G k2 - entryPos G C.k) := by
  obtain ⟨hseg, -⟩ := hlast_toMerge G C s hInv hblock f
  refine ⟨hlastMergeCF f, hlastMergeF f, (((12 + hlastByteCount f.hb) + 3) + 1),
    f.k2, "if.end473.i", .reg "%inc.i", f.nepv, hseg, rfl, rfl, by decide, f.hk2,
    f.hnepM, f.hterm, ?_⟩
  rw [f.hk2nep, entryPos_nep]
  have hΔ : G.nep - C.k = 1 := by rw [← f.hlastK]; omega
  have hc : hlastByteCount f.hb ≤ 4 := hlastByteCount_le f.hb
  simp only [Nat.zero_sub, Nat.mul_zero, Nat.add_zero, stage2EntryAllowance, hΔ]
  omega

/-- **The refusal disjunct.**  The same segment, the merge's step and the exit tail's
first two blocks: the target is `if.then` with the merge's `phi` cells in place, and the
carry's refusal offset is the invariant's (`WalkInv.eoff_le`), unchanged through the two
carries.  The price fits the entries the loop has left and the document bytes it has not
reached, which is the refusal's own accounting (`walkPotential_spend`'s direction) —
`20 + 3 ≤ 32` at `Δk = 1`, and the byte term is left as the credit it is.

`hbit` is the exit tail's test at the merge's depth: `%sp.i.1 = 0` is *false*, so the
merge's false arm takes `if.then488.i` and the refusal copy rather than `if.then490.i`
and the normal exit.  It is the one fact of the last entry's that says which of the two
outcomes this is, which is why it is an argument rather than a bundle field. -/
theorem hlast_refuse {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (f : HlastFacts G C s)
    (hbit : evalICmp .eq (BitVec.ofNat 32 f.spv) (BitVec.ofNat 32 0) = 0) :
    ∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p ∧ Cd.block = "if.then" ∧
      Cd.eoff ≤ G.n ∧
      p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
        stage2ByteAllowance * (G.n - entryPos G C.k) := by
  obtain ⟨hseg, hinv⟩ := hlast_toMerge G C s hInv hblock f
  -- the merge's step, at the terminal index
  obtain ⟨e, hstep, hInvE, he⟩ :=
    walkFinishMerge_at (calls := stage2Calls stage2SubCalls) (G := G) (C := hlastMergeCF f)
      (s := hlastMergeF f) hinv rfl (p := "if.end473.i") rfl (by decide) f.hspvM
      (by decide) f.hk2 f.hnepM f.hterm
  rw [he] at hstep hInvE
  have hsegM : WalkSegment (stage2Calls stage2SubCalls) G (hlastMergeCF f) (hlastMergeF f)
      (hlastThenC f) (hlastThenF f) 1 :=
    { run := fun n => by
        rw [show 1 + n = n + 1 from by omega]
        simp only [runFuel, hstep, hlastThenF, hlastThen]
      inv' := hInvE
      stage_eq := rfl }
  -- the exit tail's first two blocks, from the merge's `phi` cells
  have hspT : lookupName (hlastThenF f).env "%sp.i.1" =
      some (.int 32 (BitVec.ofNat 32 f.spv)) := by
    simp only [hlastThenF, hlastThen, cells,
      lookupName_cons_ne (k := "%cmp.i") (n := "%sp.i.1") _ _ (by decide),
      lookupName_cons_ne (k := "%k.2.i") (n := "%sp.i.1") _ _ (by decide),
      lookupName_cons_self]
  have heT : lookupName (hlastThenF f).env "%e" = some (.ptr C.stage.e) := by
    simp only [hlastThenF, hlastThen, cells,
      lookupName_cons_ne (k := "%cmp.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%k.2.i") (n := "%e") _ _ (by decide),
      lookupName_cons_ne (k := "%sp.i.1") (n := "%e") _ _ (by decide)]
    exact f.heM
  have h4T : lookupName (hlastThenF f).env "%4" =
      some (.int 64 (BitVec.ofNat 64 f.v)) := by
    simp only [hlastThenF, hlastThen, cells,
      lookupName_cons_ne (k := "%cmp.i") (n := "%4") _ _ (by decide),
      lookupName_cons_ne (k := "%k.2.i") (n := "%4") _ _ (by decide),
      lookupName_cons_ne (k := "%sp.i.1") (n := "%4") _ _ (by decide)]
    exact f.h4M
  obtain ⟨s₇, hseg₇, -, -, -⟩ :=
    walkFinishPath3 (G := G) (C := hlastThenC f) (s0 := hlastThenF f) hInvE rfl hspT
      hbit heT h4T (by have := f.hv63; omega)
  refine ⟨FinishCThen (hlastThenC f), s₇,
    (((12 + hlastByteCount f.hb) + 3) + 1) + 1 + 2,
    ((hseg.trans hsegM).trans hseg₇), rfl, hInv.eoff_le, ?_⟩
  have hΔ : G.nep - C.k = 1 := by rw [← f.hlastK]; omega
  have hc : hlastByteCount f.hb ≤ 4 := hlastByteCount_le f.hb
  simp only [stage2EntryAllowance, hΔ]
  omega

/-! ### The last entry's two paths, as the dispatch's result

The two arms `hlast_finish` and `hlast_refuse` prove are the `merge` and `refuse`
alternatives of `WalkDispatchResult` (`JsonStage2WalkDispatchThreeOfRun`), which is where a
dispatch takes them: `WalkDispatchResult.ofHlastMerge` builds the `merge` arm from
`hlast_finish`, and the `refuse` arm carries the word its refusing block stored
(`WalkRefuseSegment`), which `hlast_refuse` does not state — its endpoint's word is `%4`'s
rather than the store's own.

A disjunction of segments is not what the dispatch's classification consumes: the result
is one endpoint with that endpoint's facts, and the classification is the merge's own test
on the index it selected.  The depth bit does not choose between the two paths either —
the merge is reached on both — and that is why nothing here branches on it.

The use site is `walkLoopStep_of_staging` (`JsonStage2WalkPremisesOfStaging`), which
builds a `WalkDispatchResult` at each head state — the `merge` arm from the continuing
premise's own evidence, or the last entry's arm (`WalkLoopEnd.dispatch`) — and feeds
`walkLoopStepThree_of_dispatchResult`.  **This bundle is not the last entry's arm**: the
high-byte class refuses (`HlastHighByteRefusal`, `LastEntryArm.highByte`), and `HlastFacts`
here is the conditional emitting path the last level's other classes take, reached through
`hlast_finish`/`hlast_refuse` and the credit theorems rather than the dispatch. -/

/-! ### The bundle's producer

`HlastFacts` as a `Type` is inhabited by a structure literal; the question is what the
literal has to be given, and the answer separates the fields into three kinds.

**Fixed by the loop's own values.**  The entry's index and the stream's count are not free
witnesses: at the loop's last entry they are `C.k + 1` and `G.nep`, and the bundle is
produced at those.  `%4`'s word, the entry's index and the byte before the token's end are
not supplied either: they are `G.n`, `entryPos G C.k` and the document's last byte, read
off the invariant's `regs` and `idx_reg` cells and `WalkGeom.doc`.

**The map, per group.**  Produced · premised correctly (the model cannot supply it) ·
supplied as a named premise:

| group | status |
|---|---|
| the head's byte (`x`, `h8`) | **produced**: `hInv.iter.reg8` is the field, and the witness is `hlastByte G C` |
| the head byte's class (`hlt125`, `hne125`, then the other six) | **produced from the class's two**: `hlt125` and `hne125` clear put the byte at `ofNat 8 126` or `ofNat 8 127`; `hlt91`/`hlt123` and `hc110`/`hc116` follow from the signed order (`hlast_slt_zero_of_toInt_le`), `hceq116` from it (`hlast_eq_zero_of_slt_zero`), and the seam's `x = '-' ∨ x + 208 <u 10` test is `decide`d at both values (`hlast_bit6_of_class`).  So the *class* is two premises and the bundle's other six bits are consequences — the eight-bit row is what this replaced |
| the entry counts (`inc`, `nep`, `hinc`, `hnep`, `hge`) | **produced, from no supplied fact**: the witnesses are the loop's values (`hlastIncV C`, `hlastNepV G`), `hge` is `ult (C.k+1) G.nep` at `C.k + 1 = G.nep` — a word compared with itself — and the two cells are `WalkInv.inc_reg` and `%nep`'s `walkStaticRegs` row, peeled to `sw.default.i`'s entry (`headAS4_envInc`, `headAS4_envNep`) |
| the default arm's cells (`v`, `hav5`, `ix`, `hidx5`, `htok5`, `hgap5`) | **produced**: `%4` and `%t352.i` are `WalkInv.regs`' own rows — at `ofNat 64 G.n` and `C.stage.tok` — `%idxprom.i` is `WalkInv.idx_reg` at `entryPos G C.k`, `%gap.i` is `regs`'s, and each is peeled to `headAS₅` (`hlastAS5_envFour`/`…Idx`/`…Tok`/`…Gap`) |
| the byte test's value (`hugt`) | **produced**: the stream's end against this entry's index is `entryPos G C.k < G.n`, which is `hlast_entryPos_lt` (the entry's membership in the stream at `C.k < G.nep`, then `WalkGeom.inside`); `hlast_ugt_of_lt` turns the order into the bit `= 1`.  Its value `= 1` is the last entry's arm |
| the byte before the end (`b35`, `hread35`, `hv63`) | **produced**: at `v = G.n` the address is `G.b + (G.n - 1)`, the document's last byte, and `headEndS_docByte` reads it across the head path's two token-record stores — the token's staged extent is disjoint from the document's region, and `walkDoc_byte` supplies the byte.  `hv63` is `WalkGeom.maxDoc` (`G.n ≤ 2 ^ 32 < 2 ^ 63`) |
| that byte's three class bits (`hb13`, `hb32`, `hbne13`) | **premised correctly: the document's**, and they are the class the price's longest path names: no whitespace run |
| the seam's byte test (`hbit6`) | **produced (with the class above)**: `hlast_bit6_of_class` — the class's two bits leave `%8` at 126 or 127 and the test is `decide`d at both |
| the class-C span's three bits (`hc110`, `hc116`, `hceq116`) | **produced (with the class above)**: `hc110`/`hc116` by the signed order and `hceq116` by the same order's strictness — three more on the same byte, and the byte is the class's |
| the tail's counted segment (`hTail`, `r₁`, `r₂`, `r₃`, `rdv`, `xA`) | **produced**: the three calls' contracts applied at their three staged argument lists, composed by `consumerTailSegEmptyAt` in `hlastTail_of_calls`.  The scan's entry's two cells are *peeled* — `%ee.1.i` is the seam's stored end and `%cond350.i` the same word (`hlastTail_ee`, `hlastTail_cond`) — so the empty arm's equation is `rfl` and no budget is asked for.  The literal's kind (`cA`) and its `phi` operand (`hopT`) are *produced from no supplied fact*: the `phi`'s incoming operand is the immediate `ofNat 32 0` and `evalOperand` of an immediate is `Const.toValue`, so the witness is that immediate and its evaluation is `rfl` |
| the appended record's identity (`ev`, `happ₂`) | **produced**: `s2ScalarValuePost` concludes the append existentially in the record, and `hlastTail_of_calls` now *returns* that record — `∃ ev, WalkSegment … (TailCarryEnd C ev) …` — instead of taking it.  The producer names it with `Classical.choose` (the bundle is a `Type`, so an existential cannot be eliminated into it), and the field and its append are the post's own second conjunct at `hret₂` |
| the merge's cells (`k2`, `nepv`, `spv`, and their five lookups) | **produced**: `%sp.i.0248` is `WalkInv.depth_reg`, `%inc.i` is `inc_reg` and `%nep` is `regs`'s — three invariant cells, so `spv := C.sp`, `k2 := C.k + 1` and `nepv := hlastNepV G` — and `%e`/`%4` are `regs`'s two rows; the five `hlastMerge_env*` peels read `lookupName` down to `s`, so no field is stated at a state the caller would have to compute |
| `hterm`, `hk2nep` | **produced**: `G.nep` below `2^64` and the loop's equation |
| the entry being the stream's last (`hlastK`) | **produced: the loop's own guard.**  `WalkInv.k_le` bounds `C.k` by `G.nep` and the head's clause bounds it strictly below it (`WalkInv.head_lt`, read off `WalkLocal`'s `NodeBlock21` branch — the block's own branch condition); with the consumer's `¬ (C.k + 1 < G.nep)` the index is the count.  The producer takes the consumer's negation instead of the equality |

**The map's counted shape, per row: 13 produced, 1 premised correctly** — fourteen rows
in all, so **13 of 14 produced** (12 of 14 before this round, 9 of 16 before the repair).
What the count buys is unchanged: **the bundle is inhabited at a real last entry**, and it
is the conditional emitting path's — not the high-byte class's arm, which refuses
(`LastEntryArm.highByte` carries `HlastHighByteRefusal`, `JsonStage2WalkDispatchArms`).

Nothing above is a field weakened to make a proof go through: every produced witness is a
consequence of the invariant, the staging's addresses or the model's own values, and the
premise names the clause or list that *cannot* supply it.

**The premise count, measured.**  The producer's signature names **29 binders** after this
round, of which **24 are supplied** once the five fixed ones (`m0`, `G`, `C`, `s`, `hInv`)
are set aside.  The measurement is a binder-name count over the
`def`'s signature, with a group such as `(r₁ r₂ r₃ : CallOutcome)` counted as three
arguments.  What moved in the earlier round was a *substitution* rather than a deletion:
`hk` (the supplied equality `C.k + 1 = G.nep`) became `hnot` (the consumer's own `¬ (C.k +
1 < G.nep)`), and the equality is derived from it and the head's guard.  `hevlen64` was
deleted from `hlastTail_of_calls` and is derived there from `WalkInv.evlen_le` through
`evRoom` and `evcapLt`.  This round deleted the trace's count from the signature: the
head is outside the append stretch, so `WalkInv.events_le_of_tight` states it as
`C.events.length ≤ C.k` and the head's guard adds `C.k < G.nep`.  The event stream's
width (`hev64`) was tried as the geometry's
`evLt` and reverted: `stage2Pre` does not state it, so the clause's supply is a certified-
domain change in the pipeline's staging (`routePre` → `pipelineStaging` →
`stage2Pre_of_exit`), not a walk-layer edit — the survivors table records it as the
caller's, which is where it stands.

### The survivors, and what would produce each

Each surviving supplied argument, the fact it states, and the clause or lemma that would
produce it.  Two rows from earlier rounds are closed: the last index, which the head's
guard now produces, and the count, which `WalkInv.events_le_of_tight` produces at the
head.  What remains is the document's content, the event stream's width, the log's word
and the callees' premises.

| survivor | the fact it states | producer |
|---|---|---|
| `hlt125`, `hne125` (the head byte's class) | the two pivots that name the class: with both clear the byte is 126 or 127 | **the document's content, and not derivable.**  `WalkGeom.doc` fixes the byte's *term* (`G.bs.getD (entryPos G C.k) 0`) but not its *value*, so which arm the document's byte selects is the caller's case split.  `walkDoc_byte` derives the *read* of that byte; the class is a fact about the document.  The other six class bits are produced from these two (`hlast_slt_zero_of_toInt_le`, `hlast_eq_zero_of_slt_zero`, `hlast_bit6_of_class`) |
| `hb13`, `hb32`, `hbne13` (that byte's three class bits) | the no-whitespace class of `G.bs[n-1]` | **the document's content**: once `hread35`'s derivation names the byte as `G.bs.getD (G.n - 1) 0`, these are `decide`-able *for a given document*; nothing in the geometry fixes the value |
| `r₁`, `r₂`, `r₃`, `hcall₁`, `hcall₂` (the three calls' outcomes) | each helper's answer at the stale argument list | **the three contracts' `resolves`**, which produce `∃ r, call … = some r ∧ post` from the precondition alone.  They stay arguments only because `hpre₂` is stated at `r₁.mem` and `hpre₃` at `r₂.mem`: producing the answers means restating those preconditions at the memories the posts describe (`s2ValuePosPost`'s `r.mem = mem` for the first; `s2ScalarValueAppend`'s existential for the second, which is why `r₂` cannot be produced without quantifying the third call's precondition over the memory the append describes) |
| `hret₁`, `hbit0T`, `xA` | the value-position call's answer word and its arm | **`s2ValuePosPost`** for `xA`'s value; `hbit0T` is the *arm* (`x ≠ 0`, the scalar path rather than a container close), which is the class condition and not a consequence of the post |
| `hreadT`, `rdv` (the root-done slot's word) | `readBytes (writeBytes …) (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)` | **a presence-and-value clause on the root-done slot** (`WalkInv.owned` deliberately omits the four `alloca` slots, and `WalkInv.frame` covers the interval without naming the word inside it) |
| `hzread` (the log's base word) | `readBytes … C.stage.z 8 = some (wordBytes 8 G.ev)` | **a `WalkInv` clause for the log's base** (`%z + 0`), beside `log_hash`/`log_len`.  It is not a frame consequence: `%z`'s first eight bytes lie *inside* the walk's write extent, and the frame is silence *outside* it.  The clause has to survive every one of the invariant's thirty-nine construction sites, so it is the next row's own piece of work rather than a one-line addition |
| `hev64` (`G.ev < 2 ^ 64`) | the event stream's base is a word | **landed: `WalkGeom.evLt`**, the shape `bLt`/`epLt` have, supplied from `stage2Pre`'s new `ev < 2 ^ 64` clause through `WalkGeom.nonempty`, `walkGeom_at_pre` and `Stage2Run`, and produced at the pipeline's call site by `routePre` → `pipelineStaging` → `stage2Pre_of_exit`.  The field is therefore `G.evLt` now and can be dropped from this bundle |
| `hltT` (`C.events.length < C.k`) | one emitted record per emitting entry | **retired: `WalkInv.events_le_of_tight` at the loop head.**  The strict form was a defect and the repair landed: `WalkInv.events_le` is `length ≤ k + walkEmitC block`, whose allowance is zero at every block before the append, so the count at the head is `length ≤ C.k` — the tight hypothesis the emit re-establishes at its target, since `k` does not advance until the merge.  `hlastFacts_of_staging` derives it, so the bundle carries no count field |
| `hblock` (`C.block = walkLoopHead`) | which state the bundle is at | **the consumer's own hypothesis**: the bundle's statement quantifies over `C.block = walkLoopHead`, and it is what `hlastTailSeg` needs to produce `hInvT` |
| `hpre₁`, `hpre₂`, `hpre₃`, `hret₂`, `hcall₃` | the callee preconditions and the copy call | **the staging**: each is a statement about the memory, cursor and addresses the walk holds, and each has the shape `s2StringBodyPre_of_staging` assembled for the string body.  They are premises because no clause fixes the three staged widths at the callee's own argument list |
-/

/-- The entry count's word reads back as itself: it is below `2 ^ 64`. -/
theorem hlast_nep_toNat {m0 : Mem} (G : WalkGeom m0) : (hlastNepV G).toNat = G.nep := by
  have h : G.nep < 2 ^ 64 := by
    have h1 := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  simp only [hlastNepV, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ### The refill at the loop head

`WalkInv.inner_cap` bounds the inner component **above** (`C.inner ≤ walkInnerCap G`), and
that is all the invariant may say: `WalkInv` is asserted at mid-scan states, where `inner`
is being spent down.  **A lower bound that is only true at the loop head belongs to the
refill's lemma, not to the invariant** — and the last entry's bundle no longer needs one at
all, because its path enters no scan.  The lemma stays for the continuing arm's producer
(`hcontFacts_of_staging`), whose class field is what the whitespace run is derived from; the bundle has no `hinner` field.
-/

/-- **The cap is at least one.**  `walkInnerCap G = 4 * G.n + 5`. -/
theorem walkInnerCap_pos {m0 : Mem} (G : WalkGeom m0) : 1 ≤ walkInnerCap G := by
  simp only [walkInnerCap]
  omega

/-- **The inner budget at the loop head is not empty.**  The equality is the refill's —
`walkBack_step_at`'s carry and `walkSeed` both set `inner := walkInnerCap G` — and it is
this lemma's hypothesis because it is not an invariant clause. -/
theorem walkLoopHead_inner_pos {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    (_hblock : C.block = walkLoopHead) (hrefill : C.inner = walkInnerCap G) :
    1 ≤ C.inner := hrefill ▸ walkInnerCap_pos G

/-! ### The cells the merge carries, peeled to where their evidence is

Five of the bundle's merge group are closed computations of the states it names: `%inc.i`,
`%nep`, `%sp.i.0248`, `%e` and `%4`.  The peels below are the steps between the merge and
the loop head — each says that no block on the path binds the name, at every class the byte
takes. -/

/-- **The merge's five cells, at the byte's route.**  The route's pivots bind only their own
comparison cells, so the five names the merge's group reads are the loop head's at every
class. -/
theorem hlastMergeByte_envs {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (hb : HcontByteRoute (head35 b35)) (r₁ r₂ r₃ : CallOutcome) (cA rdv xA : BitVec 32) :
    lookupName (hlastMergeByte C s x inc nep v ix b35 hb r₁ r₂ r₃ cA rdv xA).env "%inc.i" =
        lookupName s.env "%inc.i" ∧
      lookupName (hlastMergeByte C s x inc nep v ix b35 hb r₁ r₂ r₃ cA rdv xA).env "%nep" =
        lookupName s.env "%nep" ∧
      lookupName (hlastMergeByte C s x inc nep v ix b35 hb r₁ r₂ r₃ cA rdv xA).env "%e" =
        lookupName s.env "%e" ∧
      lookupName (hlastMergeByte C s x inc nep v ix b35 hb r₁ r₂ r₃ cA rdv xA).env "%4" =
        lookupName s.env "%4" ∧
      lookupName (hlastMergeByte C s x inc nep v ix b35 hb r₁ r₂ r₃ cA rdv xA).env
        "%sp.i.0248" = lookupName s.env "%sp.i.0248" := by
  rcases hb with ⟨a1, a2, a3⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3⟩ <;>
    simp only [hlastMergeByte, hlastEntryByte, ScanEntry, TailS₃, hlastTailByte, HeadS413,
      HeadS405, HeadS58, HeadS60, HeadS62, hlastSeamByte, hlastP35Any, hlastP33Any,
      hlastP37Any, hlastP35Out, hlastP33Out, hlastP37Out, hlastP39Out, hlastP41Out,
      hlastP41Low, hlastP39High, seamS, seamFin, hlastLand, headEndS, condEnd349OutAt,
      headAS₅, headAS₄, headAS₃, headAS₂, headAS₁, stateAt, cells, State.bind] <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    repeat rw [lookupName_cons_ne _ _ (by decide)]

/-! ### The default arm's remaining cells

Each is a peel from `sw.default.i`'s entry to the loop head. -/

/-- `%gap.i` at the default arm is the loop head's: the head chain binds no static
register. -/
theorem hlastAS5_envGap {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64)
    (h : lookupName s.env "%gap.i" = some (.ptr (C.stage.tok + 20))) :
    lookupName (headAS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20)) := by
  simp only [headAS₅, headAS₄, headAS₃, headAS₂, headAS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- `%4` at the default arm is the loop head's word. -/
theorem hlastAS5_envFour (s : State) (x : BitVec 8) (inc nep w : BitVec 64)
    (h : lookupName s.env "%4" = some (.int 64 w)) :
    lookupName (headAS₅ s x inc nep).env "%4" = some (.int 64 w) := by
  simp only [headAS₅, headAS₄, headAS₃, headAS₂, headAS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- `%idxprom.i` at the default arm is the loop head's. -/
theorem hlastAS5_envIdx (s : State) (x : BitVec 8) (inc nep : BitVec 64) (ix : BitVec 64)
    (h : lookupName s.env "%idxprom.i" = some (.int 64 ix)) :
    lookupName (headAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix) := by
  simp only [headAS₅, headAS₄, headAS₃, headAS₂, headAS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- `%t352.i` at the default arm is the loop head's token pointer. -/
theorem hlastAS5_envTok {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64)
    (h : lookupName s.env "%t352.i" = some (.ptr C.stage.tok)) :
    lookupName (headAS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok) := by
  simp only [headAS₅, headAS₄, headAS₃, headAS₂, headAS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-! ### The tail's start's cells and its segment's target

The tail's start is `HeadS413 (hlastSeam …) x`: the class-C span's target at the
value-position call.  Six of the cells the three call links read are the loop head's —
none of the head path's blocks binds a static register — and the two the empty arm's test
reads are the seam's stored end, which is `%4`'s word. -/

/-- **The tail start's five static cells, at the byte's route.**  None of the head path's
blocks binds a static register, so each is the loop head's at every class; the route's
pivots bind only their own comparison cells. -/
theorem hlastTailByte_envs {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (hb : HcontByteRoute (head35 b35)) :
    lookupName (hlastTailByte C s x inc nep v ix b35 hb).env "%kind404.i" =
        lookupName s.env "%kind404.i" ∧
      lookupName (hlastTailByte C s x inc nep v ix b35 hb).env "%root_done.i" =
        lookupName s.env "%root_done.i" ∧
      lookupName (hlastTailByte C s x inc nep v ix b35 hb).env "%t352.i" =
        lookupName s.env "%t352.i" ∧
      lookupName (hlastTailByte C s x inc nep v ix b35 hb).env "%c.i" =
        lookupName s.env "%c.i" ∧
      lookupName (hlastTailByte C s x inc nep v ix b35 hb).env "%z" =
        lookupName s.env "%z" := by
  rcases hb with ⟨a1, a2, a3⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3⟩ <;>
    simp only [hlastTailByte, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62,
      hlastSeamByte, hlastP35Any, hlastP33Any, hlastP37Any, hlastP35Out, hlastP33Out,
      hlastP37Out, hlastP39Out, hlastP41Out, hlastP41Low, hlastP39High, seamS, seamFin,
      hlastLand, headEndS, condEnd349OutAt, headAS₅, headAS₄, headAS₃, headAS₂, headAS₁,
      stateAt, cells, State.bind] <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%kind404.i` at the tail's start is the loop head's: it is one of `walkStaticRegs`'s
twenty-five and no block of the head path binds it. -/
theorem hlastTail_envKind {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (hb : HcontByteRoute (head35 b35)) :
    lookupName (hlastTailByte C s x inc nep v ix b35 hb).env "%kind404.i" =
      lookupName s.env "%kind404.i" :=
  (hlastTailByte_envs C s x inc nep v ix b35 hb).1

/-- `%root_done.i` at the tail's start is the loop head's: the second of the body's four
alloca slots and not a name any head-path block binds. -/
theorem hlastTail_envRootDone {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (hb : HcontByteRoute (head35 b35)) :
    lookupName (hlastTailByte C s x inc nep v ix b35 hb).env "%root_done.i" =
      lookupName s.env "%root_done.i" :=
  (hlastTailByte_envs C s x inc nep v ix b35 hb).2.1

/-- `%t352.i` at the tail's start is the loop head's token record: the head path binds no
register of that name, and the tail's own blocks write *through* it, not to it. -/
theorem hlastTail_envTok {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (hb : HcontByteRoute (head35 b35)) :
    lookupName (hlastTailByte C s x inc nep v ix b35 hb).env "%t352.i" =
      lookupName s.env "%t352.i" :=
  (hlastTailByte_envs C s x inc nep v ix b35 hb).2.2.1

/-- `%c.i` at the tail's start is the loop head's cursor record. -/
theorem hlastTail_envC {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (hb : HcontByteRoute (head35 b35)) :
    lookupName (hlastTailByte C s x inc nep v ix b35 hb).env "%c.i" =
      lookupName s.env "%c.i" :=
  (hlastTailByte_envs C s x inc nep v ix b35 hb).2.2.2.1

/-- `%z` at the tail's start is the loop head's log. -/
theorem hlastTail_envZ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (hb : HcontByteRoute (head35 b35)) :
    lookupName (hlastTailByte C s x inc nep v ix b35 hb).env "%z" =
      lookupName s.env "%z" :=
  (hlastTailByte_envs C s x inc nep v ix b35 hb).2.2.2.2

/-- **The tail's start is entered from `if.else405.i`**: the class-C span's last empty
body, by the states' own `pre` fields. -/
theorem hlastTail_pre {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (hb : HcontByteRoute (head35 b35)) :
    (hlastTailByte C s x inc nep v ix b35 hb).pre = some "if.else405.i" := rfl

/-- **`if.then413.i`'s `phi` on the empty-body edge selects zero.**  The class-C span's
last edge is `if.else405.i`'s, and the `phi` reads `0` there — the literal's kind, which is
what the tail's `valuePos` call receives. -/
theorem hlastTail_phi :
    phiIncoming "if.else405.i"
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] =
      some (.imm (.int 32 (BitVec.ofNat 32 0))) := by
  decide

/-- **The tail's `%ee.1.i` is `%4`'s word**: the seam stored `%cond350.i` there and no
block of the class-C span or the tail rebinds it.  This is the cell the empty arm's test
reads, and it is why the test is `ult v v`. -/
theorem hlastTail_ee {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (hb : HcontByteRoute (head35 b35)) :
    lookupName (hlastTailByte C s x inc nep v ix b35 hb).env "%ee.1.i" =
      some (.int 64 (BitVec.ofNat 64 v)) := by
  simp only [hlastTailByte, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact hlastSeamByte_ee (hlastLand C s x inc nep v ix b35) v C.stage.tok b35 x hb

/-- **The tail's `%cond350.i` is the same word**: `cond.end349.i` bound it once, and the
whitespace check's pivots and the seam rebind other names. -/
theorem hlastTail_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (hb : HcontByteRoute (head35 b35)) :
    lookupName (hlastTailByte C s x inc nep v ix b35 hb).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v)) := by
  simp only [hlastTailByte, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  rw [hlastSeamByte_cond]
  exact hlastLand_cond C s x inc nep v ix b35

/-- **The dispatch's entry has no local clause.**  `WalkLocal`'s scan arms cover
`while.body462.i` and `land.rhs457.i`; `NodeBlock105` is not among them, so the landing's
local fact is `True` at its own carry. -/
theorem hlastLoc105 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord)
    (s : State) (idx : BitVec 64) (a q : Nat) :
    WalkLocal (ScanC₁₀₅ (TailCarryScan C ev)) (landRhs457OutAt s idx a q) := by
  simp only [WalkLocal]
  repeat rw [ite_eq_right (by decide)]
  trivial

/-- **The range leaf has no local clause either.**  `LeafBlock96` is not one of
`WalkLocal`'s scan blocks, so the leaf's local fact is `True` at its own carry. -/
theorem hlastLoc96 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord)
    (s : State) (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8) :
    WalkLocal (ScanC₉₆ (TailCarryScan C ev)) (ScanS₉₆ s idx a q x47) := by
  simp only [WalkLocal]
  repeat rw [ite_eq_right (by decide)]
  trivial

/-- **The scan's entry selects `%ee.1.i`** on the edge the copy call took: the `phi`'s two
arms, the second of which `if.then447.i` names.  The continuing arm's bundle reads it. -/
theorem hlastEntry_phiSel :
    phiIncoming "if.then447.i"
      [("while.body462.i", (Operand.reg "%inc463.i")),
       ("if.then447.i", (Operand.reg "%ee.1.i"))] = some (.reg "%ee.1.i") := by
  decide

/-! ### The empty tail's three links, from its three calls' rows

`consumerTailSegEmptyAt` (`JsonStage2WalkPrefixCount`) is the three links' composition at
*any* carry whose block is `if.then413.i` and any state whose two test cells hold one
number; the theorem below states it from the three calls' rows alone.  It is the producer
of a class's `hTail` field — `.cleanup`'s seam, the scalar route's and the last entry's all
reach `if.then413.i` — so the tail enters as three callee rows rather than as a segment.
The event record is produced, not supplied: the scalar call's post names it existentially
(`s2ScalarValuePost`), and `hret₂` selects the emit arm.

The tail's source state's two test cells are hypotheses: `%ee.1.i` is the seam's stored end
and `%cond350.i` the same word at each class's own seam, so each consumer reads them from
its own peel (`hlastTail_ee`/`hlastTail_cond`, `contTailStart_ee`, `scalarSeam_ee`/
`scalarSeam_cond`). -/
theorem emptyTailSeg_of_calls {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (r₁ r₂ r₃ : CallOutcome) (cd : Nat) {cA rdv xA : BitVec 32}
    (hInv : WalkInv G C s) (hblock : C.block = "if.then413.i")
    {p : String} (reg : String) {op : Operand}
    (hpre : s.pre = some p)
    (hphi : phiIncoming p
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some op)
    (hop : evalOperand (stateAt s.env s) op = some (.int 32 cA))
    (hkind : lookupName s.env "%kind404.i" = some (.ptr (C.stage.tok + 16)))
    (hrd : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)))
    (hread : readBytes
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4))
      (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpre₁ : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)) s.next)
    (hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)) s.next = some r₁)
    (hret₁ : r₁.ret = .int 32 xA)
    (hbit0 : evalICmp .eq xA (BitVec.ofNat 32 0) = 0)
    (hzread : readBytes
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)) C.stage.z 8 =
      some (wordBytes 8 G.ev))
    (hc : lookupName s.env "%c.i" = some (.ptr (TailCarry₂ C).stage.c))
    (ht : lookupName s.env "%t352.i" = some (.ptr (TailCarry₂ C).stage.tok))
    (ho : lookupName s.env "%z" = some (.ptr (TailCarry₂ C).stage.z))
    (hpre₂ : s2ScalarValuePre
      [.ptr (TailCarry₂ C).stage.c, .ptr (TailCarry₂ C).stage.tok,
       .ptr (TailCarry₂ C).stage.z] r₁.mem r₁.next)
    (hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr (TailCarry₂ C).stage.c, .ptr (TailCarry₂ C).stage.tok,
       .ptr (TailCarry₂ C).stage.z] r₁.mem r₁.next = some r₂)
    (hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1))
    (hev64 : G.ev < 2 ^ 64)
    (htight : C.events.length ≤ C.k) (hklt : C.k < G.nep)
    (hpre₃ : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] r₂.mem r₂.next)
    (hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] r₂.mem r₂.next = some r₃)
    (hei : lookupName s.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 cd)))
    (hcd : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd)))
    (hcd64 : cd < 2 ^ 64) :
    ∃ ev : EventRecord,
      WalkSegment (stage2Calls stage2SubCalls) G C s (TailCarryEnd C ev)
        (ScanEntry s r₁ r₂ r₃ cd cd cA rdv xA) 3 := by
  -- 1. the value-position call's contract: the caller's memory comes back unchanged
  obtain ⟨r₁', hcall₁', hpost₁, _⟩ :=
    s2ValuePosContract.resolves (next := s.next) hpre₁
  obtain ⟨v₁, _, _, hmemV₁, _⟩ := hpost₁
  have hr₁ : r₁' = r₁ := Option.some.inj (hcall₁'.symm.trans hcall₁)
  rw [hr₁] at hmemV₁
  have hzreadJ : readBytes r₁.mem C.stage.z 8 = some (wordBytes 8 G.ev) := by
    rw [hmemV₁]; exact hzread
  -- 2. the scalar call's contract: the record it appended, named by its post
  obtain ⟨r₂', hcall₂', hpost₂, _⟩ :=
    s2ScalarValueContract.resolves (next := r₁.next) hpre₂
  have hr₂ : r₂' = r₂ := Option.some.inj (hcall₂'.symm.trans hcall₂)
  rw [hr₂] at hpost₂
  obtain ⟨⟨_, _, _, _, _, _⟩, happPost⟩ := hpost₂
  obtain ⟨ev, happ₂⟩ := happPost hret₂
  -- 3. the copy call's contract: the answer and the memory it leaves
  obtain ⟨r₃', hcall₃', hpost₃, _⟩ :=
    s2AfterValueContract.resolves (next := r₂.next) hpre₃
  have hr₃ : r₃' = r₃ := Option.some.inj (hcall₃'.symm.trans hcall₃)
  rw [hr₃] at hpost₃
  obtain ⟨_, _, _, _, _⟩ := hpost₃
  exact ⟨ev, Seg.measure (consumerTailSegEmptyAt (G := G) (C := C) (s := s) r₁ r₂ r₃ ev
    cd hInv hblock p reg cA op rdv xA hpre hphi hop hkind hrd hread hpre₁ hcall₁ hret₁
    hbit0 hzreadJ hc ht ho hcall₂ happ₂ hret₂ hev64
    (by
      have h1 := hInv.evlen_le
      have h2 := G.evRoom
      have h3 := G.evcapLt
      omega)
    htight hklt hpre₃ hcall₃ hei hcd hcd64)⟩

/-! ### The tail, produced from the three calls' contracts, on the scan-free arm

The value-position call, the scalar call's emit arm and the copy call, each applied at its
own staged argument list and at the caller's own state, then composed by
`consumerTailSegEmptyAt` at their count.

Contract 1's post hands back the caller's memory (`s2ValuePosPost`), so the stream read is
stated at the staged memory and re-expressed at `r₁.mem`; contract 3's post names the copy
call's memory; contract 2's post is existential in the record, and that is now the *source*
of the bundle's `ev` rather than an obstacle: the conclusion is `∃ ev, WalkSegment …`
carrying `TailCarryEnd C ev`, and the append it needs is the post's own second conjunct at
`hret₂`.  The copy call's precondition is stated at `C.stage` instead of
`(TailCarry₃ C ev).stage` (the two are definitionally equal, a record update keeping the
stage), so no argument mentions the record that is produced here.

The two cells the empty arm's test reads are **not** premises: `%ee.1.i` is the seam's
stored end and `%cond350.i` the same word (`hlastTail_ee`, `hlastTail_cond`), so the
equation `ei = cd` is `rfl` and the arm needs no span and no budget. -/
theorem hlastTail_of_calls {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (hb : HcontByteRoute (head35 b35)) (r₁ r₂ r₃ : CallOutcome) {cA rdv xA : BitVec 32}
    (hInvT : WalkInv G (TailStartC C) (hlastTailByte C s x inc nep v ix b35 hb))
    (hblockT : (TailStartC C).block = "if.then413.i")
    {pT : String} {opT : Operand} {regT : String}
    (hpreT : (hlastTailByte C s x inc nep v ix b35 hb).pre = some pT)
    (hincT : phiIncoming pT
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some opT)
    (hopT : evalOperand (stateAt (hlastTailByte C s x inc nep v ix b35 hb).env
      (hlastTailByte C s x inc nep v ix b35 hb)) opT = some (.int 32 cA))
    (hkindT : lookupName (hlastTailByte C s x inc nep v ix b35 hb).env "%kind404.i" =
      some (.ptr (C.stage.tok + 16)))
    (hrdT : lookupName (hlastTailByte C s x inc nep v ix b35 hb).env "%root_done.i" =
      some (.ptr (G.next0 + 8)))
    (hreadT : readBytes
      (writeBytes (hlastTailByte C s x inc nep v ix b35 hb).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpre₁ : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .int 32 rdv,
       .ptr (TailStartC C).stage.ctype, .ptr (TailStartC C).stage.cst]
      (writeBytes (hlastTailByte C s x inc nep v ix b35 hb).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (hlastTailByte C s x inc nep v ix b35 hb).next)
    (hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .int 32 rdv,
       .ptr (TailStartC C).stage.ctype, .ptr (TailStartC C).stage.cst]
      (writeBytes (hlastTailByte C s x inc nep v ix b35 hb).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (hlastTailByte C s x inc nep v ix b35 hb).next = some r₁)
    (hret₁ : r₁.ret = .int 32 xA)
    (hbit0T : evalICmp .eq xA (BitVec.ofNat 32 0) = 0)
    (hzread : readBytes
      (writeBytes (hlastTailByte C s x inc nep v ix b35 hb).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) C.stage.z 8 = some (wordBytes 8 G.ev))
    (hcT : lookupName (hlastTailByte C s x inc nep v ix b35 hb).env "%c.i" =
      some (.ptr (TailCarry₂ (TailStartC C)).stage.c))
    (htT : lookupName (hlastTailByte C s x inc nep v ix b35 hb).env "%t352.i" =
      some (.ptr (TailCarry₂ (TailStartC C)).stage.tok))
    (hoT : lookupName (hlastTailByte C s x inc nep v ix b35 hb).env "%z" =
      some (.ptr (TailCarry₂ (TailStartC C)).stage.z))
    (hpre₂ : s2ScalarValuePre
      [.ptr (TailCarry₂ (TailStartC C)).stage.c, .ptr (TailCarry₂ (TailStartC C)).stage.tok,
       .ptr (TailCarry₂ (TailStartC C)).stage.z] r₁.mem r₁.next)
    (hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr (TailCarry₂ (TailStartC C)).stage.c, .ptr (TailCarry₂ (TailStartC C)).stage.tok,
       .ptr (TailCarry₂ (TailStartC C)).stage.z] r₁.mem r₁.next = some r₂)
    (hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1))
    (hev64 : G.ev < 2 ^ 64)
    (htight : C.events.length ≤ C.k) (hklt : C.k < G.nep)
    (hpre₃ : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .ptr (G.next0 + 8),
       .ptr (TailStartC C).stage.ctype,
       .ptr (TailStartC C).stage.cst] r₂.mem r₂.next)
    (hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .ptr (G.next0 + 8),
       .ptr (TailStartC C).stage.ctype,
       .ptr (TailStartC C).stage.cst] r₂.mem r₂.next = some r₃)
    (hvT : v < 2 ^ 64) :
    ∃ ev : EventRecord,
      WalkSegment (stage2Calls stage2SubCalls) G (TailStartC C)
        (hlastTailByte C s x inc nep v ix b35 hb)
        (TailCarryEnd (TailStartC C) ev)
        (hlastEntryByte C s x inc nep v ix b35 hb r₁ r₂ r₃ cA rdv xA) 3 :=
  emptyTailSeg_of_calls G (TailStartC C) (hlastTailByte C s x inc nep v ix b35 hb) r₁ r₂ r₃ v
    hInvT hblockT regT hpreT hincT hopT hkindT hrdT hreadT hpre₁ hcall₁ hret₁ hbit0T
    hzread hcT htT hoT hpre₂ hcall₂ hret₂ hev64 htight hklt hpre₃ hcall₃
    (hlastTail_ee C s x inc nep v ix b35 hb) (hlastTail_cond C s x inc nep v ix b35 hb) hvT

/-! ### The head byte's class, from the two bits that name it

The bundle's arm is the class's: with the head's `slt 125` and `eq 125` tests both clear,
the byte is `ofNat 8 126` or `ofNat 8 127` in the signed order the program's `icmp slt`
reads.  The other six class bits — two more pivots on the same byte, the seam's
`x = '-' ∨ x + 208 <u 10` test and the class-C span's three — are then closed computations
on those two values, so the class is **two premises, not eight**, and the bundle's fields
are unchanged.  `hbit6` is `decide`d at both values; the four comparisons follow from the
signed order alone, which is why they need no case split.

These are the document's facts and stay premises; what is *derived* is the arithmetic
between them, which is where a caller's mistake would otherwise be silent. -/

/-- **A signed comparison clear at a larger literal is clear at every smaller one.**  The
bit is `¬ (x.slt b)`, i.e. `b.toInt ≤ x.toInt`, and the literals are ordered. -/
theorem hlast_slt_zero_of_toInt_le {w : Nat} {x a b : BitVec w}
    (hab : a.toInt ≤ b.toInt) (h : evalICmp .slt x b = 0) : evalICmp .slt x a = 0 := by
  have hnb : ¬ x.toInt < b.toInt := by
    intro hlt
    have h2 : evalICmp .slt x b = 1 := by simp [evalICmp, BitVec.slt_eq_decide, hlt]
    rw [h] at h2
    exact absurd h2 (by decide)
  have hna : ¬ x.toInt < a.toInt := by omega
  simp [evalICmp, BitVec.slt_eq_decide, hna]

/-- **A byte clear of a larger literal is not a smaller one either.** -/
theorem hlast_eq_zero_of_slt_zero {w : Nat} {x c b : BitVec w}
    (hcb : c.toInt < b.toInt) (h : evalICmp .slt x b = 0) : evalICmp .eq x c = 0 := by
  have hnb : ¬ x.toInt < b.toInt := by
    intro hlt
    have h2 : evalICmp .slt x b = 1 := by simp [evalICmp, BitVec.slt_eq_decide, hlt]
    rw [h] at h2
    exact absurd h2 (by decide)
  have hne : x ≠ c := by
    intro heq
    have htoInt : x.toInt = c.toInt := by rw [heq]
    omega
  simp [evalICmp, hne]

/-- **The seam's byte test is decided by the class.**  `slt 125` and `eq 125` clear leave
the byte at `ofNat 8 126` or `ofNat 8 127` — the signed order caps it at `2 ^ 7 - 1` —
and `x = 45 ∨ x + 208 <u 10` is `0` at both. -/
theorem hlast_bit6_of_class {x : BitVec 8}
    (hlt125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq x (BitVec.ofNat 8 125) = 0) :
    (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := by
  have h1 : ¬ x.toInt < 125 := by
    intro hlt
    have h2 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 := by
      simp [evalICmp, BitVec.slt_eq_decide, hlt]
    rw [hlt125] at h2
    exact absurd h2 (by decide)
  have h2 : x.toInt ≠ 125 := by
    intro heq
    have hx : x = BitVec.ofNat 8 125 := BitVec.toInt_inj.mp (by rw [heq]; decide)
    rw [hx] at hne125
    exact absurd hne125 (by decide)
  have h3 : x.toInt < 128 := by
    have hlt := BitVec.toInt_lt (x := x) (w := 8)
    simpa using hlt
  have hx : x = BitVec.ofNat 8 126 ∨ x = BitVec.ofNat 8 127 := by
    have h4 : x.toInt = 126 ∨ x.toInt = 127 := by omega
    rcases h4 with h | h
    · exact Or.inl (BitVec.toInt_inj.mp (by rw [h]; decide))
    · exact Or.inr (BitVec.toInt_inj.mp (by rw [h]; decide))
  rcases hx with h | h <;> rw [h] <;> decide

/-! ### The reads the staged carriers now supply

`%4`, `%t352.i`, `%e` and `%idxprom.i` are `WalkInv`'s cells, so the three facts the
producer used to take about them are clauses now: the stream's end is `G.n`, the entry's
index is `entryPos G C.k`, and the token's and refusal records' addresses are the
staging's.  What remains is the byte before the end: it is the document's own last byte,
and the head path's two token-record stores do not touch it.
-/

/-- An entry the stream holds is inside the document, at a header index below the
count — the same fact `entryPos_lt` states above this layer. -/
theorem hlast_entryPos_lt {m0 : Mem} (G : WalkGeom m0) {k : Nat} (hk : k < G.nep) :
    entryPos G k < G.n := by
  have hlen : G.ent.length = G.nep := by
    rw [← readLanes32_length m0 G.ep G.nep G.ent G.entries]
  have hk' : k < G.ent.length := by omega
  have hget : entryPos G k = G.ent[k] := by
    simp only [entryPos, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk',
      Option.getD_some]
  rw [hget]
  exact G.inside _ (List.getElem_mem hk')

/-- `ugt` at two staged words is `1` when the right word is strictly below the
left. -/
theorem hlast_ugt_of_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : b < a) :
    evalICmp .ugt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = 1 := by
  have h' : (BitVec.ofNat 64 b).toNat < (BitVec.ofNat 64 a).toNat := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    exact h
  rw [show evalICmp .ugt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)
      = BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 b) (BitVec.ofNat 64 a)) from rfl,
    show BitVec.ult (BitVec.ofNat 64 b) (BitVec.ofNat 64 a) = true from
      (BitVec.ult_iff_toNat_lt).2 h']
  rfl

/-- **The document reads as itself at the token's end.**  `cond.end349.i` stores the
entry's position and the gap record inside the token record — two writes at
`C.stage.tok` — and the token record is disjoint from the document's staged region, so
the head path's memory holds the document's bytes.  The byte is `walkDoc_byte`'s. -/
theorem headEndS_docByte {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) {x : BitVec 8} {inc nep c ix : BitVec 64} {q : Nat}
    (hq : q < G.n) :
    readBytes (headEndS C s x inc nep c ix).mem (G.b + q) 1 = some [G.bs.getD q 0] := by
  have hsep := stage2StagedWrites_against C.stage.separate (a := G.b)
    (m := G.n + stage2ReadTail) (by simp [stage2Regions])
    (r := (C.stage.tok, stage2TokenExtent)) (by simp [stage2StagedWrites])
  have htok : stage2TokenExtent = 24 := rfl
  rw [htok] at hsep
  have h4 : (natToBytes (BitVec.ofNat 32 1).toNat 4).length = 4 := natToBytes_length ..
  have h8 : (natToBytes ix.toNat 8).length = 8 := natToBytes_length ..
  have htok : stage2TokenExtent = 24 := rfl
  simp only [headEndS, condEnd349OutAt, headAS₅, headAS₄, headAS₃, headAS₂, headAS₁,
    State.bind]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok + 20)
    (v := natToBytes (BitVec.ofNat 32 1).toNat 4) (by rw [h4]; rcases hsep with h | h <;> omega)]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok)
    (v := natToBytes ix.toNat 8) (by rw [h8]; rcases hsep with h | h <;> omega)]
  exact walkDoc_byte G C s hInv (by have h := hInv.alen_le; omega)
    (le_trans hInv.evlen_le G.evRoom) hq

/-! ### The bundle, from the entry's evidence

The two counts and the merge's index are the loop's own values, read from the invariant
(`inc_reg`, `regs`, `depth_reg`); `hge`, `hterm`, `hk2nep` follow from them; the tail is
the three calls' contracts composed at their staged argument lists on the scan-free arm,
and the merge's cells are read off the tail's target by five peels.

Three groups that used to be premises are **derived** now, and each was checked against
the statement rather than assumed.  The literal's kind is the `phi`'s immediate
(`ofNat 32 0`, with `evalOperand` of an immediate being `Const.toValue`), and the appended
record is `s2ScalarValuePost`'s own — `hlastTail_of_calls` returns it existentially and
this definition names it with `Classical.choose`, because a `Type` cannot be built by
eliminating an existential.  `hInvT` is `hlastTailSeg`'s endpoint, so the sixteen links
from the loop head to `hlastTail` are what produce it, not the caller; `hblock` is the
consumer's own hypothesis (the bundle's statement quantifies over it) and is what that
segment needs.  The head byte's **class** is the next: its two naming bits (`hlt125`,
`hne125`) are premises and the other six are derived from them, so the eight-bit row costs
two arguments rather than eight.

**The last index is derived from the loop's own guard.**  `WalkInv.head_lt` is the head
block's clause (`WalkLocal`'s `NodeBlock21` branch: `C.k < G.nep`), so with the
consumer's negation `¬ (C.k + 1 < G.nep)` and `WalkInv.k_le` the index plus one *is* the
count — the producer takes the negation, which the bundle's statement already carries,
and no equality is supplied.  The cursor width is `WalkInv.evlen_le` through `evRoom` and
`evcapLt`, derived in `hlastTail_of_calls`.

What remains supplied is the document's content, the event stream's width, the log's base
word and the three callee preconditions — the survivors table above states each one's
producer.  The trace's count is not among them: the head's block is outside the append
stretch, so `WalkInv.events_le_of_tight` gives `C.events.length ≤ C.k` here and
`WalkInv.head_lt` gives the head's guard, which is the pair `hlastTail_of_calls` takes. -/
noncomputable def hlastFacts_of_staging {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hnot : ¬ (C.k + 1 < G.nep))
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0)))
    (r₁ r₂ r₃ : CallOutcome) {rdv : BitVec 32} {xA : BitVec 32}
    (hreadT : readBytes
      (writeBytes (hlastTailRoute C s hb).mem (C.stage.tok + 16)
        (natToBytes ((0 : BitVec 32)).toNat 4)) (G.next0 + 8) 4 =
        some (natToBytes rdv.toNat 4))
    (hpre₁ : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .int 32 rdv,
       .ptr (TailStartC C).stage.ctype, .ptr (TailStartC C).stage.cst]
      (writeBytes (hlastTailRoute C s hb).mem (C.stage.tok + 16)
        (natToBytes ((0 : BitVec 32)).toNat 4)) (hlastTailRoute C s hb).next)
    (hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .int 32 rdv,
       .ptr (TailStartC C).stage.ctype, .ptr (TailStartC C).stage.cst]
      (writeBytes (hlastTailRoute C s hb).mem (C.stage.tok + 16)
        (natToBytes ((0 : BitVec 32)).toNat 4)) (hlastTailRoute C s hb).next = some r₁)
    (hret₁ : r₁.ret = .int 32 xA)
    (hbit0T : evalICmp .eq xA (BitVec.ofNat 32 0) = 0)
    (hzread : readBytes
      (writeBytes (hlastTailRoute C s hb).mem (C.stage.tok + 16)
        (natToBytes ((0 : BitVec 32)).toNat 4)) C.stage.z 8 = some (wordBytes 8 G.ev))
    (hpre₂ : s2ScalarValuePre
      [.ptr (TailCarry₂ (TailStartC C)).stage.c, .ptr (TailCarry₂ (TailStartC C)).stage.tok,
       .ptr (TailCarry₂ (TailStartC C)).stage.z] r₁.mem r₁.next)
    (hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr (TailCarry₂ (TailStartC C)).stage.c, .ptr (TailCarry₂ (TailStartC C)).stage.tok,
       .ptr (TailCarry₂ (TailStartC C)).stage.z] r₁.mem r₁.next = some r₂)
    (hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1))
    (hev64 : G.ev < 2 ^ 64)
    (hpre₃ : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .ptr (G.next0 + 8),
       .ptr (TailStartC C).stage.ctype,
       .ptr (TailStartC C).stage.cst] r₂.mem r₂.next)
    (hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .ptr (G.next0 + 8),
       .ptr (TailStartC C).stage.ctype,
       .ptr (TailStartC C).stage.cst] r₂.mem r₂.next = some r₃) :
    HlastFacts G C s := by
  -- the literal's kind is the `phi`'s immediate, `ofNat 32 0`: `%kind404.i` is built from
  -- it, so the witness is derived (and its operand evaluation is `rfl`), not supplied
  let cA : BitVec 32 := (0 : BitVec 32)
  -- **the bundle's three witnesses are the staging's own cells**: `%4` is the stream's
  -- end — the document's length word — `%idxprom.i` this entry's position in the stream
  -- and `b35` the document's last byte, which is the one before the token's end
  let v : Nat := G.n
  let ix : BitVec 64 := BitVec.ofNat 64 (entryPos G C.k)
  let b35 : UInt8 := G.bs.getD (G.n - 1) 0
  have hklt : C.k < G.nep :=
    WalkInv.head_lt hInv (by rw [hblock]; rfl)
  -- **the trace's count, tight at the loop head**: `events_le`'s allowance is zero at
  -- every block before the entry's append, and the head is one of them, so the count is
  -- the entries consumed — the hypothesis the emit must preserve rather than a supply
  have htight : C.events.length ≤ C.k :=
    WalkInv.events_le_of_tight hInv
      (by rw [hblock]; exact walkEmitC_of_not_contains (by decide))
  -- **the loop's own guard turns the consumer's negation into the last index**: the head
  -- has an entry left and no entry after this one, so the carry's index plus one is the
  -- stream's count.  This is the premise the producer used to take.
  have hk : C.k + 1 = G.nep := by
    have := hInv.k_le
    omega
  have hqn : entryPos G C.k < G.n := hlast_entryPos_lt G hklt
  have h4L : lookupName s.env "%4" = some (.int 64 (BitVec.ofNat 64 v)) := by
    show lookupName s.env "%4" = some (.int 64 (BitVec.ofNat 64 G.n))
    exact hInv.regs ("%4", .int 64 (BitVec.ofNat 64 G.n)) (by simp [walkStaticRegs])
  have hidxS : lookupName s.env "%idxprom.i" = some (.int 64 ix) := by
    show lookupName s.env "%idxprom.i" =
      some (.int 64 (BitVec.ofNat 64 (entryPos G C.k)))
    exact hInv.idx_reg
  have htokS : lookupName s.env "%t352.i" = some (.ptr C.stage.tok) :=
    hInv.regs ("%t352.i", .ptr C.stage.tok) (by simp [walkStaticRegs])
  have hv63 : v < 2 ^ 63 := by
    show G.n < 2 ^ 63
    have h := G.maxDoc
    simp only [stage2MaxDocument] at h
    omega
  have hugt : evalICmp .ugt (BitVec.ofNat 64 v) ix = 1 := by
    show evalICmp .ugt (BitVec.ofNat 64 G.n) (BitVec.ofNat 64 (entryPos G C.k)) = 1
    refine hlast_ugt_of_lt ?_ ?_ hqn
    · have h := G.maxDoc
      simp only [stage2MaxDocument] at h
      omega
    · have h := G.maxDoc
      simp only [stage2MaxDocument] at h
      omega
  have hread35 : readBytes (headEndS C s (hlastByte G C) (hlastIncV C) (hlastNepV G)
      (BitVec.ofNat 64 v) ix).mem ((G.b - 1) + v) 1 = some [b35] := by
    have haddr : (G.b - 1) + G.n = G.b + (G.n - 1) := by
      have hb := G.bPos
      omega
    rw [show (G.b - 1) + v = G.b + (G.n - 1) from haddr]
    exact headEndS_docByte G C s hInv (by omega)
  -- the head's cells, derived once: the prefix's segment reads them and the bundle
  -- records them, so neither is stated here twice
  have h8 : evalOperand s (.reg "%8") = some (.int 8 (hlastByte G C)) := by
    exact LeanLLVM.evalOperand_reg_of hInv.iter.reg8
  -- the class's other six bits, from the two that name it: the byte is 126 or 127
  have hlt91 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 91) = 0 :=
    hlast_slt_zero_of_toInt_le (by decide) hlt125
  have hlt123 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 123) = 0 :=
    hlast_slt_zero_of_toInt_le (by decide) hlt125
  have hc110 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 0 :=
    hlast_slt_zero_of_toInt_le (by decide) hlt125
  have hc116 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 116) = 0 :=
    hlast_slt_zero_of_toInt_le (by decide) hlt125
  have hceq116 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 116) = 0 :=
    hlast_eq_zero_of_slt_zero (by decide) hlt125
  have hbit6 : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 :=
    hlast_bit6_of_class hlt125 hne125
  have hincE : evalOperand (headAS₄ s (hlastByte G C)) (.reg "%inc.i") =
      some (.int 64 (hlastIncV C)) := by
    simp only [evalOperand]
    rw [headAS4_envInc s (hlastByte G C)]
    exact LeanLLVM.evalOperand_reg_of hInv.inc_reg
  have hnepE : evalOperand (headAS₄ s (hlastByte G C)) (.reg "%nep") =
      some (.int 64 (hlastNepV G)) := by
    simp only [evalOperand]
    rw [headAS4_envNep s (hlastByte G C)]
    exact LeanLLVM.evalOperand_reg_of
      (hInv.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs]))
  have hgeE : evalICmp .ult (hlastIncV C) (hlastNepV G) = 0 := by
    show evalICmp .ult (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) = 0
    rw [hk]
    exact hlast_ult_self _
  have hav5E : lookupName (headAS₅ s (hlastByte G C) (hlastIncV C) (hlastNepV G)).env "%4" =
      some (.int 64 (BitVec.ofNat 64 v)) :=
    hlastAS5_envFour s (hlastByte G C) (hlastIncV C) (hlastNepV G) (BitVec.ofNat 64 v) h4L
  have hidx5E : lookupName (headAS₅ s (hlastByte G C) (hlastIncV C) (hlastNepV G)).env
      "%idxprom.i" = some (.int 64 ix) :=
    hlastAS5_envIdx s (hlastByte G C) (hlastIncV C) (hlastNepV G) ix hidxS
  have htok5E : lookupName (headAS₅ s (hlastByte G C) (hlastIncV C) (hlastNepV G)).env
      "%t352.i" = some (.ptr C.stage.tok) :=
    hlastAS5_envTok C s (hlastByte G C) (hlastIncV C) (hlastNepV G) htokS
  have hgap5E : lookupName (headAS₅ s (hlastByte G C) (hlastIncV C) (hlastNepV G)).env
      "%gap.i" = some (.ptr (C.stage.tok + 20)) :=
    hlastAS5_envGap C s (hlastByte G C) (hlastIncV C) (hlastNepV G)
      (hInv.regs ("%gap.i", .ptr (C.stage.tok + 20)) (by simp [walkStaticRegs]))
  -- **the invariant at the tail's start is the prefix's endpoint**, not an input: the
  -- `12 + hlastByteCount hb` links `hlastTailSegByte` proves from these same cells, whose
  -- `inv'` is the field
  have hInvT : WalkInv G (TailStartC C) (hlastTailAtByte C s v ix b35 hb) := by
    have hseg := hlastTailSegByte (G := G) (C := C) (s := s) hInv hblock h8 hlt91 hlt123
      hlt125 hne125 hincE hnepE hgeE hav5E hidx5E htok5E hgap5E hugt hread35 hv63 hb
      hbit6 hc110 hc116 hceq116
    exact hseg.inv'
  -- **the appended record and the tail's segment are produced together**: the scalar
  -- call's post names the record, and the segment's carry advances the trace by it.
  -- The bundle is a `Type`, so the witness is named with `Classical.choose` rather than
  -- eliminated into it — the existence is the helper's, the naming is ours
  have htailExists : ∃ ev : EventRecord,
      WalkSegment (stage2Calls stage2SubCalls) G (TailStartC C)
        (hlastTailAtByte C s v ix b35 hb)
        (TailCarryEnd (TailStartC C) ev)
        (hlastEntryByte C s (hlastByte G C) (hlastIncV C) (hlastNepV G) v ix b35 hb
          r₁ r₂ r₃ cA rdv xA) 3 :=
    hlastTail_of_calls G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) v ix b35 hb
      r₁ r₂ r₃ (cA := cA) hInvT rfl (pT := "if.else405.i")
      (opT := .imm (.int 32 (BitVec.ofNat 32 0)))
      (regT := "%4")
      (hpreT := hlastTail_pre C s (hlastByte G C) (hlastIncV C) (hlastNepV G) v ix b35 hb)
      (hincT := hlastTail_phi) (hopT := rfl)
      (hkindT := by
        rw [hlastTail_envKind C s (hlastByte G C) (hlastIncV C) (hlastNepV G) v ix b35 hb]
        exact hInv.regs ("%kind404.i", .ptr (C.stage.tok + 16)) (by simp [walkStaticRegs]))
      (hrdT := by
        rw [hlastTail_envRootDone C s (hlastByte G C) (hlastIncV C) (hlastNepV G) v ix b35
          hb]
        exact hInv.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs]))
      hreadT hpre₁ hcall₁ hret₁ hbit0T hzread
      (hcT := by
        rw [hlastTail_envC C s (hlastByte G C) (hlastIncV C) (hlastNepV G) v ix b35 hb]
        exact hInv.regs ("%c.i", .ptr C.stage.c) (by simp [walkStaticRegs]))
      (htT := by
        rw [hlastTail_envTok C s (hlastByte G C) (hlastIncV C) (hlastNepV G) v ix b35 hb]
        exact htokS)
      (hoT := by
        rw [hlastTail_envZ C s (hlastByte G C) (hlastIncV C) (hlastNepV G) v ix b35 hb]
        exact hInv.regs ("%z", .ptr C.stage.z) (by simp [walkStaticRegs]))
      hpre₂ hcall₂ hret₂ hev64 htight hklt hpre₃ hcall₃ (by omega)
  let ev : EventRecord := Classical.choose htailExists
  have hTail : WalkSegment (stage2Calls stage2SubCalls) G (TailStartC C)
      (hlastTailAtByte C s v ix b35 hb)
      (TailCarryEnd (TailStartC C) ev)
      (hlastEntryByte C s (hlastByte G C) (hlastIncV C) (hlastNepV G) v ix b35 hb
        r₁ r₂ r₃ cA rdv xA) 3 :=
    Classical.choose_spec htailExists
  exact
  { x := hlastByte G C
    h8 := h8
    hlt91 := hlt91
    hlt123 := hlt123
    hlt125 := hlt125
    hne125 := hne125
    inc := hlastIncV C
    nep := hlastNepV G
    hinc := hincE
    hnep := hnepE
    hge := hgeE
    v := v
    hav5 := hav5E
    ix := ix
    hidx5 := hidx5E
    htok5 := htok5E
    hgap5 := hgap5E
    hugt := hugt
    b35 := b35
    hread35 := hread35
    hv63 := hv63
    hb := hb
    hbit6 := hbit6
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
    k2 := C.k + 1
    nepv := hlastNepV G
    spv := C.sp
    hk2 := by
      show evalOperand (hlastMergeAt C s v ix b35 hb r₁ r₂ r₃ cA rdv xA) (.reg "%inc.i") =
        some (.int 64 (BitVec.ofNat 64 (C.k + 1)))
      simp only [evalOperand]
      rw [(hlastMergeByte_envs C s (hlastByte G C) (hlastIncV C) (hlastNepV G) v ix b35 hb
        r₁ r₂ r₃ cA rdv xA).1]
      exact LeanLLVM.evalOperand_reg_of hInv.inc_reg
    hnepM := by
      show lookupName (hlastMergeAt C s v ix b35 hb r₁ r₂ r₃ cA rdv xA).env "%nep" =
        some (.int 64 (hlastNepV G))
      rw [(hlastMergeByte_envs C s (hlastByte G C) (hlastIncV C) (hlastNepV G) v ix b35 hb
        r₁ r₂ r₃ cA rdv xA).2.1]
      exact hInv.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs])
    hterm := by
      show C.k + 1 = (hlastNepV G).toNat
      rw [hk]
      exact (hlast_nep_toNat G).symm
    hk2nep := hk
    hspvM := by
      show evalOperand (hlastMergeAt C s v ix b35 hb r₁ r₂ r₃ cA rdv xA) (.reg "%sp.i.0248") =
        some (.int 32 (BitVec.ofNat 32 C.sp))
      simp only [evalOperand]
      rw [(hlastMergeByte_envs C s (hlastByte G C) (hlastIncV C) (hlastNepV G) v ix b35 hb
        r₁ r₂ r₃ cA rdv xA).2.2.2.2]
      exact LeanLLVM.evalOperand_reg_of hInv.depth_reg
    heM := by
      show lookupName (hlastMergeAt C s v ix b35 hb r₁ r₂ r₃ cA rdv xA).env "%e" =
        some (.ptr C.stage.e)
      rw [(hlastMergeByte_envs C s (hlastByte G C) (hlastIncV C) (hlastNepV G) v ix b35 hb
        r₁ r₂ r₃ cA rdv xA).2.2.1]
      exact hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs])
    h4M := by
      show lookupName (hlastMergeAt C s v ix b35 hb r₁ r₂ r₃ cA rdv xA).env "%4" =
        some (.int 64 (BitVec.ofNat 64 v))
      rw [(hlastMergeByte_envs C s (hlastByte G C) (hlastIncV C) (hlastNepV G) v ix b35 hb
        r₁ r₂ r₃ cA rdv xA).2.2.2.1]
      exact h4L
    hlastK := hk }

/-! ### The residual supply the producer still takes

`HlastResidue` is `hlastFacts_of_staging`'s argument list after the invariant's
clauses, the geometry and the loop's own guard have been read: the document's
byte class (the two bits that name it and the three the price's longest path
needs), the three calls' answers and their facts at the argument lists the walk
stages, the log's base word and the event stream's width.  It
is a `Type` because `rdv` and `xA` are witnesses the later fields are stated at,
exactly as the bundle is.

The structure is the *emission* arm's old evidence, and it is no longer the class's: at the
high-byte class's own route the kind literal is `if.else405.i`'s `0`, so `od_scalar_value`
answers `0` and the emission arm's `hret₂ = 1` has no inhabitant (`hlastResidue_empty`,
`JsonStage2WalkDispatchHlastSupply`).  The class's evidence is `HlastHighByteRefusal` below;
this structure stays for the conditional emission statement and its refutations
(`JsonStage2WalkHlastDomain`). -/
structure HlastResidue {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Type where
  /-- The head byte's class: the two pivots that name it. -/
  hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0
  hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0
  /-- **The byte before the token's end and its route**: the document's content, as the
  class its pivots select.  The route is a `Type` because the tail's source is the seam the
  class reaches, and the three calls' rows below are stated at it. -/
  hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0))
  /-- The three calls' answers, at the argument lists the walk stages. -/
  r₁ : CallOutcome
  r₂ : CallOutcome
  r₃ : CallOutcome
  /-- The value-position call's answer word and the root-done slot's word. -/
  rdv : BitVec 32
  xA : BitVec 32
  hreadT : readBytes
    (writeBytes (hlastTailRoute C s hb).mem (C.stage.tok + 16)
      (natToBytes ((0 : BitVec 32)).toNat 4)) (G.next0 + 8) 4 =
      some (natToBytes rdv.toNat 4)
  hpre₁ : s2ValuePosPre
    [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .int 32 rdv,
     .ptr (TailStartC C).stage.ctype, .ptr (TailStartC C).stage.cst]
    (writeBytes (hlastTailRoute C s hb).mem (C.stage.tok + 16)
      (natToBytes ((0 : BitVec 32)).toNat 4)) (hlastTailRoute C s hb).next
  hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
    [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .int 32 rdv,
     .ptr (TailStartC C).stage.ctype, .ptr (TailStartC C).stage.cst]
    (writeBytes (hlastTailRoute C s hb).mem (C.stage.tok + 16)
      (natToBytes ((0 : BitVec 32)).toNat 4)) (hlastTailRoute C s hb).next = some r₁
  hret₁ : r₁.ret = .int 32 xA
  hbit0T : evalICmp .eq xA (BitVec.ofNat 32 0) = 0
  /-- The log's base word: the event stream's own address. -/
  hzread : readBytes
    (writeBytes (hlastTailRoute C s hb).mem (C.stage.tok + 16)
      (natToBytes ((0 : BitVec 32)).toNat 4)) C.stage.z 8 = some (wordBytes 8 G.ev)
  /-- The scalar call's precondition, its answer and the emit arm's bit. -/
  hpre₂ : s2ScalarValuePre
    [.ptr (TailCarry₂ (TailStartC C)).stage.c, .ptr (TailCarry₂ (TailStartC C)).stage.tok,
     .ptr (TailCarry₂ (TailStartC C)).stage.z] r₁.mem r₁.next
  hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
    [.ptr (TailCarry₂ (TailStartC C)).stage.c, .ptr (TailCarry₂ (TailStartC C)).stage.tok,
     .ptr (TailCarry₂ (TailStartC C)).stage.z] r₁.mem r₁.next = some r₂
  hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1)
  /-- The event stream's base is a word. -/
  hev64 : G.ev < 2 ^ 64
  /-- The copy call's precondition and its answer. -/
  hpre₃ : s2AfterValuePre
    [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .ptr (G.next0 + 8),
     .ptr (TailStartC C).stage.ctype,
     .ptr (TailStartC C).stage.cst] r₂.mem r₂.next
  hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
    [.int 32 (BitVec.ofNat 32 (TailStartC C).sp), .ptr (G.next0 + 8),
     .ptr (TailStartC C).stage.ctype,
     .ptr (TailStartC C).stage.cst] r₂.mem r₂.next = some r₃

/-! ### The class's refusal evidence

`%8 ∈ {126, 127}` is not a value class: `if.then413.i`'s `phi` takes its
`if.else405.i` incoming for those bytes, so the kind word the block stores is `0`, and
`od_scalar_value` answers `0` at a zero kind (`stage2ScalarValue`'s first arm, which
writes `stage2ErrSetMsg`).  The walk leaves `if.then425.i` for `if.then432.i` and takes
the error path to `cleanup474.i` and the refusal copy — it never calls `s2_after_value`.

So the emission residue above is not this class's evidence: its `hret₂` asks for the
emit answer `1`, which the class cannot produce.  This structure is the refusal arm's
supply instead, and its answer and record are *derived* by the producer
(`JsonStage2WalkDispatchHlastSupply`) from the staged words and the model — the kind
word is the store's own `0`, so `s2ScalarValue_refused` names both `hret₂` and `hmem`.

The continuation is the class's own route, as the arm rows' segments are: the error
path's blocks (`if.then432.i`, `cond.end.i96`, the scan, `if.end.i97`, the escape tree,
`cleanup474.i`) have no composed segment in the tree, so the route to `if.then` is
carried rather than proved, and the producer of it is named where it is owed. -/
/-- The memory the tail's first call reads, at a kind literal: the token record's kind word
is the store's literal. -/
abbrev hlastKindStoreAt {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0))) (cA : BitVec 32) : Mem :=
  writeBytes (hlastTailRoute C s hb).mem (C.stage.tok + 16) (natToBytes cA.toNat 4)

/-- **The class's kind store**: the `if.else405.i` incoming is `0`. -/
abbrev hlastKindStore {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0))) : Mem :=
  hlastKindStoreAt C s hb (BitVec.ofNat 32 0)

/-- **The high-byte class's refusal evidence**: the seam's refusal rows
(`HlastSeamRefusal` at the routed tail — the two leading calls, the literal `0`, the
derived answer and record) and the class's route to the refusal copy. -/
structure HlastHighByteRefusal {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0))) : Type where
  /-- The rows at the routed tail, whose kind literal is `if.else405.i`'s `0`. -/
  rows : HlastSeamRefusal G (TailStartC C) (hlastTailRoute C s hb)
  /-- **The class's route to the refusal copy.** -/
  route : HlastRefuseRoute G C s

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hlastTailByte_envs
#print axioms LeanLLVM.Refinement.WalkScope.hlastMergeByte_envs
#print axioms LeanLLVM.Refinement.WalkScope.hlastEntryByte_envTok
#print axioms LeanLLVM.Refinement.WalkScope.hlastEntryByte_pc
#print axioms LeanLLVM.Refinement.WalkScope.hlast_toMerge
#print axioms LeanLLVM.Refinement.WalkScope.hlast_finish
#print axioms LeanLLVM.Refinement.WalkScope.hlast_refuse
#print axioms LeanLLVM.Refinement.WalkScope.hlastTail_of_calls
#print axioms LeanLLVM.Refinement.WalkScope.emptyTailSeg_of_calls
#print axioms LeanLLVM.Refinement.WalkScope.hlast_slt_zero_of_toInt_le
#print axioms LeanLLVM.Refinement.WalkScope.hlast_eq_zero_of_slt_zero
#print axioms LeanLLVM.Refinement.WalkScope.hlast_bit6_of_class
#print axioms LeanLLVM.Refinement.WalkScope.hlastFacts_of_staging

end WalkScope
end LeanLLVM.Refinement
