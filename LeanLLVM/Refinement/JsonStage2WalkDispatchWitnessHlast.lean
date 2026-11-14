/-
The walk's last entry: the two outcomes `WalkDispatchThree`'s `hlast` names.

## The premise both ends read

`hlast`'s hypothesis and the head prefix's premise are the **same fact** — the last
entry's `%inc ≥ %nep`, which `walkHeadChainToScan` takes as `hge` and `hlast` takes as
`¬ (C.k + 1 < G.nep)`.  That is why the composition is not four applications over
unrelated lemmas: it is **one premise, read at both ends**.  The last entry cannot
continue because its increments have reached the entry count, and the prefix cannot run
down the continuing arm for the same reason.

## The inventory

| piece | lemma | span |
|---|---|---|
| prefix | `walkHeadChainToScan` | `NodeBlock21 → while.body462.i` |
| scan → merge | `walkScanToMerge` | `while.body462.i → cleanup478.i` |
| merge step | `walkFinishMerge_at` | `cleanup478.i → if.then485.i` |
| path 3 | `walkFinishPath3` | `→ if.then` |
| continuation | `walkFinishRun` | `→ if.end` |
| flush | `WalkFlushAt.ofRun` | the refusal copy's four named steps |

The prefix is a `WalkChain` because its links are existential; the rest are segments,
and `WalkSegment.of_chain` is the direction between them — which is why the two live
in different shapes.


## `hlast` as stated is not provable

`ofContinueAndLast`'s second hypothesis

```lean
∀ C s, WalkInv G C s → C.block = walkLoopHead → ¬ (C.k + 1 < G.nep) → (∃ …) ∨ (∃ …)
```

is a statement about **the last entry**, and the segments it asks for are statements
about **the input**.  The prefix `walkHeadChainToScan` reads `%8`'s byte, four class
bits on it, `%inc` and `%nep`'s values, and the twelve facts the entry established —
and **none of them is invariant-carried**, so no proof of the stated hypothesis exists.
`¬ (C.k + 1 < G.nep)` supplies exactly one of them: the prefix's `hge`, that the
increments have reached the entry count.  **That is why the premise looked sufficient:
it is the one field of the input's bundle that a hypothesis about the entry can imply.**

## The bundle

`HlastFacts` is that bundle, grouped by subject: the head's byte, the entry counts, the
default arm's cells, the seam's cells, the second byte's class, the tail's counted
segment, the scan's landing, the latch's exit test, the merge's cells, and the entry
being the stream's last.
It is a `Type` rather than a `Prop` because its first member of each group is a
*witness* — the byte, the two counts, the selected operand — that the later groups'
statements are stated at; a `Prop`-valued structure cannot carry data
(`structure … : Prop` admits proof fields only), and the alternative — every witness
passed beside the bundle — is the 34-binder statement this bundle exists to avoid.
`WalkGeom` and `WalkStage` are the same shape for the same reason.

Two fields are not premises of a single lemma:

* `hlastK : C.k + 1 = G.nep` is the entry being the stream's last.  It is what the
  prefix's **price** becomes: the path's count is a `Nat` (`hlastPrefixSeg` counts it at
  `(((6 + 1) + 5) + 3) + 3 = 18`), so the price is `18 + 4 ≤ 32 · Δk` and `Δk = 1`
  follows from this equation — arithmetic, not a hypothesis.  Earlier this was a
  `∀ j` price field, because a `WalkChain`'s count is not projectable; the counted
  prefix retired it.
* `hTail` is a **segment at count `3`**, not a chain, for the same reason: the tail is
  a piece of a priced path.  The caveat is worth stating: an old supplier holding
  `hTail : WalkChain` **cannot** feed this bundle, because a chain does not imply a
  segment at a count.  No evidence was lost, only re-shaped — `consumerTailSegAt`
  builds that segment from the same three call contracts
  (`s2_value_pos`, `od_scalar_value`, `s2_after_value`) that `consumer_tail_chain`
  consumes.
* `hlatch`-group fields are stated **at the states named above** (`hlastLatch`,
  `hlastScanOut`, `hlastMerge`): the callers of `walkScanToMerge` and of
  `walkFinishMerge_at` have their premises at exactly those terms, and a fact stated
  at a term needs no peeling at its use.

**The invariant's clause is an upper bound** (`WalkInv.inner_cap`), and it must stay one:
`WalkInv` is asserted at mid-scan states, where `inner` is being spent down, so a
positivity field would make it unprovable at most of the layer.  A lower bound that is
only true at the loop head belongs to the refill's lemma (`walkLoopHead_inner_pos`), not
to the invariant.

The depth's polarity is **not** a bundle field.  The exit tail's test is
`%sp.i.1 = 0`, so the last entry's outcome is `finish` at depth zero and the refusal
otherwise: a field `≠ 0` in the bundle would make the bundle uninhabited exactly at the
depth-zero inputs, where `hlast_finish`'s alternative is the true one.  It is a fact
about the input like the rest, so it is an argument of the two lemmas that read it
(`hlast_refuse`, `hlast`), and `HlastFacts` stays free of it.

The scan's three links are re-stated rather than taken from `walkScanChain457_ws`,
because that lemma's conclusion leaves the latch *existential* (`∃ s', WalkChain …`)
and every fact the exit test reads is stated at the latch.  `WalkLink.landRhs457_at`,
`WalkLink.NodeBlock105_at` and `WalkLink.LeafBlock96_at` name their targets, so the
composition below is the same three links with the last one named — and the latch the
rest of the file reads is that name.

## The repair, in order

1. the bundle above;
2. `hlast_toMerge` — the prefix chain, its segment, the latch's exit and the merge,
   as one segment at the prefix's count plus two, with the merge's invariant;
3. `hlast_finish` — the finish disjunct: that segment, `cleanup478.i`'s block, and the
   merge's `phi` selection, its index and the entry count;
4. `hlast_refuse` — the refusal disjunct: the same segment, `walkFinishMerge_at`'s
   step, and `walkFinishPath3`'s two, at `if.then` with the carry's refusal offset;
5. `hlast` — the pair, as the disjunction.

## The assembly's premise, and why this file states the bridge

`ofContinueAndLast`'s second hypothesis is a statement about the last entry whose
facts are the input's, and the bundle belongs to the caller.  **The premise cannot name
`HlastFacts` from `JsonStage2WalkAssembly`**: that module is the walk layer's *base*
(`JsonStage2WalkSteps` and `JsonStage2WalkStepsPath` import it, and every witness module
above them does too), while the bundle's field types name states defined above it —
`headAS₄`/`headAS₅`/`headEndS` (`JsonStage2WalkHeadChainA`),
`seamAt`/`TailStart`/`TailStartC`/`ScanEntry` (`JsonStage2WalkHeadChainScan`),
`ScanC₁₀₅`/`ScanS₉₆`/`ScanCMerge`/`landRhs457OutAt` (`JsonStage2WalkStepsPath`) and
`scanLatchOut`/`Latch462S` (`JsonStage2WalkInduce`).  Importing this module into the
assembly therefore closes a cycle through `JsonStage2WalkSteps`, which the build rejects.

So the premise keeps its shape, and the composition that consumes the bundle is stated
here, where it is above both: `walkDispatchThree_ofLastFacts` re-derives
`ofContinueAndLast`'s case split at `calls := stage2Calls stage2SubCalls` (the split is
five lines: the revolution from `hcont`, and the last entry's two arms from `hlast` with
the depth's polarity), with the bundle threaded at the point the input supplies it.  That
is the assembly's use site.

Making the *assembly's own premise* name the bundle would first require the states above
to move down into `JsonStage2WalkScope` — `headAS₄`, `headAS₅`, `headEndS`, `seamAt`,
`TailStart`, `TailStartC`, `ScanEntry`, `ScanC₁₀₅`, `ScanS₉₆`, `ScanCMerge`,
`landRhs457OutAt`, `scanLatchOut`, `Latch462S` — which is a change to modules this file
does not own.  Until then, the premise's shape in the assembly is unchanged and its
producer is the theorem below.

The old and the new shapes of the premise, for whichever of those two routes is taken:

```lean
-- old (JsonStage2WalkAssembly.lean:1244–1257)
(hlast : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
  ¬ (C.k + 1 < G.nep) → (∃ … p + 2 ≤ …) ∨ (∃ … p + 2 ≤ …))

-- with the bundle (this file's route: the bundle enters at the use site)
(hlast : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
  ¬ (C.k + 1 < G.nep) → HlastFacts G C s → (∃ …) ∨ (∃ …))
```

The segments in both disjuncts are at `stage2Calls stage2SubCalls` — a segment's
`calls` is the program's, not a variable — which is why the bridge below is stated at
those calls and not at a generic `calls`.

## Why this module exists

A composition's home is above every module its pieces live in, so this one imports the
three that hold the prefix, the scan and the finish paths.  What it holds is the pair of
segments `hlast` asks for, the bundle the input supplies, and the arithmetic between
them.

-/

import LeanLLVM.Refinement.JsonStage2WalkHeadChainScan
import LeanLLVM.Refinement.JsonStage2WalkFinishPath
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessFinish
import LeanLLVM.Refinement.JsonStage2WalkPrefixCount

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The states the last entry's path names

Every state from the scan's entry on is a name, because each is where a lemma's
premises are stated and where the next lemma's hypotheses are read: `walkIfEnd473_at`
and `scanExitSeg` name their own targets, so the refusal's `phi` facts have a term to
be stated at rather than a peeling chain to be carried.
-/

/-- The extra-token scan's entry, at the bundle's terms: the tail's end state. -/
def hlastEntry {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep c ix : BitVec 64) (e : BitVec 64) (b8 : BitVec 8) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ei cd : Nat) (cA rdv xA : BitVec 32) : State :=
  ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA

/-- The scan's latch, at the bundle's terms: the range leaf's target. -/
def hlastLatch {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep c ix : BitVec 64) (e : BitVec 64) (b8 : BitVec 8) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ei cd : Nat) (cA rdv xA : BitVec 32)
    (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8) : State :=
  Latch462S (hlastEntry C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA) idx a q x47

/-- The latch's exit: `scanExitSeg`'s target, the merge's entry state. -/
def hlastScanOut {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep c ix : BitVec 64) (e : BitVec 64) (b8 : BitVec 8) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ei cd : Nat) (cA rdv xA : BitVec 32)
    (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8) (qi cw : Nat) : State :=
  scanLatchOut (hlastLatch C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47)
    "%inc463.i" "%exitcond298.not" qi cw "if.end473.i"

/-- The merge's carry: `if.end473.i`'s `br` target. -/
abbrev hlastMergeC {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (ev : EventRecord) :
    WalkCarry G :=
  { ScanLatchC C ev with block := "cleanup478.i" }

/-- The merge's state: `walkIfEnd473_at`'s target, at the merge's own block. -/
def hlastMerge {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep c ix : BitVec 64) (e : BitVec 64) (b8 : BitVec 8) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ei cd : Nat) (cA rdv xA : BitVec 32)
    (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8) (qi cw : Nat) : State :=
  { hlastScanOut C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw with
    pc := "cleanup478.i", pre := some "if.end473.i" }

/-- **The input's facts, bundled.**  The statement that needs them is the last entry's
two outcomes; this is the single argument it takes, and each group is a subject the
prefix or the finish reads. -/
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
  /-- The default arm's cells: the token's position against the entry's index. -/
  reg : String
  c : BitVec 64
  ix : BitVec 64
  hpre5 : phiIncoming "sw.default.i"
    [("cond.true345.i", Operand.reg "%conv347.i"),
     ("sw.default.i", Operand.reg "%4")] = some (.reg reg)
  hav5 : lookupName (headAS₅ s x inc nep).env reg = some (.int 64 c)
  hidx5 : lookupName (headAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix)
  htok5 : lookupName (headAS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok)
  hgap5 : lookupName (headAS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20))
  hugt : evalICmp .ugt c ix = 0
  /-- The seam's cells: the token's end `phi`, the stored word and the byte it tests. -/
  p : String
  op : Operand
  e : BitVec 64
  b8 : BitVec 8
  hpre6 : (headEndS C s x inc nep c ix).pre = some p
  hin6 : phiIncoming p
    [("cond.end349.i", (Operand.reg "%idxprom.i")),
     ("while.body370.i", (Operand.reg "%cond350.i")),
     ("LeafBlock43", (Operand.reg "%ee.0.i238")),
     ("LeafBlock46", (Operand.reg "%ee.0.i238")),
     ("LeafBlock48", (Operand.reg "%ee.0.i238")),
     ("LeafBlock33", (Operand.reg "%cond350.i")),
     ("LeafBlock35", (Operand.reg "%cond350.i")),
     ("LeafBlock37", (Operand.reg "%cond350.i"))] = some op
  hv6 : evalOperand (headEndS C s x inc nep c ix) op = some (.int 64 e)
  hend6 : lookupName (headEndS C s x inc nep c ix).env "%end.i" = some (.ptr (C.stage.tok + 8))
  h8end : lookupName (headEndS C s x inc nep c ix).env "%8" = some (.int 8 b8)
  hbit6 : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
    evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0
  /-- The second byte's class, read at the seam's name. -/
  x1 : BitVec 8
  h8c : evalOperand (seamAt C s x inc nep c ix e b8) (.reg "%8") = some (.int 8 x1)
  hc110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0
  hc116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0
  hceq116 : evalICmp .eq x1 (BitVec.ofNat 8 116) = 0
  /-- The tail's own: its three call outcomes, the event it emits, the seed's words and
  its chain from `TailStartC`'s state. -/
  r₁ : CallOutcome
  r₂ : CallOutcome
  r₃ : CallOutcome
  ev : EventRecord
  cA : BitVec 32
  rdv : BitVec 32
  xA : BitVec 32
  ei : Nat
  cd : Nat
  hTail : WalkSegment (stage2Calls stage2SubCalls) G (TailStartC C)
    (TailStart C s x inc nep c ix e b8 x1)
    (TailCarryScan (TailStartC C) ev)
    (hlastEntry C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA) 3
  /-- The scan's landing: the counter's selection, the byte's address and the byte. -/
  idx : BitVec 64
  a : Nat
  q : Nat
  bs : List UInt8
  src : String
  sel : Operand
  hpreS : (hlastEntry C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA).pre = some src
  hincS : phiIncoming src
    [("while.body462.i", (Operand.reg "%inc463.i")),
     ("if.then447.i", (Operand.reg "%ee.1.i"))] = some sel
  hopS : evalOperand (stateAt
    (hlastEntry C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA).env
    (hlastEntry C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA)) sel =
    some (.int 64 idx)
  h3S : lookupName (hlastEntry C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA).env "%3" =
    some (.ptr a)
  hpos : (idx.signExtend 64).toNat < 2 ^ 63
  hreadS : readBytes
    (hlastEntry C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA).mem
    (a + (idx.signExtend 64).toNat) 1 = some bs
  hbsS : bytesToNat bs = q
  hloc105 : WalkLocal (ScanC₁₀₅ (TailCarryScan (TailStartC C) ev))
    (landRhs457OutAt (hlastEntry C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA) idx a q)
  x47 : BitVec 8
  h47 : evalOperand
    (landRhs457OutAt (hlastEntry C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA) idx a q)
    (.reg "%47") = some (.int 8 x47)
  hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1
  hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
  hloc96 : WalkLocal (ScanC₉₆ (TailCarryScan (TailStartC C) ev))
    (ScanS₉₆ (hlastEntry C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA) idx a q x47)
  hlatch : WalkLocal { TailCarryScan (TailStartC C) ev with block := "while.body462.i" }
    (hlastLatch C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47)
  /-- The latch's exit test: the scan's counter and bound, the token record's pointer,
  and the exit's own local. -/
  qi : Nat
  cw : Nat
  tok : Nat
  hq : lookupName
    (hlastLatch C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47).env
    "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 qi))
  hcwL : lookupName
    (hlastLatch C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47).env
    "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cw))
  hqc : qi + 1 = cw
  hcw0 : 1 ≤ cw
  hcw64 : cw < 2 ^ 64
  /-- **The scan's last visit is affordable — and that is a restriction on the input.**
  With `hqc` this reads `1 ≤ C.inner`: a head state whose inner budget is zero satisfies
  `WalkInv` and admits no `HlastFacts`, so the bundle is uninhabited there.  The bound
  cannot move into `WalkInv`: the invariant is asserted at states *inside* an iteration,
  where the scans have spent `inner` down to zero, so `1 ≤ C.inner` is false there.  It
  belongs where it is — with the scan's own premise (`scanExitSeg`'s `c - i ≤ C.inner`)
  — and the lower bound a producer needs is the loop head's refill, which
  `walkLoopHead_inner_pos` supplies from `C.inner = walkInnerCap G`.  **So this field is
  now derivable** from `hqc` and the refill's equality; it stays a field until a producer
  uses that lemma, because the equality is not an invariant clause. -/
  hinner : cw - qi ≤ C.inner
  hexit : ∀ (e : State), e.pre = some "while.body462.i" →
    lookupName e.env "%inc463.i" = some (.int 64 (BitVec.ofNat 64 (qi + 1))) →
    lookupName e.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cw)) →
    WalkLocal (G := G) (ScanCMerge (ScanLatchC C ev)) e
  htokL : lookupName
    (hlastScanOut C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw).env
    "%t352.i" = some (.ptr tok)
  /-- The merge's cells: the index `%inc.i` the `phi` selects, the entry count `%nep`,
  and the depth `%sp.i.0248` the exit tail's test reads. -/
  k2 : Nat
  nepv : BitVec 64
  spv : Nat
  v : Nat
  hk2 : evalOperand
    (hlastMerge C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw)
    (.reg "%inc.i") = some (.int 64 (BitVec.ofNat 64 k2))
  hnepM : lookupName
    (hlastMerge C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw).env
    "%nep" = some (.int 64 nepv)
  hterm : k2 = nepv.toNat
  hk2nep : k2 = G.nep
  hspvM : evalOperand
    (hlastMerge C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw)
    (.reg "%sp.i.0248") = some (.int 32 (BitVec.ofNat 32 spv))
  heM : lookupName
    (hlastMerge C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw).env
    "%e" = some (.ptr C.stage.e)
  h4M : lookupName
    (hlastMerge C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw).env
    "%4" = some (.int 64 (BitVec.ofNat 64 v))
  hv64 : v < 2 ^ 64
  /-- **The entry is the stream's last.**  The carry's index plus one is the count, which
  is what makes the path's count — `18 + 4` steps — fit the entry's credit
  (`stage2EntryAllowance = 32`).  Stated rather than assumed at the price: the path's
  count is now a `Nat` (`hlastPrefixSeg`), so the price is arithmetic on this. -/
  hlastK : C.k + 1 = G.nep

/-! ### The bundle's states, at their own argument lists

An `abbrev` taking the structure keeps the lemmas' statements short: the fields are
the `def`s' arguments in order, so a lemma's `hlastMerge f` is the same term the
bundle's field types spell out.
-/

abbrev hlastEntryF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HlastFacts G C s) : State :=
  hlastEntry C s f.x f.inc f.nep f.c f.ix f.e f.b8 f.x1 f.r₁ f.r₂ f.r₃ f.ei f.cd f.cA
    f.rdv f.xA

abbrev hlastLatchF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HlastFacts G C s) : State :=
  hlastLatch C s f.x f.inc f.nep f.c f.ix f.e f.b8 f.x1 f.r₁ f.r₂ f.r₃ f.ei f.cd f.cA
    f.rdv f.xA f.idx f.a f.q f.x47

abbrev hlastScanOutF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HlastFacts G C s) : State :=
  hlastScanOut C s f.x f.inc f.nep f.c f.ix f.e f.b8 f.x1 f.r₁ f.r₂ f.r₃ f.ei f.cd f.cA
    f.rdv f.xA f.idx f.a f.q f.x47 f.qi f.cw

abbrev hlastMergeCF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HlastFacts G C s) : WalkCarry G :=
  hlastMergeC C f.ev

abbrev hlastMergeF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HlastFacts G C s) : State :=
  hlastMerge C s f.x f.inc f.nep f.c f.ix f.e f.b8 f.x1 f.r₁ f.r₂ f.r₃ f.ei f.cd f.cA
    f.rdv f.xA f.idx f.a f.q f.x47 f.qi f.cw

/-! ### The refill at the loop head

`WalkInv.inner_cap` bounds the inner component **above** (`C.inner ≤ walkInnerCap G`),
and that is all the invariant may say: `WalkInv` is asserted at mid-scan states, where
`inner` is being spent down, so a positivity field would make it unprovable at most of
the layer.  **A lower bound that is only true at the loop head belongs to the refill's
lemma, not to the invariant.**

The refill is the merge's reset (`walkBack_step_at`'s carry sets `inner := walkInnerCap G`)
and the seed's carry sets the same (`walkSeed`), so a head carry reached from either has
`inner = walkInnerCap G` by construction.  The two lemmas below are the arithmetic and the
shape that consumes it.
-/

/-- **The cap is at least one.**  `walkInnerCap G = 4 * G.n + 5`. -/
theorem walkInnerCap_pos {m0 : Mem} (G : WalkGeom m0) : 1 ≤ walkInnerCap G := by
  simp only [walkInnerCap]
  omega

/-- **A refilled carry's inner budget is not empty.**  The reset the merge performs
(`{ C with inner := walkInnerCap G }`) and the seed's own carry are both of this shape. -/
theorem walkInnerReset_pos {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) :
    1 ≤ { C with inner := walkInnerCap G }.inner := walkInnerCap_pos G

/-- **The inner budget at the loop head is not empty.**  The equality is the refill's —
`walkBack_step_at`'s carry and `walkSeed` both set `inner := walkInnerCap G` — and it is
this lemma's hypothesis because it is not an invariant clause.  This is the lemma
`HlastFacts.hinner` needs: with the scan's last visit (`qi + 1 = cw`) it gives `1 ≤
C.inner`, which is `cw - qi ≤ C.inner`. -/
theorem walkLoopHead_inner_pos {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    (_hblock : C.block = walkLoopHead) (hrefill : C.inner = walkInnerCap G) :
    1 ≤ C.inner := hrefill ▸ walkInnerCap_pos G

/-- The entry stream's position past its last entry: the totalisation's own value, which
is what makes the finish's byte term vanish. -/
theorem entryPos_nep {m0 : Mem} (G : WalkGeom m0) : entryPos G G.nep = 0 := by
  have hlen : G.ent.length = G.nep := by
    rw [← readLanes32_length m0 G.ep G.nep G.ent G.entries]
  simp only [entryPos, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl

/-! ### The merge's step target

`walkFinishMerge_at` names its target as an update of the merge's state; the exit tail's
premises are read there, so it gets a name too: the three `phi` cells of the merge, at
`if.then485.i`. -/

/-- The merge's target: `%cmp.i`, `%k.2.i` and `%sp.i.1`, at the exit tail's first block. -/
def hlastThen {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep c ix : BitVec 64) (e : BitVec 64) (b8 : BitVec 8) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ei cd : Nat) (cA rdv xA : BitVec 32)
    (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8) (qi cw k2 spv : Nat) : State :=
  { hlastMerge C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw with
    env := cells [("%cmp.i", .int 1 (0 : BitVec 1)),
      ("%k.2.i", .int 64 (BitVec.ofNat 64 k2)),
      ("%sp.i.1", .int 32 (BitVec.ofNat 32 spv))]
      (hlastMerge C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw).env
    pc := "if.then485.i", pre := some "cleanup478.i" }

abbrev hlastThenF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HlastFacts G C s) : State :=
  hlastThen C s f.x f.inc f.nep f.c f.ix f.e f.b8 f.x1 f.r₁ f.r₂ f.r₃ f.ei f.cd f.cA
    f.rdv f.xA f.idx f.a f.q f.x47 f.qi f.cw f.k2 f.spv

/-- The exit tail's carry: `if.then485.i`'s block, over the merge's. -/
abbrev hlastThenC {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HlastFacts G C s) : WalkCarry G :=
  { hlastMergeCF f with block := "if.then485.i" }

/-- **The last entry's path to the merge.**  The head path (the six-block
fall-through, the seam, the class-C span, the tail's three links and the scan's three),
as one segment at its own count plus the two the latch's exit and the merge cost.  The
count is a literal — `hlastPrefixSeg` composes it from counted pieces — which is what
lets the callers price the path by `omega`.

The scan's three links are `walkScanChain457_ws`'s, re-stated at their `_at` forms: that
lemma leaves the latch existential, and the latch is where the exit test's premises are
read.  The three named targets are `landRhs457OutAt`, `ScanS₉₆` and `hlastLatch`. -/
theorem hlast_toMerge {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (f : HlastFacts G C s) :
    WalkSegment (stage2Calls stage2SubCalls) G C s (hlastMergeCF f) (hlastMergeF f)
        ((((((6 + 1) + 5) + 3) + 3) + 1) + 1) ∧
      WalkInv G (hlastMergeCF f) (hlastMergeF f) := by
  -- the head path, counted: `hlastPrefixSeg`'s eighteen steps
  obtain ⟨s₀, hs₀, hsegP⟩ :=
    hlastPrefixSeg (G := G) (C := C) (s := s) hInv hblock f.h8 f.hlt91 f.hlt123 f.hlt125
      f.hne125 f.hinc f.hnep f.hge f.hpre5 f.hav5 f.hidx5 f.htok5 f.hgap5 f.hugt
      f.hpre6 f.hin6 f.hv6 f.hend6 f.h8end f.hbit6 f.h8c f.hc110 f.hc116 f.hceq116
      f.r₁ f.r₂ f.r₃ f.ev f.hTail f.hpreS f.hincS f.hopS
      f.h3S f.hpos f.hreadS f.hbsS f.hloc105 f.h47 f.hbit47 f.hws47 f.hloc96 f.hlatch
  have hsegL : WalkSegment (stage2Calls stage2SubCalls) G C s (ScanLatchC C f.ev)
      (hlastLatchF f) ((((6 + 1) + 5) + 3) + 3) := by
    rw [hs₀] at hsegP
    exact hsegP
  -- the latch's exit, one step
  obtain ⟨s₅, hseg₅, -, hs₅, -⟩ :=
    scanExitSeg (calls := stage2Calls stage2SubCalls) (G := G) (C := ScanLatchC C f.ev)
      (s := hlastLatchF f) hsegL.inv' rfl f.hq f.hcwL f.hinner f.hqc f.hcw64 f.hexit
  rw [hs₅] at hseg₅
  -- the merge, one step
  obtain ⟨s₆, hl₆, hs₆⟩ :=
    walkIfEnd473_at (sub := stage2SubCalls) (G := G) (C := ScanCMerge (ScanLatchC C f.ev))
      (s := hlastScanOutF f) hseg₅.inv' rfl f.htokL
  rw [hs₆] at hl₆
  have hl₆' : WalkLink (stage2Calls stage2SubCalls) G (ScanCMerge (ScanLatchC C f.ev))
      (hlastScanOutF f) (hlastMergeCF f) (hlastMergeF f) := hl₆
  have hseg₆ : WalkSegment (stage2Calls stage2SubCalls) G (ScanCMerge (ScanLatchC C f.ev))
      (hlastScanOutF f) (hlastMergeCF f) (hlastMergeF f) 1 := WalkSegment.of_link hl₆'
  exact ⟨(hsegL.trans hseg₅).trans hseg₆, hl₆'.inv'⟩

/-! ### The two outcomes -/

/-- **The finish disjunct.**  The last entry's path reaches `cleanup478.i` at the
terminal index: the segment is `hlast_toMerge`'s, the merge's index is the `phi`'s
selection `%inc.i`, and the entry count is the state's `%nep`.  The price is arithmetic:
`hlastPrefixSeg` counts the head path at `18`, the latch's exit and the merge add `2`,
and `hlastK` makes `Δk = 1`, so `22 ≤ 32`. -/
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
  refine ⟨hlastMergeCF f, hlastMergeF f, (((((6 + 1) + 5) + 3) + 3) + 1) + 1,
    f.k2, "if.end473.i", .reg "%inc.i", f.nepv, hseg, rfl, rfl, by decide, f.hk2,
    f.hnepM, f.hterm, ?_⟩
  rw [f.hk2nep, entryPos_nep]
  have hΔ : G.nep - C.k = 1 := by rw [← f.hlastK]; omega
  simp only [Nat.zero_sub, Nat.mul_zero, Nat.add_zero, stage2EntryAllowance, hΔ]
  omega

/-- **The refusal disjunct.**  The same segment, the merge's step and the exit tail's
first two blocks: the target is `if.then` with the merge's `phi` cells in place, and the
carry's refusal offset is the invariant's (`WalkInv.eoff_le`), unchanged through the
three carries.  The price fits the entries the loop has left and the document bytes it
has not reached, which is the refusal's own accounting (`walkPotential_spend`'s
direction) — `23 ≤ 32` at `Δk = 1` and the byte term is left as the credit it is.

`hbit` is the exit tail's test at the merge's depth: `%sp.i.1 = 0` is *false*, so the
merge's false arm takes `if.then488.i` and the refusal copy rather than `if.then490.i`
and the normal exit.  It is the one field of the last entry's facts that says which of
the two outcomes this is, which is why it is an argument rather than a bundle field. -/
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
      inv' := hInvE }
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
      hbit heT h4T f.hv64
  refine ⟨FinishCThen (hlastThenC f), s₇, ((((((6 + 1) + 5) + 3) + 3) + 1) + 1) + 1 + 2,
    ((hseg.trans hsegM).trans hseg₇), rfl, hInv.eoff_le, ?_⟩
  have hΔ : G.nep - C.k = 1 := by rw [← f.hlastK]; omega
  simp only [stage2EntryAllowance, hΔ]
  omega

/-- **The last entry's two outcomes.**  The bundle is the input's, and `hbit` — the
exit tail's test at the merge's depth, `%sp.i.1 ≠ 0` — selects the refusal, which is
the branch the walk takes whenever the last token leaves the stack non-empty.
`hlast_finish` states the other alternative at the same facts and needs no polarity:
it says what the segment reaches, and the merge is reached on both arms.

The two alternatives are not rivals: `hlast_refuse`'s segment is `hlast_finish`'s
`trans` three more steps (`(hseg.trans hsegM).trans hseg₇`), so the merge state is
reached on the refusal's own run at `j + 2` fuel and `if.then` at `j + 5`.  A segment
is a run prefix, not a terminal claim, so one run carries both.

`¬ (C.k + 1 < G.nep)` is carried because the assembly's premise has it and it names the
last entry, but nothing below reads it: the fact it states — that the entry's
increments have reached the stream's count — is `hge` and `hk2nep` in the bundle, and
those are the forms the prefix and the merge consume.  A premise that is subsumed
reads as unused here rather than being dropped from the disjunction's shape. -/
theorem hlast {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (_hk : ¬ (C.k + 1 < G.nep))
    (f : HlastFacts G C s)
    (hbit : evalICmp .eq (BitVec.ofNat 32 f.spv) (BitVec.ofNat 32 0) = 0) :
    (∃ (Cd : WalkCarry G) (sd : State) (p k2 : Nat) (prev : String) (kOp : Operand)
      (nepv : BitVec 64),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p ∧ Cd.block = "cleanup478.i" ∧
      sd.pre = some prev ∧ phiIncoming prev cleanupKIncoming = some kOp ∧
      evalOperand sd kOp = some (.int 64 (BitVec.ofNat 64 k2)) ∧
      lookupName sd.env "%nep" = some (.int 64 nepv) ∧ k2 = nepv.toNat ∧
      p + 2 ≤ stage2EntryAllowance * (k2 - C.k) +
        stage2ByteAllowance * (entryPos G k2 - entryPos G C.k)) ∨
    (∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p ∧ Cd.block = "if.then" ∧
      Cd.eoff ≤ G.n ∧
      p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
        stage2ByteAllowance * (G.n - entryPos G C.k)) :=
  Or.inr (hlast_refuse G C s hInv hblock f hbit)

/-! ### The assembly's use site

The last entry's premise, supplied at the calls every dispatch in this layer is stated
at.  `ofContinueAndLast` takes the bundle as the last entry's own facts, and this is the
theorem that hands it over: `hcont` stays the revolution's premise, and the last entry's
two cases come from `hlast` with the depth's polarity.
-/

/-- **`WalkDispatchThree` from the last entry's facts.**  `ofContinueAndLast`'s case
split at `stage2Calls stage2SubCalls`, with the last entry's premise discharged by
`hlast`: `hcont` is the revolution's premise unchanged, and the bundle enters where the
input supplies it.  This is the assembly's use site while the bundle cannot be named in
`JsonStage2WalkAssembly` itself. -/
theorem walkDispatchThree_ofLastFacts {m0 : Mem} (G : WalkGeom m0)
    (hcont : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      C.k + 1 < G.nep → WalkDispatchOutcome (stage2Calls stage2SubCalls) G C s)
    (hf : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      ¬ (C.k + 1 < G.nep) → HlastFacts G C s)
    (hb : ∀ (C : WalkCarry G) (s : State) (f : HlastFacts G C s),
      evalICmp .eq (BitVec.ofNat 32 f.spv) (BitVec.ofNat 32 0) = 0) :
    WalkDispatchThree (stage2Calls stage2SubCalls) G := by
  intro C s hInv hhead
  by_cases hk : C.k + 1 < G.nep
  · exact hcont C s hInv hhead hk
  · let f := hf C s hInv hhead hk
    rcases hlast G C s hInv hhead hk f (hb C s f) with
      ⟨Cd, sd, p, k2, prev, kOp, nepv, seg, hblock, hpre, hkOp, hk2, hnepv, hterm, hprice⟩ |
      ⟨Cd, sd, p, seg, hblock, herr, hprice⟩
    · exact WalkDispatchOutcome.finish Cd sd p k2 prev kOp nepv seg hblock hpre hkOp hk2
        hnepv hterm hprice
    · exact WalkDispatchOutcome.refuse Cd sd p seg hblock herr hprice


/-! ### The bundle's producer

`HlastFacts` as a `Type` is inhabited by a structure literal; the question is what the
literal has to be given, and the answer separates the fields into three kinds.

**Fixed by the loop's own values.**  The entry's index and the stream's count are not
free witnesses: at the loop's last entry they are `C.k + 1` and `G.nep`, and the bundle
is produced at those.

**The map, per group.**  Produced · reduced to a named premise · resisting, with the
reason:

| group | status |
|---|---|
| the entry counts (`inc`, `nep`, `hge`) | **produced**: the witnesses are the loop's values, and `hge` is `ult (C.k+1) G.nep` at `C.k + 1 = G.nep`, a word compared with itself |
| the merge's five cells (`%inc.i`, `%nep`, `%sp.i.0248`, `%e`, `%4`) | **produced**, from premises at the loop head: `hlastMerge_envInc`/`…Nep`/`…Sp`/`…E`/`…Four` peel `lookupName` from the merge down to `s`, so no field is stated at a state the caller would have to compute |
| `hterm`, `hk2nep`, `hcw0`, `hinner` | **produced**: `G.nep` below `2^64`, the loop's equation, the scan's last visit, and the refill's `1 ≤ C.inner` (`walkLoopHead_inner_pos`, from `C.inner = walkInnerCap G`) |
| the tail | **reduced to a named premise**: `consumerTailSegAt` — a segment at `3` from the three call contracts |
| the scan's landing | **reduced to a named premise**: `walkScanLinks457`'s, byte read included |
| the latch's exit test (`hq`, `hcwL`, `hqc`, `hcw64`, `hexit`, `htokL`) | **reduced**: `%q.0.i246` and `%cond350.i` are cells the scan's own states write; `hexit` is the exit's local at the latch |
| the head's byte and its four class bits | **resisting: the entry stream's.**  `%8` is `entryByte G C.k`; the four bits are four switch decisions on that byte, and nothing in `WalkInv` reads the stream |
| the default arm's and the seam's cells | **resisting: the entry stream's.**  `%4`'s lane, `%idxprom.i`, the token's end and its gap are the entry's own values (`hpre5` is a closed `phi` lookup and could be produced by fixing `reg`) |
| the second byte's class (`h8c` and its three bits) | **resisting: memory.**  `if.end372.i` stores the byte at `%end.i` and `h8c` reads the store back |
| the merge's `%e` and `%4` *values* | **resisting: the staging's** — peeled to `s`, and there they are the entry's error slot and its fourth argument |

Nothing above is a field weakened to make a proof go through: the four derived witnesses
and the ten produced fields are consequences, and the two shape changes (`hTail` a
segment, the refill an equality) stay.
-/

/-- `%inc.i`'s value at the last entry, as the bundle's `inc`. -/
abbrev hlastIncV {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : BitVec 64 :=
  BitVec.ofNat 64 (C.k + 1)

/-- `%nep`'s value, as the bundle's `nep`. -/
abbrev hlastNepV {m0 : Mem} (G : WalkGeom m0) : BitVec 64 :=
  BitVec.ofNat 64 G.nep

/-- The scan's entry at the last entry's counts. -/
abbrev hlastEntryAt {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (c ix : BitVec 64) (e : BitVec 64) (b8 : BitVec 8) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ei cd : Nat) (cA rdv xA : BitVec 32) : State :=
  hlastEntry C s x (hlastIncV C) (hlastNepV G) c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA

/-- The latch at the last entry's counts. -/
abbrev hlastLatchAt {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (c ix : BitVec 64) (e : BitVec 64) (b8 : BitVec 8) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ei cd : Nat) (cA rdv xA : BitVec 32)
    (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8) : State :=
  hlastLatch C s x (hlastIncV C) (hlastNepV G) c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA
    idx a q x47

/-- The latch's exit at the last entry's counts. -/
abbrev hlastScanOutAt {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (c ix : BitVec 64) (e : BitVec 64) (b8 : BitVec 8) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ei cd : Nat) (cA rdv xA : BitVec 32)
    (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8) (qi cw : Nat) : State :=
  hlastScanOut C s x (hlastIncV C) (hlastNepV G) c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA
    idx a q x47 qi cw

/-- The merge at the last entry's counts. -/
abbrev hlastMergeAt {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (c ix : BitVec 64) (e : BitVec 64) (b8 : BitVec 8) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ei cd : Nat) (cA rdv xA : BitVec 32)
    (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8) (qi cw : Nat) : State :=
  hlastMerge C s x (hlastIncV C) (hlastNepV G) c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA
    idx a q x47 qi cw

/-- `%inc.i` at the merge is `%inc.i` at the loop head: no block on the path binds it. -/
theorem hlastMerge_envInc {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (c ix : BitVec 64) (e : BitVec 64) (b8 : BitVec 8) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ei cd : Nat) (cA rdv xA : BitVec 32)
    (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8) (qi cw : Nat) :
    lookupName
        (hlastMergeAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw).env
        "%inc.i" = lookupName s.env "%inc.i" := by
  simp only [hlastMerge, hlastScanOut, hlastLatch, hlastEntry, ScanEntry, TailStart,
    TailS₃, seamAt, seamS, seamFin, headEndS, condEnd349OutAt, headAS₁, headAS₂, headAS₃,
    headAS₄, headAS₅, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, landRhs457OutAt,
    Latch462S, scanLatchOut, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%nep` at the merge is `%nep` at the loop head: no block on the path binds it. -/
theorem hlastMerge_envNep {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (c ix : BitVec 64) (e : BitVec 64) (b8 : BitVec 8) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ei cd : Nat) (cA rdv xA : BitVec 32)
    (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8) (qi cw : Nat) :
    lookupName
        (hlastMergeAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw).env
        "%nep" = lookupName s.env "%nep" := by
  simp only [hlastMerge, hlastScanOut, hlastLatch, hlastEntry, ScanEntry, TailStart,
    TailS₃, seamAt, seamS, seamFin, headEndS, condEnd349OutAt, headAS₁, headAS₂, headAS₃,
    headAS₄, headAS₅, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, landRhs457OutAt,
    Latch462S, scanLatchOut, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%e` at the merge is `%e` at the loop head: no block on the path binds it. -/
theorem hlastMerge_envE {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (c ix : BitVec 64) (e : BitVec 64) (b8 : BitVec 8) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ei cd : Nat) (cA rdv xA : BitVec 32)
    (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8) (qi cw : Nat) :
    lookupName
        (hlastMergeAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw).env
        "%e" = lookupName s.env "%e" := by
  simp only [hlastMerge, hlastScanOut, hlastLatch, hlastEntry, ScanEntry, TailStart,
    TailS₃, seamAt, seamS, seamFin, headEndS, condEnd349OutAt, headAS₁, headAS₂, headAS₃,
    headAS₄, headAS₅, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, landRhs457OutAt,
    Latch462S, scanLatchOut, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%4` at the merge is `%4` at the loop head: no block on the path binds it. -/
theorem hlastMerge_envFour {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (c ix : BitVec 64) (e : BitVec 64) (b8 : BitVec 8) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ei cd : Nat) (cA rdv xA : BitVec 32)
    (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8) (qi cw : Nat) :
    lookupName
        (hlastMergeAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw).env
        "%4" = lookupName s.env "%4" := by
  simp only [hlastMerge, hlastScanOut, hlastLatch, hlastEntry, ScanEntry, TailStart,
    TailS₃, seamAt, seamS, seamFin, headEndS, condEnd349OutAt, headAS₁, headAS₂, headAS₃,
    headAS₄, headAS₅, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, landRhs457OutAt,
    Latch462S, scanLatchOut, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%sp.i.0248` at the merge is `%sp.i.0248` at the loop head: no block on the path binds it. -/
theorem hlastMerge_envSp {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (c ix : BitVec 64) (e : BitVec 64) (b8 : BitVec 8) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ei cd : Nat) (cA rdv xA : BitVec 32)
    (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8) (qi cw : Nat) :
    lookupName
        (hlastMergeAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw).env
        "%sp.i.0248" = lookupName s.env "%sp.i.0248" := by
  simp only [hlastMerge, hlastScanOut, hlastLatch, hlastEntry, ScanEntry, TailStart,
    TailS₃, seamAt, seamS, seamFin, headEndS, condEnd349OutAt, headAS₁, headAS₂, headAS₃,
    headAS₄, headAS₅, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, landRhs457OutAt,
    Latch462S, scanLatchOut, stateAt, cells, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- An unsigned comparison of a word with itself is zero. -/
theorem hlast_ult_self {w : Nat} (a : BitVec w) : evalICmp .ult a a = 0 := by
  simp only [evalICmp, BitVec.ult_eq_decide, lt_self_iff_false]
  rfl

/-- The entry count's word reads back as itself: it is below `2 ^ 64`. -/
theorem hlast_nep_toNat {m0 : Mem} (G : WalkGeom m0) : (hlastNepV G).toNat = G.nep := by
  have h : G.nep < 2 ^ 64 := by
    have h1 := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  simp only [hlastNepV, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- **The bundle, from the entry's evidence.**  The two counts and the merge's index
are the loop's own values; `hge`, `hterm`, `hk2nep` and `hcw0` follow from them; every
other field is the input's evidence at the state the path names.  See the section
above for which fields cannot be produced from the committed layer. -/
def hlastFacts_of_staging {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (_hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 = G.nep)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (hlt123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
    (hlt125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq x (BitVec.ofNat 8 125) = 0)
    (hinc : evalOperand (headAS₄ s x) (.reg "%inc.i") = some (.int 64 (hlastIncV C)))
    (hnep : evalOperand (headAS₄ s x) (.reg "%nep") = some (.int 64 (hlastNepV G)))
    {reg : String} {c ix : BitVec 64}
    (hpre5 : phiIncoming "sw.default.i"
      [("cond.true345.i", Operand.reg "%conv347.i"),
       ("sw.default.i", Operand.reg "%4")] = some (.reg reg))
    (hav5 : lookupName (headAS₅ s x (hlastIncV C) (hlastNepV G)).env reg = some (.int 64 c))
    (hidx5 : lookupName (headAS₅ s x (hlastIncV C) (hlastNepV G)).env "%idxprom.i" =
      some (.int 64 ix))
    (htok5 : lookupName (headAS₅ s x (hlastIncV C) (hlastNepV G)).env "%t352.i" =
      some (.ptr C.stage.tok))
    (hgap5 : lookupName (headAS₅ s x (hlastIncV C) (hlastNepV G)).env "%gap.i" =
      some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt c ix = 0)
    {p : String} {op : Operand} {e : BitVec 64} {b8 : BitVec 8}
    (hpre6 : (headEndS C s x (hlastIncV C) (hlastNepV G) c ix).pre = some p)
    (hin6 : phiIncoming p
      [("cond.end349.i", (Operand.reg "%idxprom.i")),
       ("while.body370.i", (Operand.reg "%cond350.i")),
       ("LeafBlock43", (Operand.reg "%ee.0.i238")),
       ("LeafBlock46", (Operand.reg "%ee.0.i238")),
       ("LeafBlock48", (Operand.reg "%ee.0.i238")),
       ("LeafBlock33", (Operand.reg "%cond350.i")),
       ("LeafBlock35", (Operand.reg "%cond350.i")),
       ("LeafBlock37", (Operand.reg "%cond350.i"))] = some op)
    (hv6 : evalOperand (headEndS C s x (hlastIncV C) (hlastNepV G) c ix) op = some (.int 64 e))
    (hend6 : lookupName (headEndS C s x (hlastIncV C) (hlastNepV G) c ix).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (headEndS C s x (hlastIncV C) (hlastNepV G) c ix).env "%8" =
      some (.int 8 b8))
    (hbit6 : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    {x1 : BitVec 8}
    (h8c : evalOperand (seamAt C s x (hlastIncV C) (hlastNepV G) c ix e b8) (.reg "%8") =
      some (.int 8 x1))
    (hc110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (hc116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0)
    (hceq116 : evalICmp .eq x1 (BitVec.ofNat 8 116) = 0)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) {cA rdv : BitVec 32} {xA : BitVec 32}
    (ei cd : Nat)
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (TailStartC C)
      (TailStart C s x (hlastIncV C) (hlastNepV G) c ix e b8 x1)
      (TailCarryScan (TailStartC C) ev)
      (hlastEntryAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA) 3)
    {idx : BitVec 64} {a q : Nat} {bs : List UInt8} {src : String} {sel : Operand}
    (hpreS : (hlastEntryAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA).pre = some src)
    (hincS : phiIncoming src
      [("while.body462.i", (Operand.reg "%inc463.i")),
       ("if.then447.i", (Operand.reg "%ee.1.i"))] = some sel)
    (hopS : evalOperand (stateAt
      (hlastEntryAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA).env
      (hlastEntryAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA)) sel = some (.int 64 idx))
    (h3S : lookupName (hlastEntryAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA).env "%3" =
      some (.ptr a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hreadS : readBytes (hlastEntryAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA).mem
      (a + (idx.signExtend 64).toNat) 1 = some bs)
    (hbsS : bytesToNat bs = q)
    (hloc105 : WalkLocal (ScanC₁₀₅ (TailCarryScan (TailStartC C) ev))
      (landRhs457OutAt (hlastEntryAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA) idx a q))
    {x47 : BitVec 8}
    (h47 : evalOperand
      (landRhs457OutAt (hlastEntryAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA) idx a q)
      (.reg "%47") = some (.int 8 x47))
    (hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1)
    (hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1)
    (hloc96 : WalkLocal (ScanC₉₆ (TailCarryScan (TailStartC C) ev))
      (ScanS₉₆ (hlastEntryAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA) idx a q x47))
    (hlatch : WalkLocal { TailCarryScan (TailStartC C) ev with block := "while.body462.i" }
      (hlastLatchAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47))
    {qi cw tok : Nat}
    (hq : lookupName
      (hlastLatchAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47).env
      "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 qi)))
    (hcwL : lookupName
      (hlastLatchAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47).env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cw)))
    (hqc : qi + 1 = cw)
    (hcw64 : cw < 2 ^ 64)
    (hrefill : C.inner = walkInnerCap G)
    (hexit : ∀ (e : State), e.pre = some "while.body462.i" →
      lookupName e.env "%inc463.i" = some (.int 64 (BitVec.ofNat 64 (qi + 1))) →
      lookupName e.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cw)) →
      WalkLocal (G := G) (ScanCMerge (ScanLatchC C ev)) e)
    (htokL : lookupName
      (hlastScanOutAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw).env
      "%t352.i" = some (.ptr tok))
    {spv v : Nat}
    (hincL : lookupName s.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 1))))
    (hnepL : lookupName s.env "%nep" = some (.int 64 (hlastNepV G)))
    (hspvL : lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 spv)))
    (heL : lookupName s.env "%e" = some (.ptr C.stage.e))
    (h4L : lookupName s.env "%4" = some (.int 64 (BitVec.ofNat 64 v)))
    (hv64 : v < 2 ^ 64) :
    HlastFacts G C s :=
  { x := x
    h8 := h8
    hlt91 := hlt91
    hlt123 := hlt123
    hlt125 := hlt125
    hne125 := hne125
    inc := hlastIncV C
    nep := hlastNepV G
    hinc := hinc
    hnep := hnep
    hge := by
      show evalICmp .ult (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) = 0
      rw [hk]
      exact hlast_ult_self _
    reg := reg
    c := c
    ix := ix
    hpre5 := hpre5
    hav5 := hav5
    hidx5 := hidx5
    htok5 := htok5
    hgap5 := hgap5
    hugt := hugt
    p := p
    op := op
    e := e
    b8 := b8
    hpre6 := hpre6
    hin6 := hin6
    hv6 := hv6
    hend6 := hend6
    h8end := h8end
    hbit6 := hbit6
    x1 := x1
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
    ei := ei
    cd := cd
    hTail := hTail
    idx := idx
    a := a
    q := q
    bs := bs
    src := src
    sel := sel
    hpreS := hpreS
    hincS := hincS
    hopS := hopS
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
    qi := qi
    cw := cw
    tok := tok
    hq := hq
    hcwL := hcwL
    hqc := hqc
    hcw0 := by omega
    hcw64 := hcw64
    hinner := by
      have h1 : cw - qi = 1 := by omega
      have h2 : 1 ≤ C.inner := walkLoopHead_inner_pos hblock hrefill
      omega
    hexit := hexit
    htokL := htokL
    k2 := C.k + 1
    nepv := hlastNepV G
    spv := spv
    v := v
    hk2 := by
      show evalOperand (hlastMergeAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw) (.reg "%inc.i") =
        some (.int 64 (BitVec.ofNat 64 (C.k + 1)))
      simp only [evalOperand]
      rw [hlastMerge_envInc C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw]
      exact hincL
    hnepM := by
      show lookupName (hlastMergeAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw).env "%nep" = some (.int 64 (hlastNepV G))
      rw [hlastMerge_envNep C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw]
      exact hnepL
    hterm := by
      show C.k + 1 = (hlastNepV G).toNat
      rw [hk]
      exact (hlast_nep_toNat G).symm
    hk2nep := hk
    hspvM := by
      show evalOperand (hlastMergeAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw) (.reg "%sp.i.0248") =
        some (.int 32 (BitVec.ofNat 32 spv))
      simp only [evalOperand]
      rw [hlastMerge_envSp C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw]
      exact hspvL
    heM := by
      show lookupName (hlastMergeAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw).env "%e" = some (.ptr C.stage.e)
      rw [hlastMerge_envE C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw]
      exact heL
    h4M := by
      show lookupName (hlastMergeAt C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw).env "%4" = some (.int 64 (BitVec.ofNat 64 v))
      rw [hlastMerge_envFour C s x c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA idx a q x47 qi cw]
      exact h4L
    hv64 := hv64
    hlastK := hk }

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hlast_toMerge
#print axioms LeanLLVM.Refinement.WalkScope.hlast_finish
#print axioms LeanLLVM.Refinement.WalkScope.hlast_refuse
#print axioms LeanLLVM.Refinement.WalkScope.hlast
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatchThree_ofLastFacts
#print axioms LeanLLVM.Refinement.WalkScope.hlastFacts_of_staging

end WalkScope
end LeanLLVM.Refinement
