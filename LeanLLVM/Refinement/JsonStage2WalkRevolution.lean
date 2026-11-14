/-
# The continuing entry's path to the merge, priced

## The vacuity this module's bundle used to have

The prefix this file composed was `hlastPrefixSeg`'s, and that lemma is the **last**
entry's: it takes `sw.default.i`'s count test on its *failing* arm, so the walk leaves for
`cond.end349.i` directly.  A continuing entry passes the test, and its path leaves through
`cond.true345.i`, which reads the *next* entry's position lane.  The bundle nevertheless
carried the test's value as

  `hge : evalICmp .ult inc nep = 0`

and the arithmetic that makes that contradiction visible is three substitutions.  At a
head state `%inc.i = C.k + 1` (the header binds `%inc.i` as `%k.0.i249 + 1`) and
`%nep = G.nep` (`%nep` is a call argument, and no block of the walk rebinds it), so
`evalICmp .ult inc nep = 0` **is** `¬ (C.k + 1 < G.nep)` — the last entry's equation —
while this module's consumer carries `hk : C.k + 1 < G.nep`.  The two cannot both hold, so
no state inhabited the bundle: `walkRevolution_seg` was true for the wrong reason and
`WalkDispatch`'s continuing case was never produced.  The contradiction was invisible
because the bundle is stated before its consumer exists and each field is true of *its own*
path — the failing arm's value is a true fact about the last entry — so nothing inside the
bundle's module reads one group against another.  The repair is three things, and this file
is all three: the test's field is named `hnext` and carries `= 1`; the prefix is
`hcontPrefixSeg` (`JsonStage2WalkRevolutionPrefix`), the counted path through
`cond.true345.i`; and the groups read from the path are re-stated at that prefix's states.

**A field name that says "greater or equal" for a test whose value is *false* is what hid
this.**  `hnext` names the proposition it carries: a continuing entry has a next one, so
the test succeeds.

## The composition

| piece | lemma | span | count |
|---|---|---|---|
| head: four pivots, `sw.default.i`, `cond.true345.i`, `cond.end349.i` | `hcontPrefixSeg` | head → `cond.end349.i` | `7` |
| the whitespace check: `land.lhs.true357.i`, `NodeBlock41`, `NodeBlock39`, `LeafBlock35` | `hcontPrefixSeg` | → the token's end | `4` |
| seam | `WalkLink.if_end372_i_at` | `if.end372.i` → the class-C span | `1` |
| visits of the extra-token scan | `contScanRounds` | the latch → its last visit | `≤ 8·(v - 1 - ei)` |
| exit | `scanExitSeg` | the latch → `if.end473.i` | `1` |
| merge | `walkIfEnd473_at` | `if.end473.i` → `cleanup478.i` | `1` |

`23 + 1 + 1` is the prefix plus the exit and the merge, and the visits are a counted
traversal rather than part of the prefix.  The visits are composed at
`walkScanRounds457`'s **round**, not at that lemma: its conclusion keeps only the counter
at the target (`%q.0.i246 = c - 1`), and the exit test reads the bound (`%cond350.i = c`)
as well, so the traversal's own aggregation cannot reach the exit.  `contScanRounds` is
that aggregation with both registers kept; its measure, its price and its induction are
`walkScanRounds457`'s, and it consumes the same three hypotheses (`hround`, `hguard`,
`hbyte`), unweakened.

## The price

`23 + n + 2` steps, at `n ≤ 8·(v - 1 - ei)`, against `32·1 + 8·ΔA` and `k2 = C.k + 1`:
the visit count is the entry's span, `v - 1 - ei ≤ entryPos (C.k + 1) - entryPos C.k`, so
`27 + n ≤ 27 + 8·ΔA ≤ 32 + 8·ΔA`.  The fixed part grew from the last entry's `22` to `27`
— the eight extra links are the count test's succeeding arm and the whitespace check — and
it still fits the entry allowance, so the bound is not widened.  Two premises state the
span, because the scan's bound and its first index are the *document's* numbers and neither
is invariant-carried:

* `hspan : v ≤ entryPos G (C.k + 1)` — the scan stops at or before the next entry;
* `hstart : entryPos G C.k ≤ ei` — it starts at or after this one.

From those two `v < 2 ^ 64` and `v ≤ 2 ^ 63` are arithmetic (`entryPos_lt`, `maxDoc`), so
they are not premises.

## The arm this bundle describes, and the arm it cannot

The `hnext`/`hk` contradiction is gone, and there is a second boundary behind it, found the
same way — by a field against the path's own arithmetic.  `if.end372.i`'s `%ee.1.i` `phi`
selects `%cond350.i` on the three leaf edges, and on this path `%cond350.i` is the lane's
word, so the token's end is `v.toNat`; `if.then447.i`'s target then tests
`ult ei %cond350.i` and, with `ei` the scan's index, the cell is the same word:

* `contEntry_ee` — `%ee.1.i` at the scan's entry is `ofNat 64 v.toNat`;
* `contEntry_scan_empty` — therefore **`¬ (ei < v.toNat)`**.

So this bundle's own `heicd` (`ei < v.toNat`) is uninhabited on the arm where the byte
before the entry's end is **not** whitespace.  That is not a defect in the segment — the
walk really does take that path — it is the bundle naming the wrong *continuation*: with an
empty extra-token span the walk leaves the copy call for `if.end473.i` and never enters the
scan, so that arm's segment is shorter and ends at the merge.  The bundle therefore
describes **the whitespace arm**: the byte before the entry's end is `9`, `10`, `13` or
`32`, the whitespace skip runs, the token ends at the first whitespace byte `k < v.toNat`,
and the extra-token scan runs `[k, v.toNat)`.  The other three classes' arms need their own
bundle (no scan group) or a disjunction over the two; which of those is the planner's call,
and the price favours either — the scan-free arm is the cheaper one.

## `%cond350.i` is one number, not two

The bound the scan reads is the entry's end, and that is the word `cond.true345.i`
loaded: `%cond350.i` is bound once, at `cond.end349.i`, and no block from there to the
latch rebinds it.  So the bundle carries the lane's word `v` and no separate bound
witness — `contLatch_cond` (`JsonStage2WalkRevolutionPrefix`) is the peel that says the
latch's cell is `ofNat 64 v.toNat`.  A second witness would be one fact written twice.

**`hugt` is arm-specific, and both arms' values are right.**  This bundle's `hugt` is
`ugt (ofNat 64 v.toNat) ix = 1`: the entry is non-empty, `%cond350.i` is above `%idxprom.i`,
so `cond.end349.i` takes `land.lhs.true357.i` and the walk reads the byte before the end.
`HlastFacts.hugt` is `= 0`, and that is the last entry's arm: its `%cond350.i` is `%4`, and
the last entry's position is the stream's end.  Two bundles can share a field name and
correctly carry opposite values; a docstring that gives one value without its arm reads as
a contradiction in the other.

## What is supplied, and what is derived

Three groups are premises because the model's own layer does not produce them:

* the document's bytes and classes — the head's byte and its four pivot bits, the byte
  before the entry's end (`b35`) and its three class bits, the seam's byte and its two
  literal tests, and the second byte's class.  Which byte the document holds is not the
  walk's: `WalkGeom` fixes the addresses and the extents, not the values;
* the scan's traversal hypotheses (`hround`, `hguard`, `hbyte`) — `walkScanRounds457`'s
  own, unweakened: the round at a byte, the latch's guard, and the input's totality at
  every index the scan visits (the model branches on a byte it does not store);
* **the token record's register at the scan's exit** (`htok`).  `if.end473.i`'s lifetime
  marker reads `%t352.i` and no block on the scan's path rebinds it, but
  `walkScanRounds457` returns its final state *existentially*, so no named term is
  available to state the cell at, and the layer has no lemma that the extra-token scan
  preserves a register.  It is stated over the states the traversal's counters pin, which
  is the closest a length-position predicate can come to the cell.  **The lemma that would
  close it is *the extra-token scan preserves a register it does not bind***; that
  statement needs the visit's target state, which the traversal's conclusion does not
  expose — the same shape as `happ₂`'s supplied record, one level out.

Everything else is derived: the `phi`'s selection at `cond.end349.i` is a closed
computation (`contPhi6`), so no witness for it is carried; `%cond350.i`'s value at the
latch is `cond.end349.i`'s own cell; the exit's local fact holds because `if.end473.i` is
not one of `WalkLocal`'s scan blocks; and the inner budget at the last visit is the
invariant's local clause read at the counts the traversal reports (`ScanCount.same`).

## Two of the merge's cells are candidate invariant clauses

`WalkMergeCells` (`JsonStage2WalkPremisesOfStaging`) states `%inc.i = ofNat 64 (C.k + 1)`
and `%nep = ofNat 64 G.nep` at `cleanup478.i` as supplied facts, and both follow from
clauses `WalkInv` does not have: `%inc.i` is bound once, in the header, as
`%k.0.i249 + 1`, so the clause holds wherever `blockIndex` holds, and `%nep` is a parameter
no block rebinds.  Adding them is a vocabulary change — a scoping pass measured 39
`WalkInv` construction sites in 10 modules, `whileBody_step` (the only block that rebinds
`%inc.i`) and two new disequalities in `WalkPtrs.bind`/`WalkRegs.bind` — and it retires two
of that premise's three conjuncts and not the premise: the third, `Cd.k = C.k`, relates two
carries, while `WalkInv G C s` is indexed by one state and one carry.  This note is the
record that half of the merge's supply is a future clause, and which half is the wall.
-/

import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessHlast
import LeanLLVM.Refinement.JsonStage2WalkInduce
import LeanLLVM.Refinement.JsonStage2WalkRevolutionPrefix

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The latch's and the exit's cells, where the scan's own lemmas do not reach

`latch462S_counter` and `latch462S_cond` (`JsonStage2WalkInduce`) read a latch built over
a *returning* visit's `scanLatchOut`; the latch this module consumes is the one the
landing's first edge builds (`hlastPrefixSeg`'s target), over the scan's entry state.  The
cells are the same three lattice pieces in the same order, so the peels are the same ones
with one layer fewer. -/

/-- The counter at a latch state: `landRhs457OutAt` binds `%q.0.i246` to the selected
index, and the two pivot cells above it bind other names. -/
theorem latch_counter (s : State) (idx : BitVec 64) (a q : Nat) (x : BitVec 8) :
    lookupName (Latch462S s idx a q x).env "%q.0.i246" = some (.int 64 idx) := by
  simp only [landRhs457OutAt, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- The bound at a latch state is its entry state's: the lattice's six cells rebind
`%47`, `%arrayidx458.i`, `%q.0.i246`, `%Pivot106`, `%.off97` and `%SwitchLeaf98`, and
none of them is `%cond350.i`. -/
theorem latch_cond (s : State) (idx : BitVec 64) (a q : Nat) (x : BitVec 8) {c : Nat}
    (hc : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c))) :
    lookupName (Latch462S s idx a q x).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 c)) := by
  simp only [landRhs457OutAt, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact hc

/-- The token record's register at the exit test's target: the test binds `%inc463.i` and
`%exitcond298.not`, and neither is `%t352.i`. -/
theorem scanExit_tok (s : State) (i c : Nat) {tok : Nat}
    (h : lookupName s.env "%t352.i" = some (.ptr tok)) :
    lookupName (scanLatchOut s "%inc463.i" "%exitcond298.not" i c "if.end473.i").env
      "%t352.i" = some (.ptr tok) := by
  simp only [stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-! ### The continuing entry's facts, bundled

The bundle is `WalkContinueFacts`' payload (`JsonStage2WalkPremisesOfStaging`): one
argument per head state with an entry left.  Its groups are `hcontPrefixSeg`'s argument
list, in the same order, so the producer's whole job is to supply each group at the path's
states.

Three witnesses are *consequences* rather than free data, and the bundle writes the
consequence instead of a witness plus an equation:

* the landing's index — the scan's entry `phi` selects `%ee.1.i`, so the index is
  `ofNat 64 ei`, and `latch_counter` reads the latch's cell at that value;
* the scan's bound — `%cond350.i` is `cond.end349.i`'s own cell and no block from there to
  the latch rebinds it, so the bundle carries the lane's word `v` and writes `v.toNat`
  wherever the bound appears; `contLatch_cond` is the peel that says the latch's cell is
  `ofNat 64 v.toNat`;
* the `phi`'s selection at `cond.end349.i` — the predecessor is `cond.true345.i`, so the
  selection is `%conv347.i` by a closed `phi` computation (`contPhi6`), and the cell it
  selects is the link's own (`cte345OutAt_conv`).
-/
structure HcontFacts {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Type where
  /-- The head's byte. -/
  x : BitVec 8
  h8 : evalOperand s (.reg "%8") = some (.int 8 x)
  hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0
  hlt123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0
  hlt125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0
  hne125 : evalICmp .eq x (BitVec.ofNat 8 125) = 0
  /-- The entry's index and the stream's count, and the count test's value.  `hnext` is
  `1` — a continuing entry has one after it — and it is the field that used to be `hge`
  with `= 0`: see this module's header for the arithmetic that made that uninhabited. -/
  inc : BitVec 64
  nep : BitVec 64
  hinc : evalOperand (headAS₄ s x) (.reg "%inc.i") = some (.int 64 inc)
  hnep : evalOperand (headAS₄ s x) (.reg "%nep") = some (.int 64 nep)
  hnext : evalICmp .ult inc nep = 1
  /-- **The next entry's position lane**: the table's pointer, the load's word, and the
  read.  `cond.true345.i` is three instructions — `gep`, `load i32`, `zext` — and this is
  what its step consumes. -/
  ep : Nat
  v : BitVec 32
  h5 : lookupName (contAS₅ s x inc nep).env "%5" = some (.ptr ep)
  hi63 : inc.toNat < 2 ^ 63
  hread : readBytes (contAS₅ s x inc nep).mem (ep + inc.toNat * 4) 4 =
    some (natToBytes v.toNat 4)
  /-- The default arm's remaining cells, at the state `cond.true345.i` leaves. -/
  ix : BitVec 64
  hidx5 : lookupName (contAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix)
  htok5 : lookupName (contAS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok)
  hgap5 : lookupName (contAS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20))
  /-- **The entry is not empty.**  `%cond350.i` is the next entry's position, above this
  entry's own index, so `cond.end349.i` takes `land.lhs.true357.i`.

  **Arm-specific:** the last entry's bundle carries the opposite value, because its
  `%cond350.i` is `%4` and the last entry ends the stream.  Two bundles can share a field
  name and correctly carry opposite values. -/
  hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1
  /-- **The byte before the entry's end and its class.**  `land.lhs.true357.i` reads the
  document at `%cond350.i - 1`; the three pivots test it against `13`, `32` and `13`
  again, and this bundle takes the class the price's longest path names
  (`NodeBlock41 → NodeBlock39 → LeafBlock35`, no whitespace run). -/
  b35 : UInt8
  hread35 : readBytes (contEndS C s x inc nep ep v ix).mem ((G.b - 1) + v.toNat) 1 =
    some [b35]
  hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0
  hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1
  hbne13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 0
  /-- The seam's cells: the stored end, the byte and its two literal tests.  The stored
  end is `%cond350.i` — the entry's end — because the whitespace check is what sent the
  walk to `if.end372.i`. -/
  b8 : BitVec 8
  hend : lookupName (contP35S C s x inc nep ep v ix b35).env "%end.i" =
    some (.ptr (C.stage.tok + 8))
  h8end : lookupName (contP35S C s x inc nep ep v ix b35).env "%8" = some (.int 8 b8)
  hbit : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
    evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0
  /-- The entry's first byte's class, read at the seam's name. -/
  x1 : BitVec 8
  h8c : evalOperand (contSeamS C s x inc nep ep v ix b35 b8) (.reg "%8") =
    some (.int 8 x1)
  hc110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0
  hc116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0
  hceq116 : evalICmp .eq x1 (BitVec.ofNat 8 116) = 0
  /-- The tail's own: its three call outcomes, the event it emits, the seed's words and
  its segment at `ScanEntry`'s state — `consumerTailSegAt` at count `3`. -/
  r₁ : CallOutcome
  r₂ : CallOutcome
  r₃ : CallOutcome
  ev : EventRecord
  cA : BitVec 32
  rdv : BitVec 32
  xA : BitVec 32
  /-- The scan's first index, and the entry's span at it: `if.then447.i`'s target tests
  `ult ei %cond350.i`, so `ei < v.toNat` is what puts the walk on the scan rather than
  straight on `if.end473.i`.

  **This bundle describes the entries whose last byte is whitespace, and only those.**
  The seam's `%ee.1.i` `phi` selects `%cond350.i` when the whitespace check sent the walk
  there, so on this path the token's end *is* `v.toNat`, the scan's index is that same
  word (`contEntry_ee`), and the guard is `v.toNat < v.toNat`:
  `contEntry_scan_empty` (`JsonStage2WalkRevolutionPrefix`) proves this bundle's own
  `heicd` false on the arm where the byte before the entry's end is *not* whitespace.
  That arm's walk skips the scan — `if.then447.i`'s target takes `if.end473.i` — so its
  segment is a sibling bundle's, not this one's. -/
  ei : Nat
  hTail : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
    (contTailStart C s x inc nep ep v ix b35 b8 x1)
    (TailCarryScan (ContTailStartC C) ev)
    (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA) 3
  heicd : ei < v.toNat
  /-- The scan's landing: the byte's address and the byte. -/
  a : Nat
  q : Nat
  bs : List UInt8
  src : String
  sel : Operand
  hpreS : (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA).pre = some src
  hincS : phiIncoming src
    [("while.body462.i", (Operand.reg "%inc463.i")),
     ("if.then447.i", (Operand.reg "%ee.1.i"))] = some sel
  hopS : evalOperand (stateAt
    (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA).env
    (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA)) sel =
    some (.int 64 (BitVec.ofNat 64 ei))
  h3S : lookupName (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA).env
    "%3" = some (.ptr a)
  hpos : ((BitVec.ofNat 64 ei).signExtend 64).toNat < 2 ^ 63
  hreadS : readBytes
    (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA).mem
    (a + ((BitVec.ofNat 64 ei).signExtend 64).toNat) 1 = some bs
  hbsS : bytesToNat bs = q
  hloc105 : WalkLocal (ScanC₁₀₅ (TailCarryScan (ContTailStartC C) ev))
    (landRhs457OutAt (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA)
      (BitVec.ofNat 64 ei) a q)
  x47 : BitVec 8
  h47 : evalOperand
    (landRhs457OutAt (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA)
      (BitVec.ofNat 64 ei) a q)
    (.reg "%47") = some (.int 8 x47)
  hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1
  hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
  hloc96 : WalkLocal (ScanC₉₆ (TailCarryScan (ContTailStartC C) ev))
    (ScanS₉₆ (contEntry C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA)
      (BitVec.ofNat 64 ei) a q x47)
  hlatch : WalkLocal { TailCarryScan (ContTailStartC C) ev with block := "while.body462.i" }
    (contLatch C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ ei cA rdv xA
      (BitVec.ofNat 64 ei) a q x47)
  /-- **The scan runs inside the entry's span.**  Its bound is at or before the next
  entry's position, and its first index at or after this one's — the two facts that make
  the visits no more than the span, and the price's byte term. -/
  hspan : v.toNat ≤ entryPos G (C.k + 1)
  hstart : entryPos G C.k ≤ ei
  /-- **The traversal's round**: `walkScanRounds457`'s `hround`, unweakened — a visit at
  the byte the landing loads, at the counter's own index and the lane's bound. -/
  hround : ∀ (C' : WalkCarry G) (s' : State) (p a : Nat) (bs : List UInt8) (q : Nat)
    (x : BitVec 8), WalkInv G C' s' → C'.block = "while.body462.i" →
    lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
    lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) →
    p + 1 < v.toNat → p + 1 < 2 ^ 63 →
    lookupName (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i").env
      "%3" = some (.ptr a) →
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
      lookupName s''.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))
  /-- **The latch's guard**: `walkScanRounds457`'s `hguard`, unweakened. -/
  hguard : ∀ (C' : WalkCarry G) (s' : State), WalkInv G C' s' →
    C'.block = "while.body462.i" → ScanGuard s' "%q.0.i246" "%cond350.i" C'.inner
  /-- **The input's totality at every index the scan visits**: `walkScanRounds457`'s
  `hbyte`, unweakened — the model branches on a byte it does not store. -/
  hbyte : ∀ (C' : WalkCarry G) (s' : State) (p : Nat), WalkInv G C' s' →
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
        (Latch462S (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x)
  /-- **The token record's register at the scan's exit.**  Stated over the states the
  traversal's counters pin, because `walkScanRounds457` returns its final state
  existentially; every block on the path binds its own cells and none rebinds `%t352.i`,
  so the fact is true of the model and the shape is the traversal's.

  **Supplied, not derived, and the reason is structural:** a traversal whose final state is
  existential has no named term to state a register at, and the layer has no preservation
  lemma for registers — the same shape as `happ₂` in `HlastFacts`, one level out.  The lemma
  that would close it is *the extra-token scan preserves a register it does not bind*: a
  `∀` over the scan's carries and states that a name outside the latch's and the landing's
  cell lists keeps its cell across a visit.  That statement needs the visit's target state,
  which `walkScanRounds457`'s conclusion does not expose, which is why the register enters
  here as the bundle's premise rather than as a theorem beside `scanExit_tok`. -/
  htok : ∀ (C' : WalkCarry G) (s' : State), WalkInv G C' s' →
    C'.block = "while.body462.i" → ∃ tok : Nat, lookupName s'.env "%t352.i" = some (.ptr tok)

/-- The scan's entry, at the bundle's own terms.  Named for the same reason
`hlastEntryF` is: the bundle's fields are the `def`s' arguments in order, so a lemma's
statement at `contEntryF f` is the one its field types spell out. -/
abbrev contEntryF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontFacts G C s) : State :=
  contEntry C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.b8 f.x1 f.r₁ f.r₂ f.r₃ f.ei
    f.cA f.rdv f.xA

/-- The scan's latch, at the bundle's own terms. -/
abbrev contLatchF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontFacts G C s) : State :=
  contLatch C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.b8 f.x1 f.r₁ f.r₂ f.r₃ f.ei
    f.cA f.rdv f.xA (BitVec.ofNat 64 f.ei) f.a f.q f.x47

/-- **The scan's visits, counted with the registers kept.**  `walkScanRounds457` counts
the visits but keeps only the counter at its target; the exit test reads the bound too, so
the recursion here is at the round's own granularity (`hround`, the traversal's own
hypothesis) and its conclusion carries both registers.  The price bound is the traversal's
own: one byte allowance per visit, `cd - 1 - ei` of them.

**This is the two-register twin of `walkScanRounds457`, not a simplification of it, and it
must not be folded back into that lemma.**  The committed traversal concludes
`%q.0.i246 = c - 1` and nothing about `%cond350.i`, while the latch's exit test branches on
the bound (`i + 1 = c`) — so the exit is unreachable from its conclusion by construction,
whatever the induction does inside.  The extra register is not a strengthening for its own
sake: it is what the exit consumes, and the price bound is unchanged. -/
theorem contScanRounds {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (f : HcontFacts G C s) {C' : WalkCarry G} {s' : State} {i : Nat}
    (hInv : WalkInv G C' s') (hblock : C'.block = "while.body462.i")
    (hi : lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)))
    (hb : lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat)))
    (hc63 : f.v.toNat ≤ 2 ^ 63) (hic : i < f.v.toNat) :
    ∃ (C'' : WalkCarry G) (s'' : State) (n : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C' s' C'' s'' n ∧ WalkInv G C'' s'' ∧
      C''.block = "while.body462.i" ∧
      lookupName s''.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (f.v.toNat - 1))) ∧
      lookupName s''.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat)) ∧
      n ≤ stage2ByteAllowance * (f.v.toNat - 1 - i) := by
  have go : ∀ r, ∀ (i : Nat) (K : WalkCarry G) (t : State), f.v.toNat - 1 - i = r →
      WalkInv G K t → K.block = "while.body462.i" →
      ScanGuard t "%q.0.i246" "%cond350.i" K.inner →
      lookupName t.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)) →
      lookupName t.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat)) →
      i < f.v.toNat →
      ∃ (K' : WalkCarry G) (t' : State) (n : Nat),
        WalkSegment (stage2Calls stage2SubCalls) G K t K' t' n ∧ WalkInv G K' t' ∧
        K'.block = "while.body462.i" ∧
        lookupName t'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (f.v.toNat - 1))) ∧
        lookupName t'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat)) ∧
        n ≤ stage2ByteAllowance * r := by
    intro r
    induction r with
    | zero =>
        intro i K t _ hInv hblock _ hi hb hic
        have hie : i = f.v.toNat - 1 := by omega
        exact ⟨K, t, 0, Seg.measure (Seg.nil hInv), hInv, hblock,
          by rw [← hie]; exact hi, hb, by simp⟩
    | succ r ih =>
        intro i K t hr hInv hblock hg hi hb hic
        have hlt : i + 1 < f.v.toNat := by omega
        have hpos : i + 1 < 2 ^ 63 := by omega
        obtain ⟨a, bs, q, x, h3, hread, hbs, h47, hbit, hws, hl105, hl96, hll⟩ :=
          f.hbyte K t i hInv hblock hlt hi hb
        obtain ⟨K₁, t₁, j, hseg, hInv₁, hb₁, hj, hi₁, hc₁⟩ :=
          f.hround K t i a bs q x hInv hblock hi hb hlt hpos h3 hread hbs h47 hbit hws
            hl105 hl96 hll
        obtain ⟨K₂, t₂, m, hseg₂, hInv₂, hb₂, hi₂, hc₂, hm⟩ :=
          ih (i + 1) K₁ t₁ (by omega) hInv₁ hb₁ (f.hguard K₁ t₁ hInv₁ hb₁) hi₁ hc₁
            (by omega)
        refine ⟨K₂, t₂, j + m, hseg.trans hseg₂, hInv₂, hb₂, hi₂, hc₂, ?_⟩
        rw [Nat.mul_succ]
        omega
  exact go (f.v.toNat - 1 - i) i C' s' rfl hInv hblock (f.hguard C' s' hInv hblock) hi hb hic

/-! ### The producer -/

/-- **A continuing entry's dispatch, from the head to the merge.**  The head path at its
counted `23`, the scan's visits at `walkScanRounds457`'s bound, the latch's exit and the
merge: a segment to `cleanup478.i` priced at `23 + n + 2` against the entry's own credit
`32·1 + 8·ΔA`.

The endpoint's invariant and its predecessor are part of the conclusion because
`WalkDispatch` reads the merge's `phi` selection, and a selection is stated at the edge the
endpoint was entered by.  A consumer that only prices can ignore both; a consumer that
states `WalkDispatch` cannot re-derive them from an existential endpoint.

`ΔA` is the entry's span and `n` the scan's visits: `ci = v - 1 - ei ≤ ΔA` is
`hspan`/`hstart`, so the byte term pays the visits and the entry term pays the fixed part
— `hcontPrefixSeg`'s `23`, `scanExitSeg`'s `1` and `walkIfEnd473_at`'s `1` — with the two
steps the price's `+ 2` names (`cleanup478.i`'s `condbr` and `while.body.i`'s header) left
to it. -/
theorem walkRevolution_seg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (f : HcontFacts G C s) :
    ∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p ∧
      Cd.block = "cleanup478.i" ∧
      WalkInv G Cd sd ∧
      sd.pre = some "if.end473.i" ∧
      p + 2 ≤ stage2EntryAllowance * (C.k + 1 - C.k) +
        stage2ByteAllowance * (entryPos G (C.k + 1) - entryPos G C.k) := by
  -- the head path, counted: twenty-three steps to the scan's latch
  obtain ⟨s₀, hs₀, hsegP⟩ :=
    hcontPrefixSeg (G := G) (C := C) (s := s) hInv hblock f.h8 f.hlt91 f.hlt123 f.hlt125
      f.hne125 f.hinc f.hnep f.hnext f.h5 f.hi63 f.hread f.hidx5 f.htok5 f.hgap5 f.hugt
      f.hread35 f.hb13 f.hb32 f.hbne13 f.hend f.h8end f.hbit f.h8c f.hc110 f.hc116
      f.hceq116 f.r₁ f.r₂ f.r₃ f.ev f.hTail f.hpreS f.hincS f.hopS f.h3S f.hpos f.hreadS
      f.hbsS f.hloc105 f.h47 f.hbit47 f.hws47 f.hloc96 f.hlatch
  have hsegP' : WalkSegment (stage2Calls stage2SubCalls) G C s (ContLatchC C f.ev)
      (contLatchF f) 23 := by
    rw [hs₀] at hsegP
    exact hsegP
  -- the latch's two registers: its own construction's cells
  have hcounter : lookupName (contLatchF f).env "%q.0.i246" =
      some (.int 64 (BitVec.ofNat 64 f.ei)) :=
    latch_counter (contEntryF f) (BitVec.ofNat 64 f.ei) f.a f.q f.x47
  have hbound : lookupName (contLatchF f).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 f.v.toNat)) :=
    contLatch_cond C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.b8 f.x1 f.r₁ f.r₂ f.r₃ f.ei
      f.cA f.rdv f.xA (BitVec.ofNat 64 f.ei) f.a f.q f.x47
  -- the bound's width, from the span
  have hcdLt : f.v.toNat < G.n := lt_of_le_of_lt f.hspan (entryPos_lt G hk)
  have hmax : G.n ≤ 2 ^ 32 := by
    have := G.maxDoc
    simpa only [stage2MaxDocument] using this
  have hc64 : f.v.toNat < 2 ^ 64 := by
    have := f.v.isLt; omega
  have hc63 : f.v.toNat ≤ 2 ^ 63 := by
    have := f.v.isLt; omega
  -- the bundle's three arithmetic premises, at the terms `omega` reads
  have hspan := f.hspan
  have hstart := f.hstart
  have heicd := f.heicd
  have hcd1 : 1 ≤ f.v.toNat := by omega
  -- the visits, with the scan's counter and bound at the last one
  obtain ⟨Cm, sm, n, hsegR, hInvR, hbR, hiR, hcR, hnR⟩ :=
    contScanRounds G C s f hsegP'.inv' rfl hcounter hbound hc63 f.heicd
  -- the exit, one step: the inner budget is the invariant's local clause at the counts
  have hlocal : ScanCount sm "%q.0.i246" "%cond350.i" Cm.inner := by
    have h := hInvR.blockLocal
    rwa [WalkLocal.extraToken hbR] at h
  have hinner : f.v.toNat - (f.v.toNat - 1) ≤ Cm.inner :=
    ScanCount.same hlocal hiR hcR hc64 (by omega)
  have hie : (f.v.toNat - 1) + 1 = f.v.toNat := by omega
  obtain ⟨s₁, hseg₁, hpc₁, hs₁, hInv₁⟩ :=
    scanExitSeg (calls := stage2Calls stage2SubCalls) (G := G) (C := Cm) (s := sm)
      hInvR hbR hiR hcR hinner hie hc64 (by intro e _ _ _; simp [WalkLocal])
  -- the merge, one step, from the token record's register
  obtain ⟨tok, htok⟩ := f.htok Cm sm hInvR hbR
  have htok₁ : lookupName s₁.env "%t352.i" = some (.ptr tok) := by
    rw [hs₁]
    exact scanExit_tok sm (f.v.toNat - 1) f.v.toNat htok
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    walkIfEnd473_at (sub := stage2SubCalls) (G := G) (C := ScanCMerge Cm) (s := s₁)
      hInv₁ rfl htok₁
  refine ⟨{ ScanCMerge Cm with block := "cleanup478.i" }, s₂, ((23 + n) + 1) + 1,
    ?_, rfl, hl₂.inv', ?_, ?_⟩
  · exact ((hsegP'.trans hsegR).trans hseg₁).trans (WalkSegment.of_link hl₂)
  · rw [hs₂]
    show some s₁.pc = some "if.end473.i"
    rw [hpc₁]
  · -- the price: the visits are the entry's span
    have hd : f.v.toNat - 1 - f.ei ≤ entryPos G (C.k + 1) - entryPos G C.k := by
      have h1 : f.v.toNat - 1 ≤ entryPos G (C.k + 1) - 1 := Nat.sub_le_sub_right hspan 1
      have h2 : f.v.toNat - 1 - f.ei ≤ (entryPos G (C.k + 1) - 1) - f.ei :=
        Nat.sub_le_sub_right h1 f.ei
      have h3 : (entryPos G (C.k + 1) - 1) - f.ei ≤
          (entryPos G (C.k + 1) - 1) - entryPos G C.k :=
        Nat.sub_le_sub_left hstart (entryPos G (C.k + 1) - 1)
      have h4 : (entryPos G (C.k + 1) - 1) - entryPos G C.k ≤
          entryPos G (C.k + 1) - entryPos G C.k :=
        Nat.sub_le_sub_right (Nat.sub_le (entryPos G (C.k + 1)) 1) (entryPos G C.k)
      exact le_trans h2 (le_trans h3 h4)
    have hn2 : n ≤ 8 * (entryPos G (C.k + 1) - entryPos G C.k) :=
      le_trans hnR (Nat.mul_le_mul_left 8 hd)
    have hΔ : C.k + 1 - C.k = 1 := by omega
    simp only [stage2EntryAllowance, stage2ByteAllowance, hΔ, Nat.mul_one]
    have hl : 23 + n + 1 + 1 + 2 = n + 27 := by omega
    rw [hl]
    have h8 : n + 27 ≤ 8 * (entryPos G (C.k + 1) - entryPos G C.k) + 27 :=
      Nat.add_le_add_right hn2 27
    have h27 : 8 * (entryPos G (C.k + 1) - entryPos G C.k) + 27 ≤
        32 + 8 * (entryPos G (C.k + 1) - entryPos G C.k) := by
      have hstep := Nat.add_le_add_left (by decide : (27 : Nat) ≤ 32)
        (8 * (entryPos G (C.k + 1) - entryPos G C.k))
      simpa only [Nat.add_comm] using hstep
    exact le_trans h8 h27

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.contScanRounds
#print axioms LeanLLVM.Refinement.WalkScope.walkRevolution_seg

end WalkScope
end LeanLLVM.Refinement
