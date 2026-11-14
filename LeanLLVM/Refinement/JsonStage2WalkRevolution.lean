/-
# The continuing entry's path to the merge, priced

`WalkDispatch` (`JsonStage2WalkAssembly`) asks, at a head state with an entry left after
this one, for a segment from the loop head to `cleanup478.i` whose price plus the merge's
and the header's two steps fits `32·Δk + 8·ΔA`.  The last entry's side of that is
`hlast_toMerge` (`JsonStage2WalkDispatchWitnessHlast`); this module states the continuing
side, at the class the head chain to `if.then413.i` names: the entry's own bytes are the
whitespace scan's, so its dispatch runs one visit per byte of the entry's span.

## The composition

| piece | lemma | span | count |
|---|---|---|---|
| prefix | `hlastPrefixSeg` | head → the scan's latch | `18` |
| visits | `contScanRounds` | the latch → its last visit | `≤ 8·(cd - 1 - ei)` |
| exit | `scanExitSeg` | the latch → `if.end473.i` | `1` |
| merge | `walkIfEnd473_at` | `if.end473.i` → `cleanup478.i` | `1` |

The visits are composed at `walkScanRounds457`'s **round**, not at that lemma: its
conclusion keeps only the counter at the target (`%q.0.i246 = cd - 1`), and the exit test
reads the bound (`%cond350.i = cd`) as well, so the traversal's own aggregation cannot
reach the exit.  `contScanRounds` is that aggregation with both registers kept; its
measure, its price and its induction are
`walkScanRounds457`'s, and it consumes the same three hypotheses (`hround`, `hguard`,
`hbyte`), unweakened.

`hlastPrefixSeg` is the **counted** twin of `walkHeadChainToScan`: a consumer that must
price needs a segment, not a chain, because a `WalkChain`'s step count is existential.
`consumerTailSegAt` is the tail's counted form and reaches the prefix as the bundle's
`hTail`, exactly as it does in `HlastFacts` (`hlastTail_of_calls` is its producer from the
three calls' contracts).

The visit end is `cd - 1`: `walkScanRounds457` starts at the counter `ei` the landing's
`phi` selected (`%ee.1.i`, the copy call's answer) and stops one short of the bound
`%cond350.i = cd` the token's record carries, and the latch's exit (`i + 1 = c`) is the
`1` in `scanExitSeg`.

## The price

`18 + n + 2` steps, at `n ≤ 8·(cd - 1 - ei)`, against `32·1 + 8·ΔA` and `k2 = C.k + 1`:
the visit count is the entry's span, `cd - 1 - ei ≤ entryPos (C.k + 1) - entryPos C.k`, so
`22 + n ≤ 22 + 8·ΔA ≤ 32 + 8·ΔA`.  Two premises state the span, because the scan's bound
and its first index are the *document's* numbers and neither is invariant-carried:

* `hspan : cd ≤ entryPos G (C.k + 1)` — the scan stops at or before the next entry;
* `hstart : entryPos G C.k ≤ ei` — it starts at or after this one.

From those two `cd < 2 ^ 64` and `cd ≤ 2 ^ 63` are arithmetic (`entryPos_lt`, `maxDoc`),
so they are not premises.

## What is supplied, and what is derived

Three groups are premises because the model's own layer does not produce them:

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
* the prefix group, at the same shape `HlastFacts` carries it: the head's byte and its four
  class bits, the entry counts, the default arm's cells, the seam's, the second byte's
  class, the tail's segment and the scan's landing.

Everything else is derived: the latch's counter and bound are cells of the latch state's
own construction (`latch_counter`, `latch_cond`), the exit's local fact holds because
`if.end473.i` is not one of `WalkLocal`'s scan blocks, and the inner budget at the last
visit is the invariant's local clause read at the counts the traversal reports
(`ScanCount.same`).
-/

import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessHlast
import LeanLLVM.Refinement.JsonStage2WalkInduce

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

The prefix group is `HlastFacts`' (`JsonStage2WalkDispatchWitnessHlast`), field for field
and type for type, because it is the same path to the same latch: what changes at a
continuing index is the scan's *length*, so the last-entry fields (`qi + 1 = cw`,
`hterm`, `hlastK`, the merge's cells) are replaced by `cd`'s span and the traversal's
hypotheses.

Two witnesses are fixed rather than carried, and for the same reason: they are
*consequences* of the facts around them rather than free data.

* `idx` — the landing's `phi` selects `%ee.1.i`, so the scan's index is `ei`; a field
  `idx` plus a premise `idx = ofNat 64 ei` would be one fact written twice.  The bundle
  therefore writes `BitVec.ofNat 64 ei` where `HlastFacts` writes `idx`.
* `cw`, `qi` — the scan's bound is the tail's own `cd` (`%cond350.i` is not rebound on the
  path from `if.then447.i`), and its last visit is `cd - 1`.  `HlastFacts` carried both
  because the last entry's scan visits exactly one byte; here the traversal's own
  parameter is the bound.

**Two of the cells this bundle's consumer states at the merge are candidate invariant
clauses.**  `WalkMergeCells` (`JsonStage2WalkPremisesOfStaging`) states
`%inc.i = ofNat 64 (C.k + 1)` and `%nep = ofNat 64 G.nep` at `cleanup478.i` as supplied
facts, and both follow from clauses `WalkInv` does not have: `%inc.i` is bound once, in
the header, as `%k.0.i249 + 1`, so the clause holds wherever `blockIndex` holds, and
`%nep` is a parameter no block rebinds.  Adding them is a vocabulary change — a scoping
pass measured 39 `WalkInv` construction sites in 10 modules, `whileBody_step` (the only
block that rebinds `%inc.i`) and two new disequalities in `WalkPtrs.bind`/`WalkRegs.bind`
— and it retires two of that premise's three conjuncts and not the premise: the third,
`Cd.k = C.k`, relates two carries, while `WalkInv G C s` is indexed by one state and one
carry.  This note is the record that half of the merge's supply is a future clause, and
which half is the wall.
-/
structure HcontFacts {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Type where
  /-- The head's byte. -/
  x : BitVec 8
  h8 : evalOperand s (.reg "%8") = some (.int 8 x)
  hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0
  hlt123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0
  hlt125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0
  hne125 : evalICmp .eq x (BitVec.ofNat 8 125) = 0
  /-- The entry counts, read at the default arm: the entry's index and the stream's
  count, and the test a continuing entry passes. -/
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
  its segment from `TailStartC`'s state — `consumerTailSegAt` at count `3`. -/
  r₁ : CallOutcome
  r₂ : CallOutcome
  r₃ : CallOutcome
  ev : EventRecord
  cA : BitVec 32
  rdv : BitVec 32
  xA : BitVec 32
  /-- The scan's first index, and its bound: the copy call's answer and the token's
  record.  `ei < cd` is the scan's non-emptiness, which the exit's own step needs. -/
  ei : Nat
  cd : Nat
  hTail : WalkSegment (stage2Calls stage2SubCalls) G (TailStartC C)
    (TailStart C s x inc nep c ix e b8 x1)
    (TailCarryScan (TailStartC C) ev)
    (hlastEntry C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA) 3
  heicd : ei < cd
  /-- The scan's landing: the byte's address and the byte. -/
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
    some (.int 64 (BitVec.ofNat 64 ei))
  h3S : lookupName (hlastEntry C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA).env
    "%3" = some (.ptr a)
  hpos : ((BitVec.ofNat 64 ei).signExtend 64).toNat < 2 ^ 63
  hreadS : readBytes
    (hlastEntry C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA).mem
    (a + ((BitVec.ofNat 64 ei).signExtend 64).toNat) 1 = some bs
  hbsS : bytesToNat bs = q
  hloc105 : WalkLocal (ScanC₁₀₅ (TailCarryScan (TailStartC C) ev))
    (landRhs457OutAt (hlastEntry C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA)
      (BitVec.ofNat 64 ei) a q)
  x47 : BitVec 8
  h47 : evalOperand
    (landRhs457OutAt (hlastEntry C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA)
      (BitVec.ofNat 64 ei) a q)
    (.reg "%47") = some (.int 8 x47)
  hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1
  hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
  hloc96 : WalkLocal (ScanC₉₆ (TailCarryScan (TailStartC C) ev))
    (ScanS₉₆ (hlastEntry C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA)
      (BitVec.ofNat 64 ei) a q x47)
  hlatch : WalkLocal { TailCarryScan (TailStartC C) ev with block := "while.body462.i" }
    (hlastLatch C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA
      (BitVec.ofNat 64 ei) a q x47)
  /-- The latch's bound: `%cond350.i` is the tail's `cd`, not rebound on the path. -/
  hcwL : lookupName
    (hlastLatch C s x inc nep c ix e b8 x1 r₁ r₂ r₃ ei cd cA rdv xA
      (BitVec.ofNat 64 ei) a q x47).env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd))
  /-- **The scan runs inside the entry's span.**  Its bound is at or before the next
  entry's position, and its first index at or after this one's — the two facts that make
  the visits no more than the span, and the price's byte term. -/
  hspan : cd ≤ entryPos G (C.k + 1)
  hstart : entryPos G C.k ≤ ei
  /-- **The traversal's round**: `walkScanRounds457`'s `hround`, unweakened — a visit at
  the byte the landing loads, at the counter's own index and the bundle's bound. -/
  hround : ∀ (C' : WalkCarry G) (s' : State) (p a : Nat) (bs : List UInt8) (q : Nat)
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
      lookupName s''.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd))
  /-- **The latch's guard**: `walkScanRounds457`'s `hguard`, unweakened. -/
  hguard : ∀ (C' : WalkCarry G) (s' : State), WalkInv G C' s' →
    C'.block = "while.body462.i" → ScanGuard s' "%q.0.i246" "%cond350.i" C'.inner
  /-- **The input's totality at every index the scan visits**: `walkScanRounds457`'s
  `hbyte`, unweakened — the model branches on a byte it does not store. -/
  hbyte : ∀ (C' : WalkCarry G) (s' : State) (p : Nat), WalkInv G C' s' →
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
  hlastEntry C s f.x f.inc f.nep f.c f.ix f.e f.b8 f.x1 f.r₁ f.r₂ f.r₃ f.ei f.cd f.cA
    f.rdv f.xA

/-- The scan's latch, at the bundle's own terms. -/
abbrev contLatchF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontFacts G C s) : State :=
  hlastLatch C s f.x f.inc f.nep f.c f.ix f.e f.b8 f.x1 f.r₁ f.r₂ f.r₃ f.ei f.cd f.cA
    f.rdv f.xA (BitVec.ofNat 64 f.ei) f.a f.q f.x47

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
    (hb : lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.cd)))
    (hc63 : f.cd ≤ 2 ^ 63) (hic : i < f.cd) :
    ∃ (C'' : WalkCarry G) (s'' : State) (n : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C' s' C'' s'' n ∧ WalkInv G C'' s'' ∧
      C''.block = "while.body462.i" ∧
      lookupName s''.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (f.cd - 1))) ∧
      lookupName s''.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.cd)) ∧
      n ≤ stage2ByteAllowance * (f.cd - 1 - i) := by
  have go : ∀ r, ∀ (i : Nat) (K : WalkCarry G) (t : State), f.cd - 1 - i = r →
      WalkInv G K t → K.block = "while.body462.i" →
      ScanGuard t "%q.0.i246" "%cond350.i" K.inner →
      lookupName t.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)) →
      lookupName t.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.cd)) →
      i < f.cd →
      ∃ (K' : WalkCarry G) (t' : State) (n : Nat),
        WalkSegment (stage2Calls stage2SubCalls) G K t K' t' n ∧ WalkInv G K' t' ∧
        K'.block = "while.body462.i" ∧
        lookupName t'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (f.cd - 1))) ∧
        lookupName t'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.cd)) ∧
        n ≤ stage2ByteAllowance * r := by
    intro r
    induction r with
    | zero =>
        intro i K t _ hInv hblock _ hi hb hic
        have hie : i = f.cd - 1 := by omega
        exact ⟨K, t, 0, Seg.measure (Seg.nil hInv), hInv, hblock,
          by rw [← hie]; exact hi, hb, by simp⟩
    | succ r ih =>
        intro i K t hr hInv hblock hg hi hb hic
        have hlt : i + 1 < f.cd := by omega
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
  exact go (f.cd - 1 - i) i C' s' rfl hInv hblock (f.hguard C' s' hInv hblock) hi hb hic

/-! ### The producer -/

/-- **A continuing entry's dispatch, from the head to the merge.**  The head path at its
counted `18`, the scan's visits at `walkScanRounds457`'s bound, the latch's exit and the
merge: a segment to `cleanup478.i` priced at `18 + n + 2` against the entry's own credit
`32·1 + 8·ΔA`.

`ΔA` is the entry's span and `n` the scan's visits: `ci = cd - 1 - ei ≤ ΔA` is
`hspan`/`hstart`, so the byte term pays the visits and the entry term pays the fixed part
— `hlastPrefixSeg`'s `18`, `scanExitSeg`'s `1` and `walkIfEnd473_at`'s `1` — with the two
steps the price's `+ 2` names (`cleanup478.i`'s `condbr` and `while.body.i`'s header) left
to it. -/
theorem walkRevolution_seg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (f : HcontFacts G C s) :
    ∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p ∧
      Cd.block = "cleanup478.i" ∧
      p + 2 ≤ stage2EntryAllowance * (C.k + 1 - C.k) +
        stage2ByteAllowance * (entryPos G (C.k + 1) - entryPos G C.k) := by
  -- the head path, counted: eighteen steps to the scan's latch
  obtain ⟨s₀, hs₀, hsegP⟩ :=
    hlastPrefixSeg (G := G) (C := C) (s := s) hInv hblock f.h8 f.hlt91 f.hlt123 f.hlt125
      f.hne125 f.hinc f.hnep f.hge f.hpre5 f.hav5 f.hidx5 f.htok5 f.hgap5 f.hugt f.hpre6
      f.hin6 f.hv6 f.hend6 f.h8end f.hbit6 f.h8c f.hc110 f.hc116 f.hceq116 f.r₁ f.r₂
      f.r₃ f.ev f.hTail f.hpreS f.hincS f.hopS f.h3S f.hpos f.hreadS f.hbsS f.hloc105
      f.h47 f.hbit47 f.hws47 f.hloc96 f.hlatch
  have hsegP' : WalkSegment (stage2Calls stage2SubCalls) G C s (ScanLatchC C f.ev)
      (contLatchF f) ((((6 + 1) + 5) + 3) + 3) := by
    rw [hs₀] at hsegP
    exact hsegP
  -- the latch's two registers: its own construction's cells
  have hcounter : lookupName (contLatchF f).env "%q.0.i246" =
      some (.int 64 (BitVec.ofNat 64 f.ei)) :=
    latch_counter (contEntryF f) (BitVec.ofNat 64 f.ei) f.a f.q f.x47
  have hbound : lookupName (contLatchF f).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 f.cd)) := f.hcwL
  -- the bound's width, from the span
  have hcdLt : f.cd < G.n := lt_of_le_of_lt f.hspan (entryPos_lt G hk)
  have hmax : G.n ≤ 2 ^ 32 := by
    have := G.maxDoc
    simpa only [stage2MaxDocument] using this
  have hc64 : f.cd < 2 ^ 64 := by omega
  have hc63 : f.cd ≤ 2 ^ 63 := by omega
  -- the bundle's three arithmetic premises, at the terms `omega` reads
  have hspan := f.hspan
  have hstart := f.hstart
  have heicd := f.heicd
  have hcd1 : 1 ≤ f.cd := by omega
  -- the visits, with the scan's counter and bound at the last one
  obtain ⟨Cm, sm, n, hsegR, hInvR, hbR, hiR, hcR, hnR⟩ :=
    contScanRounds G C s f hsegP'.inv' rfl hcounter hbound hc63 f.heicd
  -- the exit, one step: the inner budget is the invariant's local clause at the counts
  have hlocal : ScanCount sm "%q.0.i246" "%cond350.i" Cm.inner := by
    have h := hInvR.blockLocal
    rwa [WalkLocal.extraToken hbR] at h
  have hinner : f.cd - (f.cd - 1) ≤ Cm.inner :=
    ScanCount.same hlocal hiR hcR hc64 (by omega)
  have hie : (f.cd - 1) + 1 = f.cd := by omega
  obtain ⟨s₁, hseg₁, -, hs₁, hInv₁⟩ :=
    scanExitSeg (calls := stage2Calls stage2SubCalls) (G := G) (C := Cm) (s := sm)
      hInvR hbR hiR hcR hinner hie hc64 (by intro e _ _ _; simp [WalkLocal])
  -- the merge, one step, from the token record's register
  obtain ⟨tok, htok⟩ := f.htok Cm sm hInvR hbR
  have htok₁ : lookupName s₁.env "%t352.i" = some (.ptr tok) := by
    rw [hs₁]
    exact scanExit_tok sm (f.cd - 1) f.cd htok
  obtain ⟨s₂, hl₂, -⟩ :=
    walkIfEnd473_at (sub := stage2SubCalls) (G := G) (C := ScanCMerge Cm) (s := s₁)
      hInv₁ rfl htok₁
  refine ⟨{ ScanCMerge Cm with block := "cleanup478.i" }, s₂, ((18 + n) + 1) + 1,
    ?_, rfl, ?_⟩
  · exact ((hsegP'.trans hsegR).trans hseg₁).trans (WalkSegment.of_link hl₂)
  · -- the price: the visits are the entry's span
    have hd : f.cd - 1 - f.ei ≤ entryPos G (C.k + 1) - entryPos G C.k := by
      have h1 : f.cd - 1 ≤ entryPos G (C.k + 1) - 1 := Nat.sub_le_sub_right hspan 1
      have h2 : f.cd - 1 - f.ei ≤ (entryPos G (C.k + 1) - 1) - f.ei :=
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
    have hl : 18 + n + 1 + 1 + 2 = n + 22 := by omega
    rw [hl]
    have h8 : n + 22 ≤ 8 * (entryPos G (C.k + 1) - entryPos G C.k) + 22 :=
      Nat.add_le_add_right hn2 22
    have h22 : 8 * (entryPos G (C.k + 1) - entryPos G C.k) + 22 ≤
        32 + 8 * (entryPos G (C.k + 1) - entryPos G C.k) := by
      have hstep := Nat.add_le_add_left (by decide : (22 : Nat) ≤ 32)
        (8 * (entryPos G (C.k + 1) - entryPos G C.k))
      simpa only [Nat.add_comm] using hstep
    exact le_trans h8 h22

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.contScanRounds
#print axioms LeanLLVM.Refinement.WalkScope.walkRevolution_seg

end WalkScope
end LeanLLVM.Refinement
