/-
# The run class, from the staging

`HcontArm.run` (`JsonStage2WalkDispatchHcontArms`) and `LastEntryArm.run`
(`JsonStage2WalkDispatchArms`) are the default arm's run continuation: the byte before the
entry's end is whitespace, so the whitespace skip runs, the token's end `%ee.1.i` is the
run's stop, the copy call's test is true, the extra-token scan traverses the span between
the stop and the seam's bound, and the merge follows the scan's exit.  The continuing
composition is `runScanMerge_at` (`JsonStage2WalkDispatchRun`), its bundle `RunFacts`; the
terminal one is `runLastMerge_at` at `RunLastFacts`, priced in the document bytes the
entry has left to reach.

This module produces both bundles at every state that carries the invariant, and the two
arms from them.  Which side of the count a state is on is the dispatch's hypothesis, so the
arms carry nothing about it; the two bundles differ exactly where the prices do (the head
chain's count, the seam's bound and the document bounds), and each producer states its own.

## What is derived, and what is taken

Six rows of either bundle are derived, and the terminal bundle's other two: three are read
off the invariant at a *named* state — the head state for `x`/`h8`, the head chain's
endpoint for `h8m`, the scan's landing for `hinc`/`hnep` — one off the geometry once the
scan's span is in hand (`hcw`), one off the continuing price (`hbudget`), and the
terminal bundle's three document bounds off the stop, the length and the entry's position.

| row | how it is derived |
|---|---|
| `x`, `h8` | the witness `hlastByte G C` and `WalkInv.iter.reg8` at the head state |
| `h8m` | the head chain's **endpoint** invariant: `WalkInv.iter.reg8` at `sm` is the byte at `entryPos G Cm.k`, and `hmk` reads that as `hlastByte G C` |
| `hinc` | the landing's endpoint invariant, `WalkInv.inc_reg`, at `hkC` |
| `hnep` | the landing's endpoint invariant, `%nep`'s `walkStaticRegs` row |
| `hcw` | `entryPos_lt` at the head's guard (continuing), `G.maxDoc` at the seam's bound (terminal) |
| `hbudget` | the continuing price's own arithmetic — `runBudget_of_bytePrice`, at the entry's byte credit |
| `hstart`, `hNdoc` | the terminal stop's own bounds — `terminalStop_ge`, and `terminalStop_le` with the length read off the geometry |
| `hspanDoc` | the seam's bound being `%4`: `hc` at `le_of_eq` (terminal) |

Two of the continuing rows the census's tables do not credit as derivable, and neither is
the terminal bundle's: `h8m` is marked **F** there, and it is a theorem of the segment the
arm already carries — a `WalkSegment` records its target's invariant, and the target's
`WalkIter` is the byte cell at the target's index, which `hmk` names; `hbudget` is marked
**D-in-principle**, and it is derived from the price at the byte allowance's eight per visit
(weaker than the field's four per visit, so the derivation spends nothing).  The terminal
bundle has no budget row at all: its three document bounds are read off the stop, and
`runLastMerge_at` applies `runLast_price_with_credit` to them.

## What is taken, and what supplies it

| premise | what supplies it |
|---|---|
| `hbit` | **the head byte's tag test**: `HcontClass.otherValue`'s clear bit at `hlastByte G C` — the document's byte, so the class's own premise |
| `N` | **the run's count**: the whitespace skip's length.  The head segment contains the run, so the chain's count is `12 + N` at a continuing entry and `11 + N` at the last; at the whitespace class the same count is `contWsRunF`'s |
| `hHead`, `hnH`, `hm`, `hmk` | **the head's counted chain to `if.else387.i`**: the four pivots, the count test, the bound's `phi`, the whitespace check and the seam — twelve links at a continuing entry, eleven at the last, plus the run inside that segment.  The four are the class's own: the pivots take different blocks per byte, so no class-independent composition exists, and the census marks the row **D** for that reason |
| `hSpan`, `hnS`, `hs` | **the byte's span below the seam**: `lettersSpan`, `fSpan` or one of the class-C leaves, at `nS ≤ 5` |
| `hTail`, `ht`, `htk` | **the tail's three calls on their scan arm**: the three callees' preconditions and answers at the argument lists the walk stages — the staging's, which no `WalkInv` clause fixes |
| `hLatch`, `hl`, `hkC` | **the scan's landing**: three links through `land.rhs457.i`'s load and its two leaves |
| `i`, `c`, `hcounter`, `hbound`, `hic` | **the scan's counter, the seam's bound and the copy call's test**: `WalkInv` names neither cell, and the bound's value is the lane's at a continuing entry and `%4` at the last |
| `hbyte` | **the scan's per-visit totality** (`walkScanRounds457_of_cell`'s `hbyte`): the visited byte and its read, the two class bits the visit's leaves test, and the three local facts of the visit.  Its *read* half is derivable in principle — `%3` is `WalkPtrs`'s `G.b` at every invariant-carrying state and `walkDoc_byte` reads the document at `G.b + p` — but the two class bits are the visited byte's **content**, the input's, so splitting the read out trades one premise for another of the same size; the arm takes the traversal whole, as the whitespace class's bundle does |
| `hprice`, `hspanStart`, `hstart` | **the document's numbers**: `%cond350.i`'s value at or before the next entry's position (`HcontFacts`'s `hspan`), the run starting at or after the entry's position, and the price at the byte allowance's eight |
| `hstop`, `hN`, `hc` | **the document's numbers, at the terminal index**: the scan's stop is `terminalStop`, the run's count is the stop's distance from the entry, and `%cond350.i` is `%4` = `G.n`.  The bundle's three bounds and the composition's price are proved from these; nothing about the document's length is assumed |

## Which reusable pieces serve, and which do not

The register witness is what `cont_reg8_at` (`JsonStage2WalkDispatchSpansOfStaging`)
establishes at the head state; here the same cell is read at the head chain's endpoint, so
`h8m` follows without a new lemma.  The other two pieces do **not** serve this arm, and the
reason is the bundle's shape rather than a shortage of lemmas:

* **the entry-lane arithmetic** (`contLane_gt`, `slt_one_of_toInt_le`) converts a lane word's
  order into an order between document positions, which is `hspanStart`/`hstart`'s content.
  Those two are the input's — the lane's word — and the bundle states them at the scan's
  cells rather than at the word, so the conversion would still need the cell's naming
  equality, which is `hbound`'s premise.  The lane's arithmetic is spent by the bundle that
  states the word as a field (`HcontFacts.hspan`), not by this one.
* **the document byte across a block's stores** (`cont_hread35`, `sEnd_mem`) transports a
  byte read from a named staged state; this bundle's byte reads are `hbyte`'s, quantified
  over arbitrary invariant-carrying states, so there is no named state to transport across.
  The same is true of **the token-to-log separation** (`token_log_sep`): the run bundles
  carry no log word, that row being `.scalar`'s and `.highByte`'s.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchHcontArms
import LeanLLVM.Refinement.JsonStage2WalkTerminalPrice

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The traversal's proposition, named once

`RunFacts.hbyte` and `RunLastFacts.hbyte` are the same proposition, and each producer takes
it as its premise.  Naming it here keeps the two producers' signatures from repeating the
quantifier, and the two bundles' fields remain the statements of record. -/
abbrev ScanVisits {m0 : Mem} (G : WalkGeom m0) (c : Nat) : Prop :=
  ∀ (K' : WalkCarry G) (t' : State) (p : Nat), WalkInv G K' t' →
    K'.block = "while.body462.i" → p + 1 < c →
    lookupName t'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
    lookupName t'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)) →
    ∃ (a : Nat) (bs : List UInt8) (q : Nat) (x : BitVec 8),
      lookupName (scanLatchOut t' "%inc463.i" "%exitcond298.not" p c
        "land.rhs457.i").env "%3" = some (.ptr a) ∧
      readBytes t'.mem (a + (p + 1)) 1 = some bs ∧ bytesToNat bs = q ∧
      evalOperand (landRhs457OutAt (scanLatchOut t' "%inc463.i" "%exitcond298.not" p c
        "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) ∧
      evalICmp .slt x (BitVec.ofNat 8 13) = 1 ∧
      evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 ∧
      WalkLocal (ScanC₁₀₅ (ScanCLand K'))
        (landRhs457OutAt (scanLatchOut t' "%inc463.i" "%exitcond298.not" p c
          "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) ∧
      WalkLocal (ScanC₉₆ (ScanCLand K'))
        (ScanS₉₆ (scanLatchOut t' "%inc463.i" "%exitcond298.not" p c "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x) ∧
      WalkLocal { ScanCLand K' with block := "while.body462.i" }
        (Latch462S (scanLatchOut t' "%inc463.i" "%exitcond298.not" p c "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x)

/-! ### The budgets, from the prices that state them

`RunFacts.hbudget` is `N + 4·(c - 1 - i) ≤ 8·ΔA + 5`: the run's count and the scan's visits
at four links each, at the entry's byte credit plus the five the price spares.
`RunLastFacts` states no budget: its three terminals are the document's bounds, and
`runLast_price_with_credit` (`JsonStage2WalkDispatchRun`) turns them into the price at the
composition, where the potential is in hand. -/

/-- **The four-per-visit budget follows from the byte allowance's eight.**  The field is
`contWsPriceAt`'s inequality at this arm's tighter per-visit price: one visit costs
`scanRoundSeg4`'s four links, and the allowance pays eight, so the price form with eight per
visit implies the form the bundle states.  Nothing is spent: every visit the premise charges
eight for, the field charges four. -/
theorem runBudget_of_bytePrice {N c i Δ : Nat}
    (h : N + stage2ByteAllowance * (c - 1 - i) ≤ stage2ByteAllowance * Δ + 5) :
    N + 4 * (c - 1 - i) ≤ 8 * Δ + 5 := by
  simp only [stage2ByteAllowance] at h ⊢
  omega

/-- **The budget, from the whitespace class's own price.**  `contWsPriceAt`
(`JsonStage2WalkRevolution`) proves `N + 8·(v - 1 - k) ≤ 8·ΔA + 5` at the class's stop `k`
and the lane's bound `v`.  The run class's own numbers are the same span — the stop is the
run's *start* here and the bound is downstream of it — so `k ≤ i` and `c ≤ v` carry the
class's price to the bundle's field.  This is the derivation the bundle's `hbudget` note
names; it is a proof where that note had an implication. -/
theorem runBudget_of_wsPrice {N c i v k Δ : Nat} (hki : k ≤ i) (hcv : c ≤ v)
    (h : N + stage2ByteAllowance * (v - 1 - k) ≤ stage2ByteAllowance * Δ + 5) :
    N + 4 * (c - 1 - i) ≤ 8 * Δ + 5 := by
  apply runBudget_of_bytePrice
  have hmono : c - 1 - i ≤ v - 1 - k := by omega
  simp only [stage2ByteAllowance] at h ⊢
  omega

/-! ### The continuing bundle

Produced at the invariant's own witness for the head's byte, and at the two segments'
endpoint invariants for the three cells the walk's own blocks keep.  The segments, their
counts and endpoints, the scan's two cells and the traversal enter as premises, each named
in the header's table. -/

/-- **The run bundle on the continuing head, from the entry's evidence.**  `RunFacts` at
every state that carries the invariant and has an entry left: the head's byte is
`hlastByte G C`, and `h8`, `h8m`, `hinc`, `hnep`, `hcw` and `hbudget` are this module's.
`hprice` is the price at the byte allowance's eight per visit — `contWsPriceAt`'s own form,
carried across by `runBudget_of_wsPrice` — and the field's four per visit is
`runBudget_of_bytePrice`'s. -/
def runFacts_of_staging {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    (hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (N : Nat)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 12 + N)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    {Cs : WalkCarry G} {ss : State} {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS)
    (hnS : nS ≤ 5) (hs : Cs.block = "if.then413.i")
    {Ct : WalkCarry G} {st : State}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3)
    (ht : Ct.block = "land.rhs457.i") (htk : Ct.k = C.k)
    {Cl : WalkCarry G} {tl : State}
    (hLatch : WalkSegment (stage2Calls stage2SubCalls) G Ct st Cl tl 3)
    (hl : Cl.block = "while.body462.i") (hkC : Cl.k = C.k)
    (i c : Nat)
    (hcounter : lookupName tl.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbound : lookupName tl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hic : i < c)
    (hbyte : ScanVisits G c)
    (hprice : N + stage2ByteAllowance * (c - 1 - i) ≤
      stage2ByteAllowance * (entryPos G (C.k + 1) - entryPos G C.k) + 5)
    (hspanStart : c ≤ entryPos G (C.k + 1))
    (hstart : entryPos G C.k ≤ i) :
    RunFacts G C s :=
  { x := hlastByte G C
    h8 := by
      show evalOperand s (.reg "%8") = some (.int 8 (hlastByte G C))
      simp only [evalOperand]
      exact hInv.iter.reg8
    hbit := hbit
    N := N
    Cm := Cm
    sm := sm
    nH := nH
    hHead := hHead
    hnH := hnH
    hm := hm
    hmk := hmk
    h8m := by
      show evalOperand sm (.reg "%8") = some (.int 8 (hlastByte G C))
      simp only [evalOperand]
      have hcell := hHead.inv'.iter.reg8
      rw [hmk] at hcell
      simpa only [hlastByte] using hcell
    Cs := Cs
    ss := ss
    nS := nS
    hSpan := hSpan
    hnS := hnS
    hs := hs
    Ct := Ct
    st := st
    hTail := hTail
    ht := ht
    htk := htk
    Cl := Cl
    tl := tl
    hLatch := hLatch
    hl := hl
    hk := hkC
    i := i
    c := c
    hcounter := hcounter
    hbound := hbound
    hinc := by
      rw [← hkC]
      exact hLatch.inv'.inc_reg
    hnep := hLatch.inv'.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep))
      (by simp [walkStaticRegs])
    hic := hic
    hcw := by
      have hpos := entryPos_lt G hk
      have hmax := G.maxDoc
      simp only [stage2MaxDocument] at hmax
      omega
    hbyte := hbyte
    hbudget := runBudget_of_bytePrice (N := N) (c := c) (i := i)
      (Δ := entryPos G (C.k + 1) - entryPos G C.k) hprice
    hspanStart := hspanStart
    hstart := hstart }

/-! ### The terminal bundle

The same composition at the last entry, where the head chain is one link shorter, the
seam's bound is the document's length and the price's terminals are the document's own
bounds.  Nothing is taken from the price: the bundle carries the run's count inside the
bytes the entry has left (`hNdoc`), its start at the entry's position (`hstart`) and the
scan's bound inside the document (`hspanDoc`), and `runLastMerge_at` applies
`runLast_price_with_credit` to the three. -/

/-- **The run bundle at the last entry, from the entry's evidence.**  `RunLastFacts` at
every state that carries the invariant: the head's byte is `hlastByte G C` and `h8`, `h8m`,
`hinc`, `hnep`, `hcw` and the three document bounds are this module's.  The document's own
numbers enter as premises — the scan's stop `terminalStop`, the run's count's distance from
the entry's position, and `%4` = `G.n` — so `N`, `i` and `c` are the document's, and the
bounds are proved from them rather than assumed: `hstart` is the stop's own lower bound and
`hNdoc` is the stop inside the document (`terminalStop_le`), with the length read off the
geometry. -/
def runLastFacts_of_staging {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s)
    (hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (N : Nat)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 11 + N)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    {Cs : WalkCarry G} {ss : State} {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS)
    (hnS : nS ≤ 5) (hs : Cs.block = "if.then413.i")
    {Ct : WalkCarry G} {st : State}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3)
    (ht : Ct.block = "land.rhs457.i") (htk : Ct.k = C.k)
    {Cl : WalkCarry G} {tl : State}
    (hLatch : WalkSegment (stage2Calls stage2SubCalls) G Ct st Cl tl 3)
    (hl : Cl.block = "while.body462.i") (hkC : Cl.k = C.k)
    (i c : Nat)
    (hcounter : lookupName tl.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbound : lookupName tl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hic : i < c)
    (hbyte : ScanVisits G c)
    (hstop : i = terminalStop G.bs (entryPos G C.k))
    (hN : N = i - entryPos G C.k)
    (hc : c = G.n) :
    RunLastFacts G C s :=
  { x := hlastByte G C
    h8 := by
      show evalOperand s (.reg "%8") = some (.int 8 (hlastByte G C))
      simp only [evalOperand]
      exact hInv.iter.reg8
    hbit := hbit
    N := N
    Cm := Cm
    sm := sm
    nH := nH
    hHead := hHead
    hnH := hnH
    hm := hm
    hmk := hmk
    h8m := by
      show evalOperand sm (.reg "%8") = some (.int 8 (hlastByte G C))
      simp only [evalOperand]
      have hcell := hHead.inv'.iter.reg8
      rw [hmk] at hcell
      simpa only [hlastByte] using hcell
    Cs := Cs
    ss := ss
    nS := nS
    hSpan := hSpan
    hnS := hnS
    hs := hs
    Ct := Ct
    st := st
    hTail := hTail
    ht := ht
    htk := htk
    Cl := Cl
    tl := tl
    hLatch := hLatch
    hl := hl
    hk := hkC
    i := i
    c := c
    hcounter := hcounter
    hbound := hbound
    hinc := by
      rw [← hkC]
      exact hLatch.inv'.inc_reg
    hnep := hLatch.inv'.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep))
      (by simp [walkStaticRegs])
    hic := hic
    hcw := by
      have hmax := G.maxDoc
      simp only [stage2MaxDocument] at hmax
      omega
    hbyte := hbyte
    hstart := by
      rw [hstop]
      exact terminalStop_ge G.bs (entryPos G C.k)
    hNdoc := by
      have hbs : G.bs.length = G.n := walkReadBytes_length G.doc
      have hix : entryPos G C.k ≤ G.bs.length := by
        rw [hbs]
        exact le_trans (boundary_ge_entryPos G C.k) (boundary_le G C.k)
      have hle := terminalStop_le G.bs hix
      rw [hN, hstop]
      omega
    hspanDoc := le_of_eq hc }

/-! ### The arms, and their dispatches -/

/-- **The continuing run arm, from the staging.**  `HcontArm.run` at every state that
carries the invariant and has an entry left, its payload the producer above. -/
def hcontArm_run_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    (hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (N : Nat)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 12 + N)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    {Cs : WalkCarry G} {ss : State} {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS)
    (hnS : nS ≤ 5) (hs : Cs.block = "if.then413.i")
    {Ct : WalkCarry G} {st : State}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3)
    (ht : Ct.block = "land.rhs457.i") (htk : Ct.k = C.k)
    {Cl : WalkCarry G} {tl : State}
    (hLatch : WalkSegment (stage2Calls stage2SubCalls) G Ct st Cl tl 3)
    (hl : Cl.block = "while.body462.i") (hkC : Cl.k = C.k)
    (i c : Nat)
    (hcounter : lookupName tl.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbound : lookupName tl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hic : i < c)
    (hbyte : ScanVisits G c)
    (hprice : N + stage2ByteAllowance * (c - 1 - i) ≤
      stage2ByteAllowance * (entryPos G (C.k + 1) - entryPos G C.k) + 5)
    (hspanStart : c ≤ entryPos G (C.k + 1))
    (hstart : entryPos G C.k ≤ i) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .run (runFacts_of_staging G C s hInv hk hbit N hHead hnH hm hmk hSpan hnS hs hTail ht htk
    hLatch hl hkC i c hcounter hbound hic hbyte hprice hspanStart hstart)

/-- **The last entry's run arm, from the staging.**  `LastEntryArm.run` at every state that
carries the invariant, its payload the terminal producer above.  Which side of the count the
state is on is the dispatch's hypothesis, so the arm carries nothing about it. -/
def lastEntryArm_run_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s)
    (hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (N : Nat)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 11 + N)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    {Cs : WalkCarry G} {ss : State} {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS)
    (hnS : nS ≤ 5) (hs : Cs.block = "if.then413.i")
    {Ct : WalkCarry G} {st : State}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3)
    (ht : Ct.block = "land.rhs457.i") (htk : Ct.k = C.k)
    {Cl : WalkCarry G} {tl : State}
    (hLatch : WalkSegment (stage2Calls stage2SubCalls) G Ct st Cl tl 3)
    (hl : Cl.block = "while.body462.i") (hkC : Cl.k = C.k)
    (i c : Nat)
    (hcounter : lookupName tl.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbound : lookupName tl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hic : i < c)
    (hbyte : ScanVisits G c)
    (hstop : i = terminalStop G.bs (entryPos G C.k))
    (hN : N = i - entryPos G C.k)
    (hc : c = G.n) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .run (runLastFacts_of_staging G C s hInv hbit N hHead hnH hm hmk hSpan hnS hs hTail ht htk
    hLatch hl hkC i c hcounter hbound hic hbyte hstop hN hc)

/-- **The continuing run dispatch, from the staging.** -/
theorem walkDispatch_at_run_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (N : Nat)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 12 + N)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    {Cs : WalkCarry G} {ss : State} {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS)
    (hnS : nS ≤ 5) (hs : Cs.block = "if.then413.i")
    {Ct : WalkCarry G} {st : State}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3)
    (ht : Ct.block = "land.rhs457.i") (htk : Ct.k = C.k)
    {Cl : WalkCarry G} {tl : State}
    (hLatch : WalkSegment (stage2Calls stage2SubCalls) G Ct st Cl tl 3)
    (hl : Cl.block = "while.body462.i") (hkC : Cl.k = C.k)
    (i c : Nat)
    (hcounter : lookupName tl.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbound : lookupName tl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hic : i < c)
    (hbyte : ScanVisits G c)
    (hprice : N + stage2ByteAllowance * (c - 1 - i) ≤
      stage2ByteAllowance * (entryPos G (C.k + 1) - entryPos G C.k) + 5)
    (hspanStart : c ≤ entryPos G (C.k + 1))
    (hstart : entryPos G C.k ≤ i) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_run_of_staging C s hInv hk hbit N hHead hnH hm hmk hSpan hnS hs hTail ht htk
      hLatch hl hkC i c hcounter hbound hic hbyte hprice hspanStart hstart)

/-- **The last entry's run dispatch, from the staging.**  The level's negated count, at the
arm the terminal producer inhabits. -/
theorem walkDispatch_at_run_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (N : Nat)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 11 + N)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    {Cs : WalkCarry G} {ss : State} {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS)
    (hnS : nS ≤ 5) (hs : Cs.block = "if.then413.i")
    {Ct : WalkCarry G} {st : State}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3)
    (ht : Ct.block = "land.rhs457.i") (htk : Ct.k = C.k)
    {Cl : WalkCarry G} {tl : State}
    (hLatch : WalkSegment (stage2Calls stage2SubCalls) G Ct st Cl tl 3)
    (hl : Cl.block = "while.body462.i") (hkC : Cl.k = C.k)
    (i c : Nat)
    (hcounter : lookupName tl.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbound : lookupName tl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hic : i < c)
    (hbyte : ScanVisits G c)
    (hstop : i = terminalStop G.bs (entryPos G C.k))
    (hN : N = i - entryPos G C.k)
    (hc : c = G.n) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_run_of_staging C s hInv hbit N hHead hnH hm hmk hSpan hnS hs hTail ht htk
      hLatch hl hkC i c hcounter hbound hic hbyte hstop hN hc)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.runBudget_of_bytePrice
#print axioms LeanLLVM.Refinement.WalkScope.runBudget_of_wsPrice
#print axioms LeanLLVM.Refinement.WalkScope.runFacts_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.runLastFacts_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_run_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_run_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_run_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_run_last_of_staging

end WalkScope
end LeanLLVM.Refinement
