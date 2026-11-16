/-
The default arm's run class: the scan's rounds at the seam's own bound, and the segment.

## The class, and why it is not `.ws`'s

Where the byte before the entry's end is whitespace the walk runs that run first, so the
token's end `%ee.1.i` is the run's *stop* `k` and the copy call's test
`ult %ee.1.i %cond350.i` is `ult k v` — true — so the walk enters the extra-token scan at
`land.rhs457.i`.  The scan then visits `[k, v)` and the merge follows.  That is the run
class, and it is a continuation *orthogonal* to the head switch's byte classes: every
default-arm span (`lettersSpan`, `fSpan`, the class-C leaves' four) has a run and a
scan-free arm, exactly as `126`/`127` have `.ws` and `.cleanup`.

`HcontArm.ws` carries this continuation **at `126`/`127` only**, because `HcontFacts`'s own
class bits are those two bytes; its composition is `walkRevolutionMergeSegWs`.  This module
is the arm for the same continuation at every other head class, so its span enters as a
segment at `nS ≤ 5` — the byte's own proved span — and its head chain as a segment at
`nH ≤ 12`.

## The bound, and why `scanWsRounds` is not it

`scanWsRounds` (`JsonStage2WalkRevolutionSeg`) is stated over `HcontFacts` and reads the
bound out of the bundle's `v` — the lane word `cond.true345.i` loaded.  A bundle can only be
inhabited at its own head class, so a lemma stated over it cannot serve another class's
states, and `HcontFacts`'s `v` is not a number the seam's own state carries.  What the
rounds actually need is the word the **seam's bound cell** holds: `%cond350.i`, which the
seam's path binds once (`cond.end349.i`) and no block from there to the latch rebinds, and
which the landing's first edge reads.  `scanRoundsAt` states the traversal at that cell's
value `c` — a parameter, not a bundle's projection — so it applies at any head state whose
latch carries `%cond350.i = ofNat 64 c`:

| piece | lemma | count |
|---|---|---|
| one visit (the latch and the dispatch's three links) | `scanRoundSeg4` | `4` |
| the visits | `scanRoundsAt` | `nSc ≤ 4·(c - 1 - i)` |

The conclusion keeps what the merge reads and what the exit test reads: the counter at the
last visit, the bound, `%inc.i`, `%nep` and the carry's index.  The price is four per visit,
the round's own count, rather than the byte allowance's eight — `scanWsRounds`'s choice, and
the reason the bound below is not widened.

## The composition

`runScanMerge_at` composes

| piece | source | links |
|---|---|---|
| the head's chain through the seam to `if.else387.i` | `f.hHead` | `nH ≤ 12 + N` |
| the byte's span | `f.hSpan` | `nS ≤ 5` |
| the tail's three calls on their **scan** arm | `f.hTail` | `3` |
| the scan's landing | `f.hLatch` | `3` |
| the visits | `scanRoundsAt` | `nSc` |
| the latch's exit | `scanExitSeg` | `1` |
| the merge | `walkIfEnd473_at` | `1` |

to `revMergeS sm c` at `revMergeC Cm`: both are terms of the composition, which is what
lets the merge's three cells be read where the run actually ends.  Its price is
`nH + nS + 8 + nSc + 2 ≤ 32·Δk + 8·ΔA`: the fixed part is twenty-seven including the
price's own two, and `N + 4·(c - 1 - i) ≤ 8·ΔA + 5` (the bundle's `hbudget`) pays the run
and the visits out of the entry's byte span.  The head's chain is bounded by `12 + N`
because the whitespace run is upstream of the seam and inside that segment.

## What the bundle supplies, and what it derives

The bundle's fields are the *input's*: the document's bytes (the landing's and the visits'),
the head and tail segments (their callees' contracts, which no `WalkInv` clause fixes), and
the two facts that place the scan inside the entry's span.  The **token record's register**
at the scan's exit is the one supplied preservation fact, for `HcontFacts`'s reason: the
traversal returns its final state existentially, and the layer has no lemma that the scan
preserves a register it does not bind.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassC
import LeanLLVM.Refinement.JsonStage2WalkRevolutionSeg

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The visits, at the seam's bound

`scanWsRounds`'s induction with the bundle's `v.toNat` replaced by the bound cell's value
`c`, and its per-visit hypothesis taken as a hypothesis rather than read off a bundle.  The
round is `scanRoundSeg4`, which was already stated at a plain bound; what this lemma adds is
the aggregation over the visits with the three registers the merge reads carried across. -/
theorem scanRoundsAt {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    {K : WalkCarry G} {t : State} {i c : Nat} {inc0 nep0 : BitVec 64}
    {k0 : Nat} (hInv : WalkInv G K t) (hblock : K.block = "while.body462.i")
    (hi : lookupName t.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)))
    (hb : lookupName t.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hinc : lookupName t.env "%inc.i" = some (.int 64 inc0))
    (hnep : lookupName t.env "%nep" = some (.int 64 nep0))
    (hk : K.k = k0) (hcw : c < 2 ^ 64) (hc63 : c < 2 ^ 63) (hic : i < c)
    (hbyte : ∀ (K' : WalkCarry G) (t' : State) (p : Nat), WalkInv G K' t' →
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
            (BitVec.ofNat 64 (p + 1)) a q x)) :
    ∃ (K' : WalkCarry G) (t' : State) (n : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G K t K' t' n ∧ WalkInv G K' t' ∧
      K'.block = "while.body462.i" ∧ K'.k = k0 ∧
      lookupName t'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (c - 1))) ∧
      lookupName t'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)) ∧
      lookupName t'.env "%inc.i" = some (.int 64 inc0) ∧
      lookupName t'.env "%nep" = some (.int 64 nep0) ∧
      n ≤ 4 * (c - 1 - i) := by
  have go : ∀ r, ∀ (i : Nat) (K : WalkCarry G) (t : State) (inc0 nep0 : BitVec 64)
      (k0 : Nat), c - 1 - i = r →
      WalkInv G K t → K.block = "while.body462.i" →
      lookupName t.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)) →
      lookupName t.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)) →
      lookupName t.env "%inc.i" = some (.int 64 inc0) →
      lookupName t.env "%nep" = some (.int 64 nep0) →
      K.k = k0 → i < c →
      ∃ (K' : WalkCarry G) (t' : State) (n : Nat),
        WalkSegment (stage2Calls stage2SubCalls) G K t K' t' n ∧ WalkInv G K' t' ∧
        K'.block = "while.body462.i" ∧ K'.k = k0 ∧
        lookupName t'.env "%q.0.i246" =
          some (.int 64 (BitVec.ofNat 64 (c - 1))) ∧
        lookupName t'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)) ∧
        lookupName t'.env "%inc.i" = some (.int 64 inc0) ∧
        lookupName t'.env "%nep" = some (.int 64 nep0) ∧
        n ≤ 4 * r := by
    intro r
    induction r with
    | zero =>
        intro i K t inc0 nep0 k0 hr hInv hblock hi hb hinc hnep hk hic
        have hie : i = c - 1 := by omega
        exact ⟨K, t, 0, Seg.measure (Seg.nil hInv), hInv, hblock, hk,
          by rw [← hie]; exact hi, hb, hinc, hnep, by simp⟩
    | succ r ih =>
        intro i K t inc0 nep0 k0 hr hInv hblock hi hb hinc hnep hk hic
        have hlt : i + 1 < c := by omega
        obtain ⟨a, bs, q, x, h3, hread, hbs, h47, hbit, hws, hl105, hl96, hll⟩ :=
          hbyte K t i hInv hblock hlt hi hb
        have hSC : ScanCount t "%q.0.i246" "%cond350.i" K.inner := by
          have h := hInv.blockLocal
          rwa [WalkLocal.extraToken hblock] at h
        have hinner : c - i ≤ K.inner := ScanCount.same hSC hi hb hcw hic
        have hinner' : c - (i + 1) ≤ K.inner := by omega
        have hposi : i + 1 < 2 ^ 63 := by omega
        have hseg : WalkSegment (stage2Calls stage2SubCalls) G K t
            { ScanCLand K with block := "while.body462.i" }
            (Latch462S (scanLatchOut t "%inc463.i" "%exitcond298.not" i c
              "land.rhs457.i") (BitVec.ofNat 64 (i + 1)) a q x) 4 :=
          scanRoundSeg4 (calls := stage2Calls stage2SubCalls) G K t hInv hblock hi hb hcw
            hlt hposi hinner' h3 hread hbs hl105 h47 hbit hws hl96 hll
        obtain ⟨K₂, t₂, m, hseg₂, hInv₂, hb₂, hk₂, hi₂, hc₂, hinc₂, hnep₂, hm⟩ :=
          ih (i + 1) { ScanCLand K with block := "while.body462.i" }
            (Latch462S (scanLatchOut t "%inc463.i" "%exitcond298.not" i c
              "land.rhs457.i") (BitVec.ofNat 64 (i + 1)) a q x) inc0 nep0 k0
            (by omega) hseg.inv' rfl
            (latch462S_counter (m0 := m0) t i c (BitVec.ofNat 64 (i + 1)) a q x)
            (latch462S_cond (m0 := m0) t i c (BitVec.ofNat 64 (i + 1)) a q x hb)
            (by rw [scanRoundOut_inc]; exact hinc)
            (by rw [scanRoundOut_nep]; exact hnep)
            hk (by omega)
        refine ⟨K₂, t₂, 4 + m, hseg.trans hseg₂, hInv₂, hb₂, hk₂, hi₂, hc₂, hinc₂, hnep₂, ?_⟩
        rw [Nat.mul_succ]
        omega
  exact go (c - 1 - i) i K t inc0 nep0 k0 rfl hInv hblock hi hb hinc hnep hk hic

/-! ### The bundle, and the segment

The run class's inputs, one structure: the head chain, the span, the tail's scan arm, the
landing, the per-visit facts, the register's preservation across the scan, and the two
facts that put the scan inside the entry's span.  Nothing in it is the merge's — the
composition derives the merge's cells. -/
structure RunFacts {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Type where
  /-- The head's byte, and the tag test's clear arm: the default arm's class. -/
  x : BitVec 8
  h8 : evalOperand s (.reg "%8") = some (.int 8 x)
  hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
    evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0
  /-- The head's chain to the seam, and the byte's span below it.  **`N` is the
  whitespace run's count**, which the head segment contains: the run is upstream of the
  seam, so the chain's count is `12 + N` and the arm carries `N` beside it. -/
  N : Nat
  Cm : WalkCarry G
  sm : State
  nH : Nat
  hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH
  hnH : nH ≤ 12 + N
  hm : Cm.block = "if.else387.i"
  hmk : Cm.k = C.k
  h8m : evalOperand sm (.reg "%8") = some (.int 8 x)
  Cs : WalkCarry G
  ss : State
  nS : Nat
  hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS
  hnS : nS ≤ 5
  hs : Cs.block = "if.then413.i"
  /-- The tail's three calls on their **scan** arm: they end at the landing. -/
  Ct : WalkCarry G
  st : State
  hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3
  ht : Ct.block = "land.rhs457.i"
  htk : Ct.k = C.k
  /-- The scan's landing: three links to the latch. -/
  Cl : WalkCarry G
  tl : State
  hLatch : WalkSegment (stage2Calls stage2SubCalls) G Ct st Cl tl 3
  hl : Cl.block = "while.body462.i"
  hk : Cl.k = C.k
  /-- The latch's counter, its bound and the two registers the merge reads.  The bound is
  the seam's: `%cond350.i`, bound once at `cond.end349.i` and never rebound on the path. -/
  i : Nat
  c : Nat
  hcounter : lookupName tl.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i))
  hbound : lookupName tl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c))
  hinc : lookupName tl.env "%inc.i" =
    some (.int 64 (BitVec.ofNat 64 (C.k + 1)))
  hnep : lookupName tl.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep))
  hic : i < c
  hcw : c < 2 ^ 64
  /-- The input's totality at every index the visits read (`walkScanRounds457`'s `hbyte`,
  unweakened). -/
  hbyte : ∀ (K' : WalkCarry G) (t' : State) (p : Nat), WalkInv G K' t' →
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
  /-- **The token record's register at the scan's exit.**  Supplied, for `HcontFacts`'s
  reason: the traversal returns its final state existentially, so no named term states the
  cell at, and the layer has no lemma that the scan preserves a register it does not
  bind.  Stated over the states the traversal's counters pin. -/
  htok : ∀ (K' : WalkCarry G) (t' : State), WalkInv G K' t' →
    K'.block = "while.body462.i" → ∃ tok : Nat, lookupName t'.env "%t352.i" = some (.ptr tok)
  /-- **The budget is not double-spent: the run and the visits share the entry's span.**
  The run's count `N` and the scan's visits `4·(c - 1 - i)` are together at most the
  entry's byte credit plus the five the `+5` spares.  This is `contWsPriceF`'s inequality
  (`N + 8·(v - 1 - k) ≤ 8·ΔA + 5`, proved at the class-C route) at this module's *tighter*
  four-per-visit price: `4·(c - 1 - i) ≤ 8·(v - 1 - k)` because `c ≤ v` and `i ≥ k`, so
  the fact is implied by the existing derivation rather than being a price this arm
  invents.  It enters as a field for the same reason the head segment does — the run's
  derivation (`contWsRunF`, `wsRun`) is stated at the whitespace check's named states,
  which are the class-C route's, and a generic arm has no term for them. -/
  hbudget : N + 4 * (c - 1 - i) ≤
    8 * (entryPos G (C.k + 1) - entryPos G C.k) + 5
  /-- **The scan runs inside the entry's span.**  Its bound is at or before the next
  entry's position, and its first index at or after this one's. -/
  hspanStart : c ≤ entryPos G (C.k + 1)
  hstart : entryPos G C.k ≤ i

/-- **The run class's segment to the merge, with the merge's cells at its endpoint.**  The
head, the span, the tail's scan arm and the landing at their own counts, the visits by
`scanRoundsAt` at the seam's bound `c`, the latch's exit and the merge — to `revMergeS sm c`
at `revMergeC Cm`, both terms of the composition, so the three cells are read where the run
actually ends.

The price is `nH + nS + 11 + nSc + 2 ≤ 32·Δk + 8·ΔA`: `nH ≤ 12 + N` and `nS ≤ 5` fix it at
`27 + N + nSc`, `nSc ≤ 4·(c - 1 - i)`, and the bundle's `hbudget` places `N + 4·(c - 1 - i)`
inside `8·ΔA + 5` — so the whole is `32 + 8·ΔA`, the budget spent and not double-spent.

**The continuing level's price, and why the terminal one is different.**  `ΔA` is
`entryPos (C.k + 1) - entryPos C.k`, which is a positive entry span only while
`C.k + 1 < G.nep`; at the terminal index `entryPos G G.nep = 0` (`walkEntryPos_at_nep`), so
the byte credit is empty rather than small, and the same `hbudget` would read
`N + 4·(c - 1 - i) ≤ 5`.  That is why this composition is the **continuing** run class's,
and the last entry's has its own bundle beside it: `RunLastFacts` states the six links the
entry allowance leaves at the terminal index, and `runLastMerge_at` spends exactly those
against `WalkDispatchResult.mergeLast` — the price without a byte term, which is sound
there because the span it would charge does not exist. -/
theorem runScanMerge_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (f : RunFacts G C s) :
    ∃ (Cm : WalkCarry G) (sm : State) (nSc : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C s (revMergeC Cm)
        (revMergeS sm f.c) (f.nH + f.nS + 8 + nSc) ∧
      WalkInv G (revMergeC Cm) (revMergeS sm f.c) ∧
      (revMergeC Cm).block = "cleanup478.i" ∧
      (revMergeS sm f.c).pre = some "if.end473.i" ∧
      (revMergeC Cm).k = C.k ∧
      lookupName (revMergeS sm f.c).env "%inc.i" =
        some (.int 64 (BitVec.ofNat 64 (C.k + 1))) ∧
      lookupName (revMergeS sm f.c).env "%nep" =
        some (.int 64 (BitVec.ofNat 64 G.nep)) ∧
      nSc ≤ 4 * (f.c - 1 - f.i) ∧
      (f.nH + f.nS + 8 + nSc) + 2 ≤
        stage2EntryAllowance * (C.k + 1 - C.k) +
          stage2ByteAllowance * (entryPos G (C.k + 1) - entryPos G C.k) := by
  -- 1. the head's chain, the span and the tail's scan arm
  have hsegHS : WalkSegment (stage2Calls stage2SubCalls) G C s f.Cs f.ss (f.nH + f.nS) :=
    f.hHead.trans (Seg.measure f.hSpan)
  have hsegT : WalkSegment (stage2Calls stage2SubCalls) G C s f.Ct f.st
      (f.nH + f.nS + 3) := hsegHS.trans f.hTail
  -- 2. the landing's three links
  have hsegL : WalkSegment (stage2Calls stage2SubCalls) G C s f.Cl f.tl
      (f.nH + f.nS + 3 + 3) := hsegT.trans f.hLatch
  -- 3. the visits, at the seam's bound: `c` is a document position, so it is below 2^63
  have hcn : f.c < G.n :=
    lt_of_le_of_lt f.hspanStart (entryPos_lt G hk)
  have hc63 : f.c < 2 ^ 63 := by
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  obtain ⟨Cm, sm, nSc, hsegS, hInvR, hbR, hkR, hiR, hcR, hincR, hnepR, hnR⟩ :=
    scanRoundsAt (G := G) (C := C) (s := s) f.hLatch.inv' f.hl f.hcounter f.hbound
      f.hinc f.hnep f.hk f.hcw hc63 f.hic f.hbyte
  have hsegP : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm
      (f.nH + f.nS + 3 + 3 + nSc) := hsegL.trans hsegS
  -- 4. the exit: the inner budget is the invariant's local clause at the counts
  have hlocal : ScanCount sm "%q.0.i246" "%cond350.i" Cm.inner := by
    have h := hInvR.blockLocal
    rwa [WalkLocal.extraToken hbR] at h
  have hcpos : 0 < f.c := by have := f.hic; omega
  have hlt : f.c - 1 < f.c := by omega
  have hinner : f.c - (f.c - 1) ≤ Cm.inner :=
    ScanCount.same hlocal hiR hcR f.hcw hlt
  have hie : (f.c - 1) + 1 = f.c := Nat.sub_add_cancel (by omega)
  obtain ⟨s₁, hseg₁, -, hs₁, hInv₁⟩ :=
    scanExitSeg (calls := stage2Calls stage2SubCalls) (G := G) (C := Cm) (s := sm)
      hInvR hbR hiR hcR hinner hie f.hcw (by intro e _ _ _; simp [WalkLocal])
  have hs₁' : s₁ = revExitS sm f.c := hs₁
  subst hs₁'
  -- 5. the merge, one step, from the token record's register
  obtain ⟨tok, htok⟩ := f.htok Cm sm hInvR hbR
  have htok₁ : lookupName (revExitS sm f.c).env "%t352.i" = some (.ptr tok) :=
    scanExit_tok sm (f.c - 1) f.c htok
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    walkIfEnd473_at (sub := stage2SubCalls) (G := G) (C := revExitC Cm)
      (s := revExitS sm f.c) hInv₁ rfl htok₁
  have hs₂' : s₂ = revMergeS sm f.c := hs₂
  rw [hs₂'] at hl₂
  -- the cells at the merge
  have hincM : lookupName (revMergeS sm f.c).env "%inc.i" =
      some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := by
    rw [revMergeS_inc, revExitS_inc, hincR]
  have hnepM : lookupName (revMergeS sm f.c).env "%nep" =
      some (.int 64 (BitVec.ofNat 64 G.nep)) := by
    rw [revMergeS_nep, revExitS_nep, hnepR]
  have hkM : (revMergeC Cm).k = C.k := by
    rw [revMergeC_k]; exact hkR
  have hpreM : (revMergeS sm f.c).pre = some "if.end473.i" := by
    show (some (revExitS sm f.c).pc : Option String) = some "if.end473.i"
    rw [show (revExitS sm f.c).pc = "if.end473.i" from rfl]
  refine ⟨Cm, sm, nSc, ?_, hl₂.inv', rfl, hpreM, hkM, hincM, hnepM, hnR, ?_⟩
  · -- the segment: the exit's one step and the merge's one, beside the visits
    have hexit : WalkSegment (stage2Calls stage2SubCalls) G C s
        (revExitC Cm) (revExitS sm f.c) (f.nH + f.nS + 3 + 3 + nSc + 1) := by
      rw [show f.nH + f.nS + 3 + 3 + nSc + 1 = (f.nH + f.nS + 3 + 3 + nSc) + 1
        from by omega]
      exact hsegP.trans hseg₁
    rw [show f.nH + f.nS + 8 + nSc = f.nH + f.nS + 3 + 3 + nSc + 1 + 1 from by omega]
    exact hexit.trans (WalkSegment.of_link hl₂)
  · -- the price: the fixed part at its bounds, and the run and visits inside the span
    have hnH := f.hnH
    have hnS := f.hnS
    have hbudget := f.hbudget
    have hΔ : C.k + 1 - C.k = 1 := by omega
    simp only [stage2EntryAllowance, stage2ByteAllowance, hΔ, Nat.mul_one]
    omega

/-! ### The terminal index's run class

The same path, at the last entry, priced against the entry allowance alone.  Its merge
index is the stream's end — `k2 = G.nep` — so it lands against
`WalkDispatchResult.mergeLast` (`JsonStage2WalkDispatchThreeOfRun`) rather than `merge`.

**What changes, and why.**  Three things, and each is the terminal index's own:

| the continuing bundle | the terminal bundle | why |
|---|---|---|
| `nH ≤ 12 + N` | `nH ≤ 11 + N` | the head chain's fixed part is eleven here: `sw.default.i`'s count test *fails* at the last entry, so the `cond.true345.i` link the continuing route takes is not on this path (`.letters`' last-entry count) |
| `c ≤ entryPos G (C.k + 1)` | `c ≤ G.n` | the scan's bound `%cond350.i` is `%4`, the document's length, at the last entry, not the next entry's position (`HcontFacts`' note on the two bundles' opposite values of the same lane) |
| `N + 4·(c - 1 - i) ≤ 8·ΔA + 5` | `N + 4·(c - 1 - i) ≤ 6` | there is no `ΔA`: `entryPos G G.nep = 0`, and the entry allowance leaves six links for the run and the scan together |

The fixed part is twenty-four links — the head's eleven, the byte's span at most five,
the tail's three, the landing's three, the exit's one and the merge's one — and with the
price's own two, the run's visits and the scan's share the remaining six.  So the bundle's
`hbudget` is exactly the arithmetic `mergeLast` can pay, and the composition below spends
it without a byte term.

**Why this is a class and not a weakening.**  A document whose terminal run exceeds those
six links has no arm here: the price is not available at the terminal index, and inventing
one by shortening the count would be the very weakening the split exists to prevent.  The
class states the budget as a premise of its own, so the arm's coverage is exactly what
`mergeLast` pays for.

**The bundle's fields are the input's**, as `RunFacts`' are: the document's bytes (the
landing's and the visits'), the head and tail segments with their own counts, the seam's
bound and the token record's register.  Two of `RunFacts`' fields are absent rather than
copied: `hspanStart` states the scan inside the *next* entry's span, which the terminal
index has not got (the budget does that work here), and `hstart` places the run's start in
the entry — true at the last entry too, but no proof reads it, so carrying it would narrow
the class for nothing. -/

/-- **The terminal run class's inputs**, at the last entry: the head's chain through the
seam (`nH ≤ 11 + N`, the whitespace run's count `N` inside it), the byte's span at
`nS ≤ 5`, the tail's three calls on their *scan* arm, the landing, the seam's bound and its
two registers, the visits' totality, the token record's register, and the budget: the run
and the visits together inside the six links the entry allowance leaves.

`hspanDoc` is the terminal analogue of `RunFacts.hspanStart`: at the last entry the scan's
bound `%cond350.i` is `%4`, the document's length, so the bound is at most `G.n` rather
than at most the next entry's position (which is zero here). -/
structure RunLastFacts {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Type where
  /-- The head's byte, and the tag test's clear arm: the default arm's class. -/
  x : BitVec 8
  h8 : evalOperand s (.reg "%8") = some (.int 8 x)
  hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
    evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0
  /-- The head's chain to the seam, and the byte's span below it.  **`N` is the
  whitespace run's count**, which the head segment contains: the run is upstream of the
  seam, so the chain's count is `11 + N` at the last entry and the arm carries `N`. -/
  N : Nat
  Cm : WalkCarry G
  sm : State
  nH : Nat
  hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH
  hnH : nH ≤ 11 + N
  hm : Cm.block = "if.else387.i"
  hmk : Cm.k = C.k
  h8m : evalOperand sm (.reg "%8") = some (.int 8 x)
  Cs : WalkCarry G
  ss : State
  nS : Nat
  hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS
  hnS : nS ≤ 5
  hs : Cs.block = "if.then413.i"
  /-- The tail's three calls on their **scan** arm: they end at the landing. -/
  Ct : WalkCarry G
  st : State
  hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3
  ht : Ct.block = "land.rhs457.i"
  htk : Ct.k = C.k
  /-- The scan's landing: three links to the latch. -/
  Cl : WalkCarry G
  tl : State
  hLatch : WalkSegment (stage2Calls stage2SubCalls) G Ct st Cl tl 3
  hl : Cl.block = "while.body462.i"
  hk : Cl.k = C.k
  /-- The latch's counter, its bound and the two registers the merge reads.  The bound is
  the seam's `%cond350.i`, which is `%4` — the document's length — at the last entry. -/
  i : Nat
  c : Nat
  hcounter : lookupName tl.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i))
  hbound : lookupName tl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c))
  hinc : lookupName tl.env "%inc.i" =
    some (.int 64 (BitVec.ofNat 64 (C.k + 1)))
  hnep : lookupName tl.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep))
  hic : i < c
  hcw : c < 2 ^ 64
  /-- The input's totality at every index the visits read (`walkScanRounds457`'s `hbyte`,
  unweakened). -/
  hbyte : ∀ (K' : WalkCarry G) (t' : State) (p : Nat), WalkInv G K' t' →
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
  /-- **The token record's register at the scan's exit.**  Supplied, for `RunFacts`'s
  reason: the traversal returns its final state existentially, so no named term states
  the cell at, and the layer has no lemma that the scan preserves a register it does not
  bind. -/
  htok : ∀ (K' : WalkCarry G) (t' : State), WalkInv G K' t' →
    K'.block = "while.body462.i" → ∃ tok : Nat, lookupName t'.env "%t352.i" = some (.ptr tok)
  /-- **The entry allowance's six remaining links pay for the run and the scan.**  The
  fixed part is twenty-four links and the price's own two are the other twenty-six of the
  thirty-two; `N` is the run's count and `4·(c - 1 - i)` the visits' count
  (`scanRoundsAt`'s four per visit).  There is no byte term to spend: the terminal index's
  credit is the entry allowance's alone. -/
  hbudget : N + 4 * (c - 1 - i) ≤ 6
  /-- **The scan's bound is inside the document.**  `%cond350.i` is `%4` at the last
  entry, and `%4` is the document's length, so this is the terminal form of
  `RunFacts.hspanStart` and it is what puts the bound below `2 ^ 63` at the width the
  document has. -/
  hspanDoc : c ≤ G.n

/-- **The terminal run class's segment to the merge, with the merge's cells at its
endpoint.**  The same composition as `runScanMerge_at` — head, span, the tail's scan arm,
the landing, the visits by `scanRoundsAt` at the seam's bound `c`, the exit and the
merge — to `revMergeS sm f.c` at `revMergeC Cm`, and the price is
`nH + nS + 8 + nSc + 2 ≤ 32·(G.nep - C.k)`: at `nH ≤ 11 + N` and `nS ≤ 5` the fixed part is
twenty-four, the price's own two make twenty-six, and `hbudget` places
`N + 4·(c - 1 - i)` inside the six that remain.

The right-hand side is stated as `32·(G.nep - C.k)` — the entry term `mergeLast` carries —
and no byte term appears, because there is none to carry: `entryPos G G.nep = 0`.  The
dispatch reads `G.nep - C.k = 1` from the head's own guard and hands this price to
`WalkDispatchResult.mergeLast` unchanged. -/
theorem runLastMerge_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (f : RunLastFacts G C s) :
    ∃ (Cm : WalkCarry G) (sm : State) (nSc : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C s (revMergeC Cm)
        (revMergeS sm f.c) (f.nH + f.nS + 8 + nSc) ∧
      WalkInv G (revMergeC Cm) (revMergeS sm f.c) ∧
      (revMergeC Cm).block = "cleanup478.i" ∧
      (revMergeS sm f.c).pre = some "if.end473.i" ∧
      (revMergeC Cm).k = C.k ∧
      lookupName (revMergeS sm f.c).env "%inc.i" =
        some (.int 64 (BitVec.ofNat 64 (C.k + 1))) ∧
      lookupName (revMergeS sm f.c).env "%nep" =
        some (.int 64 (BitVec.ofNat 64 G.nep)) ∧
      nSc ≤ 4 * (f.c - 1 - f.i) ∧
      (f.nH + f.nS + 8 + nSc) + 2 ≤ stage2EntryAllowance * (G.nep - C.k) := by
  -- 1. the head's chain, the span and the tail's scan arm
  have hsegHS : WalkSegment (stage2Calls stage2SubCalls) G C s f.Cs f.ss (f.nH + f.nS) :=
    f.hHead.trans (Seg.measure f.hSpan)
  have hsegT : WalkSegment (stage2Calls stage2SubCalls) G C s f.Ct f.st
      (f.nH + f.nS + 3) := hsegHS.trans f.hTail
  -- 2. the landing's three links
  have hsegL : WalkSegment (stage2Calls stage2SubCalls) G C s f.Cl f.tl
      (f.nH + f.nS + 3 + 3) := hsegT.trans f.hLatch
  -- 3. the visits, at the seam's bound: `c` is inside the document, so below 2^63
  have hc63 : f.c < 2 ^ 63 := by
    have h2 := G.maxDoc
    have hc := f.hspanDoc
    simp only [stage2MaxDocument] at h2
    omega
  obtain ⟨Cm, sm, nSc, hsegS, hInvR, hbR, hkR, hiR, hcR, hincR, hnepR, hnR⟩ :=
    scanRoundsAt (G := G) (C := C) (s := s) f.hLatch.inv' f.hl f.hcounter f.hbound
      f.hinc f.hnep f.hk f.hcw hc63 f.hic f.hbyte
  have hsegP : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm
      (f.nH + f.nS + 3 + 3 + nSc) := hsegL.trans hsegS
  -- 4. the exit: the inner budget is the invariant's local clause at the counts
  have hlocal : ScanCount sm "%q.0.i246" "%cond350.i" Cm.inner := by
    have h := hInvR.blockLocal
    rwa [WalkLocal.extraToken hbR] at h
  have hcpos : 0 < f.c := by have := f.hic; omega
  have hlt : f.c - 1 < f.c := by omega
  have hinner : f.c - (f.c - 1) ≤ Cm.inner :=
    ScanCount.same hlocal hiR hcR f.hcw hlt
  have hie : (f.c - 1) + 1 = f.c := Nat.sub_add_cancel (by omega)
  obtain ⟨s₁, hseg₁, -, hs₁, hInv₁⟩ :=
    scanExitSeg (calls := stage2Calls stage2SubCalls) (G := G) (C := Cm) (s := sm)
      hInvR hbR hiR hcR hinner hie f.hcw (by intro e _ _ _; simp [WalkLocal])
  have hs₁' : s₁ = revExitS sm f.c := hs₁
  subst hs₁'
  -- 5. the merge, one step, from the token record's register
  obtain ⟨tok, htok⟩ := f.htok Cm sm hInvR hbR
  have htok₁ : lookupName (revExitS sm f.c).env "%t352.i" = some (.ptr tok) :=
    scanExit_tok sm (f.c - 1) f.c htok
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    walkIfEnd473_at (sub := stage2SubCalls) (G := G) (C := revExitC Cm)
      (s := revExitS sm f.c) hInv₁ rfl htok₁
  have hs₂' : s₂ = revMergeS sm f.c := hs₂
  rw [hs₂'] at hl₂
  -- the cells at the merge
  have hincM : lookupName (revMergeS sm f.c).env "%inc.i" =
      some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := by
    rw [revMergeS_inc, revExitS_inc, hincR]
  have hnepM : lookupName (revMergeS sm f.c).env "%nep" =
      some (.int 64 (BitVec.ofNat 64 G.nep)) := by
    rw [revMergeS_nep, revExitS_nep, hnepR]
  have hkM : (revMergeC Cm).k = C.k := by
    rw [revMergeC_k]; exact hkR
  have hpreM : (revMergeS sm f.c).pre = some "if.end473.i" := by
    show (some (revExitS sm f.c).pc : Option String) = some "if.end473.i"
    rw [show (revExitS sm f.c).pc = "if.end473.i" from rfl]
  refine ⟨Cm, sm, nSc, ?_, hl₂.inv', rfl, hpreM, hkM, hincM, hnepM, hnR, ?_⟩
  · -- the segment: the exit's one step and the merge's one, beside the visits
    have hexit : WalkSegment (stage2Calls stage2SubCalls) G C s
        (revExitC Cm) (revExitS sm f.c) (f.nH + f.nS + 3 + 3 + nSc + 1) := by
      rw [show f.nH + f.nS + 3 + 3 + nSc + 1 = (f.nH + f.nS + 3 + 3 + nSc) + 1
        from by omega]
      exact hsegP.trans hseg₁
    rw [show f.nH + f.nS + 8 + nSc = f.nH + f.nS + 3 + 3 + nSc + 1 + 1 from by omega]
    exact hexit.trans (WalkSegment.of_link hl₂)
  · -- the price: twenty-four fixed links, the price's two, and the six the budget shares
    have hnH := f.hnH
    have hnS := f.hnS
    have hbudget := f.hbudget
    have hguard : C.k < G.nep :=
      WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)
    have hΔ : 1 ≤ G.nep - C.k := by omega
    simp only [stage2EntryAllowance]
    omega

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.scanRoundsAt
#print axioms LeanLLVM.Refinement.WalkScope.runScanMerge_at
#print axioms LeanLLVM.Refinement.WalkScope.runLastMerge_at

end WalkScope
end LeanLLVM.Refinement
