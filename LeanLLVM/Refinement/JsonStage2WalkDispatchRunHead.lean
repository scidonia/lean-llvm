/-
# The run class's head and scan tail, composed into `RunFacts`

`JsonStage2WalkDispatchRunOfStaging` produces `RunFacts` from the staging, and
`JsonStage2WalkDispatchSegments` states its four segments.  Two of them were fields:
the head's chain and the scan's landing.  This module composes both from what the layer
already derives, and builds the whole bundle from `HcontFacts` — the whitespace class's
bundle — and the invariant.

## The head: `contPrefixLand` and the run

`HcontFacts`'s run is `contWsRunF`'s — a segment from the whitespace check (`ContAC₄ C`,
`contLandS …`) to the seam (`ContSeamC C`, `contWsSeamS …`) at a count
`N ≤ 5·(k - i) + 10` — and upstream of it is `contPrefixLand`'s eight links, the head's
chain to the whitespace check.  Composed, they are the head's chain to `if.else387.i` at
`8 + N`, which is inside `RunFacts`'s bound `12 + N` with four links to spare; the run's own
price (`contWsPriceAt`) is `RunFacts`'s `hprice` with the run's stop `k` for the scan's first
index and the lane's word for its bound.

The composition is at the bundle's own states, so the seam's byte cell is `HcontFacts`'s
`h8c`, the stop's bound is `contWsRunF`'s third conjunct, and the endpoint invariant is the
composed segment's.

## The span and the tail

The class-C span from the seam is `walkHeadChainCSeg`'s five links: `HcontFacts`'s seam byte
is at or above `110`, below `116` and not `116` (`hc110`, `hc116`, `hceq116`), so the span
ends at `HeadS413 (contWsSeamS …) x1` — exactly the tail's source
`contWsTailStart C (wsSlS …) k x1 x1`.  The tail is the bundle's `hTail`, which
`consumerTailSegAt` produced from the three callees' rows.

## The landing

`walkScanLinks457` (`JsonStage2WalkInduce`) states the landing's three links as a segment at
`land.rhs457.i`, and `HcontFacts` carries each of its premises at the scan's entry: the
seam's stored end (`h3S`, `hpos`, `hreadS`, `hbsS`), the pivot's two cells (`h47`, `hbit47`,
`hws47`), the three local facts (`hloc105`, `hloc96`, `hlatch`), and the entry's predecessor
and selection (`contWsEntry_pre`, `contWsEntry_hopS`).  The latch's two cells are
`latch_counter`'s and `contWsLatch_cond`'s.

## What the bundle then derives

`runFacts_of_wsFacts` fills `RunFacts`'s head, span, tail, landing, the scan's counter and
bound, the traversal and the budget from `HcontFacts` and the invariant — so the payload's
`trav` rows build the run's fields, and no `RunFacts` field is supplied at the whitespace
class beyond the bundle's own callee and traversal rows.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchSegments
import LeanLLVM.Refinement.JsonStage2WalkDispatchRunOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchLettersHead
import LeanLLVM.Refinement.JsonStage2WalkRevolutionSeg

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The head's chain, at the run's own count -/

/-- **The run class's head chain, as the data `RunFacts` reads.**  A structure rather than
an existential: `RunFacts` is a `Type`, and a `Prop`-valued existential cannot be eliminated
into one, so the head's bundle is its own data. -/
structure WsRunHead {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (f : HcontFacts G C s) : Type where
  /-- The run's count. -/
  N : Nat
  /-- The chain is inside `RunFacts`'s `12 + N`. -/
  hnH : 8 + N ≤ 12 + N
  /-- The head's chain to `if.else387.i`. -/
  seg : WalkSegment (stage2Calls stage2SubCalls) G C s (ContSeamC C)
    (contWsSeamS C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k f.x1) (8 + N)
  /-- The endpoint is the class-C span's entry. -/
  hblock : (ContSeamC C).block = "if.else387.i"
  /-- The endpoint carries the head's index. -/
  hk : (ContSeamC C).k = C.k
  /-- `%8` at the seam is the head's byte. -/
  h8 : evalOperand (contWsSeamS C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k
    f.x1) (.reg "%8") = some (.int 8 (hlastByte G C))
  /-- The stop's bound cell, which the latch's bound is. -/
  hcond : lookupName (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k).env "%cond350.i" =
    some (.int 64 (BitVec.ofNat 64 f.v.toNat))
  /-- The price at the byte allowance's eight per visit — `contWsPriceAt`'s own form. -/
  hprice : N + 8 * (f.v.toNat - 1 - f.k) ≤
    8 * (entryPos G (C.k + 1) - entryPos G C.k) + 5

/-- **The run class's head chain to `if.else387.i`.**  `contPrefixLand`'s eight links and
`contWsRunF`'s run: the count is `8 + N`, inside `RunFacts`'s `12 + N`; the endpoint is the
bundle's own seam state, whose `%8` is `hlastByte G C` by the composed segment's invariant;
the stop's bound cell is `contWsRunF`'s; and the price is `contWsPriceAt`'s.

`N` is the run's count and `f.k` its stop, so `RunFacts`'s `N` and `i` are this producer's
`N` and `f.k`. -/
noncomputable def wsRunHeadSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (f : HcontFacts G C s) (hk : C.k + 1 < G.nep) : WsRunHead G C s f := by
  classical
  -- the eight links to the whitespace check
  have hseg8 : WalkSegment (stage2Calls stage2SubCalls) G C s (ContAC₄ C)
      (contLandS C s f.x f.inc f.nep f.ep f.v f.ix f.b35) 8 :=
    contPrefixLand (G := G) (C := C) (s := s) hInv hblock f.h8 f.hlt91 f.hlt123 f.hlt125
      f.hne125 f.hinc f.hnep f.hnext f.h5 f.hi63 f.hread f.hidx5 f.htok5 f.hgap5 f.hugt
      f.hread35
  -- the run, at its own count
  let hc := contWsRunF G C (contLandS C s f.x f.inc f.nep f.ep f.v f.ix f.b35)
    (hcontRunFacts_of_contFacts G C s f hseg8.inv') hk
  let N := hc.choose
  have hspec := hc.choose_spec
  have hN : N ≤ 5 * (f.k - f.ix.toNat) + 10 := hspec.1
  have hsl : wsSlAt G (contLandS C s f.x f.inc f.nep f.ep f.v f.ix f.b35) f.b35 f.ix f.v f.k =
      wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k :=
    wsSlAt_transport G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k
  have hrun : WalkSegment (stage2Calls stage2SubCalls) G (ContAC₄ C)
      (contLandS C s f.x f.inc f.nep f.ep f.v f.ix f.b35) (ContSeamC C)
      (contWsSeamS C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k f.x1) N := by
    rw [← hsl]
    exact hspec.2.1
  have hcond : lookupName (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k).env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat)) := by
    rw [← hsl]
    exact hspec.2.2
  have hseg : WalkSegment (stage2Calls stage2SubCalls) G C s (ContSeamC C)
      (contWsSeamS C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k f.x1)
      (8 + N) := hseg8.trans hrun
  -- `%8` at the seam is the head's byte
  have hcell := hseg.inv'.iter.reg8
  have h8 : evalOperand (contWsSeamS C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k)
      f.k f.x1) (.reg "%8") = some (.int 8 (hlastByte G C)) := by
    show lookupName (contWsSeamS C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k)
      f.k f.x1).env "%8" = some (.int 8 (hlastByte G C))
    simpa only [hlastByte] using hcell
  exact ⟨N, by omega, hseg, rfl, rfl, h8, hcond,
    contWsPriceAt G C (contLandS C s f.x f.inc f.nep f.ep f.v f.ix f.b35)
      (hcontRunFacts_of_contFacts G C s f hseg8.inv') hN⟩

/-! ### The landing's three links, at the bundle's entry -/

/-- **The scan's landing, at `HcontFacts`'s own entry.**  `walkScanLinks457`'s three links,
with the bundle's fields at every premise, and the latch named at `contWsLatchF`. -/
theorem wsLandingSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (f : HcontFacts G C s) :
    WalkSegment (stage2Calls stage2SubCalls) G (TailCarryScan (ContTailStartC C) f.ev)
      (contWsEntryF f) { TailCarryScan (ContTailStartC C) f.ev with
        block := "while.body462.i" } (contWsLatchF f) 3 := by
  obtain ⟨s', hs', hseg⟩ :=
    walkScanLinks457 (calls := stage2Calls stage2SubCalls) (G := G)
      (C := TailCarryScan (ContTailStartC C) f.ev) (s := contWsEntryF f) f.hTail.inv' rfl
      (contWsEntry_pre f) hlastEntry_phiSel (contWsEntry_hopS f) f.h3S f.hpos f.hreadS
      f.hbsS f.hloc105 f.h47 f.hbit47 f.hws47 f.hloc96 f.hlatch
  rw [hs'] at hseg
  exact hseg

/-! ### The bundle -/

/-- **`RunFacts` from the whitespace class's bundle.**  The head is `wsRunHeadSeg`'s, the
span is `walkHeadChainCSeg`'s five at the bundle's seam byte, the tail is `f.hTail`, the
landing is `wsLandingSeg`, and the scan's counter, bound and budget are the latch's and the
price's.  Every field is derived; `HcontFacts`'s own callee and traversal rows are the
bundle's supply. -/
noncomputable def runFacts_of_wsFacts {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (f : HcontFacts G C s) (hk : C.k + 1 < G.nep) :
    RunFacts G C s := by
  -- 1. the head's chain, at `8 + N`
  let w := wsRunHeadSeg G C s hInv hblock f hk
  -- 2. the byte's span below the seam, at the bundle's own byte
  have hspan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
      (contWsSeamS C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k f.x1)
      (ContTailStartC C)
      (contWsTailStart C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k f.x1
        f.x1) 5 :=
    walkHeadChainCSeg (G := G) (C := ContSeamC C)
      (s := contWsSeamS C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k f.x1)
      w.seg.inv' rfl f.h8c f.hc110 f.hc116 f.hceq116
  -- 3. the landing's three links
  have hland := wsLandingSeg G C s f
  refine
    { x := hlastByte G C
      h8 := by
        show evalOperand s (.reg "%8") = some (.int 8 (hlastByte G C))
        simp only [evalOperand]
        exact hInv.iter.reg8
      hbit := by
        rw [← hlastByte_of_reg8 hInv f.h8]
        exact hlast_bit6_of_class f.hlt125 f.hne125
      N := w.N
      Cm := ContSeamC C
      sm := contWsSeamS C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k f.x1
      nH := 8 + w.N
      hHead := w.seg
      hnH := w.hnH
      hm := rfl
      hmk := rfl
      h8m := w.h8
      Cs := ContTailStartC C
      ss := contWsTailStart C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k
        f.x1 f.x1
      nS := 5
      hSpan := hspan
      hnS := le_rfl
      hs := rfl
      Ct := TailCarryScan (ContTailStartC C) f.ev
      st := contWsEntryF f
      hTail := f.hTail
      ht := rfl
      htk := rfl
      Cl := { TailCarryScan (ContTailStartC C) f.ev with block := "while.body462.i" }
      tl := contWsLatchF f
      hLatch := hland
      hl := rfl
      hk := rfl
      i := f.k
      c := f.v.toNat
      hcounter := latch_counter (contWsEntryF f) (BitVec.ofNat 64 f.k) f.a f.q f.x47
      hbound := contWsLatch_cond f w.hcond
      hinc := by
        rw [contWsLatch_inc]
        exact contWsSeamS_inc C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k
          f.x1 w.seg.inv'
      hnep := by
        rw [contWsLatch_nep]
        exact contWsSeamS_nep C (wsSlS G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k) f.k
          f.x1 w.seg.inv'
      hic := f.heicd
      hcw := by have := f.v.isLt; omega
      hbyte := f.hbyte
      hbudget := runBudget_of_wsPrice (N := w.N) (c := f.v.toNat) (i := f.k)
        (v := f.v.toNat) (k := f.k)
        (Δ := entryPos G (C.k + 1) - entryPos G C.k) le_rfl le_rfl w.hprice
      hspanStart := f.hspan
      hstart := f.hstart }

/-! ### `RunFacts` at any class's check state

`runFacts_of_wsFacts` is the class-C route's instance of one producer.  The classes that
reach their own check state — the six default classes, whose byte before the entry's end is
whitespace and whose head chain is their prefix joined to `contSwToLandSeg`'s four — take
the *same* bundle and the class's own span, so the run's fields are derived once here.

What the class supplies and what the bundle supplies are disjoint: the class supplies its
chain to the check state (`hPre`, at most the prefix's four and `contSwToLandSeg`'s four)
and the class-C span (`hSpan`, the byte's own leaf), and the bundle supplies everything from
the check state on — the stop, the landing's byte and its class, the tail and the traversal.
`runFacts_of_wsFacts` is this at `sl := contLandS …`, `nPre := 8` and
`walkHeadChainCSeg`'s span. -/

/-- **`RunFacts` from the run's bundle, at any class's check state.** -/
noncomputable def runFacts_of_runBundle {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (sl : State) (nPre : Nat)
    (hPre : WalkSegment (stage2Calls stage2SubCalls) G C s (ContAC₄ C) sl nPre)
    (hnPre : nPre ≤ 8) (f : HcontRunFacts G C sl) (hk : C.k + 1 < G.nep)
    (hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
      (contWsSeamS C (wsSlAt G sl f.b35 f.ix f.v f.k) f.k f.x1) (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl f.b35 f.ix f.v f.k) f.k f.x1 f.x1) 5) :
    RunFacts G C s := by
  let w := wsRunHeadAt G C s sl nPre hPre hnPre f hk
  refine
    { x := hlastByte G C
      h8 := by
        show evalOperand s (.reg "%8") = some (.int 8 (hlastByte G C))
        simp only [evalOperand]
        exact hInv.iter.reg8
      hbit := by
        rw [← hcontRunFacts_x1 f]
        exact f.hbit
      N := w.N
      Cm := ContSeamC C
      sm := contWsSeamS C (wsSlAt G sl f.b35 f.ix f.v f.k) f.k f.x1
      nH := nPre + w.N
      hHead := w.seg
      hnH := w.hnH
      hm := rfl
      hmk := rfl
      h8m := w.h8
      Cs := ContTailStartC C
      ss := contWsTailStart C (wsSlAt G sl f.b35 f.ix f.v f.k) f.k f.x1 f.x1
      nS := 5
      hSpan := hSpan
      hnS := le_rfl
      hs := rfl
      Ct := TailCarryScan (ContTailStartC C) f.ev
      st := contWsEntryAt f
      hTail := f.hTail
      ht := rfl
      htk := rfl
      Cl := { TailCarryScan (ContTailStartC C) f.ev with block := "while.body462.i" }
      tl := contWsLatchAt f
      hLatch := wsLandingSegAt f
      hl := rfl
      hk := rfl
      i := f.k
      c := f.v.toNat
      hcounter := latch_counter (contWsEntryAt f) (BitVec.ofNat 64 f.k) f.a f.q f.x47
      hbound := contWsLatchAt_cond f w.hcond
      hinc := by
        rw [contWsLatchAt_inc]
        exact contWsSeamS_inc C (wsSlAt G sl f.b35 f.ix f.v f.k) f.k f.x1 w.seg.inv'
      hnep := by
        rw [contWsLatchAt_nep]
        exact contWsSeamS_nep C (wsSlAt G sl f.b35 f.ix f.v f.k) f.k f.x1 w.seg.inv'
      hic := f.heicd
      hcw := by have := f.v.isLt; omega
      hbyte := f.hbyte
      hbudget := runBudget_of_wsPrice (N := w.N) (c := f.v.toNat) (i := f.k)
        (v := f.v.toNat) (k := f.k)
        (Δ := entryPos G (C.k + 1) - entryPos G C.k) le_rfl le_rfl w.hprice
      hspanStart := f.hspan
      hstart := f.hstart }

/-- **`RunFacts` at a default class.**  The class's prefix to `sw.default.i`
(`hPrefix`, at most four links: `.defaultValueLow`'s three, the four others' four) and
`contSwToLandSeg`'s shared four bring the head to the check state; the bundle and the
class's own span are the rest.  One theorem covers the six default classes, because what
differs between them is exactly the prefix — the pivots' carries and states — which enters
as the segment's index. -/
noncomputable def runFacts_of_defaultClass {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (q5 : State) (nq : Nat)
    (hPrefix : WalkSegment (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) q5 nq)
    (hnq : nq ≤ 4)
    {inc nep : BitVec 64}
    (hinc : evalOperand q5 (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand q5 (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    {ep : Nat} {v : BitVec 32}
    (h5 : lookupName (contSwOut q5 inc nep).env "%5" = some (.ptr ep))
    (hi63 : inc.toNat < 2 ^ 63)
    (hread : readBytes (contSwOut q5 inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    {ix : BitVec 64}
    (hidx : lookupName (contSwOut q5 inc nep).env "%idxprom.i" = some (.int 64 ix))
    (htok : lookupName (contSwOut q5 inc nep).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap : lookupName (contSwOut q5 inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    {b35 : UInt8}
    (hread35 : readBytes (contMidS C q5 inc nep ep v ix).mem ((G.b - 1) + v.toNat) 1 =
      some [b35])
    (f : HcontRunFacts G C
      (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35))
    (hk : C.k + 1 < G.nep)
    (hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
      (contWsSeamS C (wsSlAt G
        (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35)
        f.b35 f.ix f.v f.k) f.k f.x1) (ContTailStartC C)
      (contWsTailStart C (wsSlAt G
        (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35)
        f.b35 f.ix f.v f.k) f.k f.x1 f.x1) 5) :
    RunFacts G C s :=
  runFacts_of_runBundle G C s hInv hblock _
    (nq + 4)
    (hPrefix.trans (contSwToLandSeg G C q5 hPrefix.inv' rfl hinc hnep hnext h5 hi63 hread
      hidx htok hgap hugt hread35))
    (by omega) f hk hSpan

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.wsRunHeadSeg
#print axioms LeanLLVM.Refinement.WalkScope.wsLandingSeg
#print axioms LeanLLVM.Refinement.WalkScope.runFacts_of_wsFacts
#print axioms LeanLLVM.Refinement.WalkScope.runFacts_of_runBundle
#print axioms LeanLLVM.Refinement.WalkScope.runFacts_of_defaultClass

end WalkScope
end LeanLLVM.Refinement
