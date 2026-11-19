/-
# The run's head and scan tail, composed into `RunFacts`

`JsonStage2WalkDispatchRunOfStaging` produces `RunFacts` from the staging, and
`JsonStage2WalkDispatchSegments` states its four segments.  Two of them were fields: the
head's chain and the scan's landing.  This module composes the whole bundle from the run's
own bundle (`HcontRunFacts`) and the class's chain to its check state.

## The composition

`runFacts_of_runBundle` fills `RunFacts`'s head, span, tail, landing, the scan's counter and
bound, the traversal and the budget from `HcontRunFacts` and the invariant, at any class's
check state with `nPre ≤ 8` and the class's own span at `nS ≤ 5`; `runFacts_of_defaultClass`
is the six default classes' producer at that shape.  Every field is derived; the bundle's
own callee and traversal rows are the supply.

The whitespace class's instance (`runFacts_of_wsFacts`, `wsRunHeadSeg`, `wsLandingSeg`,
`WsRunHead`) was retired with its route: at `126`/`127` the emitted dispatch reaches
`if.then413.i` through `if.else405.i`'s literal `0`, so the class is the refusal's and no
state the walk occupies builds `HcontFacts`.
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

/-! ### `RunFacts` at any class's check state

The classes that reach their own check state — the six default classes, whose byte before
the entry's end is whitespace and whose head chain is their prefix joined to
`contSwToLandSeg`'s four — take the same bundle and the class's own span, so the run's
fields are derived once here.

What the class supplies and what the bundle supplies are disjoint: the class supplies its
chain to the check state (`hPre`, at most the prefix's four and `contSwToLandSeg`'s four)
and the class-C span (`hSpan`, the byte's own leaf), and the bundle supplies everything from
the check state on — the stop, the landing's byte and its class, the tail and the traversal. -/

/-- **`RunFacts` from the run's bundle, at any class's check state.** -/
noncomputable def runFacts_of_runBundle {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (sl : State) (nPre : Nat)
    (hPre : WalkSegment (stage2Calls stage2SubCalls) G C s (ContAC₄ C) sl nPre)
    (hnPre : nPre ≤ 8) (f : HcontRunFacts G C sl) (hk : C.k + 1 < G.nep)
    {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
      (contWsSeamS C (wsSlAt G sl f.b35 f.ix f.v f.k) f.k f.x1) (ContTailStartC C)
      f.ss nS)
    (hnS : nS ≤ 5) :
    RunFacts G C s := by
  let w := wsRunHeadAt G C s sl nPre hPre hnPre f hk
  refine
    { x := hlastByte G C
      h8 := by
        show evalOperand s (.reg "%8") = some (.int 8 (hlastByte G C))
        exact LeanLLVM.evalOperand_reg_of hInv.iter.reg8
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
      ss := f.ss
      nS := nS
      hSpan := hSpan
      hnS := hnS
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
      hbound := contWsLatchAt_cond f
      hinc := contWsLatchAt_inc f
      hnep := contWsLatchAt_nep f
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
    {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
      (contWsSeamS C (wsSlAt G
        (contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35)
        f.b35 f.ix f.v f.k) f.k f.x1) (ContTailStartC C) f.ss nS)
    (hnS : nS ≤ 5) :
    RunFacts G C s :=
  runFacts_of_runBundle G C s hInv hblock _
    (nq + 4)
    (hPrefix.trans (contSwToLandSeg G C q5 hPrefix.inv' rfl hinc hnep hnext h5 hi63 hread
      hidx htok hgap hugt hread35))
    (by omega) f hk hSpan hnS

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.runFacts_of_runBundle
#print axioms LeanLLVM.Refinement.WalkScope.runFacts_of_defaultClass

end WalkScope
end LeanLLVM.Refinement
