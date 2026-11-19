/-
# The last entry's run seam, as a state group

`RunLastFacts` (`JsonStage2WalkDispatchRun`) is the terminal run class's bundle, and its
`hTail` is the scan arm's three links from the seam at `TailStartC`.  `runLastFacts_of_staging`
(`JsonStage2WalkDispatchRunOfStaging`) takes that segment as an input, because the state it
starts from is further along the walk than the head: the whitespace run's stop `k`, the
seam's environment and the token record's stores are all new.

This module states that seam as a group — the analogue of `hcontRunFacts_of_seam`
(`JsonStage2WalkDispatchSeams`), which derives the continuing run class's bundle from its
seam — and derives the bundle from it:
`hlastRunTail_of_seam` is `scanTailSeg_at` at the group's own invariant and cells, and
`runLastFacts_of_seam` builds every field of `RunLastFacts` from the group and the
remaining pieces, so the tail enters as the composition's result rather than as an input.

## The seam's state

`hlastRunSeam` is the seam the run reaches: `seamS` at the last check state's leaf `sl`,
storing the run's stop `k` as the token's end and the bound `c` as `%cond350.i`.  Unlike
`hlastTail` (the scan-free class's seam), the two test cells are *different* numbers — that
is what makes the copy call's test `ult k c` true and the scan run — so the group carries
both and the inequality `k < c`.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchRunOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchSeams

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- **The last entry's run seam**: the token's end's run at the stop the whitespace skip
reached, on its else arm.  The stored end is `k` (the run's stop) and the bound is the
state's `%cond350.i`, so the copy call's test is `ult k c`. -/
def hlastRunSeam {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (sl : State) (k : Nat)
    (b8 : BitVec 8) : State :=
  seamS sl (BitVec.ofNat 64 k) b8 C.stage.tok

/-- **The last entry's run seam, as a state group.**  The invariant at `hlastRunSeam` and
the cells the tail's three calls read: the predecessor and the `phi`'s kind, the five
static registers, the root word across the kind store, the two test cells, the carry's two
bounds and the span the copy call's third link needs.

**Why a group.**  `RunLastFacts`'s `hTail` is stated at this seam, so deriving it from the
three call rows needs the seam's invariant and cells.  They are state data — the invariant
is the run's chain's `inv'`, and each cell is a lookup at the seam state — and no field is
a segment or a bundle. -/
structure HlastWsSeam {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (sl : State)
    (k c : Nat) (b8 : BitVec 8)
    (calls : HcontSeamCalls G (TailStartC C) (hlastRunSeam C sl k b8)) : Type where
  /-- The invariant at the seam, from the run's segment and the byte's span. -/
  hInv : WalkInv G (TailStartC C) (hlastRunSeam C sl k b8)
  /-- The `phi`'s predecessor, its operand and the operand's value. -/
  hpre : (hlastRunSeam C sl k b8).pre = some "if.else405.i"
  hphi : phiIncoming "if.else405.i"
    [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
     ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
     ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
     ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
     ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] =
    some (.imm (.int 32 (BitVec.ofNat 32 0)))
  hop : evalOperand (stateAt (hlastRunSeam C sl k b8).env (hlastRunSeam C sl k b8))
    (.imm (.int 32 (BitVec.ofNat 32 0))) = some (.int 32 calls.cA)
  /-- The five static registers the three calls read. -/
  hkind : lookupName (hlastRunSeam C sl k b8).env "%kind404.i" =
    some (.ptr ((TailStartC C).stage.tok + 16))
  hrd : lookupName (hlastRunSeam C sl k b8).env "%root_done.i" =
    some (.ptr (G.next0 + 8))
  hc : lookupName (hlastRunSeam C sl k b8).env "%c.i" =
    some (.ptr (TailCarry₂ (TailStartC C)).stage.c)
  ht : lookupName (hlastRunSeam C sl k b8).env "%t352.i" =
    some (.ptr (TailCarry₂ (TailStartC C)).stage.tok)
  ho : lookupName (hlastRunSeam C sl k b8).env "%z" =
    some (.ptr (TailCarry₂ (TailStartC C)).stage.z)
  /-- The root slot's word at the memory the first call reads. -/
  hread : readBytes
    (writeBytes (hlastRunSeam C sl k b8).mem ((TailStartC C).stage.tok + 16)
      (natToBytes calls.cA.toNat 4)) (G.next0 + 8) 4 =
    some (natToBytes calls.rdv.toNat 4)
  /-- The copy call's two test cells: the run's stop and the bound. -/
  hei : lookupName (hlastRunSeam C sl k b8).env "%ee.1.i" =
    some (.int 64 (BitVec.ofNat 64 k))
  hcd : lookupName (hlastRunSeam C sl k b8).env "%cond350.i" =
    some (.int 64 (BitVec.ofNat 64 c))
  /-- The span the copy call's third link needs, and the test's two values. -/
  hinner : c - k ≤ (TailStartC C).inner
  heicd : k < c
  hcd64 : c < 2 ^ 64
  /-- The carry's two bounds the tail's contracts read. -/
  htight : (TailStartC C).events.length ≤ (TailStartC C).k
  hklt : (TailStartC C).k < G.nep

/-- **The last entry's scan tail, from the seam group.**  `scanTailSeg_at` at the group's
own invariant and cells: every premise is a field or one of the three call rows, so the
tail is a consequence of the group, not an input. -/
theorem hlastRunTail_of_seam {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (sl : State)
    (k c : Nat) (b8 : BitVec 8)
    (calls : HcontSeamCalls G (TailStartC C) (hlastRunSeam C sl k b8))
    (seam : HlastWsSeam G C sl k c b8 calls) (ev : EventRecord)
    (happ : s2ScalarValueAppend calls.r₁.mem calls.r₂.mem
      (TailCarry₂ (TailStartC C)).stage.z ev.encodedBytes) :
    WalkSegment (stage2Calls stage2SubCalls) G (TailStartC C) (hlastRunSeam C sl k b8)
      (TailCarryScan (TailStartC C) ev)
      (ScanEntry (hlastRunSeam C sl k b8) calls.r₁ calls.r₂ calls.r₃ k c calls.cA
        calls.rdv calls.xA) 3 :=
  scanTailSeg_at G (TailStartC C) (hlastRunSeam C sl k b8) calls ev happ calls.hzread_mem
    seam.hInv rfl "if.else405.i" (op := .imm (.int 32 (BitVec.ofNat 32 0)))
    seam.hpre seam.hphi seam.hop seam.hkind seam.hrd seam.hread seam.hc seam.ht seam.ho
    seam.htight seam.hklt seam.hei seam.hcd seam.hinner seam.heicd seam.hcd64

/-- **The last entry's run bundle, from the entry's evidence and the seam group.**  The
head's chain, the byte's span, the seam's group and the three call rows are the inputs;
the tail is `hlastRunTail_of_seam`'s, and every other field is `runLastFacts_of_staging`'s
derivation at the same terms. -/
noncomputable def runLastFacts_of_seam {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (N : Nat)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 11 + N)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (sl : State) (k c : Nat) (b8 : BitVec 8)
    {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm (TailStartC C)
      (hlastRunSeam C sl k b8) nS)
    (hnS : nS ≤ 5)
    (calls : HcontSeamCalls G (TailStartC C) (hlastRunSeam C sl k b8))
    (seam : HlastWsSeam G C sl k c b8 calls) (ev : EventRecord)
    (happ : s2ScalarValueAppend calls.r₁.mem calls.r₂.mem
      (TailCarry₂ (TailStartC C)).stage.z ev.encodedBytes)
    {Cl : WalkCarry G} {tl : State}
    (hLatch : WalkSegment (stage2Calls stage2SubCalls) G
      (TailCarryScan (TailStartC C) ev)
      (ScanEntry (hlastRunSeam C sl k b8) calls.r₁ calls.r₂ calls.r₃ k c calls.cA
        calls.rdv calls.xA) Cl tl 3)
    (hl : Cl.block = "while.body462.i") (hkC : Cl.k = C.k)
    (i c' : Nat)
    (hcounter : lookupName tl.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbound : lookupName tl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c')))
    (hic : i < c')
    (hbyte : ScanVisits G c' i)
    (hstop : i = terminalStop G.bs (entryPos G C.k))
    (hN : N = i - entryPos G C.k)
    (hc : c' = G.n) :
    RunLastFacts G C s :=
  { x := hlastByte G C
    h8 := by
      show evalOperand s (.reg "%8") = some (.int 8 (hlastByte G C))
      exact LeanLLVM.evalOperand_reg_of hInv.iter.reg8
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
      have hcell := hHead.inv'.iter.reg8
      rw [hmk] at hcell
      exact LeanLLVM.evalOperand_reg_of hcell
    Cs := TailStartC C
    ss := hlastRunSeam C sl k b8
    nS := nS
    hSpan := hSpan
    hnS := hnS
    hs := rfl
    Ct := TailCarryScan (TailStartC C) ev
    st := ScanEntry (hlastRunSeam C sl k b8) calls.r₁ calls.r₂ calls.r₃ k c calls.cA
      calls.rdv calls.xA
    hTail := hlastRunTail_of_seam G C sl k c b8 calls seam ev happ
    ht := rfl
    htk := rfl
    Cl := Cl
    tl := tl
    hLatch := hLatch
    hl := hl
    hk := hkC
    i := i
    c := c'
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
    hstart := (terminalStop_bounds (C := C) (i := i) (c := c') (N := N) hstop hN hc).1
    hNdoc := (terminalStop_bounds (C := C) (i := i) (c := c') (N := N) hstop hN hc).2.1
    hspanDoc := (terminalStop_bounds (C := C) (i := i) (c := c') (N := N) hstop hN hc).2.2 }

/-- **The last entry's run arm, from the seam group.**  `LastEntryArm.run` at the bundle
the group produces. -/
noncomputable def lastEntryArm_run_of_seam {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s)
    (hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (N : Nat)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hnH : nH ≤ 11 + N)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (sl : State) (k c : Nat) (b8 : BitVec 8)
    {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm (TailStartC C)
      (hlastRunSeam C sl k b8) nS)
    (hnS : nS ≤ 5)
    (calls : HcontSeamCalls G (TailStartC C) (hlastRunSeam C sl k b8))
    (seam : HlastWsSeam G C sl k c b8 calls) (ev : EventRecord)
    (happ : s2ScalarValueAppend calls.r₁.mem calls.r₂.mem
      (TailCarry₂ (TailStartC C)).stage.z ev.encodedBytes)
    {Cl : WalkCarry G} {tl : State}
    (hLatch : WalkSegment (stage2Calls stage2SubCalls) G
      (TailCarryScan (TailStartC C) ev)
      (ScanEntry (hlastRunSeam C sl k b8) calls.r₁ calls.r₂ calls.r₃ k c calls.cA
        calls.rdv calls.xA) Cl tl 3)
    (hl : Cl.block = "while.body462.i") (hkC : Cl.k = C.k)
    (i c' : Nat)
    (hcounter : lookupName tl.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbound : lookupName tl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c')))
    (hic : i < c')
    (hbyte : ScanVisits G c' i)
    (hstop : i = terminalStop G.bs (entryPos G C.k))
    (hN : N = i - entryPos G C.k)
    (hc : c' = G.n) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .run (runLastFacts_of_seam G C s hInv hbit N hHead hnH hm hmk sl k c b8 hSpan hnS calls
    seam ev happ hLatch hl hkC i c' hcounter hbound hic hbyte hstop hN hc)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hlastRunTail_of_seam
#print axioms LeanLLVM.Refinement.WalkScope.runLastFacts_of_seam
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_run_of_seam

end WalkScope
end LeanLLVM.Refinement
