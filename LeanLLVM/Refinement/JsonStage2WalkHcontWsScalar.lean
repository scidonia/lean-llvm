/-
# The numeral route's whitespace run: the last cell of the continuing matrix

The plain-value class's arm (`.scalar`, `HcontScalarFacts`) takes the document byte
before the entry's end to be one of the three non-whitespace classes: its `hb` is
`HcontByteRoute`, and each of the three leaves reaches `if.end372.i` and then
`if.then413.i` with no run.  The fourth class — the whitespace byte — is the run class
on the high-byte route (`HcontFacts`) and on the default arm (`RunFacts`), but neither
bundle's head is this route's: `HcontFacts`'s prefix is the head chain's
`contPrefixLand`, `RunFacts`'s takes `hbit = 0` and its span below `if.else387.i`, and
this route's head is the numeral's four pivots and its tag test is `1`.

So `.value` × `wsByte` had no arm, and the continuing census was not total: a numeral
followed by whitespace is admitted by the header, its head byte is the plain-value
class, and every constructor excluded it.  This module states the missing arm's evidence
and proves it, rather than supplying it.

## The run, restated at the numeral prefix

The whitespace run reads only cells: the byte before the entry's end (`%35`), the
entry's index (`%idxprom.i`), the bound (`%cond350.i`), and the document's bytes.  Its
machinery (`wsEntryAt33/35/37`, `wsFirstSeg43/46/48`, `wsRun`, `wsStopAt`, `wsSlAt`) is
stated at an arbitrary check state `sl`, so the numeral route takes it as it is; what it
does not have is this route's **seam**.  `wsSeamSeg` leaves `if.end372.i` for
`if.else387.i` (the tag test clear), and this route's tag test is `1`, so the seam is
one link to `if.then413.i` — `scWsSeamSeg`, `WalkLink.if_end372_i_true_at` at the run's
stop.

The composition is the four pieces, in the order the work names them:

| piece | statement | links |
|---|---|---|
| the prefix's own chain at `scS₅` | `scPrefixLand` | `8` |
| the whitespace skip at `%35` and `if.end372.i` | `scWsRunAt33/35/37` (`scWsAfterPreAt`) | `N ≤ 5·(k - ix) + 10` |
| the byte's span: `if.end372.i`'s true arm | `scWsSeamSeg` (inside the `N` above) | `1` |
| the scan tail, the latch, the visits, the merge | `hTail`, `walkScanLinks457`, `scanRoundsAt`, `scanExitSeg`, `walkIfEnd473_at` | `3 + 3 + nSc + 1 + 1` |

`N` counts the entry dispatch (two or three links), the first visit (four or five), the
run's visits (five each) and the seam; `nSc ≤ 4·(v - 1 - k)` counts the scan's visits at
the four-per-visit price `scanRoundsAt` states.

## What the arm carries, and what it establishes

`HcontScalarWsFacts` is the document's and the callees': the head's class and the lane
(`HcontScalarPrefix`'s fields, without the three-route `hb` the run replaces), the
byte's class at the entry's end with the run's stop and its per-index facts, the tail's
three calls as their segment, the landing's byte and the visits' totality.  It carries
no `WalkInv` consequence.  The tail's segment is a field for the same reason
`HcontScalarFacts.hTail` is: `scanTailSeg_of_calls` produces it from the seam's three
call rows, and the row tier above this module does that, so the arm's producer is
row-based and the evidence is derived.

## The price

The path's fixed part is `8 + 3 + 3 + 1 + 1 = 16` links and the price's own two, so
`18 + N + nSc ≤ 32·Δk + 8·ΔA`: `N ≤ 5·(k - ix) + 10`, `nSc ≤ 4·(v - 1 - k)`, and the
run and the visit share the entry's byte credit (`wsPrice`), which is
`N + 8·(v - 1 - k) ≤ 8·ΔA + 5`.  So the arm spends the entry allowance and the entry's
bytes, exactly as the whitespace class's other two arms do.
-/
import LeanLLVM.Refinement.JsonStage2WalkHcontScalar
import LeanLLVM.Refinement.JsonStage2WalkDispatchRun
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessHlast
import LeanLLVM.Refinement.JsonStage2WalkDispatchThreeOfRun

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The route's states

The check state is the prefix's `sLand`; the stop is `wsSlAt` at it; the seam is
`if.end372.i`'s true arm at the stop; the tail's start, the scan's entry and the latch
are the three calls' `TailS₁…₃` and `Latch462S` at that seam. -/

/-- The numeral route's stop: the whitespace skip's last state at `if.end372.i`. -/
abbrev scWsSl {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8)
    (k : Nat) : State :=
  wsSlAt G (sLand C s x inc nep ep v ix b35) b35 ix v k

/-- **The numeral route's seam**: `if.end372.i`'s tag-true arm at the run's stop.  Its
predecessor is the stop's block, so the tail's kind `phi` reads `if.end372.i`'s literal
`7`; `seamFin`'s cells and memory are the else seam's (`seamS`), which is why the
route's own tail and landing read the same peels at one state term. -/
def scWsSeam {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q4 : State) (k : Nat)
    (x : BitVec 8) : State :=
  { seamS q4 (BitVec.ofNat 64 k) x C.stage.tok with pc := "if.then413.i" }

/-- The numeral route's scan entry: the tail's end at `land.rhs457.i`, its first index the
run's stop and its bound the lane's word. -/
def scWsEntry {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q4 : State) (k : Nat)
    (x : BitVec 8) (v : BitVec 32) (r₁ r₂ r₃ : CallOutcome) (cA rdv xA : BitVec 32) :
    State :=
  ScanEntry (scWsSeam C q4 k x) r₁ r₂ r₃ k v.toNat cA rdv xA

/-- The numeral route's latch: the scan's first visit. -/
def scWsLatch {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q4 : State) (k : Nat)
    (x : BitVec 8) (v : BitVec 32) (r₁ r₂ r₃ : CallOutcome) (cA rdv xA : BitVec 32)
    (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8) : State :=
  Latch462S (scWsEntry C q4 k x v r₁ r₂ r₃ cA rdv xA) idx a q x47

/-! ### The prefix's cells, at the route's check state

`wsSlAt`/`wsPreSAt` read `%35`, `%idxprom.i` and `%cond350.i`; the prefix's check state
has all three, and `%8`/`%end.i` are the loop head's. -/

/-- `%35` at the numeral route's check state, in the form the run's entry dispatch reads
it. -/
theorem scWsLand_35 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    evalOperand (sLand C s x inc nep ep v ix b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) := by
  simp only [evalOperand]
  exact sLand_35 C s x inc nep ep v ix b35

/-- `%idxprom.i` at the numeral route's check state is the loop head's. -/
theorem scWsLand_idx {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) :
    lookupName (sLand C s x inc nep ep v ix b35).env "%idxprom.i" =
      lookupName s.env "%idxprom.i" := by
  simp only [sLand, stateAt, cells, sEnd, condEnd349OutAt, cte345OutAt, scS₅, scS₄, scS₃,
    scS₂, scS₁, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%8` at the numeral route's check state is the head's byte. -/
theorem scWsLand_8 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (h : lookupName s.env "%8" = some (.int 8 x)) :
    lookupName (sLand C s x inc nep ep v ix b35).env "%8" = some (.int 8 x) := by
  rw [sLand_env8]
  exact h

/-- `%end.i` at the numeral route's check state is the loop head's. -/
theorem scWsLand_end {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (h : lookupName s.env "%end.i" = some (.ptr (C.stage.tok + 8))) :
    lookupName (sLand C s x inc nep ep v ix b35).env "%end.i" =
      some (.ptr (C.stage.tok + 8)) := by
  rw [sLand_envEnd]
  exact h

/-! ### The seam's one link

`WalkLink.if_end372_i_true_at` states the block's step with its target named, at the tag
test's `1` arm: the token's end `phi`, the store at `%end.i`, the two tests and the edge.
The run's stop carries `if.end372.i`, so the link is one step from it to `scWsSeam`. -/

/-- **The numeral route's seam link**: `if.end372.i`'s step, from the run's stop to the
tail's start at the tag test's true arm.  The `phi` selects the stop's own index cell
(`%ee.0.i238` on the leaf edges), the stored end is the run's stop `k`, and the byte's
test is the class's `1`. -/
theorem scWsSeamSeg {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) {k : Nat} {x : BitVec 8} {p : String}
    (hInv : WalkInv G { C with block := "if.end372.i" } sl)
    (hpre : sl.pre = some p)
    (hin : phiIncoming p
      [("cond.end349.i", (Operand.reg "%idxprom.i")),
       ("while.body370.i", (Operand.reg "%cond350.i")),
       ("LeafBlock43", (Operand.reg "%ee.0.i238")),
       ("LeafBlock46", (Operand.reg "%ee.0.i238")),
       ("LeafBlock48", (Operand.reg "%ee.0.i238")),
       ("LeafBlock33", (Operand.reg "%cond350.i")),
       ("LeafBlock35", (Operand.reg "%cond350.i")),
       ("LeafBlock37", (Operand.reg "%cond350.i"))] = some (.reg "%ee.0.i238"))
    (hi : lookupName sl.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 k)))
    (hend : lookupName sl.env "%end.i" = some (.ptr (C.stage.tok + 8)))
    (h8 : lookupName sl.env "%8" = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1) :
    WalkSegment calls G { C with block := "if.end372.i" } sl
      { C with block := "if.then413.i" } (scWsSeam C sl k x) 1 := by
  have hv : evalOperand sl (.reg "%ee.0.i238") =
      some (.int 64 (BitVec.ofNat 64 k)) := hi
  obtain ⟨s', hl, hs⟩ :=
    WalkLink.if_end372_i_true_at (calls := calls) (G := G)
      (C := { C with block := "if.end372.i" }) (s := sl) hInv rfl hpre hin hv hend h8 hbit
  have hs' : s' = scWsSeam C sl k x := hs
  rw [hs'] at hl
  exact WalkSegment.of_link hl

/-! ### The run at the numeral prefix

`contWsAfterPreAt`'s composition at this route's seam: the caller's entry dispatch, the
first visit at the entry's own byte, `wsRun` from the latch it reaches, and the seam's
one link — the last of those being `scWsSeamSeg` here rather than `wsSeamSeg`, and the
endpoint `scWsSeam` rather than `contWsSeamS`.  Every other piece is the shared
machinery's, unchanged. -/

/-- **The run's tail from the preheader, at the numeral route's seam.**  The first visit
at the entry's own byte `i`, the run from the latch to the stop `k`, and the seam — with
the stop's `%cond350.i` cell as the third conjunct.  The entry dispatch is the caller's,
so the source is the state parameter. -/
theorem scWsAfterPreAt {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (v : BitVec 32) (ix : BitVec 64) (pre : State) {k : Nat} {b8 : BitVec 8}
    {j : Nat}
    (hEntry : WalkSegment calls G (ContAC₄ C) sl
      { C with block := "land.rhs.i.preheader" } pre j)
    (hj : j ≤ 4)
    (hpc : pre.pc = "land.rhs.i.preheader")
    (hidx : lookupName pre.env "%idxprom.i" = some (.int 64 ix))
    (hcond : lookupName pre.env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)))
    (hiv : ix.toNat < v.toNat) (hvsub : v.toNat - ix.toNat ≤ C.inner)
    (hcw : v.toNat < 2 ^ 64) (hi63 : ix.toNat < 2 ^ 63) (hgn : ix.toNat < G.n)
    (hik : ix.toNat < k) (hkv : k < v.toNat)
    (hcontI : wsCont G ix.toNat)
    (hcls : ∀ q, ix.toNat < q → q < k → wsCont G q)
    (hstop : wsStop G k)
    (hpos : ∀ q, ix.toNat < q → q ≤ k → q < 2 ^ 63)
    (hqn : ∀ q, ix.toNat < q → q ≤ k → q < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (h8sl : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
      ix.toNat v.toNat k).env "%8" = some (.int 8 b8))
    (hendsl : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
      ix.toNat v.toNat k).env "%end.i" = some (.ptr (C.stage.tok + 8)))
    (hbitsl : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1) :
    ∃ N, N ≤ 5 * (k - ix.toNat) + 10 ∧
      WalkSegment calls G (ContAC₄ C) sl { C with block := "if.then413.i" }
        (scWsSeam C (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
          ix.toNat v.toNat k) k b8) N ∧
      lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
        ix.toNat v.toNat k).env "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  -- the preheader's entry fact and the first visit's landing fact
  have hie : (BitVec.ofNat 64 ix.toNat) = ix := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hscan : ScanEntered { pre with pc := "land.rhs.i", pre := some pre.pc }
      "land.rhs.i.preheader" "%idxprom.i" "%cond350.i" C.inner := by
    refine ⟨ix.toNat, v.toNat, hvsub, hiv, hcw, ?_, ?_, ?_⟩
    · show some pre.pc = some "land.rhs.i.preheader"
      rw [hpc]
    · show lookupName pre.env "%idxprom.i" = some (.int 64 (BitVec.ofNat 64 ix.toNat))
      simpa only [hie] using hidx
    · exact hcond
  have hsc2 : ScanCount (landRhsIOutAt G (landRhsPreheaderOutAt pre)
      (BitVec.ofNat 64 ix.toNat) (scanB G (BitVec.ofNat 64 ix.toNat)))
      "%ee.0.i238" "%cond350.i" C.inner := by
    rw [scanB_ofNat G hi63]
    refine ⟨ix.toNat, v.toNat, hvsub, hiv, hcw, ?_, ?_⟩
    · simpa only [wsLandS] using wsLandS_ee G (landRhsPreheaderOutAt pre) ix.toNat
    · simpa only [wsLandS] using
        wsLandS_cond G (landRhsPreheaderOutAt pre) ix.toNat hcond
  -- the first visit, by the entry's own byte's class
  have hFirst : ∃ first, first ≤ 5 ∧
      WalkSegment calls G { C with block := "land.rhs.i.preheader" } pre
        { C with block := "while.body370.i" }
        (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat) first := by
    rcases hcontI with ⟨h13, hws0⟩ | ⟨h13, h32, hq13⟩ | ⟨h13, h32, hq32⟩
    · exact ⟨4, by omega, wsFirstSeg43 G C pre hEntry.inv' hpc hscan
        (by simpa only [evalOperand, landRhsPreheaderOutAt, hie] using hidx)
        rfl hi63 hgn halen hevlen h13 hws0 hsc2⟩
    · exact ⟨5, by omega, wsFirstSeg46 G C pre hEntry.inv' hpc hscan
        (by simpa only [evalOperand, landRhsPreheaderOutAt, hie] using hidx)
        rfl hi63 hgn halen hevlen h13 h32 hq13 hsc2⟩
    · exact ⟨5, by omega, wsFirstSeg48 G C pre hEntry.inv' hpc hscan
        (by simpa only [evalOperand, landRhsPreheaderOutAt, hie] using hidx)
        rfl hi63 hgn halen hevlen h13 h32 hq32 hsc2⟩
  obtain ⟨first, hfirst, hsegFirst⟩ := hFirst
  -- the run from the latch the first visit reaches
  have hiLatch : lookupName (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat).env
      "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 ix.toNat)) := by
    rcases hcontI with ⟨h13, -⟩ | ⟨h13, h32, -⟩ | ⟨h13, h32, -⟩
    · exact wsLeafS_43_ee G (landRhsPreheaderOutAt pre) ix.toNat h13
    · exact wsLeafS_46_ee G (landRhsPreheaderOutAt pre) ix.toNat h13 h32
    · exact wsLeafS_48_ee G (landRhsPreheaderOutAt pre) ix.toNat h13 h32
  have hcLatch : lookupName (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat).env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
    rcases hcontI with ⟨h13, -⟩ | ⟨h13, h32, -⟩ | ⟨h13, h32, -⟩
    · exact wsLeafS_43_cond G (landRhsPreheaderOutAt pre) ix.toNat v.toNat h13 hcond
    · exact wsLeafS_46_cond G (landRhsPreheaderOutAt pre) ix.toNat v.toNat h13 h32 hcond
    · exact wsLeafS_48_cond G (landRhsPreheaderOutAt pre) ix.toNat v.toNat h13 h32 hcond
  obtain ⟨n, hn, hsegRun, -, heeSl, hcondSl⟩ :=
    wsRun (calls := calls) G { C with block := "while.body370.i" }
      (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
      hsegFirst.inv' rfl hiLatch hcLatch hcw hik hkv hcls hstop hpos hqn halen hevlen
  -- the seam at the stop's class
  have hSeam : ∃ seam, seam ≤ 1 ∧
      WalkSegment calls G { C with block := "if.end372.i" }
        (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat) ix.toNat v.toNat k)
        { C with block := "if.then413.i" }
        (scWsSeam C (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
          ix.toNat v.toNat k) k b8) seam := by
    rcases hstop with ⟨h13, hws⟩ | ⟨h13, h32, hq⟩ | ⟨h13, h32, hq⟩
    · have hpre : (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
          ix.toNat v.toNat k).pre = some "LeafBlock43" :=
        wsStopAt_pre43 G _ (v := v.toNat) hik h13
      exact ⟨1, by omega, scWsSeamSeg G C _ hsegRun.inv' hpre
        (by decide) heeSl hendsl h8sl hbitsl⟩
    · have hpre : (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
          ix.toNat v.toNat k).pre = some "LeafBlock46" :=
        wsStopAt_pre46 G _ (v := v.toNat) hik h13 h32
      exact ⟨1, by omega, scWsSeamSeg G C _ hsegRun.inv' hpre
        (by decide) heeSl hendsl h8sl hbitsl⟩
    · have hpre : (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt pre) ix.toNat)
          ix.toNat v.toNat k).pre = some "LeafBlock48" :=
        wsStopAt_pre48 G _ (v := v.toNat) hik h13 h32
      exact ⟨1, by omega, scWsSeamSeg G C _ hsegRun.inv' hpre
        (by decide) heeSl hendsl h8sl hbitsl⟩
  obtain ⟨seam, hseam, hsegSeam⟩ := hSeam
  refine ⟨j + first + n + seam, by omega, ?_, hcondSl⟩
  exact ((hEntry.trans hsegFirst).trans hsegRun).trans hsegSeam

/-! ### The three entry classes, at the numeral route

The byte before the entry's end is one of the four whitespace bytes, so the entry
dispatch is `LeafBlock33`'s (two links), `LeafBlock35`'s or `LeafBlock37`'s (three), and
the stop's leaf is the same class.  The three wrappers are `contWsRunAt33/35/37`'s
twins: the class's `pre` at the check state, then `scWsAfterPreAt`. -/

/-- **The run at `LeafBlock33`'s entry class**, at the numeral route's check state. -/
theorem scWsRunAt33 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (b35 : UInt8) {ix : BitVec 64} {v : BitVec 32} {k : Nat} {b8 : BitVec 8}
    (hInv : WalkInv G (ContAC₄ C) sl)
    (h35 : evalOperand sl (.reg "%35") = some (.int 8 (cont35 b35)))
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1)
    (hws : evalICmp .ule (cont35 b35 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1)
    (hidx0 : lookupName sl.env "%idxprom.i" = some (.int 64 ix))
    (hcond0 : lookupName sl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)))
    (hiv : ix.toNat < v.toNat) (hvsub : v.toNat - ix.toNat ≤ C.inner)
    (hcw : v.toNat < 2 ^ 64) (hi63 : ix.toNat < 2 ^ 63) (hgn : ix.toNat < G.n)
    (hik : ix.toNat < k) (hkv : k < v.toNat)
    (hcontI : wsCont G ix.toNat)
    (hcls : ∀ q, ix.toNat < q → q < k → wsCont G q)
    (hstop : wsStop G k)
    (hpos : ∀ q, ix.toNat < q → q ≤ k → q < 2 ^ 63)
    (hqn : ∀ q, ix.toNat < q → q ≤ k → q < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (h8sl : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock33OutAt
      (nodeBlock41OutAt sl (cont35 b35)) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
      "%8" = some (.int 8 b8))
    (hendsl : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock33OutAt
      (nodeBlock41OutAt sl (cont35 b35)) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
      "%end.i" = some (.ptr (C.stage.tok + 8)))
    (hbitsl : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1) :
    ∃ N, N ≤ 5 * (k - ix.toNat) + 10 ∧
      WalkSegment calls G (ContAC₄ C) sl { C with block := "if.then413.i" }
        (scWsSeam C (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock33OutAt
          (nodeBlock41OutAt sl (cont35 b35)) (cont35 b35))) ix.toNat) ix.toNat v.toNat k)
          k b8) N ∧
      lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock33OutAt
        (nodeBlock41OutAt sl (cont35 b35)) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
        "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  have hpre := wsPreSAt_33 sl b35 hb13
  have hidx : lookupName (leafBlock33OutAt (nodeBlock41OutAt sl (cont35 b35))
      (cont35 b35)).env "%idxprom.i" = some (.int 64 ix) := by
    rw [← hpre, wsPreSAt_idx]; exact hidx0
  have hcond : lookupName (leafBlock33OutAt (nodeBlock41OutAt sl (cont35 b35))
      (cont35 b35)).env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
    rw [← hpre, wsPreSAt_cond]; exact hcond0
  exact scWsAfterPreAt G C sl v ix _ (j := 2)
    (wsEntryAt33 G C sl b35 hInv h35 hb13 hws) (by omega)
    rfl hidx hcond hiv hvsub hcw hi63 hgn hik hkv hcontI hcls hstop hpos hqn halen hevlen
    h8sl hendsl hbitsl

/-- **The run at `LeafBlock35`'s entry class**, at the numeral route's check state. -/
theorem scWsRunAt35 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (b35 : UInt8) {ix : BitVec 64} {v : BitVec 32} {k : Nat} {b8 : BitVec 8}
    (hInv : WalkInv G (ContAC₄ C) sl)
    (h35 : evalOperand sl (.reg "%35") = some (.int 8 (cont35 b35)))
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hbq13 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 1)
    (hidx0 : lookupName sl.env "%idxprom.i" = some (.int 64 ix))
    (hcond0 : lookupName sl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)))
    (hiv : ix.toNat < v.toNat) (hvsub : v.toNat - ix.toNat ≤ C.inner)
    (hcw : v.toNat < 2 ^ 64) (hi63 : ix.toNat < 2 ^ 63) (hgn : ix.toNat < G.n)
    (hik : ix.toNat < k) (hkv : k < v.toNat)
    (hcontI : wsCont G ix.toNat)
    (hcls : ∀ q, ix.toNat < q → q < k → wsCont G q)
    (hstop : wsStop G k)
    (hpos : ∀ q, ix.toNat < q → q ≤ k → q < 2 ^ 63)
    (hqn : ∀ q, ix.toNat < q → q ≤ k → q < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (h8sl : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock35OutAt
      (wsP39Out (wsP41Out sl b35) b35) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
      "%8" = some (.int 8 b8))
    (hendsl : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock35OutAt
      (wsP39Out (wsP41Out sl b35) b35) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
      "%end.i" = some (.ptr (C.stage.tok + 8)))
    (hbitsl : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1) :
    ∃ N, N ≤ 5 * (k - ix.toNat) + 10 ∧
      WalkSegment calls G (ContAC₄ C) sl { C with block := "if.then413.i" }
        (scWsSeam C (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock35OutAt
          (wsP39Out (wsP41Out sl b35) b35) (cont35 b35))) ix.toNat) ix.toNat v.toNat k)
          k b8) N ∧
      lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock35OutAt
        (wsP39Out (wsP41Out sl b35) b35) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
        "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  have hpre := wsPreSAt_35 sl b35 hb13 hb32
  have hidx : lookupName (leafBlock35OutAt (wsP39Out (wsP41Out sl b35) b35)
      (cont35 b35)).env "%idxprom.i" = some (.int 64 ix) := by
    rw [← hpre, wsPreSAt_idx]; exact hidx0
  have hcond : lookupName (leafBlock35OutAt (wsP39Out (wsP41Out sl b35) b35)
      (cont35 b35)).env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
    rw [← hpre, wsPreSAt_cond]; exact hcond0
  exact scWsAfterPreAt G C sl v ix _ (j := 3)
    (wsEntryAt35 G C sl b35 hInv h35 hb13 hb32 hbq13) (by omega)
    rfl hidx hcond hiv hvsub hcw hi63 hgn hik hkv hcontI hcls hstop hpos hqn halen hevlen
    h8sl hendsl hbitsl

/-- **The run at `LeafBlock37`'s entry class**, at the numeral route's check state. -/
theorem scWsRunAt37 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (b35 : UInt8) {ix : BitVec 64} {v : BitVec 32} {k : Nat} {b8 : BitVec 8}
    (hInv : WalkInv G (ContAC₄ C) sl)
    (h35 : evalOperand sl (.reg "%35") = some (.int 8 (cont35 b35)))
    (hb13 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0)
    (hbq32 : evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 1)
    (hidx0 : lookupName sl.env "%idxprom.i" = some (.int 64 ix))
    (hcond0 : lookupName sl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)))
    (hiv : ix.toNat < v.toNat) (hvsub : v.toNat - ix.toNat ≤ C.inner)
    (hcw : v.toNat < 2 ^ 64) (hi63 : ix.toNat < 2 ^ 63) (hgn : ix.toNat < G.n)
    (hik : ix.toNat < k) (hkv : k < v.toNat)
    (hcontI : wsCont G ix.toNat)
    (hcls : ∀ q, ix.toNat < q → q < k → wsCont G q)
    (hstop : wsStop G k)
    (hpos : ∀ q, ix.toNat < q → q ≤ k → q < 2 ^ 63)
    (hqn : ∀ q, ix.toNat < q → q ≤ k → q < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (h8sl : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock37OutAt
      (wsP37Out (wsP41Out sl b35) b35) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
      "%8" = some (.int 8 b8))
    (hendsl : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock37OutAt
      (wsP37Out (wsP41Out sl b35) b35) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
      "%end.i" = some (.ptr (C.stage.tok + 8)))
    (hbitsl : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1) :
    ∃ N, N ≤ 5 * (k - ix.toNat) + 10 ∧
      WalkSegment calls G (ContAC₄ C) sl { C with block := "if.then413.i" }
        (scWsSeam C (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock37OutAt
          (wsP37Out (wsP41Out sl b35) b35) (cont35 b35))) ix.toNat) ix.toNat v.toNat k)
          k b8) N ∧
      lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock37OutAt
        (wsP37Out (wsP41Out sl b35) b35) (cont35 b35))) ix.toNat) ix.toNat v.toNat k).env
        "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  have hpre := wsPreSAt_37 sl b35 hb13 hb32
  have hidx : lookupName (leafBlock37OutAt (wsP37Out (wsP41Out sl b35) b35)
      (cont35 b35)).env "%idxprom.i" = some (.int 64 ix) := by
    rw [← hpre, wsPreSAt_idx]; exact hidx0
  have hcond : lookupName (leafBlock37OutAt (wsP37Out (wsP41Out sl b35) b35)
      (cont35 b35)).env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
    rw [← hpre, wsPreSAt_cond]; exact hcond0
  exact scWsAfterPreAt G C sl v ix _ (j := 3)
    (wsEntryAt37 G C sl b35 hInv h35 hb13 hb32 hbq32) (by omega)
    rfl hidx hcond hiv hvsub hcw hi63 hgn hik hkv hcontI hcls hstop hpos hqn halen hevlen
    h8sl hendsl hbitsl

/-! ### The seam's cells, and the tail's and landing's

`scWsSeam` is `seamS` at the tag-true `pc`, so its environment and memory are the else
seam's: the three calls' cells and the landing's reads are the same peels at one name. -/

/-- `%ee.1.i` at the numeral route's seam is the run's stop. -/
theorem scWsSeam_ee {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q4 : State) (k : Nat)
    (x : BitVec 8) :
    lookupName (scWsSeam C q4 k x).env "%ee.1.i" =
      some (.int 64 (BitVec.ofNat 64 k)) := by
  simp only [scWsSeam, seamS, seamFin, stateAt]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- `%cond350.i` at the numeral route's seam is its source's. -/
theorem scWsSeam_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q4 : State)
    (k : Nat) (x : BitVec 8) :
    lookupName (scWsSeam C q4 k x).env "%cond350.i" = lookupName q4.env "%cond350.i" := by
  simp only [scWsSeam, seamS, seamFin, stateAt]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%8` at the numeral route's seam is its source's. -/
theorem scWsSeam_env8 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q4 : State)
    (k : Nat) (x : BitVec 8) :
    lookupName (scWsSeam C q4 k x).env "%8" = lookupName q4.env "%8" := by
  simp only [scWsSeam, seamS, seamFin, stateAt]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- `%end.i` at the numeral route's seam is its source's. -/
theorem scWsSeam_envEnd {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q4 : State)
    (k : Nat) (x : BitVec 8) :
    lookupName (scWsSeam C q4 k x).env "%end.i" = lookupName q4.env "%end.i" := by
  simp only [scWsSeam, seamS, seamFin, stateAt]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- The numeral route's seam is reached from `if.end372.i`: the tail's kind `phi` reads
that predecessor. -/
theorem scWsSeam_pre {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q4 : State)
    (k : Nat) (x : BitVec 8) : (scWsSeam C q4 k x).pre = some q4.pc := rfl

/-- **The run's stop is at `if.end372.i`**: the skip's last visit leaves there, so the
seam's predecessor is that block. -/
theorem scWsSl_pc {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) (x : BitVec 8)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8)
    {k : Nat} (hik : ix.toNat < k) :
    (scWsSl G C s x inc nep ep v ix b35 k).pc = "if.end372.i" := by
  have hki : k - ix.toNat = (k - ix.toNat - 1) + 1 := by omega
  show (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (wsPreSAt
    (sLand C s x inc nep ep v ix b35) b35)) ix.toNat) ix.toNat v.toNat k).pc =
      "if.end372.i"
  unfold wsStopAt
  rw [hki]
  rfl

/-- **The seam's memory**: the stop's with the token's end stored. -/
theorem scWsSeam_mem {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q4 : State)
    (k : Nat) (x : BitVec 8) :
    (scWsSeam C q4 k x).mem =
      writeBytes q4.mem (C.stage.tok + 8) (natToBytes (BitVec.ofNat 64 k).toNat 8) := rfl

/-- **A store inside the token record leaves the root slot's word alone**, at the numeral
route's seam and the tail's own kind store. -/
theorem scWsSeam_rootRead {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} (q4 : State)
    (k : Nat) (x : BitVec 8) {cA rdv : BitVec 32}
    (hroot : readBytes q4.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)) :
    readBytes
      (writeBytes (scWsSeam C q4 k x).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4) := by
  rw [scWsSeam_mem]
  rw [walkReadBytes_rootSlot_of_tokStore (C := C) (off := 16) (len := 4)
    (v := natToBytes cA.toNat 4) (by decide) (natToBytes_length _ _)]
  rw [walkReadBytes_rootSlot_of_tokStore (C := C) (off := 8) (len := 8)
    (v := natToBytes (BitVec.ofNat 64 k).toNat 8) (by decide) (natToBytes_length _ _)]
  exact hroot

/-- `%ee.1.i` at the numeral route's scan entry is the run's stop. -/
theorem scWsEntry_ee {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q4 : State) (k : Nat)
    (x : BitVec 8) (v : BitVec 32) (r₁ r₂ r₃ : CallOutcome) (cA rdv xA : BitVec 32) :
    lookupName (scWsEntry C q4 k x v r₁ r₂ r₃ cA rdv xA).env "%ee.1.i" =
      some (.int 64 (BitVec.ofNat 64 k)) := by
  simp only [scWsEntry, ScanEntry, TailS₃, TailS₂, TailS₁, stateAt, cells, State.bind,
    lookupName_cons_ne (k := "%cmp451.i") (n := "%ee.1.i") _ _ (by decide),
    lookupName_cons_ne (k := "%tobool428.not.i") (n := "%ee.1.i") _ _ (by decide),
    lookupName_cons_ne (k := "%call427.i") (n := "%ee.1.i") _ _ (by decide),
    lookupName_cons_ne (k := "%tobool417.not.i") (n := "%ee.1.i") _ _ (by decide),
    lookupName_cons_ne (k := "%call416.i") (n := "%ee.1.i") _ _ (by decide),
    lookupName_cons_ne (k := "%38") (n := "%ee.1.i") _ _ (by decide),
    lookupName_cons_ne (k := "%.sink372") (n := "%ee.1.i") _ _ (by decide)]
  exact scWsSeam_ee C q4 k x

/-- `%cond350.i` at the numeral route's scan entry is the seam's. -/
theorem scWsEntry_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q4 : State)
    (k : Nat) (x : BitVec 8) (v : BitVec 32) (r₁ r₂ r₃ : CallOutcome)
    (cA rdv xA : BitVec 32) :
    lookupName (scWsEntry C q4 k x v r₁ r₂ r₃ cA rdv xA).env "%cond350.i" =
      lookupName q4.env "%cond350.i" := by
  simp only [scWsEntry, ScanEntry, TailS₃, TailS₂, TailS₁, stateAt, cells, State.bind,
    lookupName_cons_ne (k := "%cmp451.i") (n := "%cond350.i") _ _ (by decide),
    lookupName_cons_ne (k := "%tobool428.not.i") (n := "%cond350.i") _ _ (by decide),
    lookupName_cons_ne (k := "%call427.i") (n := "%cond350.i") _ _ (by decide),
    lookupName_cons_ne (k := "%tobool417.not.i") (n := "%cond350.i") _ _ (by decide),
    lookupName_cons_ne (k := "%call416.i") (n := "%cond350.i") _ _ (by decide),
    lookupName_cons_ne (k := "%38") (n := "%cond350.i") _ _ (by decide),
    lookupName_cons_ne (k := "%.sink372") (n := "%cond350.i") _ _ (by decide)]
  exact scWsSeam_cond C q4 k x

/-- The numeral route's scan entry is at `if.then447.i`, the copy call's test. -/
theorem scWsEntry_pre {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q4 : State)
    (k : Nat) (x : BitVec 8) (v : BitVec 32) (r₁ r₂ r₃ : CallOutcome)
    (cA rdv xA : BitVec 32) :
    (scWsEntry C q4 k x v r₁ r₂ r₃ cA rdv xA).pre = some "if.then447.i" := by
  simp only [scWsEntry, ScanEntry, TailS₃, TailS₂]

/-- `%cond350.i` at the numeral route's latch is the lane's word. -/
theorem scWsLatch_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q4 : State)
    (k : Nat) (x : BitVec 8) (v : BitVec 32) (r₁ r₂ r₃ : CallOutcome)
    (cA rdv xA : BitVec 32) (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8)
    (hcond : lookupName q4.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))) :
    lookupName (scWsLatch C q4 k x v r₁ r₂ r₃ cA rdv xA idx a q x47).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) :=
  latch_cond (scWsEntry C q4 k x v r₁ r₂ r₃ cA rdv xA) idx a q x47
    (scWsEntry_cond C q4 k x v r₁ r₂ r₃ cA rdv xA ▸ hcond)

/-- The numeral route's latch counter is its own index. -/
theorem scWsLatch_counter {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (q4 : State)
    (k : Nat) (x : BitVec 8) (v : BitVec 32) (r₁ r₂ r₃ : CallOutcome)
    (cA rdv xA : BitVec 32) (idx : BitVec 64) (a q : Nat) (x47 : BitVec 8) :
    lookupName (scWsLatch C q4 k x v r₁ r₂ r₃ cA rdv xA idx a q x47).env "%q.0.i246" =
      some (.int 64 idx) :=
  latch_counter (scWsEntry C q4 k x v r₁ r₂ r₃ cA rdv xA) idx a q x47

/-! ### The run at the bundle's own state

The three wrappers at `sLand`, where the byte's class is the bundle's own `hClass` and
the stop is `scWsSl`.  The class-dependent stop term is `wsSlAt` by
`wsPreSAt_33/35/37`, so the three branches differ only in which wrapper runs. -/

/-- **The run from the numeral prefix's check state to its seam**, at the byte's class:
the prefix's eight links, then the three entry classes' wrappers at the bundle's own
cells and the stop `scWsSl`. -/
theorem scWsRunF {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) {x : BitVec 8} {inc nep : BitVec 64} {ep : Nat} {v : BitVec 32}
    {ix : BitVec 64} {b35 : UInt8} {k : Nat}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
    (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
    (hinc : evalOperand (scS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (scS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hnext : evalICmp .ult inc nep = 1)
    (h5 : lookupName (scS₅ s x inc nep).env "%5" = some (.ptr ep))
    (hi63inc : inc.toNat < 2 ^ 63)
    (hread : readBytes (scS₅ s x inc nep).mem (ep + inc.toNat * 4) 4 =
      some (natToBytes v.toNat 4))
    (hidx5 : lookupName (scS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix))
    (htok5 : lookupName (scS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap5 : lookupName (scS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1)
    (hidxS : lookupName s.env "%idxprom.i" = some (.int 64 ix))
    (hread35 : readBytes (sEnd C s x inc nep ep v ix).mem ((G.b - 1) + v.toNat) 1 =
      some [b35])
    (hClass :
      ((evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 ∧
          evalICmp .ule (cont35 b35 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) ∨
        (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0 ∧
          evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 ∧
          evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 1) ∨
        (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0 ∧
          evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0 ∧
          evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 1)) ∧
      (∀ q, ix.toNat ≤ q → q < k → wsCont G q) ∧ wsStop G k ∧ ix.toNat < k ∧
      v.toNat - ix.toNat ≤ C.inner ∧ entryPos G C.k ≤ ix.toNat)
    (hcond : lookupName (sLand C s x inc nep ep v ix b35).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)))
    (hiv : ix.toNat < v.toNat) (hcw : v.toNat < 2 ^ 64)
    (hi63 : ix.toNat < 2 ^ 63) (hgn : ix.toNat < G.n)
    (hcontI : wsCont G ix.toNat) (heicd : k < v.toNat)
    (hpos : ∀ q, ix.toNat < q → q ≤ k → q < 2 ^ 63)
    (hqn : ∀ q, ix.toNat < q → q ≤ k → q < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve) (hevlen : C.evlen ≤ G.evcap)
    (h8sl : lookupName (scWsSl G C s x inc nep ep v ix b35 k).env "%8" = some (.int 8 x))
    (hendsl : lookupName (scWsSl G C s x inc nep ep v ix b35 k).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1) :
    ∃ N, N ≤ 8 + 5 * (k - ix.toNat) + 10 ∧
      WalkSegment (stage2Calls stage2SubCalls) G C s { C with block := "if.then413.i" }
        (scWsSeam C (scWsSl G C s x inc nep ep v ix b35 k) k x) N ∧
      lookupName (scWsSl G C s x inc nep ep v ix b35 k).env "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  obtain ⟨hcase, hcls, hstop, hik, hvsub, hstart⟩ := hClass
  have hseg8 : WalkSegment (stage2Calls stage2SubCalls) G C s (Scc₈ C)
      (sLand C s x inc nep ep v ix b35) 8 :=
    scPrefixLand (G := G) (C := C) (s := s) hInv hblock h8 hlt91 h44 h58 hne44 hinc hnep
      hnext h5 hi63inc hread hidx5 htok5 hgap5 hugt hread35
  have hInvL : WalkInv G (ContAC₄ C) (sLand C s x inc nep ep v ix b35) := hseg8.inv'
  have h35L : evalOperand (sLand C s x inc nep ep v ix b35) (.reg "%35") =
      some (.int 8 (cont35 b35)) :=
    scWsLand_35 C s x inc nep ep v ix b35
  have hidxL : lookupName (sLand C s x inc nep ep v ix b35).env "%idxprom.i" =
      some (.int 64 ix) := by
    rw [scWsLand_idx]
    exact hidxS
  have hcondL : lookupName (sLand C s x inc nep ep v ix b35).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := hcond
  have hcls' : ∀ q, ix.toNat < q → q < k → wsCont G q :=
    fun q h1 h2 => hcls q (by omega) h2
  rcases hcase with ⟨hb13, hws⟩ | ⟨hb13, hb32, hbq13⟩ | ⟨hb13, hb32, hbq32⟩
  · have hpre := wsPreSAt_33 (sLand C s x inc nep ep v ix b35) b35 hb13
    have h8m : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock33OutAt
        (nodeBlock41OutAt (sLand C s x inc nep ep v ix b35) (cont35 b35)) (cont35 b35)))
        ix.toNat) ix.toNat v.toNat k).env "%8" = some (.int 8 x) := by
      simpa only [scWsSl, wsSlAt, hpre] using h8sl
    have hem : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock33OutAt
        (nodeBlock41OutAt (sLand C s x inc nep ep v ix b35) (cont35 b35)) (cont35 b35)))
        ix.toNat) ix.toNat v.toNat k).env "%end.i" = some (.ptr (C.stage.tok + 8)) := by
      simpa only [scWsSl, wsSlAt, hpre] using hendsl
    obtain ⟨N, hN, hseg, hcd⟩ := scWsRunAt33 G C (sLand C s x inc nep ep v ix b35) b35
      hInvL h35L hb13 hws hidxL hcondL hiv hvsub hcw hi63 hgn hik heicd hcontI hcls'
      hstop hpos hqn halen hevlen h8m hem hbit
    refine ⟨8 + N, by omega, ?_, ?_⟩
    · exact hseg8.trans (by simpa only [scWsSl, wsSlAt, hpre] using hseg)
    · simpa only [scWsSl, wsSlAt, hpre] using hcd
  · have hpre := wsPreSAt_35 (sLand C s x inc nep ep v ix b35) b35 hb13 hb32
    have h8m : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock35OutAt
        (wsP39Out (wsP41Out (sLand C s x inc nep ep v ix b35) b35) b35) (cont35 b35)))
        ix.toNat) ix.toNat v.toNat k).env "%8" = some (.int 8 x) := by
      simpa only [scWsSl, wsSlAt, hpre] using h8sl
    have hem : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock35OutAt
        (wsP39Out (wsP41Out (sLand C s x inc nep ep v ix b35) b35) b35) (cont35 b35)))
        ix.toNat) ix.toNat v.toNat k).env "%end.i" = some (.ptr (C.stage.tok + 8)) := by
      simpa only [scWsSl, wsSlAt, hpre] using hendsl
    obtain ⟨N, hN, hseg, hcd⟩ := scWsRunAt35 G C (sLand C s x inc nep ep v ix b35) b35
      hInvL h35L hb13 hb32 hbq13 hidxL hcondL hiv hvsub hcw hi63 hgn hik heicd hcontI hcls'
      hstop hpos hqn halen hevlen h8m hem hbit
    refine ⟨8 + N, by omega, ?_, ?_⟩
    · exact hseg8.trans (by simpa only [scWsSl, wsSlAt, hpre] using hseg)
    · simpa only [scWsSl, wsSlAt, hpre] using hcd
  · have hpre := wsPreSAt_37 (sLand C s x inc nep ep v ix b35) b35 hb13 hb32
    have h8m : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock37OutAt
        (wsP37Out (wsP41Out (sLand C s x inc nep ep v ix b35) b35) b35) (cont35 b35)))
        ix.toNat) ix.toNat v.toNat k).env "%8" = some (.int 8 x) := by
      simpa only [scWsSl, wsSlAt, hpre] using h8sl
    have hem : lookupName (wsStopAt G (wsLeafS G (landRhsPreheaderOutAt (leafBlock37OutAt
        (wsP37Out (wsP41Out (sLand C s x inc nep ep v ix b35) b35) b35) (cont35 b35)))
        ix.toNat) ix.toNat v.toNat k).env "%end.i" = some (.ptr (C.stage.tok + 8)) := by
      simpa only [scWsSl, wsSlAt, hpre] using hendsl
    obtain ⟨N, hN, hseg, hcd⟩ := scWsRunAt37 G C (sLand C s x inc nep ep v ix b35) b35
      hInvL h35L hb13 hb32 hbq32 hidxL hcondL hiv hvsub hcw hi63 hgn hik heicd hcontI hcls'
      hstop hpos hqn halen hevlen h8m hem hbit
    refine ⟨8 + N, by omega, ?_, ?_⟩
    · exact hseg8.trans (by simpa only [scWsSl, wsSlAt, hpre] using hseg)
    · simpa only [scWsSl, wsSlAt, hpre] using hcd

/-! ### The bundle

The arm's evidence: the head's class and the lane (`HcontScalarPrefix`'s fields, minus
the three-route `hb` the run replaces), the byte's class at the entry's end with the run's
stop and its per-index facts, the seam's two cells, the tail's three calls as their
segment, and the scan's landing with the visits' totality.  The seam's two cells are
fields for `HcontRunFacts.h8c`'s reason: the run's link reads `%8` and `%end.i` at the
seam's name, and a state's cell is a fact about that state, not a consequence of the
bundle's own shape. -/

/-- **The numeral route's whitespace bundle.**  The prefix's half is the plain-value
class's document row; the run's half is the byte's class, its stop `k` and the
per-index facts the skip's visits read; the tail's half is the three calls' segment at
the seam the run reaches; the scan's half is the landing's byte and the visits'
totality. -/
structure HcontScalarWsFacts {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) : Type where
  /-- The head's byte and the four scalar-arm pivots. -/
  x : BitVec 8
  h8 : evalOperand s (.reg "%8") = some (.int 8 x)
  hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1
  h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0
  h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1
  hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0
  /-- **The tag test is `1`**: a digit or `-`, so `if.end372.i` leaves for
  `if.then413.i` — this route's seam, not the class-C span's. -/
  hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
    evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1
  /-- The counts and the count test's value. -/
  inc : BitVec 64
  nep : BitVec 64
  hinc : evalOperand (scS₄ s x) (.reg "%inc.i") = some (.int 64 inc)
  hnep : evalOperand (scS₄ s x) (.reg "%nep") = some (.int 64 nep)
  hnext : evalICmp .ult inc nep = 1
  /-- The next entry's position lane. -/
  ep : Nat
  v : BitVec 32
  h5 : lookupName (scS₅ s x inc nep).env "%5" = some (.ptr ep)
  hi63 : inc.toNat < 2 ^ 63
  hread : readBytes (scS₅ s x inc nep).mem (ep + inc.toNat * 4) 4 =
    some (natToBytes v.toNat 4)
  /-- The default arm's remaining cells. -/
  ix : BitVec 64
  hidx5 : lookupName (scS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix)
  htok5 : lookupName (scS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok)
  hgap5 : lookupName (scS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20))
  hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1
  /-- The head's index cell: `WalkInv.idx_reg`'s witness at the loop head. -/
  hidxS : lookupName s.env "%idxprom.i" = some (.int 64 ix)
  /-- The byte before the entry's end and its read. -/
  b35 : UInt8
  hread35 : readBytes (sEnd C s x inc nep ep v ix).mem ((G.b - 1) + v.toNat) 1 =
    some [b35]
  /-- The head's byte is the carry's: `WalkInv.iter.reg8`'s witness. -/
  hx : x = hlastByte G C
  /-- **The whitespace skip's stop, its byte class and its per-index facts.**  `%35` is
  one of the four whitespace bytes (the three disjuncts), every byte the skip reads
  continues the token until `k`, and `k` stops it. -/
  k : Nat
  hClass :
    ((evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 1 ∧
        evalICmp .ule (cont35 b35 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1) ∨
      (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0 ∧
        evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 1 ∧
        evalICmp .eq (cont35 b35) (BitVec.ofNat 8 13) = 1) ∨
      (evalICmp .slt (cont35 b35) (BitVec.ofNat 8 13) = 0 ∧
        evalICmp .slt (cont35 b35) (BitVec.ofNat 8 32) = 0 ∧
        evalICmp .eq (cont35 b35) (BitVec.ofNat 8 32) = 1)) ∧
    (∀ q, ix.toNat ≤ q → q < k → wsCont G q) ∧ wsStop G k ∧ ix.toNat < k ∧
    v.toNat - ix.toNat ≤ C.inner ∧ entryPos G C.k ≤ ix.toNat
  /-- The run's stop is inside the entry. -/
  heicd : k < v.toNat
  /-- The entry's end is at or before the next entry's position. -/
  hspan : v.toNat ≤ entryPos G (C.k + 1)
  /-- `%8` at the seam: the head's byte, read where the seam link reads it. -/
  h8m : evalOperand (scWsSeam C (scWsSl G C s x inc nep ep v ix b35 k) k x) (.reg "%8") =
    some (.int 8 x)
  /-- `%end.i` at the seam: the token record's end pointer. -/
  hendm : lookupName (scWsSeam C (scWsSl G C s x inc nep ep v ix b35 k) k x).env "%end.i" =
    some (.ptr (C.stage.tok + 8))
  /-- The tail's three calls on their **scan** arm, from the seam to the landing. -/
  r₁ : CallOutcome
  r₂ : CallOutcome
  r₃ : CallOutcome
  ev : EventRecord
  cA : BitVec 32
  rdv : BitVec 32
  xA : BitVec 32
  hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (ContAC₇ C))
    (scWsSeam C (scWsSl G C s x inc nep ep v ix b35 k) k x)
    (TailCarryScan (HeadC₄₁₃ (ContAC₇ C)) ev)
    (scWsEntry C (scWsSl G C s x inc nep ep v ix b35 k) k x v r₁ r₂ r₃ cA rdv xA) 3
  /-- The scan's landing: the byte's address and the byte, at the run's stop. -/
  a : Nat
  q : Nat
  bs : List UInt8
  h3S : lookupName
    (scWsEntry C (scWsSl G C s x inc nep ep v ix b35 k) k x v r₁ r₂ r₃ cA rdv xA).env
    "%3" = some (.ptr a)
  hpos : ((BitVec.ofNat 64 k).signExtend 64).toNat < 2 ^ 63
  hreadS : readBytes
    (scWsEntry C (scWsSl G C s x inc nep ep v ix b35 k) k x v r₁ r₂ r₃ cA rdv xA).mem
    (a + ((BitVec.ofNat 64 k).signExtend 64).toNat) 1 = some bs
  hbsS : bytesToNat bs = q
  hloc105 : WalkLocal (ScanC₁₀₅ (TailCarryScan (HeadC₄₁₃ (ContAC₇ C)) ev))
    (landRhs457OutAt
      (scWsEntry C (scWsSl G C s x inc nep ep v ix b35 k) k x v r₁ r₂ r₃ cA rdv xA)
      (BitVec.ofNat 64 k) a q)
  x47 : BitVec 8
  h47 : evalOperand
    (landRhs457OutAt
      (scWsEntry C (scWsSl G C s x inc nep ep v ix b35 k) k x v r₁ r₂ r₃ cA rdv xA)
      (BitVec.ofNat 64 k) a q) (.reg "%47") = some (.int 8 x47)
  hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1
  hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
  hloc96 : WalkLocal (ScanC₉₆ (TailCarryScan (HeadC₄₁₃ (ContAC₇ C)) ev))
    (ScanS₉₆ (scWsEntry C (scWsSl G C s x inc nep ep v ix b35 k) k x v r₁ r₂ r₃ cA rdv xA)
      (BitVec.ofNat 64 k) a q x47)
  hlatch : WalkLocal
    { TailCarryScan (HeadC₄₁₃ (ContAC₇ C)) ev with block := "while.body462.i" }
    (scWsLatch C (scWsSl G C s x inc nep ep v ix b35 k) k x v r₁ r₂ r₃ cA rdv xA
      (BitVec.ofNat 64 k) a q x47)
  /-- **The visits' totality**: the document's byte at every index the scan visits, from
  the run's stop on, with its class and the three local facts each visit needs. -/
  hbyte : ∀ (C' : WalkCarry G) (s' : State) (p : Nat), WalkInv G C' s' →
    C'.block = "while.body462.i" → k < p + 1 → p + 1 < v.toNat →
    lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
    lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) →
    ∃ (a : Nat) (bs : List UInt8) (q : Nat) (x : BitVec 8),
      lookupName (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
        "land.rhs457.i").env "%3" = some (.ptr a) ∧
      readBytes s'.mem (a + (p + 1)) 1 = some bs ∧ bytesToNat bs = q ∧
      evalOperand (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p
        v.toNat "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") =
        some (.int 8 x) ∧
      evalICmp .slt x (BitVec.ofNat 8 13) = 1 ∧
      evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 ∧
      WalkLocal (ScanC₁₀₅ (ScanCLand C'))
        (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
          "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) ∧
      WalkLocal (ScanC₉₆ (ScanCLand C'))
        (ScanS₉₆ (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x) ∧
      WalkLocal { ScanCLand C' with block := "while.body462.i" }
        (Latch462S (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
          "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q x)

/-- The bundle's stop, at its own fields. -/
abbrev scWsSlF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontScalarWsFacts G C s) : State :=
  scWsSl G C s f.x f.inc f.nep f.ep f.v f.ix f.b35 f.k

/-- The bundle's seam, at its own fields. -/
abbrev scWsSeamF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontScalarWsFacts G C s) : State :=
  scWsSeam C (scWsSlF f) f.k f.x

/-- The bundle's scan entry, at its own fields. -/
abbrev scWsEntryF {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : HcontScalarWsFacts G C s) : State :=
  scWsEntry C (scWsSlF f) f.k f.x f.v f.r₁ f.r₂ f.r₃ f.cA f.rdv f.xA

/-! ### The dispatch

The path: the prefix's eight, the run at its own count, the tail's three, the landing's
three, the visits by `scanRoundsAt` at the seam's bound `v.toNat`, the exit's one and the
merge's one — to `cleanup478.i`, with the merge's three cells read at the endpoint the
composition reaches.  The price is `18 + N + nSc ≤ 32·Δk + 8·ΔA`. -/

/-- **The numeral route's continuing dispatch, from the arm's evidence.**  The segment is
the composition's (`N` the run's count, `nSc` the visits'), the endpoint is the merge,
and the three cells are the merge's — `%inc.i` and `%nep` across the exit, the depth the
invariant's. -/
theorem walkDispatch_at_continue_scalarWs {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep) (f : HcontScalarWsFacts G C s) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  -- 1. the prefix's eight links, and the check state's cells
  have hseg8 : WalkSegment (stage2Calls stage2SubCalls) G C s (Scc₈ C)
      (sLand C s f.x f.inc f.nep f.ep f.v f.ix f.b35) 8 :=
    scPrefixLand (G := G) (C := C) (s := s) hInv hblock f.h8 f.hlt91 f.h44 f.h58 f.hne44
      f.hinc f.hnep f.hnext f.h5 f.hi63 f.hread f.hidx5 f.htok5 f.hgap5 f.hugt f.hread35
  have hInvL : WalkInv G (ContAC₄ C) (sLand C s f.x f.inc f.nep f.ep f.v f.ix f.b35) :=
    hseg8.inv'
  have h8L : lookupName (sLand C s f.x f.inc f.nep f.ep f.v f.ix f.b35).env "%8" =
      some (.int 8 f.x) := by
    simpa only [f.hx] using hInvL.iter.reg8
  have hidxL : lookupName (sLand C s f.x f.inc f.nep f.ep f.v f.ix f.b35).env
      "%idxprom.i" = some (.int 64 f.ix) := by
    rw [scWsLand_idx]
    exact f.hidxS
  have hcondL : lookupName (sLand C s f.x f.inc f.nep f.ep f.v f.ix f.b35).env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 f.v.toNat)) :=
    sLand_cond C s f.x f.inc f.nep f.ep f.v f.ix f.b35
  -- 2. the run, at the byte's class
  have hiv : f.ix.toNat < f.v.toNat := by
    have h := (evalICmp_ugt_one_iff_toNat (BitVec.ofNat 64 f.v.toNat) f.ix).1 f.hugt
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := f.v.isLt; omega)] at h
    exact h
  have hcw : f.v.toNat < 2 ^ 64 := by have := f.v.isLt; omega
  have hi63L : f.ix.toNat < 2 ^ 63 := by
    have h1 := G.maxDoc
    simp only [stage2MaxDocument] at h1
    omega
  have hgn : f.ix.toNat < G.n := by
    have h1 := G.maxDoc
    simp only [stage2MaxDocument] at h1
    have h2 : f.v.toNat ≤ entryPos G (C.k + 1) := f.hspan
    have h3 := entryPos_lt G hk
    omega
  have hposR : ∀ q, f.ix.toNat < q → q ≤ f.k → q < 2 ^ 63 := by
    intro q h1 h2
    have h1' := G.maxDoc
    simp only [stage2MaxDocument] at h1'
    have h4 : f.k < f.v.toNat := f.heicd
    have h5 : f.v.toNat ≤ entryPos G (C.k + 1) := f.hspan
    have h6 := entryPos_lt G hk
    omega
  have hqnR : ∀ q, f.ix.toNat < q → q ≤ f.k → q < G.n := by
    intro q h1 h2
    have h4 : f.k < f.v.toNat := f.heicd
    have h5 : f.v.toNat ≤ entryPos G (C.k + 1) := f.hspan
    have h6 := entryPos_lt G hk
    omega
  have halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve := by
    have h := hInv.alen_le
    change C.alen ≤ G.ndst0 + G.n at h
    omega
  have hevlen : C.evlen ≤ G.evcap := by
    have h1 := hInv.evlen_le
    change C.evlen ≤ G.nev0 + stage2RecordBytes * G.n at h1
    have h2 := G.evRoom
    omega
  have hcontI : wsCont G f.ix.toNat := f.hClass.2.1 f.ix.toNat le_rfl f.hClass.2.2.2.1
  have hikF : f.ix.toNat < f.k := f.hClass.2.2.2.1
  have hkvF : f.k < f.v.toNat := f.heicd
  have h8sl : lookupName (scWsSlF f).env "%8" = some (.int 8 f.x) := by
    have h := scWsSeam_env8 C (scWsSlF f) f.k f.x
    have h2 : evalOperand (scWsSeamF f) (.reg "%8") = some (.int 8 f.x) := f.h8m
    rw [evalOperand] at h2
    rw [← h]
    exact h2
  have hendsl : lookupName (scWsSlF f).env "%end.i" = some (.ptr (C.stage.tok + 8)) := by
    have h := scWsSeam_envEnd C (scWsSlF f) f.k f.x
    rw [← h]
    exact f.hendm
  obtain ⟨N, hN, hsegRun, hcondSl⟩ :=
    scWsRunF G C s hInv hblock f.h8 f.hlt91 f.h44 f.h58 f.hne44 f.hinc f.hnep f.hnext
      f.h5 f.hi63 f.hread f.hidx5 f.htok5 f.hgap5 f.hugt f.hidxS f.hread35 f.hClass
      hcondL hiv hcw hi63L hgn hcontI f.heicd hposR hqnR halen hevlen h8sl hendsl f.hbit
  -- 3. the tail's three links
  have hsegT : WalkSegment (stage2Calls stage2SubCalls) G C s
      (TailCarryScan (HeadC₄₁₃ (ContAC₇ C)) f.ev) (scWsEntryF f) (N + 3) :=
    hsegRun.trans f.hTail
  -- 4. the landing's three links
  obtain ⟨s', hs', hsegL⟩ :=
    walkScanLinks457 (calls := stage2Calls stage2SubCalls) (G := G)
      (C := TailCarryScan (HeadC₄₁₃ (ContAC₇ C)) f.ev) (s := scWsEntryF f)
      f.hTail.inv' rfl (scWsEntry_pre C (scWsSlF f) f.k f.x f.v f.r₁ f.r₂ f.r₃ f.cA f.rdv
        f.xA) hlastEntry_phiSel (by
          simp only [evalOperand, stateAt]
          exact scWsEntry_ee C (scWsSlF f) f.k f.x f.v f.r₁ f.r₂ f.r₃ f.cA f.rdv f.xA)
      f.h3S f.hpos f.hreadS f.hbsS f.hloc105 f.h47 f.hbit47 f.hws47 f.hloc96 f.hlatch
  rw [hs'] at hsegL
  -- 5. the visits, at the seam's bound
  have hk63 : f.k < 2 ^ 63 := by
    have h1 := G.maxDoc
    simp only [stage2MaxDocument] at h1
    have h4 : f.k < f.v.toNat := f.heicd
    have h5 : f.v.toNat ≤ entryPos G (C.k + 1) := f.hspan
    have h6 := entryPos_lt G hk
    omega
  have hcw' : f.v.toNat < 2 ^ 64 := hcw
  have hc63 : f.v.toNat < 2 ^ 63 := by
    have h1 := G.maxDoc
    simp only [stage2MaxDocument] at h1
    have h5 : f.v.toNat ≤ entryPos G (C.k + 1) := f.hspan
    have h6 := entryPos_lt G hk
    omega
  have hincL : lookupName (scWsLatch C (scWsSlF f) f.k f.x f.v f.r₁ f.r₂ f.r₃ f.cA f.rdv
      f.xA (BitVec.ofNat 64 f.k) f.a f.q f.x47).env "%inc.i" =
      some (.int 64 (BitVec.ofNat 64 (C.k + 1))) :=
    hsegL.inv'.inc_reg
  have hnepL : lookupName (scWsLatch C (scWsSlF f) f.k f.x f.v f.r₁ f.r₂ f.r₃ f.cA f.rdv
      f.xA (BitVec.ofNat 64 f.k) f.a f.q f.x47).env "%nep" =
      some (.int 64 (BitVec.ofNat 64 G.nep)) :=
    hsegL.inv'.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs])
  obtain ⟨Cm, sm, nSc, hsegS, hInvR, hbR, hkR, hiR, hcR, hincR, hnepR, hnR⟩ :=
    scanRoundsAt (G := G) (C := TailCarryScan (HeadC₄₁₃ (ContAC₇ C)) f.ev)
      (s := scWsLatch C (scWsSlF f) f.k f.x f.v f.r₁ f.r₂ f.r₃ f.cA f.rdv f.xA
        (BitVec.ofNat 64 f.k) f.a f.q f.x47)
      hsegL.inv' rfl
      (scWsLatch_counter C (scWsSlF f) f.k f.x f.v f.r₁ f.r₂ f.r₃ f.cA f.rdv f.xA
        (BitVec.ofNat 64 f.k) f.a f.q f.x47)
      (scWsLatch_cond C (scWsSlF f) f.k f.x f.v f.r₁ f.r₂ f.r₃ f.cA f.rdv f.xA
        (BitVec.ofNat 64 f.k) f.a f.q f.x47 hcondSl)
      hincL hnepL rfl hcw' hc63 f.heicd f.hbyte
  -- 6. the exit: the inner budget is the invariant's local clause at the counts
  have hlocal : ScanCount sm "%q.0.i246" "%cond350.i" Cm.inner := by
    have h := hInvR.blockLocal
    rwa [WalkLocal.extraToken hbR] at h
  have hcpos : 0 < f.v.toNat := by have := f.heicd; omega
  have hlt : f.v.toNat - 1 < f.v.toNat := by omega
  have hinner : f.v.toNat - (f.v.toNat - 1) ≤ Cm.inner :=
    ScanCount.same hlocal hiR hcR hcw' hlt
  have hie : (f.v.toNat - 1) + 1 = f.v.toNat := Nat.sub_add_cancel (by omega)
  obtain ⟨s₁, hseg₁, -, hs₁, hInv₁⟩ :=
    scanExitSeg (calls := stage2Calls stage2SubCalls) (G := G) (C := Cm) (s := sm)
      hInvR hbR hiR hcR hinner hie hcw' (by intro e _ _ _; simp [WalkLocal])
  -- 7. the merge, one step, from the token record's register
  have htok₁ : lookupName
      (scanLatchOut sm "%inc463.i" "%exitcond298.not" (f.v.toNat - 1) f.v.toNat
        "if.end473.i").env "%t352.i" = some (.ptr Cm.stage.tok) := by
    have h := hInvR.regs ("%t352.i", .ptr Cm.stage.tok) (by simp [walkStaticRegs])
    exact scanExit_tok sm (f.v.toNat - 1) f.v.toNat h
  have htok₁' : lookupName s₁.env "%t352.i" = some (.ptr Cm.stage.tok) := by
    rw [hs₁]
    exact htok₁
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    walkIfEnd473_at (sub := stage2SubCalls) (G := G)
      (C := { Cm with block := "if.end473.i" }) (s := s₁) hInv₁ rfl htok₁'
  -- 8. the whole path, and the merge's cells at its endpoint
  have hsegA : WalkSegment (stage2Calls stage2SubCalls) G C s
      { TailCarryScan (HeadC₄₁₃ (ContAC₇ C)) f.ev with block := "while.body462.i" }
      (scWsLatch C (scWsSlF f) f.k f.x f.v f.r₁ f.r₂ f.r₃ f.cA f.rdv f.xA
        (BitVec.ofNat 64 f.k) f.a f.q f.x47) (N + 3 + 3) := by
    rw [show N + 3 + 3 = (N + 3) + 3 from by omega]
    exact hsegT.trans hsegL
  have hsegP : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm
      (N + 3 + 3 + nSc) := by
    rw [show N + 3 + 3 + nSc = (N + 3 + 3) + nSc from by omega]
    exact hsegA.trans hsegS
  have hexit : WalkSegment (stage2Calls stage2SubCalls) G C s
      { Cm with block := "if.end473.i" } s₁ (N + 3 + 3 + nSc + 1) := by
    rw [show N + 3 + 3 + nSc + 1 = (N + 3 + 3 + nSc) + 1 from by omega]
    exact hsegP.trans hseg₁
  have hmerge : WalkSegment (stage2Calls stage2SubCalls) G C s
      { Cm with block := "cleanup478.i" }
      { s₁ with pc := "cleanup478.i", pre := some s₁.pc } (N + 3 + 3 + nSc + 1 + 1) := by
    rw [show N + 3 + 3 + nSc + 1 + 1 = (N + 3 + 3 + nSc + 1) + 1 from by omega]
    have hstep : WalkSegment (stage2Calls stage2SubCalls) G
        { Cm with block := "if.end473.i" } s₁
        { { Cm with block := "if.end473.i" } with block := "cleanup478.i" }
        { s₁ with pc := "cleanup478.i", pre := some s₁.pc } 1 := by
      rw [hs₂] at hl₂
      exact WalkSegment.of_link hl₂
    exact hexit.trans hstep
  have hInvD : WalkInv G { Cm with block := "cleanup478.i" }
      { s₁ with pc := "cleanup478.i", pre := some s₁.pc } := hmerge.inv'
  have hkD : ({ Cm with block := "cleanup478.i" } : WalkCarry G).k = C.k := by
    rw [show ({ Cm with block := "cleanup478.i" } : WalkCarry G).k = Cm.k from rfl, hkR]
  have hpreD : ({ s₁ with pc := "cleanup478.i", pre := some s₁.pc } : State).pre =
      some "if.end473.i" := by
    rw [hs₁]
  have hk2D : evalOperand ({ s₁ with pc := "cleanup478.i", pre := some s₁.pc } : State)
      (.reg "%inc.i") = some (.int 64 (BitVec.ofNat 64 (C.k + 1))) := by
    have h := hInvD.inc_reg
    rw [hkD] at h
    exact h
  have hnepvD : lookupName ({ s₁ with pc := "cleanup478.i", pre := some s₁.pc } : State).env
      "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep)) :=
    hInvD.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs])
  have hcapD : C.k + 1 ≤ (BitVec.ofNat 64 G.nep).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have h1 := G.nep_le
      have h2 := G.maxDoc
      simp only [stage2MaxDocument] at h2
      omega)]
    omega
  have hspvD : evalOperand ({ s₁ with pc := "cleanup478.i", pre := some s₁.pc } : State)
      (.reg "%sp.i.0248") =
      some (.int 32 (BitVec.ofNat 32 ({ Cm with block := "cleanup478.i" } : WalkCarry G).sp)) :=
    hInvD.depth_reg
  have hpriceD : (N + 3 + 3 + nSc + 1 + 1) + 2 ≤
      stage2EntryAllowance * (C.k + 1 - C.k) +
        stage2ByteAllowance * (entryPos G (C.k + 1) - entryPos G C.k) := by
    have hN' : N ≤ 5 * (f.k - f.ix.toNat) + 18 := by omega
    have hnSc : nSc ≤ 4 * (f.v.toNat - 1 - f.k) := hnR
    have hstart' : entryPos G C.k ≤ f.ix.toNat := f.hClass.2.2.2.2.2
    have hspan' : f.v.toNat ≤ entryPos G (C.k + 1) := f.hspan
    have hvi : f.v.toNat - f.ix.toNat ≤
        entryPos G (C.k + 1) - entryPos G C.k := by omega
    have hcomb : 5 * (f.k - f.ix.toNat) + 4 * (f.v.toNat - 1 - f.k) ≤
        5 * (entryPos G (C.k + 1) - entryPos G C.k) := by
      have hsum : (f.k - f.ix.toNat) + (f.v.toNat - 1 - f.k) =
          f.v.toNat - 1 - f.ix.toNat := by omega
      have ht : f.v.toNat - 1 - f.ix.toNat ≤
          entryPos G (C.k + 1) - entryPos G C.k := by omega
      omega
    have hΔ : C.k + 1 - C.k = 1 := by omega
    simp only [stage2EntryAllowance, stage2ByteAllowance, hΔ, Nat.mul_one]
    omega
  exact WalkDispatchResult.merge { Cm with block := "cleanup478.i" }
    { s₁ with pc := "cleanup478.i", pre := some s₁.pc }
    (N + 3 + 3 + nSc + 1 + 1) ({ Cm with block := "cleanup478.i" } : WalkCarry G).sp
    (C.k + 1) "if.end473.i" (Operand.reg "%sp.i.0248") (Operand.reg "%inc.i")
    (BitVec.ofNat 64 G.nep) hmerge rfl hkD hpreD (by decide) hspvD (by decide) hk2D
    hnepvD (by omega) hcapD hInvD.depth_cap hInvD.sp_le_wlen hpriceD

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.scPrefixLand
#print axioms LeanLLVM.Refinement.WalkScope.scWsSeamSeg
#print axioms LeanLLVM.Refinement.WalkScope.scWsAfterPreAt
#print axioms LeanLLVM.Refinement.WalkScope.scWsRunAt33
#print axioms LeanLLVM.Refinement.WalkScope.scWsRunAt35
#print axioms LeanLLVM.Refinement.WalkScope.scWsRunAt37
#print axioms LeanLLVM.Refinement.WalkScope.scWsSeam_ee
#print axioms LeanLLVM.Refinement.WalkScope.scWsSeam_rootRead
#print axioms LeanLLVM.Refinement.WalkScope.scWsEntry_ee
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_continue_scalarWs

end WalkScope
end LeanLLVM.Refinement

