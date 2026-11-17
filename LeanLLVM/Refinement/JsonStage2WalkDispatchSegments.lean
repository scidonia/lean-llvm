/-
# The head's twelve links, and the class-C span at the arm's endpoint

`hcontToSpan` (`JsonStage2WalkRevolutionPrefix`) composes a continuing entry's path to the
tail's start at seventeen links, and it builds that path from two pieces stated by name:
the head's **twelve** links to the class-C span's entry (`hcontHeadSeg12`, upstream of it)
and the class-C span's **five**.  This module states the span's interface, the two tails
that follow it, and the run class's counted composition.  The bundle-level applications of
the head's twelve and of the seventeen-link composition are
`hcontHeadSeg12_of_cleanup`/`hcontSpan17_of_cleanup`/`hcontPrefixCleanupSeg`
(`JsonStage2WalkDispatchCleanupSpan`), upstream of the merge they serve.

## Why the twelve are the high-byte class's, and not every class's

The four pivots above `sw.default.i` select **different blocks per byte class**: `97` takes
`NodeBlock19 → NodeBlock11 → LeafBlock9` and `200` takes `NodeBlock5 → LeafBlock`, as
`JsonStage2WalkDispatchLettersDomain` records.  So "the head's twelve links" is not one
composition over all bytes — it is one per head-switch class, of which the prefixes are
`contPrefixLand` (the high-byte class, `91 ≤ %8`, `123 ≤ %8`, `125 ≤ %8`, `%8 ≠ 125`) and
`scPrefixLand` (the plain-value class).  `hcontHeadSeg12` is the high-byte class's twelve,
the one `hcontToSpan` proves; it is the twelve `HcontFacts` and `HcontCleanupFacts` carry
(as four class bits), and `hcontHeadSeg12_of_cleanup` applies it to the scan-free bundle's
own fields — so that bundle's head chain is a theorem, not a field.

The letters class (`slt %8 110 = 1`) is **not** this statement's: its bytes fall in several
head-switch classes (`97` and `200` above), and only the two prefixes' classes have a
segment.  That is why `HcontArm.letters`/`.fLetter`/`.classC` keep their head chain as a
field: it is a per-class composition, not one lemma's.

## The class-C span's four leaves, as one interface

`c56TrueSpan`, `c56ElseSpan`, `c58TrueSpan` and `c58ElseSpan`
(`JsonStage2WalkDispatchClassC`) are the four leaf routes below `if.else387.i`, each at its
own target carry and state — a leaf's `bind` is a term.  `classCSpan_at` states them at
**one** interface: at a seam byte clear of `slt %8 110` the span exists, ends at
`if.then413.i`, and costs at most five links, which is the shape `classCMerge_at` consumes
(`hSpan`, `hs`, `hnS`).  That is what makes the span a segment a producer can pass rather
than only the `> 116` route's five links.  The class's **upper** bound is not a premise:
`126`/`127` take `LeafBlock58`'s else arm too, and what separates `.classC` from
`.ws`/`.cleanup` is upstream of the seam.

The arm's tail is stated at the span's *endpoint*, and an existential endpoint cannot be
the source of a later hypothesis, so a producer that passes both must name the leaf: the
span is derivable wherever the endpoint is a term (`classCHeadSpan_at` composes it with the
head's twelve at `12 + nS`) and is the arm's field otherwise.  That is a fact about the
arm's shape, not a missing lemma.

## The empty tail's three links, and the scan-free arm

`emptyTailSeg_of_calls` (`JsonStage2WalkDispatchWitnessHlast`) is
`consumerTailSegEmptyAt`'s composition stated from the three callees' rows at any carry
whose block is `if.then413.i`, so a bundle's `hTail` is produced from an `abi`-shaped group
rather than supplied as a segment.  Four consumers use it:
`hlastTail_of_calls` (the last entry's high-byte tail) and `scalarTail_of_calls` (the last
entry's plain-value tail) are its instances, `hcontTail_of_calls` applies it to the
scan-free continuing class's seam, where `hcontArm_cleanup_of_calls` and
`walkDispatch_at_cleanup_of_calls` build the arm and its dispatch — `.cleanup`'s `hTail`
field retired — and `scContTail_of_calls` is the continuing scalar route's instance, at
`scSeamS` with that seam's own two cells (`scSeam_ee`, `scSeam_cond`).

## The run class's counted composition

`runSegmentsAt` states the run's four segments (head, span, tail, latch) and their
composition at `nH + nS + 3 + 3`; the composition is `runToLatchSeg_at`, the segment a
scan's rounds append to.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassC
import LeanLLVM.Refinement.JsonStage2WalkDispatchCleanupOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchCleanupSpan
import LeanLLVM.Refinement.JsonStage2WalkDispatchRun
import LeanLLVM.Refinement.JsonStage2WalkDispatchSpansOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessHlast
import LeanLLVM.Refinement.JsonStage2WalkHcontFactsOfStaging
import LeanLLVM.Refinement.JsonStage2WalkHcontScalar
import LeanLLVM.Refinement.JsonStage2WalkRevolutionSeg

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The twelve links live upstream

`hcontHeadSeg12` is stated in `JsonStage2WalkRevolutionPrefix`, where `hcontToSpan`
composes it with the class-C span; this module does not restate the head's path.  The
bundle-level applications (`hcontHeadSeg12_of_cleanup`, `hcontSpan17_of_cleanup`) and the
twenty-link composition `hcontPrefixCleanupSeg` are in
`JsonStage2WalkDispatchCleanupSpan`, upstream of the merge they serve. -/

/-! ### The class-C span, at one interface

The four leaves' segments are each at their own target; the class is their union.  A
producer that holds the class's two bits and the seam's byte therefore has a span, and
which leaf it is stays inside the proof. -/

/-- The two values a one-bit test can take. -/
theorem clsBit_one_zero (b : BitVec 1) : b = 1 ∨ b = 0 := by
  revert b
  decide

/-- A one-bit test that is not `1` is `0`. -/
theorem clsBit_zero_of_ne_one {b : BitVec 1} (h : ¬ (b = 1)) : b = 0 := by
  rcases clsBit_one_zero b with h1 | h0
  · exact absurd h1 h
  · exact h0

/-- **The class-C span at the arm's endpoint.**  At the seam and a byte at or above `110`
in the signed order the class's span exists: it ends at `if.then413.i` and costs at most
five links — `110` through `LeafBlock56`'s true arm (five), `111 … 115` through its else
arm (five), `116` from `LeafBlock58` itself (four) and everything above it through its
else arm (five, which `126`/`127` also take).  The target carry and state stay existential
because each leaf's `bind` is a different term; the block and the count are what
`classCMerge_at` reads.

The class's **upper** bound is not a premise: it is what separates `.classC` from
`.ws`/`.cleanup`, and both sides below the seam take the same four leaf routes. -/
theorem classCSpan_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.else387.i")
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0) :
    ∃ (Cs : WalkCarry G) (ss : State) (nS : Nat),
      Seg calls G C s Cs ss nS ∧ Cs.block = "if.then413.i" ∧ nS ≤ 5 := by
  by_cases h116 : evalICmp .slt x (BitVec.ofNat 8 116) = 1
  · -- `110 … 115`: `LeafBlock56`'s two arms
    by_cases h110e : evalICmp .eq x (BitVec.ofNat 8 110) = 1
    · exact ⟨_, _, 5, c56TrueSpan G C s hInv hblock h8 h110 h116 h110e, rfl, by decide⟩
    · have h110e0 : evalICmp .eq x (BitVec.ofNat 8 110) = 0 := clsBit_zero_of_ne_one h110e
      exact ⟨_, _, 5, c56ElseSpan G C s hInv hblock h8 h110 h116 h110e0, rfl, by decide⟩
  · -- `116 … 125`: `LeafBlock58`'s two arms
    have h116z : evalICmp .slt x (BitVec.ofNat 8 116) = 0 := clsBit_zero_of_ne_one h116
    by_cases h116e : evalICmp .eq x (BitVec.ofNat 8 116) = 1
    · exact ⟨_, _, 4, c58TrueSpan G C s hInv hblock h8 h110 h116z h116e, rfl, by decide⟩
    · have h116e0 : evalICmp .eq x (BitVec.ofNat 8 116) = 0 := clsBit_zero_of_ne_one h116e
      exact ⟨_, _, 5, c58ElseSpan G C s hInv hblock h8 h110 h116z h116e0, rfl, by decide⟩

/-- **The class's path to its leaf's endpoint, from the head segment and the class's
bits.**  The head's twelve links and `classCSpan_at`'s span compose at `12 + nS`, which is
the piece a producer of the merge needs before the tail: the endpoint is the class's leaf,
whose block and count bound are all `classCMerge_at` reads. -/
theorem classCHeadSpan_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm 12)
    (hm : Cm.block = "if.else387.i")
    {x : BitVec 8} (h8 : evalOperand sm (.reg "%8") = some (.int 8 x))
    (h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 0) :
    ∃ (Cs : WalkCarry G) (ss : State) (nS : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cs ss (12 + nS) ∧
      Cs.block = "if.then413.i" ∧ nS ≤ 5 := by
  obtain ⟨Cs, ss, nS, hSpan, hs, hnS⟩ :=
    classCSpan_at (G := G) (C := Cm) (s := sm) hHead.inv' hm h8 h110
  exact ⟨Cs, ss, nS, hHead.trans (Seg.measure hSpan), hs, hnS⟩

/-! ### The composition the exposure buys

`hcontToSpan` is `hcontHeadSeg12` composed with the class-C span; at the scan-free bundle
that composition is `hcontSpan17_of_cleanup` (`JsonStage2WalkDispatchCleanupSpan`), where
`HcontCleanupFacts` is in scope, and its consumer is `hcontPrefixCleanupSeg` there and
`walkRevolutionMergeSeg` (`JsonStage2WalkRevolutionSeg`). -/

/-! ### The run class's four segments, at the run's own count

`RunFacts` carries the class's four: the head's chain (`nH ≤ 12 + N`, the run `N` inside
it), the byte's span (`nS ≤ 5`), the tail's three calls on their scan arm and the scan's
landing's three links.  The composition below states them as one segment at that count,
which is the piece `runScanMerge_at` builds before the visits. -/
theorem runSegmentsAt {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : RunFacts G C s) :
    WalkSegment (stage2Calls stage2SubCalls) G C s f.Cm f.sm f.nH ∧
      Seg (stage2Calls stage2SubCalls) G f.Cm f.sm f.Cs f.ss f.nS ∧
      WalkSegment (stage2Calls stage2SubCalls) G f.Cs f.ss f.Ct f.st 3 ∧
      WalkSegment (stage2Calls stage2SubCalls) G f.Ct f.st f.Cl f.tl 3 ∧
      WalkSegment (stage2Calls stage2SubCalls) G C s f.Cl f.tl (f.nH + f.nS + 3 + 3) :=
  ⟨f.hHead, f.hSpan, f.hTail, f.hLatch,
    f.hHead.trans ((Seg.measure f.hSpan).trans (f.hTail.trans f.hLatch))⟩

/-! ### The empty tail's three links, for the scan-free class

`emptyTailSeg_of_calls` (`JsonStage2WalkDispatchWitnessHlast`) states the three links from
the three calls' rows at any carry whose block is `if.then413.i`.  The scan-free class's
carry is `ContTailStartC C` and its state `contTailStart`, so its `hTail` is that theorem
with the two test cells peeled: `%ee.1.i` is the seam's stored end (`contTailStart_ee`) and
`%cond350.i` the lane's word. -/

/-- **`%cond350.i` at the tail's start is the lane's word.**  `cond.end349.i` bound it and
no block of the byte's pivots or of the seam rebinds it. -/
theorem contTailStart_cond {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8) :
    lookupName (contTailStart C s x inc nep ep v ix b35 b8 x1).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 v.toNat)) := by
  simp only [contTailStart, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62, contSeamS, seamS,
    seamFin, stateAt, State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact contEndS_cond C s x inc nep ep v ix

/-- **The scan-free continuing tail, from the three calls' rows.**  `HcontCleanupFacts`'s
`hTail`, at the class's own seam. -/
theorem hcontTail_of_calls {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8) (b8 : BitVec 8) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) {cA rdv xA : BitVec 32}
    (hInvT : WalkInv G (ContTailStartC C) (contTailStart C s x inc nep ep v ix b35 b8 x1))
    (hblockT : (ContTailStartC C).block = "if.then413.i")
    {pT : String} (reg : String) {opT : Operand}
    (hpreT : (contTailStart C s x inc nep ep v ix b35 b8 x1).pre = some pT)
    (hincT : phiIncoming pT
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some opT)
    (hopT : evalOperand (stateAt (contTailStart C s x inc nep ep v ix b35 b8 x1).env
      (contTailStart C s x inc nep ep v ix b35 b8 x1)) opT = some (.int 32 cA))
    (hkindT : lookupName (contTailStart C s x inc nep ep v ix b35 b8 x1).env "%kind404.i" =
      some (.ptr (C.stage.tok + 16)))
    (hrdT : lookupName (contTailStart C s x inc nep ep v ix b35 b8 x1).env "%root_done.i" =
      some (.ptr (G.next0 + 8)))
    (hreadRoot : readBytes
      (writeBytes (contTailStart C s x inc nep ep v ix b35 b8 x1).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpre₁ : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (ContTailStartC C).sp), .int 32 rdv,
       .ptr (ContTailStartC C).stage.ctype, .ptr (ContTailStartC C).stage.cst]
      (writeBytes (contTailStart C s x inc nep ep v ix b35 b8 x1).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (contTailStart C s x inc nep ep v ix b35 b8 x1).next)
    (hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (ContTailStartC C).sp), .int 32 rdv,
       .ptr (ContTailStartC C).stage.ctype, .ptr (ContTailStartC C).stage.cst]
      (writeBytes (contTailStart C s x inc nep ep v ix b35 b8 x1).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (contTailStart C s x inc nep ep v ix b35 b8 x1).next =
      some r₁)
    (hret₁ : r₁.ret = .int 32 xA)
    (hbit0T : evalICmp .eq xA (BitVec.ofNat 32 0) = 0)
    (hzread : readBytes
      (writeBytes (contTailStart C s x inc nep ep v ix b35 b8 x1).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) C.stage.z 8 = some (wordBytes 8 G.ev))
    (hcT : lookupName (contTailStart C s x inc nep ep v ix b35 b8 x1).env "%c.i" =
      some (.ptr (TailCarry₂ (ContTailStartC C)).stage.c))
    (htT : lookupName (contTailStart C s x inc nep ep v ix b35 b8 x1).env "%t352.i" =
      some (.ptr (TailCarry₂ (ContTailStartC C)).stage.tok))
    (hoT : lookupName (contTailStart C s x inc nep ep v ix b35 b8 x1).env "%z" =
      some (.ptr (TailCarry₂ (ContTailStartC C)).stage.z))
    (hpre₂ : s2ScalarValuePre
      [.ptr (TailCarry₂ (ContTailStartC C)).stage.c,
       .ptr (TailCarry₂ (ContTailStartC C)).stage.tok,
       .ptr (TailCarry₂ (ContTailStartC C)).stage.z] r₁.mem r₁.next)
    (hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr (TailCarry₂ (ContTailStartC C)).stage.c,
       .ptr (TailCarry₂ (ContTailStartC C)).stage.tok,
       .ptr (TailCarry₂ (ContTailStartC C)).stage.z] r₁.mem r₁.next = some r₂)
    (hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1))
    (hev64 : G.ev < 2 ^ 64)
    (htight : (ContTailStartC C).events.length ≤ (ContTailStartC C).k)
    (hklt : (ContTailStartC C).k < G.nep)
    (hpre₃ : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 (ContTailStartC C).sp), .ptr (G.next0 + 8),
       .ptr (ContTailStartC C).stage.ctype,
       .ptr (ContTailStartC C).stage.cst] r₂.mem r₂.next)
    (hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 (ContTailStartC C).sp), .ptr (G.next0 + 8),
       .ptr (ContTailStartC C).stage.ctype,
       .ptr (ContTailStartC C).stage.cst] r₂.mem r₂.next = some r₃)
    (hv64 : v.toNat < 2 ^ 64) :
    ∃ ev : EventRecord,
      WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
        (contTailStart C s x inc nep ep v ix b35 b8 x1)
        (TailCarryEnd (ContTailStartC C) ev)
        (contCleanupEnd C s x inc nep ep v ix b35 b8 x1 r₁ r₂ r₃ cA rdv xA) 3 :=
  emptyTailSeg_of_calls G (ContTailStartC C)
    (contTailStart C s x inc nep ep v ix b35 b8 x1) r₁ r₂ r₃ v.toNat hInvT hblockT reg
    hpreT hincT hopT hkindT hrdT hreadRoot hpre₁ hcall₁ hret₁ hbit0T hzread hcT htT hoT
    hpre₂ hcall₂ hret₂ hev64 htight hklt hpre₃ hcall₃
    (contTailStart_ee C s x inc nep ep v ix b35 b8 x1)
    (contTailStart_cond C s x inc nep ep v ix b35 b8 x1) hv64

/-! ### The scalar route's tail, from the three calls' rows

`HcontScalarFacts` (`JsonStage2WalkHcontScalar`) carries its tail as a field.  Its seam is
`scSeamS`, the tag test's *true* arm, and its two test cells are that seam's own:
`scSeam_ee` is the stored end (`%ee.1.i = ofNat 64 v.toNat`) and `scSeam_cond` the bound, so
the copy call's guard is `ult v v` and the walk leaves for `if.end473.i`.  With those two
peels the field is the same producer the high-byte route consumes:
`emptyTailSeg_of_calls`, at this seam's carry and state. -/

/-- **The continuing scalar route's tail, from the three calls' rows.**  `HcontScalarFacts`'s
`hTail`, at the tag-true seam: the value-position call, the scalar call's emit arm and the
copy call, then the scan-free arm's three links. -/
theorem scContTail_of_calls {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8)
    (r₁ r₂ r₃ : CallOutcome) {cA rdv xA : BitVec 32}
    (hInvS : WalkInv G (HeadC₄₁₃ (ContAC₇ C)) (scSeamS C s x inc nep ep v ix b35))
    {pT : String} (reg : String) {opT : Operand}
    (hpreT : (scSeamS C s x inc nep ep v ix b35).pre = some pT)
    (hincT : phiIncoming pT
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some opT)
    (hopT : evalOperand (stateAt (scSeamS C s x inc nep ep v ix b35).env
      (scSeamS C s x inc nep ep v ix b35)) opT = some (.int 32 cA))
    (hkindT : lookupName (scSeamS C s x inc nep ep v ix b35).env "%kind404.i" =
      some (.ptr (C.stage.tok + 16)))
    (hrdT : lookupName (scSeamS C s x inc nep ep v ix b35).env "%root_done.i" =
      some (.ptr (G.next0 + 8)))
    (hreadRoot : readBytes
      (writeBytes (scSeamS C s x inc nep ep v ix b35).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpre₁ : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (HeadC₄₁₃ (ContAC₇ C)).sp), .int 32 rdv,
       .ptr (HeadC₄₁₃ (ContAC₇ C)).stage.ctype, .ptr (HeadC₄₁₃ (ContAC₇ C)).stage.cst]
      (writeBytes (scSeamS C s x inc nep ep v ix b35).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (scSeamS C s x inc nep ep v ix b35).next)
    (hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (HeadC₄₁₃ (ContAC₇ C)).sp), .int 32 rdv,
       .ptr (HeadC₄₁₃ (ContAC₇ C)).stage.ctype, .ptr (HeadC₄₁₃ (ContAC₇ C)).stage.cst]
      (writeBytes (scSeamS C s x inc nep ep v ix b35).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (scSeamS C s x inc nep ep v ix b35).next = some r₁)
    (hret₁ : r₁.ret = .int 32 xA)
    (hbit0T : evalICmp .eq xA (BitVec.ofNat 32 0) = 0)
    (hzread : readBytes
      (writeBytes (scSeamS C s x inc nep ep v ix b35).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) C.stage.z 8 = some (wordBytes 8 G.ev))
    (hcT : lookupName (scSeamS C s x inc nep ep v ix b35).env "%c.i" =
      some (.ptr (TailCarry₂ (HeadC₄₁₃ (ContAC₇ C))).stage.c))
    (htT : lookupName (scSeamS C s x inc nep ep v ix b35).env "%t352.i" =
      some (.ptr (TailCarry₂ (HeadC₄₁₃ (ContAC₇ C))).stage.tok))
    (hoT : lookupName (scSeamS C s x inc nep ep v ix b35).env "%z" =
      some (.ptr (TailCarry₂ (HeadC₄₁₃ (ContAC₇ C))).stage.z))
    (hpre₂ : s2ScalarValuePre
      [.ptr (TailCarry₂ (HeadC₄₁₃ (ContAC₇ C))).stage.c,
       .ptr (TailCarry₂ (HeadC₄₁₃ (ContAC₇ C))).stage.tok,
       .ptr (TailCarry₂ (HeadC₄₁₃ (ContAC₇ C))).stage.z] r₁.mem r₁.next)
    (hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr (TailCarry₂ (HeadC₄₁₃ (ContAC₇ C))).stage.c,
       .ptr (TailCarry₂ (HeadC₄₁₃ (ContAC₇ C))).stage.tok,
       .ptr (TailCarry₂ (HeadC₄₁₃ (ContAC₇ C))).stage.z] r₁.mem r₁.next = some r₂)
    (hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1))
    (hev64 : G.ev < 2 ^ 64)
    (htight : (HeadC₄₁₃ (ContAC₇ C)).events.length ≤ (HeadC₄₁₃ (ContAC₇ C)).k)
    (hklt : (HeadC₄₁₃ (ContAC₇ C)).k < G.nep)
    (hpre₃ : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 (HeadC₄₁₃ (ContAC₇ C)).sp), .ptr (G.next0 + 8),
       .ptr (HeadC₄₁₃ (ContAC₇ C)).stage.ctype,
       .ptr (HeadC₄₁₃ (ContAC₇ C)).stage.cst] r₂.mem r₂.next)
    (hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 (HeadC₄₁₃ (ContAC₇ C)).sp), .ptr (G.next0 + 8),
       .ptr (HeadC₄₁₃ (ContAC₇ C)).stage.ctype,
       .ptr (HeadC₄₁₃ (ContAC₇ C)).stage.cst] r₂.mem r₂.next = some r₃)
    (hv64 : v.toNat < 2 ^ 64) :
    ∃ ev : EventRecord,
      WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (ContAC₇ C))
        (scSeamS C s x inc nep ep v ix b35)
        (scTailC C ev)
        (scEnd C s x inc nep ep v ix b35 r₁ r₂ r₃ cA rdv xA) 3 :=
  emptyTailSeg_of_calls G (HeadC₄₁₃ (ContAC₇ C))
    (scSeamS C s x inc nep ep v ix b35) r₁ r₂ r₃ v.toNat hInvS rfl reg
    hpreT hincT hopT hkindT hrdT hreadRoot hpre₁ hcall₁ hret₁ hbit0T hzread hcT htT hoT
    hpre₂ hcall₂ hret₂ hev64 htight hklt hpre₃ hcall₃
    (scSeam_ee C s x inc nep ep v ix b35)
    (scSeam_cond C s x inc nep ep v ix b35) hv64

/-! ### The run's counted composition

`runSegmentsAt`'s last conjunct is the four segments as one, which is what the scan's
composition appends its rounds to.  Named here so the counted form has a consumer at the
count it is stated at. -/

/-- **The run class's four segments, composed.**  The head's `nH`, the span's `nS`, the
tail's three and the latch's three, from `f.Cl`/`f.tl` back to the head. -/
theorem runToLatchSeg_at {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (f : RunFacts G C s) :
    WalkSegment (stage2Calls stage2SubCalls) G C s f.Cl f.tl (f.nH + f.nS + 3 + 3) :=
  (runSegmentsAt f).2.2.2.2

/-! ### The scan-free arm, from the three calls' rows

The staging producer (`hcontCleanupFacts_of_staging`) takes the bundle's `hTail` as a
premise; with `hcontTail_of_calls` it takes the three callees' rows instead, and the
bundle's `ev` is the producer's existentially — so the arm no longer forces a caller to
name the event record.  Nothing else about the arm changes: the head's class, the lane and
the document's byte still enter as the staging producer takes them. -/

/-- The class's tail start, at the staging's own three witnesses: `%8`'s byte, the two
counts, the position table, the entry's index and the byte before the entry's end. -/
abbrev contTailStartAt {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (v : BitVec 32) : State :=
  contTailStart C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v (contIx G C)
    (contB35 G v) (hlastByte G C) (hlastByte G C)

/-- **The scan-free continuing arm, from the three calls' rows.** -/
theorem hcontArm_cleanup_of_calls {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    {v : BitVec 32}
    (hread : readBytes (contAS₅ s (hlastByte G C) (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4))
    (hspan : v.toNat ≤ entryPos G (C.k + 1))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat)
      (BitVec.ofNat 64 (entryPos G C.k)) = 1)
    (hb13 : evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 (contB35 G v)) (BitVec.ofNat 8 13) = 0)
    (r₁ r₂ r₃ : CallOutcome) {cA rdv xA : BitVec 32} (reg : String)
    (hInvT : WalkInv G (ContTailStartC C) (contTailStartAt (C := C) (s := s) v))
    (hblockT : (ContTailStartC C).block = "if.then413.i")
    {pT : String} {opT : Operand}
    (hpreT : (contTailStartAt (C := C) (s := s) v).pre = some pT)
    (hincT : phiIncoming pT
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some opT)
    (hopT : evalOperand (stateAt (contTailStartAt (C := C) (s := s) v).env
      (contTailStartAt (C := C) (s := s) v)) opT = some (.int 32 cA))
    (hkindT : lookupName (contTailStartAt (C := C) (s := s) v).env "%kind404.i" =
      some (.ptr (C.stage.tok + 16)))
    (hrdT : lookupName (contTailStartAt (C := C) (s := s) v).env "%root_done.i" =
      some (.ptr (G.next0 + 8)))
    (hreadRoot : readBytes
      (writeBytes (contTailStartAt (C := C) (s := s) v).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpre₁ : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (ContTailStartC C).sp), .int 32 rdv,
       .ptr (ContTailStartC C).stage.ctype, .ptr (ContTailStartC C).stage.cst]
      (writeBytes (contTailStartAt (C := C) (s := s) v).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (contTailStartAt (C := C) (s := s) v).next)
    (hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (ContTailStartC C).sp), .int 32 rdv,
       .ptr (ContTailStartC C).stage.ctype, .ptr (ContTailStartC C).stage.cst]
      (writeBytes (contTailStartAt (C := C) (s := s) v).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (contTailStartAt (C := C) (s := s) v).next = some r₁)
    (hret₁ : r₁.ret = .int 32 xA)
    (hbit0T : evalICmp .eq xA (BitVec.ofNat 32 0) = 0)
    (hzread : readBytes
      (writeBytes (contTailStartAt (C := C) (s := s) v).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) C.stage.z 8 = some (wordBytes 8 G.ev))
    (hcT : lookupName (contTailStartAt (C := C) (s := s) v).env "%c.i" =
      some (.ptr (TailCarry₂ (ContTailStartC C)).stage.c))
    (htT : lookupName (contTailStartAt (C := C) (s := s) v).env "%t352.i" =
      some (.ptr (TailCarry₂ (ContTailStartC C)).stage.tok))
    (hoT : lookupName (contTailStartAt (C := C) (s := s) v).env "%z" =
      some (.ptr (TailCarry₂ (ContTailStartC C)).stage.z))
    (hpre₂ : s2ScalarValuePre
      [.ptr (TailCarry₂ (ContTailStartC C)).stage.c,
       .ptr (TailCarry₂ (ContTailStartC C)).stage.tok,
       .ptr (TailCarry₂ (ContTailStartC C)).stage.z] r₁.mem r₁.next)
    (hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr (TailCarry₂ (ContTailStartC C)).stage.c,
       .ptr (TailCarry₂ (ContTailStartC C)).stage.tok,
       .ptr (TailCarry₂ (ContTailStartC C)).stage.z] r₁.mem r₁.next = some r₂)
    (hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1))
    (hev64 : G.ev < 2 ^ 64)
    (htight : (ContTailStartC C).events.length ≤ (ContTailStartC C).k)
    (hklt : (ContTailStartC C).k < G.nep)
    (hpre₃ : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 (ContTailStartC C).sp), .ptr (G.next0 + 8),
       .ptr (ContTailStartC C).stage.ctype,
       .ptr (ContTailStartC C).stage.cst] r₂.mem r₂.next)
    (hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 (ContTailStartC C).sp), .ptr (G.next0 + 8),
       .ptr (ContTailStartC C).stage.ctype,
       .ptr (ContTailStartC C).stage.cst] r₂.mem r₂.next = some r₃)
    (hv64 : v.toNat < 2 ^ 64) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  obtain ⟨ev, hTail⟩ :=
    hcontTail_of_calls G C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v
      (contIx G C) (contB35 G v) (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ hInvT hblockT
      reg hpreT hincT hopT hkindT hrdT hreadRoot hpre₁ hcall₁ hret₁ hbit0T hzread hcT htT
      hoT hpre₂ hcall₂ hret₂ hev64 htight hklt hpre₃ hcall₃ hv64
  exact ⟨hcontArm_cleanup_of_staging G C s hInv hk hlt125 hne125 hread hspan hugt hb13
    hb32 hbne13 r₁ r₂ r₃ ev (cA := cA) (rdv := rdv) (xA := xA) hTail⟩

/-- **The scan-free continuing dispatch, from the three calls' rows.** -/
theorem walkDispatch_at_cleanup_of_calls {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    {v : BitVec 32}
    (hread : readBytes (contAS₅ s (hlastByte G C) (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4))
    (hspan : v.toNat ≤ entryPos G (C.k + 1))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat)
      (BitVec.ofNat 64 (entryPos G C.k)) = 1)
    (hb13 : evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 13) = 0)
    (hb32 : evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 32) = 1)
    (hbne13 : evalICmp .eq (cont35 (contB35 G v)) (BitVec.ofNat 8 13) = 0)
    (r₁ r₂ r₃ : CallOutcome) {cA rdv xA : BitVec 32} (reg : String)
    (hInvT : WalkInv G (ContTailStartC C) (contTailStartAt (C := C) (s := s) v))
    (hblockT : (ContTailStartC C).block = "if.then413.i")
    {pT : String} {opT : Operand}
    (hpreT : (contTailStartAt (C := C) (s := s) v).pre = some pT)
    (hincT : phiIncoming pT
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some opT)
    (hopT : evalOperand (stateAt (contTailStartAt (C := C) (s := s) v).env
      (contTailStartAt (C := C) (s := s) v)) opT = some (.int 32 cA))
    (hkindT : lookupName (contTailStartAt (C := C) (s := s) v).env "%kind404.i" =
      some (.ptr (C.stage.tok + 16)))
    (hrdT : lookupName (contTailStartAt (C := C) (s := s) v).env "%root_done.i" =
      some (.ptr (G.next0 + 8)))
    (hreadRoot : readBytes
      (writeBytes (contTailStartAt (C := C) (s := s) v).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4))
    (hpre₁ : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (ContTailStartC C).sp), .int 32 rdv,
       .ptr (ContTailStartC C).stage.ctype, .ptr (ContTailStartC C).stage.cst]
      (writeBytes (contTailStartAt (C := C) (s := s) v).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (contTailStartAt (C := C) (s := s) v).next)
    (hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 (ContTailStartC C).sp), .int 32 rdv,
       .ptr (ContTailStartC C).stage.ctype, .ptr (ContTailStartC C).stage.cst]
      (writeBytes (contTailStartAt (C := C) (s := s) v).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) (contTailStartAt (C := C) (s := s) v).next = some r₁)
    (hret₁ : r₁.ret = .int 32 xA)
    (hbit0T : evalICmp .eq xA (BitVec.ofNat 32 0) = 0)
    (hzread : readBytes
      (writeBytes (contTailStartAt (C := C) (s := s) v).mem (C.stage.tok + 16)
        (natToBytes cA.toNat 4)) C.stage.z 8 = some (wordBytes 8 G.ev))
    (hcT : lookupName (contTailStartAt (C := C) (s := s) v).env "%c.i" =
      some (.ptr (TailCarry₂ (ContTailStartC C)).stage.c))
    (htT : lookupName (contTailStartAt (C := C) (s := s) v).env "%t352.i" =
      some (.ptr (TailCarry₂ (ContTailStartC C)).stage.tok))
    (hoT : lookupName (contTailStartAt (C := C) (s := s) v).env "%z" =
      some (.ptr (TailCarry₂ (ContTailStartC C)).stage.z))
    (hpre₂ : s2ScalarValuePre
      [.ptr (TailCarry₂ (ContTailStartC C)).stage.c,
       .ptr (TailCarry₂ (ContTailStartC C)).stage.tok,
       .ptr (TailCarry₂ (ContTailStartC C)).stage.z] r₁.mem r₁.next)
    (hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr (TailCarry₂ (ContTailStartC C)).stage.c,
       .ptr (TailCarry₂ (ContTailStartC C)).stage.tok,
       .ptr (TailCarry₂ (ContTailStartC C)).stage.z] r₁.mem r₁.next = some r₂)
    (hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1))
    (hev64 : G.ev < 2 ^ 64)
    (htight : (ContTailStartC C).events.length ≤ (ContTailStartC C).k)
    (hklt : (ContTailStartC C).k < G.nep)
    (hpre₃ : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 (ContTailStartC C).sp), .ptr (G.next0 + 8),
       .ptr (ContTailStartC C).stage.ctype,
       .ptr (ContTailStartC C).stage.cst] r₂.mem r₂.next)
    (hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 (ContTailStartC C).sp), .ptr (G.next0 + 8),
       .ptr (ContTailStartC C).stage.ctype,
       .ptr (ContTailStartC C).stage.cst] r₂.mem r₂.next = some r₃)
    (hv64 : v.toNat < 2 ^ 64) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s := by
  obtain ⟨arm⟩ := hcontArm_cleanup_of_calls G C s hInv hk hlt125 hne125 hread hspan hugt
    hb13 hb32 hbne13 r₁ r₂ r₃ reg hInvT hblockT hpreT hincT hopT hkindT hrdT hreadRoot
    hpre₁ hcall₁ hret₁ hbit0T hzread hcT htT hoT hpre₂ hcall₂ hret₂ hev64 htight hklt
    hpre₃ hcall₃ hv64
  exact HcontArm.dispatch hInv hblock hk arm

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.clsBit_one_zero
#print axioms LeanLLVM.Refinement.WalkScope.clsBit_zero_of_ne_one
#print axioms LeanLLVM.Refinement.WalkScope.classCSpan_at
#print axioms LeanLLVM.Refinement.WalkScope.classCHeadSpan_at
#print axioms LeanLLVM.Refinement.WalkScope.runSegmentsAt
#print axioms LeanLLVM.Refinement.WalkScope.contTailStart_cond
#print axioms LeanLLVM.Refinement.WalkScope.hcontTail_of_calls
#print axioms LeanLLVM.Refinement.WalkScope.scContTail_of_calls
#print axioms LeanLLVM.Refinement.WalkScope.runToLatchSeg_at
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_cleanup_of_calls
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_cleanup_of_calls

end WalkScope
end LeanLLVM.Refinement
