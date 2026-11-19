/-
# The last entry's arm rows: what is produced, and what is still supply

`HlastArmRows` (`JsonStage2WalkDispatchLastRows`) carries five rows, each one a
`lastEntryArm_*_of_staging` producer's argument list after the invariant, the guard and the
class's bits.  This module settles which of the five the tree can *produce* and which it can
only take.

## The rows, and what each one is

| row | fields | what the tree supplies |
|---|---|---|
| `.scalar` | the last byte's three class bits, one root-slot read, the three calls at `scalarSeam` | **nothing**: the document's last byte's class and the three callees' rows are the supply itself |
| `.letters` | a head chain to `if.else387.i`, a tail at `LetS413 sm x` | **the tail**, from the three calls (`lettersSpan` + `emptyTailSeg_of_calls`); the head chain is the row's input |
| `.fLetter` | the same at `FS413 sm x` | **the tail**, from the same three calls (`fSpan` + `emptyTailSeg_of_calls`) |
| `.classC` | a head chain, a span, a tail | **the span** (`classCSpan_at`, from the head's `%8 < 110` bit) and **the tail**; the head chain and the span's endpoint are the row's input |
| `.run` | a head chain, a span, a tail, a latch, the scan's counters and `ScanVisits` | **nothing**: the head is the same missing chain as `.letters`, and the remainder is the run's seam group and traversal |

So the two default-arm leaves' tails and the class-C row's span and tail are theorems here:
a row no longer assumes a tail segment, only the three callees' rows at the seam.  The
rows themselves are `hlastLettersRows_of_head`, `hlastFLetterRows_of_head` and
`hlastClassCRows_of_span`, with the class-C span's producer `hlastClassCSpan_of_head`
beside them; `.scalar` and `.run` have no producer here.  The three things that remain,
and that no theorem in this tree produces, are:

* **the head chain at a document byte on `if.end372.i`'s leaf routes.**  The last
  entry's chains (`contLastLowHeadSeg` … `contLastBrcHeadSeg`,
  `JsonStage2WalkDispatchLettersHead`) are stated for a document whose last byte is the
  *scan-free* class (`slt %8 13 = 0`, `slt %8 32 = 1`, `%8 ≠ 13`), but a row's guard names
  the entry's byte and says nothing about the document's.  The other two byte routes reach
  `if.end372.i` through `LeafBlock33`/`LeafBlock37` (`contByteSegScanFree`/`Low`/`High`,
  `JsonStage2WalkDispatchLeafBytes`), which is stated at the *continuing* count only;
  their last-entry twins are the producer the head chains above are waiting on;
* **the three callees' rows at the seam each class reaches** — `.scalar`'s at `scalarSeam`
  with the scalar route's kind literal, the letters and `'f'` routes' at `LetS413`/`FS413`
  (kinds `0`, `9`), and the class-C leaves' at `ClsS413T`/`ClsS413F`/`ClsS58T`/`HeadS413`
  (kinds `10`, `10`, `8`, `7`).  `HlastClassRows.seam` states the group at the byte-route
  seam with one kind literal, its `cA`; the letters and class-C routes read their own
  literal, so that field does not supply their tails;
* **the run's own traversal** — its stop, the landing's byte and the scan's visits — which
  `HlastWsSeam`/`runLastFacts_of_seam` (`JsonStage2WalkDispatchRunLastSeam`) state but do
  not produce at a variable geometry.

## The guards, and the classes they name

`HlastArmRows`' fields are `∀`-fields, so a row is demanded at every byte its guard admits.
Three guards admitted a byte the head switch sends to another arm, and `HlastArmRows` now
excludes the ones the case decides first: `.letters` and `.run` carry `%8 ≠ 34` (the
standalone opener) and `.classC` carries `%8 ≠ 123`, `%8 ≠ 125` (the container braces).
The theorems below witness both halves — the bits that still hold at those bytes, and the
exclusion that now fails there — so the exclusion is what closes the overlap and not a
changed conclusion.

Two residual overlaps remain, and they are recorded rather than repaired:

* `.letters`' narrowed guard still holds at `44`, `58`, `91` and `93` — the comma, the
  colon and the two brackets — which the class case dispatches to their own arms
  (`h44eq`, `h58eq`, `h91eq`, `h93eq` in `JsonStage2WalkPremisesOfStaging`);
* `.run`'s narrowed guard still holds at those four bytes and at `123`/`125`, because its
  guard is the tag test, the exclusion and `wsStop G (G.n - 1)` alone.

`.scalar`'s guard is exact at all of them (`%8 < 44` holds at `34`, and `%8 < 58` fails at
`123`), and `.fLetter`'s pins `%8 = 102`, so the imprecision is in those two rows.  A row
whose guard admits a byte the switch sends elsewhere must hold at that byte too; whether
the letters route reaches `if.else387.i` from a lone `"` or a comma is a question about the
walk's path, not about this module, and the byte facts above are the evidence the question
rests on.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchLastRows

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The seam's supply, as one structure

`emptyTailSeg_of_calls` reads twenty-eight premises, and every one of them is a fact about
the seam *state* or a callee's answer — none is a segment.  The structure below groups them
so a row's producer takes one argument, and so the report can name what the row still
waits on.  The kind literal `cA` and the two cells `%ee.1.i`/`%cond350.i` are fields
because the memories the calls read mention them. -/
structure HlastSeamTailSupply {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  /-- The predecessor the seam's `phi` reads, and the operand it selects. -/
  p : String
  op : Operand
  /-- The kind literal `if.then413.i`'s `phi` selects. -/
  cA : BitVec 32
  /-- The root-done slot's word, as the first call's argument list carries it. -/
  rdv : BitVec 32
  xA : BitVec 32
  r₁ : CallOutcome
  r₂ : CallOutcome
  r₃ : CallOutcome
  /-- The two test cells' one number: `%ee.1.i` and `%cond350.i` at the seam. -/
  cd : Nat
  hpre : s.pre = some p
  hphi : phiIncoming p
    [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
     ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
     ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
     ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
     ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some op
  hop : evalOperand (stateAt s.env s) op = some (.int 32 cA)
  hkind : lookupName s.env "%kind404.i" = some (.ptr (C.stage.tok + 16))
  hrd : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8))
  hread : readBytes
    (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4))
    (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)
  hpre₁ : s2ValuePosPre
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
     .ptr C.stage.ctype, .ptr C.stage.cst]
    (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)) s.next
  hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
     .ptr C.stage.ctype, .ptr C.stage.cst]
    (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)) s.next = some r₁
  hret₁ : r₁.ret = .int 32 xA
  hbit0 : evalICmp .eq xA (BitVec.ofNat 32 0) = 0
  hzread : readBytes
    (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)) C.stage.z 8 =
      some (wordBytes 8 G.ev)
  hc : lookupName s.env "%c.i" = some (.ptr (TailCarry₂ C).stage.c)
  ht : lookupName s.env "%t352.i" = some (.ptr (TailCarry₂ C).stage.tok)
  ho : lookupName s.env "%z" = some (.ptr (TailCarry₂ C).stage.z)
  hpre₂ : s2ScalarValuePre
    [.ptr (TailCarry₂ C).stage.c, .ptr (TailCarry₂ C).stage.tok,
     .ptr (TailCarry₂ C).stage.z] r₁.mem r₁.next
  hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
    [.ptr (TailCarry₂ C).stage.c, .ptr (TailCarry₂ C).stage.tok,
     .ptr (TailCarry₂ C).stage.z] r₁.mem r₁.next = some r₂
  hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1)
  hev64 : G.ev < 2 ^ 64
  /-- The trace is not past the entry: the copy call's room, and the append's. -/
  htight : C.events.length ≤ C.k
  hklt : C.k < G.nep
  hpre₃ : s2AfterValuePre
    [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
     .ptr C.stage.ctype, .ptr C.stage.cst] r₂.mem r₂.next
  hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
    [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
     .ptr C.stage.ctype, .ptr C.stage.cst] r₂.mem r₂.next = some r₃
  hei : lookupName s.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 cd))
  hcd : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd))
  hcd64 : cd < 2 ^ 64

/-! ### The token cell survives the tail's three states -/

/-- `%t352.i` at the scan's entry is the tail's source's: the three tail blocks bind their
own cells (`%.sink372`, `%38`, `%cmp451.i` and the four answer cells) and none of them is
the token record's register. -/
theorem lastArmScanEntry_envTok (s : State) (r₁ r₂ r₃ : CallOutcome) (ei cd : Nat)
    (c rdv xA : BitVec 32) :
    lookupName (ScanEntry s r₁ r₂ r₃ ei cd c rdv xA).env "%t352.i" =
      lookupName s.env "%t352.i" := by
  simp only [ScanEntry, TailS₃, stateAt, cells]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-! ### The letters row's tail

`lettersSpan` composes the four links below `if.else387.i` from the class's bits and the
head segment's invariant, and `emptyTailSeg_of_calls` composes the three calls at its
endpoint.  So the row's `hTail`, its target's block and index, and the token cell are
theorems given the head segment and the seam's supply. -/

/-- **The letters row, from the head segment and the seam's supply.**  The head chain is
the row's input — the tree's last-entry chains are stated for a scan-free document byte
only, so a producer of the chain at every byte does not exist yet — and everything else in
the row is produced here. -/
noncomputable def hlastLettersRows_of_head {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH) (hnH : nH ≤ 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (hlastByte G C)))
    (h110 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 1)
    (hne102 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 102) = 0)
    (sup : HlastSeamTailSupply G (HeadC₄₁₃ (LetC₄₀₅ Cm))
      (LetS413 sm (hlastByte G C))) :
    HlastLettersRows G C s := by
  have hspan : Seg (stage2Calls stage2SubCalls) G Cm sm
      (HeadC₄₁₃ (LetC₄₀₅ Cm)) (LetS413 sm (hlastByte G C)) 4 :=
    lettersSpan (calls := stage2Calls stage2SubCalls) (G := G) (C := Cm) (s := sm)
      hHead.inv' hm h8m h110 hne102
  have hInv : WalkInv G (HeadC₄₁₃ (LetC₄₀₅ Cm)) (LetS413 sm (hlastByte G C)) :=
    (Seg.measure hspan).inv'
  have hblock : (HeadC₄₁₃ (LetC₄₀₅ Cm)).block = "if.then413.i" := rfl
  have hEx : ∃ ev : EventRecord,
      WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
        (LetS413 sm (hlastByte G C)) (TailCarryEnd (HeadC₄₁₃ (LetC₄₀₅ Cm)) ev)
        (ScanEntry (LetS413 sm (hlastByte G C)) sup.r₁ sup.r₂ sup.r₃ sup.cd sup.cd sup.cA
          sup.rdv sup.xA) 3 :=
    emptyTailSeg_of_calls G (HeadC₄₁₃ (LetC₄₀₅ Cm)) (LetS413 sm (hlastByte G C))
      sup.r₁ sup.r₂ sup.r₃ sup.cd hInv hblock (p := sup.p) (reg := "%8") (op := sup.op)
      sup.hpre sup.hphi sup.hop
      sup.hkind sup.hrd sup.hread sup.hpre₁ sup.hcall₁ sup.hret₁ sup.hbit0 sup.hzread sup.hc
      sup.ht sup.ho sup.hpre₂ sup.hcall₂ sup.hret₂ sup.hev64 sup.htight sup.hklt sup.hpre₃
      sup.hcall₃ sup.hei sup.hcd sup.hcd64
  let ev : EventRecord := Classical.choose hEx
  have hseg : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
      (LetS413 sm (hlastByte G C)) (TailCarryEnd (HeadC₄₁₃ (LetC₄₀₅ Cm)) ev)
      (ScanEntry (LetS413 sm (hlastByte G C)) sup.r₁ sup.r₂ sup.r₃ sup.cd sup.cd sup.cA
        sup.rdv sup.xA) 3 :=
    Classical.choose_spec hEx
  refine ⟨Cm, sm, nH, hHead, hnH, hm, hmk, h8m,
    TailCarryEnd (HeadC₄₁₃ (LetC₄₀₅ Cm)) ev,
    ScanEntry (LetS413 sm (hlastByte G C)) sup.r₁ sup.r₂ sup.r₃ sup.cd sup.cd sup.cA sup.rdv
      sup.xA,
    (TailCarry₂ (HeadC₄₁₃ (LetC₄₀₅ Cm))).stage.tok, hseg, rfl, ?_, ?_⟩
  · show Cm.k = C.k
    exact hmk
  · rw [lastArmScanEntry_envTok]
    exact sup.ht

/-! ### The `'f'` row's tail -/

/-- **The `'f'` row, from the head segment and the seam's supply.**  The same shape at
`fSpan`'s four links and `FS413`'s endpoint. -/
noncomputable def hlastFLetterRows_of_head {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH) (hnH : nH ≤ 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (hlastByte G C)))
    (h110 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 1)
    (h102 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 102) = 1)
    (sup : HlastSeamTailSupply G (FC₄₁₃ Cm) (FS413 sm (hlastByte G C))) :
    HlastFLetterRows G C s := by
  have hspan : Seg (stage2Calls stage2SubCalls) G Cm sm (FC₄₁₃ Cm)
      (FS413 sm (hlastByte G C)) 4 :=
    fSpan (calls := stage2Calls stage2SubCalls) (G := G) (C := Cm) (s := sm)
      hHead.inv' hm h8m h110 h102
  have hInv : WalkInv G (FC₄₁₃ Cm) (FS413 sm (hlastByte G C)) :=
    (Seg.measure hspan).inv'
  have hblock : (FC₄₁₃ Cm).block = "if.then413.i" := rfl
  have hEx : ∃ ev : EventRecord,
      WalkSegment (stage2Calls stage2SubCalls) G (FC₄₁₃ Cm)
        (FS413 sm (hlastByte G C)) (TailCarryEnd (FC₄₁₃ Cm) ev)
        (ScanEntry (FS413 sm (hlastByte G C)) sup.r₁ sup.r₂ sup.r₃ sup.cd sup.cd sup.cA
          sup.rdv sup.xA) 3 :=
    emptyTailSeg_of_calls G (FC₄₁₃ Cm) (FS413 sm (hlastByte G C))
      sup.r₁ sup.r₂ sup.r₃ sup.cd hInv hblock (p := sup.p) (reg := "%8") (op := sup.op)
      sup.hpre sup.hphi sup.hop
      sup.hkind sup.hrd sup.hread sup.hpre₁ sup.hcall₁ sup.hret₁ sup.hbit0 sup.hzread sup.hc
      sup.ht sup.ho sup.hpre₂ sup.hcall₂ sup.hret₂ sup.hev64 sup.htight sup.hklt sup.hpre₃
      sup.hcall₃ sup.hei sup.hcd sup.hcd64
  let ev : EventRecord := Classical.choose hEx
  have hseg : WalkSegment (stage2Calls stage2SubCalls) G (FC₄₁₃ Cm)
      (FS413 sm (hlastByte G C)) (TailCarryEnd (FC₄₁₃ Cm) ev)
      (ScanEntry (FS413 sm (hlastByte G C)) sup.r₁ sup.r₂ sup.r₃ sup.cd sup.cd sup.cA
        sup.rdv sup.xA) 3 :=
    Classical.choose_spec hEx
  refine ⟨Cm, sm, nH, hHead, hnH, hm, hmk, h8m, TailCarryEnd (FC₄₁₃ Cm) ev,
    ScanEntry (FS413 sm (hlastByte G C)) sup.r₁ sup.r₂ sup.r₃ sup.cd sup.cd sup.cA sup.rdv
      sup.xA,
    (TailCarry₂ (FC₄₁₃ Cm)).stage.tok, hseg, rfl, ?_, ?_⟩
  · show Cm.k = C.k
    exact hmk
  · rw [lastArmScanEntry_envTok]
    exact sup.ht

/-! ### The class-C row's span

`classCSpan_at` states the byte's four leaves below `if.else387.i` at the arm's endpoint
from the class's `%8 < 110` bit alone — the upper bound is not a premise — so the class-C
row's span is a theorem of the head segment.  Its endpoint is one of four named states, so
the tail's supply is indexed by it rather than stated at the head. -/
theorem hlastClassCSpan_of_head {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    {Cm : WalkCarry G} {sm : State} {nH : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH)
    (hm : Cm.block = "if.else387.i")
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (hlastByte G C)))
    (h110z : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 0) :
    ∃ (Cs : WalkCarry G) (ss : State) (nS : Nat),
      Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS ∧
        Cs.block = "if.then413.i" ∧ nS ≤ 5 :=
  classCSpan_at (G := G) (C := Cm) (s := sm) hHead.inv' hm h8m h110z

/-- **The class-C row, from the span and the seam's supply.**  `classCSpan_at` produces the
byte's span (`hlastClassCSpan_of_head` states it at the head segment), so a caller has one;
what the span's *type* does not carry is its endpoint carry's index, `Cs.k = C.k`, which
each of the four concrete endpoints satisfies by `rfl` (`{ClsC₄₀₃ Cm with block := …}`,
`HeadC₄₁₃ (ClsC₄₀₅ Cm)`, `{HeadC₅₈ Cm with block := …}`, `HeadC₄₁₃ Cm`).  The supply is a
function of the endpoint because the four leaves reach four different seams. -/
noncomputable def hlastClassCRows_of_span {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) {Cm : WalkCarry G} {sm : State} {nH : Nat}
    {Cs : WalkCarry G} {ss : State} {nS : Nat}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH) (hnH : nH ≤ 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = C.k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (hlastByte G C)))
    (hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS)
    (hs : Cs.block = "if.then413.i") (hnS : nS ≤ 5) (hkCs : Cs.k = C.k)
    (sup : HlastSeamTailSupply G Cs ss) :
    HlastClassCRows G C s := by
  have hInv : WalkInv G Cs ss := (Seg.measure hSpan).inv'
  have hEx : ∃ ev : EventRecord,
      WalkSegment (stage2Calls stage2SubCalls) G Cs ss (TailCarryEnd Cs ev)
        (ScanEntry ss sup.r₁ sup.r₂ sup.r₃ sup.cd sup.cd sup.cA sup.rdv sup.xA) 3 :=
    emptyTailSeg_of_calls G Cs ss sup.r₁ sup.r₂ sup.r₃ sup.cd hInv hs
      (p := sup.p) (reg := "%8") (op := sup.op) sup.hpre sup.hphi sup.hop
      sup.hkind sup.hrd sup.hread sup.hpre₁ sup.hcall₁ sup.hret₁ sup.hbit0 sup.hzread sup.hc
      sup.ht sup.ho sup.hpre₂ sup.hcall₂ sup.hret₂ sup.hev64 sup.htight sup.hklt sup.hpre₃
      sup.hcall₃ sup.hei sup.hcd sup.hcd64
  let ev : EventRecord := Classical.choose hEx
  have hseg : WalkSegment (stage2Calls stage2SubCalls) G Cs ss (TailCarryEnd Cs ev)
      (ScanEntry ss sup.r₁ sup.r₂ sup.r₃ sup.cd sup.cd sup.cA sup.rdv sup.xA) 3 :=
    Classical.choose_spec hEx
  refine ⟨Cm, sm, nH, hHead, hnH, hm, hmk, h8m, Cs, ss, nS, hSpan, hs, hnS,
    TailCarryEnd Cs ev,
    ScanEntry ss sup.r₁ sup.r₂ sup.r₃ sup.cd sup.cd sup.cA sup.rdv sup.xA,
    (TailCarry₂ Cs).stage.tok, hseg, rfl, ?_, ?_⟩
  · show Cs.k = C.k
    exact hkCs
  · rw [lastArmScanEntry_envTok]
    exact sup.ht

/-! ### The narrowed guards' witnesses

`HlastArmRows` now excludes the bytes the head switch decides first: `.letters` and `.run`
carry `%8 ≠ 34`, `.classC` carries `%8 ≠ 123` and `%8 ≠ 125`.  The theorems below witness
both halves of each repair — the bits that still hold at the excluded byte, and the
exclusion that fails there — and then the overlaps the narrowing does not close.
`JsonStage2WalkPremisesOfStaging`'s class case decides those bytes before it reaches the
default arm (`h34`, `h44eq`, `h58eq`, `h91eq`, `h93eq`, `h123eq`, `h125eq`). -/

/-- `.letters`' three class bits hold at `34`, the standalone opener: the exclusion, not a
class bit, is what removes the byte from the row. -/
theorem hlast_letters_bits_at_stringOpener :
    (evalICmp .eq (BitVec.ofNat 8 34) (BitVec.ofNat 8 45) |||
        evalICmp .ult (BitVec.ofNat 8 34 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 ∧
      evalICmp .slt (BitVec.ofNat 8 34) (BitVec.ofNat 8 110) = 1 ∧
      evalICmp .eq (BitVec.ofNat 8 34) (BitVec.ofNat 8 102) = 0 := by
  decide

/-- The exclusion `.letters` added: `%8 = 34` is set at `34`, so `%8 ≠ 34` fails there. -/
theorem hlast_letters_exclusion_at_stringOpener :
    evalICmp .eq (BitVec.ofNat 8 34) (BitVec.ofNat 8 34) = 1 := by
  decide

/-- `.classC`'s two class bits hold at `123`, the open brace. -/
theorem hlast_classC_bits_at_openBrace :
    evalICmp .slt (BitVec.ofNat 8 123) (BitVec.ofNat 8 110) = 0 ∧
      (evalICmp .slt (BitVec.ofNat 8 123) (BitVec.ofNat 8 125) = 1 ∨
        evalICmp .eq (BitVec.ofNat 8 123) (BitVec.ofNat 8 125) = 1) := by
  decide

/-- `.classC`'s two class bits hold at `125`, the close brace. -/
theorem hlast_classC_bits_at_closeBrace :
    evalICmp .slt (BitVec.ofNat 8 125) (BitVec.ofNat 8 110) = 0 ∧
      (evalICmp .slt (BitVec.ofNat 8 125) (BitVec.ofNat 8 125) = 1 ∨
        evalICmp .eq (BitVec.ofNat 8 125) (BitVec.ofNat 8 125) = 1) := by
  decide

/-- The exclusion `.classC` added at `123`. -/
theorem hlast_classC_exclusion_at_openBrace :
    evalICmp .eq (BitVec.ofNat 8 123) (BitVec.ofNat 8 123) = 1 := by
  decide

/-- The exclusion `.classC` added at `125`. -/
theorem hlast_classC_exclusion_at_closeBrace :
    evalICmp .eq (BitVec.ofNat 8 125) (BitVec.ofNat 8 125) = 1 := by
  decide

/-- `.run`'s byte guard (the tag test) holds at `34`. -/
theorem hlast_run_tag_at_stringOpener :
    (evalICmp .eq (BitVec.ofNat 8 34) (BitVec.ofNat 8 45) |||
      evalICmp .ult (BitVec.ofNat 8 34 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := by
  decide

/-- The exclusion `.run` added at `34`. -/
theorem hlast_run_exclusion_at_stringOpener :
    evalICmp .eq (BitVec.ofNat 8 34) (BitVec.ofNat 8 34) = 1 := by
  decide

/-- **The `.letters` guard still admits the comma, the colon and the two brackets.**  At
`44`, `58`, `91` and `93` the three class bits and the new exclusion all hold, and the
class case dispatches those bytes to their own arms before the default one. -/
theorem hlast_letters_guard_residual : ∀ x : BitVec 8,
    x = BitVec.ofNat 8 44 ∨ x = BitVec.ofNat 8 58 ∨ x = BitVec.ofNat 8 91 ∨
      x = BitVec.ofNat 8 93 →
    (evalICmp .eq x (BitVec.ofNat 8 45) |||
        evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 ∧
      evalICmp .slt x (BitVec.ofNat 8 110) = 1 ∧
      evalICmp .eq x (BitVec.ofNat 8 102) = 0 ∧
      evalICmp .eq x (BitVec.ofNat 8 34) = 0 := by
  decide

/-- **The `.run` guard still admits those four bytes and the two braces.**  Its guard is the
tag test, the exclusion and `wsStop G (G.n - 1)` alone, so anything tag-clear but `34`
reaches it. -/
theorem hlast_run_guard_residual : ∀ x : BitVec 8,
    x = BitVec.ofNat 8 44 ∨ x = BitVec.ofNat 8 58 ∨ x = BitVec.ofNat 8 91 ∨
      x = BitVec.ofNat 8 93 ∨ x = BitVec.ofNat 8 123 ∨ x = BitVec.ofNat 8 125 →
    (evalICmp .eq x (BitVec.ofNat 8 45) |||
        evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 ∧
      evalICmp .eq x (BitVec.ofNat 8 34) = 0 := by
  decide

/-- `.scalar`'s guard does **not** hold at `34`: `%8 < 44` is set there.  The positive
control for the byte facts above. -/
theorem hlast_scalar_guard_excludes_stringOpener :
    evalICmp .slt (BitVec.ofNat 8 34) (BitVec.ofNat 8 44) = 1 := by
  decide

/-- `.scalar`'s guard does not hold at `123` either: `%8 < 58` is clear. -/
theorem hlast_scalar_guard_excludes_openBrace :
    evalICmp .slt (BitVec.ofNat 8 123) (BitVec.ofNat 8 58) = 0 := by
  decide

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.lastArmScanEntry_envTok
#print axioms LeanLLVM.Refinement.WalkScope.hlastLettersRows_of_head
#print axioms LeanLLVM.Refinement.WalkScope.hlastFLetterRows_of_head
#print axioms LeanLLVM.Refinement.WalkScope.hlastClassCSpan_of_head
#print axioms LeanLLVM.Refinement.WalkScope.hlastClassCRows_of_span
#print axioms LeanLLVM.Refinement.WalkScope.hlast_letters_bits_at_stringOpener
#print axioms LeanLLVM.Refinement.WalkScope.hlast_letters_exclusion_at_stringOpener
#print axioms LeanLLVM.Refinement.WalkScope.hlast_classC_bits_at_openBrace
#print axioms LeanLLVM.Refinement.WalkScope.hlast_classC_bits_at_closeBrace
#print axioms LeanLLVM.Refinement.WalkScope.hlast_classC_exclusion_at_openBrace
#print axioms LeanLLVM.Refinement.WalkScope.hlast_classC_exclusion_at_closeBrace
#print axioms LeanLLVM.Refinement.WalkScope.hlast_run_tag_at_stringOpener
#print axioms LeanLLVM.Refinement.WalkScope.hlast_run_exclusion_at_stringOpener
#print axioms LeanLLVM.Refinement.WalkScope.hlast_letters_guard_residual
#print axioms LeanLLVM.Refinement.WalkScope.hlast_run_guard_residual
#print axioms LeanLLVM.Refinement.WalkScope.hlast_scalar_guard_excludes_stringOpener
#print axioms LeanLLVM.Refinement.WalkScope.hlast_scalar_guard_excludes_openBrace

end WalkScope
end LeanLLVM.Refinement
