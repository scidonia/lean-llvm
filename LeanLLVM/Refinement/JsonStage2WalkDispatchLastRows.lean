/-
# The last entry's per-class rows

`HlastPayload` (`JsonStage2WalkDispatchSupply`) carries the two groups the last entry's
byte class needs without a class: the openers' value-position call and the high-byte
class's three calls.  The remainder of the last entry's arms take rows whose types name
states defined *above* `JsonStage2WalkDispatchClassRows` — the scalar route's seam
(`scalarSeam`, `ScalarC₁₁`), the default arm's leaves (`LetS413`, `FS413`, `ClsS413*`) and
the run's seam states — so they cannot be fields of that payload or of `HlastClassRows`:
naming them there would close an import cycle.  This module is their home, above every
producer, and the closure theorem takes it as its third premise.

## Why five groups, and not eighteen

The head switch has thirteen classes at the last entry, but eleven of them derive their
premises: the openers read `HlastAbi.openCall` and `WalkInv.depth_cap`, the refusals and
the delimiter classes read the class bit and the invariant's own cells, the string opener
reads the class bit alone, and the high-byte class is `HlastLane`/`HlastAbi.highByte`, whose
refusal row (`HlastHighByteRefusal`) is the whole of its supply.  A group for any of those
would be a field with no consumer.  What is left
is the five classes whose producers take supply the invariant cannot give: the document's
last byte's scalar route and its three calls, the default arm's three leaf routes with
their chains, and the run's own body.

Each group is exactly one producer's argument list after the invariant, the guard and the
class's bits, and each is guarded by its class — the bits that name the class are
arguments of the row, not of the structure — so no field is stated at every head.

## The segments a group carries

`.letters`, `.fLetter` and `.classC` carry a head chain, a span and a tail.  Those are the
arm's own routes: the arm (`LastEntryArm.letters` …) carries them too, and no producer
claims to establish them.  A row that carried something the producer proves would be the
defect the ledger's c2 entry is written against; these are its premises.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassRows
import LeanLLVM.Refinement.JsonStage2WalkDispatchScalarOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchSpansOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchRunOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchOpenersOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchRefusalsOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchClosersOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchZeroOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchAboveZeroOfStaging

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The scalar class's row

The document's last byte is the scalar route's (`13 ≤ b < 32` is the *high* byte route;
this one is `b < 13` with the offset test clear, i.e. `LeafBlock33`), which is the class
`lastEntryArm_scalar_of_staging` reads as `hb13`/`hb32`/`hbne32`.  The three calls are
stated at `scalarSeam` — the scalar route's own seam, which is not the tail's. -/

/-- The scalar route's seam at the last entry's own witnesses: the entry's end
(`C.k + 1`), the stream's end, the document's length, the entry's position and the
document's last byte. -/
abbrev hlastScalarSeam {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) : State :=
  scalarSeam C s (hlastByte G C) (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep)
    G.n (BitVec.ofNat 64 (entryPos G C.k)) (G.bs.getD (G.n - 1) 0)

/-- **The scalar class's row.**  Consumed by `lastEntryArm_scalar_of_staging`: the last
byte's route bits, the three callees' answers and their rows at the scalar route's seam. -/
structure HlastScalarRows {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  /-- The last byte is the low leaf's: `LeafBlock33`, its offset test clearing. -/
  hb13 : evalICmp .slt (head35 (G.bs.getD (G.n - 1) 0)) (BitVec.ofNat 8 13) = 0
  hb32 : evalICmp .slt (head35 (G.bs.getD (G.n - 1) 0)) (BitVec.ofNat 8 32) = 0
  hbne32 : evalICmp .eq (head35 (G.bs.getD (G.n - 1) 0)) (BitVec.ofNat 8 32) = 0
  r₁ : CallOutcome
  r₂ : CallOutcome
  r₃ : CallOutcome
  rdv : BitVec 32
  xA : BitVec 32
  hreadT : readBytes
    (writeBytes (hlastScalarSeam C s).mem (C.stage.tok + 16) (natToBytes (7 : Nat) 4))
    (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)
  hpre₁ : s2ValuePosPre
    [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .int 32 rdv,
     .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst]
    (writeBytes (hlastScalarSeam C s).mem (C.stage.tok + 16) (natToBytes (7 : Nat) 4))
    (hlastScalarSeam C s).next
  hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
    [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .int 32 rdv,
     .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst]
    (writeBytes (hlastScalarSeam C s).mem (C.stage.tok + 16) (natToBytes (7 : Nat) 4))
    (hlastScalarSeam C s).next = some r₁
  hret₁ : r₁.ret = .int 32 xA
  hbit0T : evalICmp .eq xA (BitVec.ofNat 32 0) = 0
  hpre₂ : s2ScalarValuePre
    [.ptr (TailCarry₂ (ScalarC₁₁ C)).stage.c, .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.tok,
     .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.z] r₁.mem r₁.next
  hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
    [.ptr (TailCarry₂ (ScalarC₁₁ C)).stage.c, .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.tok,
     .ptr (TailCarry₂ (ScalarC₁₁ C)).stage.z] r₁.mem r₁.next = some r₂
  hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1)
  hpre₃ : s2AfterValuePre
    [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .ptr (G.next0 + 8),
     .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst] r₂.mem r₂.next
  hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
    [.int 32 (BitVec.ofNat 32 (ScalarC₁₁ C).sp), .ptr (G.next0 + 8),
     .ptr (ScalarC₁₁ C).stage.ctype, .ptr (ScalarC₁₁ C).stage.cst] r₂.mem r₂.next =
      some r₃

/-! ### The default arm's three leaf rows

Each carries the head chain to `if.else387.i` (the class's own prefix, which the case
builds from the lane row and the head bits), the endpoint's `%8`, and the leaf's span and
tail.  The span and the tail are the arm's own routes. -/

/-- **The letters class's row.**  Consumed by `lastEntryArm_letters_of_staging`. -/
structure HlastLettersRows {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  Cm : WalkCarry G
  sm : State
  nH : Nat
  hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH
  hnH : nH ≤ 11
  hm : Cm.block = "if.else387.i"
  hmk : Cm.k = C.k
  h8m : evalOperand sm (.reg "%8") = some (.int 8 (hlastByte G C))
  Ct : WalkCarry G
  st : State
  tok : Nat
  hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
    (LetS413 sm (hlastByte G C)) Ct st 3
  ht : Ct.block = "if.end473.i"
  htk : Ct.k = C.k
  htok : lookupName st.env "%t352.i" = some (.ptr tok)

/-- **The `'f'` leaf's row.**  Consumed by `lastEntryArm_fLetter_of_staging`. -/
structure HlastFLetterRows {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  Cm : WalkCarry G
  sm : State
  nH : Nat
  hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH
  hnH : nH ≤ 11
  hm : Cm.block = "if.else387.i"
  hmk : Cm.k = C.k
  h8m : evalOperand sm (.reg "%8") = some (.int 8 (hlastByte G C))
  Ct : WalkCarry G
  st : State
  tok : Nat
  hTail : WalkSegment (stage2Calls stage2SubCalls) G (FC₄₁₃ Cm)
    (FS413 sm (hlastByte G C)) Ct st 3
  ht : Ct.block = "if.end473.i"
  htk : Ct.k = C.k
  htok : lookupName st.env "%t352.i" = some (.ptr tok)

/-- **The class-C class's row.**  Consumed by `lastEntryArm_classC_of_staging`: the same
head chain with the byte's own span below `if.else387.i` beside the tail. -/
structure HlastClassCRows {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  Cm : WalkCarry G
  sm : State
  nH : Nat
  hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH
  hnH : nH ≤ 11
  hm : Cm.block = "if.else387.i"
  hmk : Cm.k = C.k
  h8m : evalOperand sm (.reg "%8") = some (.int 8 (hlastByte G C))
  Cs : WalkCarry G
  ss : State
  nS : Nat
  hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS
  hs : Cs.block = "if.then413.i"
  hnS : nS ≤ 5
  Ct : WalkCarry G
  st : State
  tok : Nat
  hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3
  ht : Ct.block = "if.end473.i"
  htk : Ct.k = C.k
  htok : lookupName st.env "%t352.i" = some (.ptr tok)

/-- **The run class's row.**  Consumed by `lastEntryArm_run_of_staging`: the head chain,
the byte's span, the tail on its scan arm, the latch, the traversal's numbers and the
document's own bounds.  No field is a segment the producer composes. -/
structure HlastRunRows {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  N : Nat
  Cm : WalkCarry G
  sm : State
  nH : Nat
  hHead : WalkSegment (stage2Calls stage2SubCalls) G C s Cm sm nH
  hnH : nH ≤ 11 + N
  hm : Cm.block = "if.else387.i"
  hmk : Cm.k = C.k
  Cs : WalkCarry G
  ss : State
  nS : Nat
  hSpan : Seg (stage2Calls stage2SubCalls) G Cm sm Cs ss nS
  hnS : nS ≤ 5
  hs : Cs.block = "if.then413.i"
  Ct : WalkCarry G
  st : State
  hTail : WalkSegment (stage2Calls stage2SubCalls) G Cs ss Ct st 3
  ht : Ct.block = "land.rhs457.i"
  htk : Ct.k = C.k
  Cl : WalkCarry G
  tl : State
  hLatch : WalkSegment (stage2Calls stage2SubCalls) G Ct st Cl tl 3
  hl : Cl.block = "while.body462.i"
  hkC : Cl.k = C.k
  i : Nat
  c : Nat
  hcounter : lookupName tl.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 i))
  hbound : lookupName tl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c))
  hic : i < c
  hbyte : ScanVisits G c i
  hstop : i = terminalStop G.bs (entryPos G C.k)
  hN : N = i - entryPos G C.k
  hc : c = G.n

/-! ### The five groups, as one structure

Each field's guard is its class's own bits at the last entry's byte, and each field's
consumer is the producer named in its docstring.  The thirteen other classes of the head
switch take no field: their premises are the invariant's cells, the class bit, and the
payload's `openCall`/`highByte` groups — a field for any of them would have no consumer. -/

/-- **The last entry's per-class rows.**  The third premise of a `WalkLoopEnd` producer
beside `HlastPayload`'s openers/high-byte groups and `HlastClassRows`' document and seam
rows: what the staging supplies for the five classes the invariant cannot reach.

Every field is guarded by the class bits that name it — so no field is stated at every
head — and no field is a segment a producer is meant to establish: the chain, span and tail
segments are the arms' own routes.

Three guards also exclude the bytes the head switch sends elsewhere before the default arm:
`.letters` and `.run` exclude the standalone opener's `34`, and `.classC` excludes the
braces `123` and `125`.  `.letters`' guard still admits the comma, the colon and the two
brackets (`44`, `58`, `91`, `93`), which the class case dispatches to their own arms; those
exclusions are not stated, and `JsonStage2WalkDispatchLastArmRows` records the byte facts
they would rest on. -/
structure HlastArmRows {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- The scalar class's row (`HlastScalarRows`); consumer
  `lastEntryArm_scalar_of_staging`. -/
  scalar : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    ¬ (C.k + 1 < G.nep) →
    (h44 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 44) = 0) →
    (h58 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 58) = 1) →
    (hne44 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 44) = 0) →
    (hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1) →
    HlastScalarRows G C s
  /-- The letters class's row (`HlastLettersRows`); consumer
  `lastEntryArm_letters_of_staging`.  The guard excludes the standalone opener's byte
  (`%8 = 34`), which the head switch sends to its own arm, so the row is quantified only
  over the bytes the class case dispatches to it. -/
  letters : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    ¬ (C.k + 1 < G.nep) →
    (hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) →
    (h110 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 1) →
    (hne102 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 102) = 0) →
    (hne34 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 0) →
    HlastLettersRows G C s
  /-- The `'f'` leaf's row (`HlastFLetterRows`); consumer
  `lastEntryArm_fLetter_of_staging`. -/
  fLetter : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    ¬ (C.k + 1 < G.nep) →
    (hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) →
    (h110 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 1) →
    (h102 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 102) = 1) →
    HlastFLetterRows G C s
  /-- The class-C class's row (`HlastClassCRows`); consumer
  `lastEntryArm_classC_of_staging`.  The guard excludes the two brace bytes (`%8 = 123`,
  `%8 = 125`), which the head switch sends to the container open and close arms, so the
  row is quantified only over the bytes the class case dispatches to it. -/
  classC : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    ¬ (C.k + 1 < G.nep) →
    (h110 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 0) →
    (h125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 1) →
    (hne123 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 0) →
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0) →
    HlastClassCRows G C s
  /-- The run class's row (`HlastRunRows`); consumer `lastEntryArm_run_of_staging`.  Its
  guard is the class's own: the byte before the token's end is whitespace, which is what
  sends the walk into the run's scan rather than straight to the seam — beside the tag
  test and the exclusion of the standalone opener's byte (`%8 = 34`), which the head
  switch sends to its own arm. -/
  run : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    ¬ (C.k + 1 < G.nep) →
    (hbit : (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
      evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) →
    (hne34 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 0) →
    wsStop G (G.n - 1) →
    HlastRunRows G C s

/-! ### The tag test at the default arm's non-numeric classes

`HeadArm.defaultValue`'s `%8 < 91` arm splits on the tag test (`%8 = '-'` or a digit),
which is `HcontClass.value`/`.otherValue`; the other `HeadArm` arms do not carry the bit.
At their bytes it is clear, and the five facts are exhaustive over those ranges — a
`decide` over the 256 byte values, since no arithmetic identity states a bitvector test's
value over a range. -/

/-- At the low class (`%8 < 44` signed) the tag test is clear. -/
theorem hlast_tag_low : ∀ x : BitVec 8,
    evalICmp .slt x (BitVec.ofNat 8 44) = 1 →
    (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := by
  decide

/-- At `%8 < 91` and `58 ≤ %8` the tag test is clear. -/
theorem hlast_tag_mid : ∀ x : BitVec 8,
    evalICmp .slt x (BitVec.ofNat 8 91) = 1 →
    evalICmp .slt x (BitVec.ofNat 8 58) = 0 →
    (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := by
  decide

/-- At `91 ≤ %8 < 123` and `%8 < 93` the tag test is clear. -/
theorem hlast_tag_bracket : ∀ x : BitVec 8,
    evalICmp .slt x (BitVec.ofNat 8 91) = 0 →
    evalICmp .slt x (BitVec.ofNat 8 123) = 1 →
    evalICmp .slt x (BitVec.ofNat 8 93) = 1 →
    (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := by
  decide

/-- At `93 ≤ %8 < 123` the tag test is clear. -/
theorem hlast_tag_bracketHigh : ∀ x : BitVec 8,
    evalICmp .slt x (BitVec.ofNat 8 91) = 0 →
    evalICmp .slt x (BitVec.ofNat 8 123) = 1 →
    evalICmp .slt x (BitVec.ofNat 8 93) = 0 →
    (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := by
  decide

/-- At `123 ≤ %8 < 125` the tag test is clear. -/
theorem hlast_tag_brace : ∀ x : BitVec 8,
    evalICmp .slt x (BitVec.ofNat 8 91) = 0 →
    evalICmp .slt x (BitVec.ofNat 8 123) = 0 →
    evalICmp .slt x (BitVec.ofNat 8 125) = 1 →
    (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := by
  decide

end WalkScope
end LeanLLVM.Refinement
