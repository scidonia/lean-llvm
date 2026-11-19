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

## Why six groups, and not eighteen

The head switch has thirteen classes at the last entry, but eleven of them derive their
premises: the openers read `HlastAbi.openCall` and `WalkInv.depth_cap`, the refusals and
the delimiter classes read the class bit and the invariant's own cells, the string opener
reads the class bit alone, and the high-byte class is `HlastLane`/`HlastAbi.highByte`, whose
refusal row (`HlastHighByteRefusal`) is the whole of its supply.  A group for any of those
would be a field with no consumer.  What is left
is the five classes whose producers take supply the invariant cannot give: the document's
last byte's scalar route and its three calls, the default arm's three leaf routes with
their chains, and the run's own body.  The class-C range splits by its kind literal — the
two emitting leaves (`110`, `116`) beside the refusing ones — so it is two fields, not one.

Each group is exactly one producer's argument list after the invariant, the guard and the
class's bits, and each is guarded by its class — the bits that name the class are
arguments of the row, not of the structure — so no field is stated at every head.

## The segments a group carries

`.fLetter` and `.classCTrue` carry a head chain, a span and an emitting tail.  Those are
the arm's own routes: the arm (`LastEntryArm.fLetter`, `.classC`) carries them too, and no
producer claims to establish them.  A row that carried something the producer proves would
be the defect the ledger's c2 entry is written against; these are its premises.

`.letters` and `.classC` carry no emitting tail: their seams take `if.else405.i`'s literal
`0`, where the walk refuses, so those rows carry the seam's refusal group
(`HlastSeamRefusal`) and the class's counted route to the refusal copy
(`HlastRefuseRoute`).  The route is supply, as `HcontClassRows.refuseSeg` is, because the
error path's blocks have no composed segment in the tree.

## The class-C range's two guards

The class-C range is the only class whose guard splits, and the split is a **partition**,
not two overlapping readings of one guard.  `.classCTrue` takes exactly the emitting leaves
— `%8 = 110` (`ClsS413T`, `if.then403.i`'s literal `10`) and `%8 = 116` (`ClsS58T`,
`LeafBlock58`'s own `8`) — because only there does `od_scalar_value` answer `1` and the
tail reach `if.end473.i`.  `.classC` takes the class range with `%8 ≠ 110`, `%8 ≠ 116`, and
the brace exclusions, i.e. the leaves `111 … 115` and `117 … 125`, whose `if.else405.i`
literal is `0` and whose arm is `LastEntryArm.refuse`.  The class case decides the two
equalities first and calls exactly one field; neither field is inhabited at the other's
bytes.
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
  /-- The last byte is the high leaf's: `LeafBlock33`'s test clearing, `LeafBlock35`'s
  clearing, and `LeafBlock37`'s `eq 32` test clearing.  The byte is the *document's* last,
  not the entry's, so no guard of this row pins it. -/
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

/-! ### The default arm's leaf rows

Each carries the head chain to `if.else387.i` (the class's own prefix, which the case
builds from the lane row and the head bits) and the endpoint's `%8`; the class-C rows add
the byte's span.  The span is the arm's own route.  The letters and the class-C refusing
leaves end at `if.else405.i`'s literal `0`, so their payload is the seam's refusal group
and the class's route; the `'f'` leaf and the two class-C emitting leaves keep the emitting
tail. -/

/-- **The letters class's row.**  Consumed by `lastEntryArm_letters_of_staging`'s refusal
twin: the head chain's endpoint, whose seam `LetS413` takes `if.else405.i`'s kind literal
`0` — so the tail's rows are the **refusal group** (`HlastSeamRefusal`: the two leading
calls, the literal `0`, the derived answer `0` and the record) and the arm is the class's
route to the refusal copy (`HlastRefuseRoute`, from the head state).  No three-call tail
exists at that literal, so the row carries no emitting segment. -/
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
  /-- The seam's refusal rows at `LetS413` — the letters span's target, whose predecessor
  is `if.else405.i`. -/
  seam : HlastSeamRefusal G (HeadC₄₁₃ (LetC₄₀₅ Cm)) (LetS413 sm (hlastByte G C))
  /-- The class's counted, priced route from the head state to the refusal copy. -/
  route : HlastRefuseRoute G C s

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

/-- **The class-C class's row at the refusing leaves.**  Consumed by the class case's
refusal branches: the bytes `111 … 115` (`LeafBlock56`'s else arm) and `117 … 125`
(`LeafBlock58`'s else arm) reach `if.else405.i`, whose kind literal is `0`, so the tail's
rows are the **refusal group** (`HlastSeamRefusal` at the span's endpoint) and the arm is
the class's route to the refusal copy.  No three-call tail exists at that literal. -/
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
  /-- The seam's refusal rows at the span's endpoint. -/
  seam : HlastSeamRefusal G Cs ss
  /-- The class's counted, priced route from the head state to the refusal copy. -/
  route : HlastRefuseRoute G C s

/-- **The class-C class's row at the emitting leaves.**  `110` (`LeafBlock56`'s true arm,
kind `10`) and `116` (`LeafBlock58` itself, kind `8`) reach `if.then413.i` with a nonzero
literal, so `od_scalar_value` answers `1` and the tail's three calls reach `if.end473.i`.
The row carries the byte's own span and the arm's tail, as `HlastFLetterRows` does. -/
structure HlastClassCTrueRows {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
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

/-! ### The six groups, as one structure

Each field's guard is its class's own bits at the last entry's byte, and each field's
consumer is the producer named in its docstring.  The thirteen other classes of the head
switch take no field: their premises are the invariant's cells, the class bit, and the
payload's `openCall`/`highByte` groups — a field for any of them would have no consumer. -/

/-- **The last entry's per-class rows.**  The third premise of a `WalkLoopEnd` producer
beside `HlastPayload`'s openers/high-byte groups and `HlastClassRows`' document and seam
rows: what the staging supplies for the classes the invariant cannot reach.

Every field is guarded by the class bits that name it — so no field is stated at every
head — and no field is a segment a producer is meant to establish: the chain, span and tail
segments are the arms' own routes.

The default arm's kind literal splits three of the classes.  `.letters` and the class-C
refusal row (`.classC`, the leaves `111 … 115` and `117 … 125`) reach `if.else405.i`, whose
literal is `0`: their seams carry the refusal group (`HlastSeamRefusal`), no three-call
tail exists there, and their arms are the class's route to the refusal copy
(`LastEntryArm.refuse`).  The two class-C emitting leaves (`110` and `116`) are
`.classCTrue`, whose seam literal is `10` and `8`.

Three guards also exclude the bytes the head switch sends elsewhere before the default arm:
`.letters` and `.run` exclude the standalone opener's `34`, and `.classC`/`.classCTrue`
exclude the braces `123` and `125`.  `.letters`' guard still admits the comma, the colon
and the two brackets (`44`, `58`, `91`, `93`), which the class case dispatches to their own
arms; those exclusions are not stated, and `JsonStage2WalkDispatchLastArmRows` records the
byte facts they would rest on. -/
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
  /-- The letters class's row (`HlastLettersRows`): the class case's refusal branch reads
  its `route`.  The guard excludes the standalone opener's byte (`%8 = 34`), which the
  head switch sends to its own arm, so the row is quantified only over the bytes the class
  case dispatches to it. -/
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
  /-- The class-C class's row at the refusing leaves (`HlastClassCRows`): the class case's
  refusal branch reads its `route`.  The guard is the class's range with the two brace
  bytes (`%8 = 123`, `%8 = 125`, the container arms') and the two emitting leaves
  (`%8 = 110`, `%8 = 116`, `classCTrue`'s) excluded; `111 … 115` and `117 … 125` reach
  `if.else405.i`. -/
  classC : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    ¬ (C.k + 1 < G.nep) →
    (h110 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 0) →
    (h125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 1) →
    (hne123 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 0) →
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0) →
    (hne110 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 110) = 0) →
    (hne116 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 116) = 0) →
    HlastClassCRows G C s
  /-- The class-C class's row at the emitting leaves (`HlastClassCTrueRows`): `110` and
  `116`, whose seams write `if.then403.i`'s `10` and `LeafBlock58`'s `8`.  Its consumer is
  `lastEntryArm_classC_of_staging`, and the class case takes it only at those two bytes. -/
  classCTrue : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    ¬ (C.k + 1 < G.nep) →
    (h110 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 110) = 0) →
    (h125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 1) →
    (hne123 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 0) →
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0) →
    (hleaf : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 110) = 1 ∨
      evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 116) = 1) →
    HlastClassCTrueRows G C s
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
