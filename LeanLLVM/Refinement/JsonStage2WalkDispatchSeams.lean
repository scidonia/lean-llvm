/-
# The seam's three calls, and the scan tail they produce

`JsonStage2WalkDispatchWitnessHlast`'s `emptyTailSeg_of_calls` states the tail's three
links from the three callees' rows **on the empty arm** — the arm where the copy call's
test `ult %ee.1.i %cond350.i` is false and the walk leaves for `if.end473.i`.  This module
adds the two pieces the scan arm needs, and it states them at the granularity the payloads
in `JsonStage2WalkDispatchSupply` are stated at: **facts about a document and a call
environment, never a segment and never a bundle.**

## The seam's call rows

`HcontSeamCalls` is the three calls at one seam: the value-position call, the scalar call's
emit arm and the copy call, each with its precondition at the staged argument list, its
outcome and the memory chain the three read and leave.  The structure carries the kind
literal `cA` and the root-done word `rdv` because the *memories* mention them: the first
call's argument list and the copy's test are read at the memory
`writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)`, so those two words are part
of what the rows are about.  Nothing else is: the seam's own cells (`%ee.1.i`,
`%cond350.i`, `%kind404.i`, `%root_done.i`, `%c.i`, `%t352.i`, `%z`, the state's `pre` and
the `phi`'s operand) are the *state's*, and a theorem that consumes the rows takes them at
the state it is given — they are the same peels at every seam
(`contTailStart_ee`/`contTailStart_cond`, `scSeamByte_ee`/`scSeamByte_cond`,
`hlastTail_ee`/`hlastTail_cond`).

`HcontSeamAbi` is that structure as one `∀`-field per seam.  The edge fixes the field: the
run class's `if.then413.i` at `if.else405.i`'s `0` is the *refusal* seam (the two leading
calls, the answer `0` and the refusal record's memory), and `if.then397.i`'s `9`,
`if.then403.i`'s `10` and `LeafBlock58`'s `8` are the three *emit* seams (the three call
rows).  Every field has an inhabitant at its leaf, so the group costs the staged words plus
the single emit row `hemit` at the three emit seams — nothing at the refusal one.

## The scan arm's tail, from the rows

`scanTailSeg_of_calls` is `emptyTailSeg_of_calls`'s twin on `consumerTailSegAt`: the three
links at count `3`, ending at `TailCarryScan C ev` and the scan's entry `ScanEntry s …`
instead of the scan-free `TailCarryEnd C ev`.  What changes is the copy call's test: the
empty arm supplies the equation `%ee.1.i = %cond350.i` (`rfl` at its seam), while the scan
arm supplies the strict inequality and the span the three links then need —
`ei < cd` and `cd - ei ≤ C.inner`.  Both are consequences of the class's own field, not new
premises: at the run class `cd` is the lane's word `v.toNat`, `ei` is the stop `k`, and
`k < v.toNat` is `HcontRunFacts.heicd` while `v.toNat - k ≤ C.inner` follows from
`v.toNat - ix.toNat ≤ C.inner` and `ix.toNat < k`.

## What remains between these statements and the bundles

The two bundle theorems (`walkContinueFacts_of_payload`
(`JsonStage2WalkDispatchContinuing`), `walkLoopEnd_of_payload`
(`JsonStage2WalkPremisesOfStaging`)) are stated from the rows this module's seams produce,
and what stood in their way was not a segment: every segment an arm carries is
produced per class from rows that already exist — the head chain by
`JsonStage2WalkDispatchDefaultLane`'s `bhHeadChain_of_lane` (from the lane's
`defaultLane`, at `.defaultValueBracketHigh`, the one default class whose leaves emit), the
refusal arm by `hcontArm_badToken_of_row` at the class's `refuseSeg` (the other five
default classes' `if.else405.i` leaves), the class-C span by `classCSpan_at` (from the
class's `slt %8 110` bit), the default classes' shared four by `contSwToLandSeg`, the empty
tail by `emptyTailSeg_of_calls`, and the scan arm's tail by `hcontScanTail_at` below.

What the class case reads is **per-class document rows the payload does not carry**: the
producers for `.ws` and `.scalar` take their bundle's document facts — the byte before the
entry's end with its class, the entry lane and its order, the whitespace stop with its
per-index `∀`, the log's two words — which are `HcontFacts`'s and `HcontScalarFacts`'s
non-callee fields.  The refusals' arms take `%idxprom.i` and `%e` beside the byte and the
depth, the above-zero markers take the two stacks' bytes at `C.sp - 1` (which are `WalkInv`
clauses), and the openers and the standalone string are the two classes the payload's `lane`
and `abi` groups reach.  So the groups the theorem takes are the class rows' ones: the
continuing payload's `lane`/`abi`/`trav`, `HcontClassRows`' seam and run rows, and
`HcontWsRows` for `.ws` × `.defaultValueHigh` — which is what
`walkContinueFacts_of_payload` (`JsonStage2WalkDispatchContinuing`) is stated over.  The
last entry's is the same shape for `LastEntryArm`'s classes and `RunLastFacts`'s rows,
stated by `walkLoopEnd_of_payload`.

**One class no longer waits on this list.**  `JsonStage2WalkDispatchSeamRows` closes
`.cleanup` end to end: the class's document row, the lane's root word and the three call
rows produce the seventeen-link chain, the seam's invariant, its five environment cells,
the predecessor's `phi` with the literal `0` it selects, the root slot's word across the
seam's three token-record stores, and the arm itself
(`hcontArm_cleanup_of_rows`/`walkDispatch_at_cleanup_of_rows`).  No segment and no bundle
is among its inputs, so the class's arm no longer waits on the rows above — the remaining
classes' rows are the same kind, at their own seams.
-/

import LeanLLVM.Refinement.JsonStage2WalkDispatchRunHead

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The seam's three calls, as one group -/

/-- **The three calls at a seam**: the value-position call, the scalar call's emit arm and
the copy call, each with its staged argument list's precondition, its outcome and the
memory it reads and leaves.

The kind literal `cA` and the root-done word `rdv` are fields because the first call's
argument list and the copy's test are read at the post-store memory
`writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)`: the rows are *about* those
two words.  The seam's own cells are not fields — they are the state's, and the consumer
reads them at the state it is given. -/
structure HcontSeamCalls {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Type where
  /-- The kind literal `if.then413.i`'s `phi` selects, read at its own store. -/
  cA : BitVec 32
  /-- The root-done slot's word, as the first call's argument list carries it. -/
  rdv : BitVec 32
  /-- The value-position call. -/
  r₁ : CallOutcome
  xA : BitVec 32
  hpre₁ : s2ValuePosPre
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
     .ptr C.stage.ctype, .ptr C.stage.cst]
    (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)) s.next
  hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
     .ptr C.stage.ctype, .ptr C.stage.cst]
    (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)) s.next = some r₁
  hret₁ : r₁.ret = .int 32 xA
  /-- The call's zero test: the arm that continues at `if.then425.i`. -/
  hbit0 : evalICmp .eq xA (BitVec.ofNat 32 0) = 0
  /-- The log's base word, read at the post-store memory. -/
  hzread : readBytes
    (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)) C.stage.z 8 =
      some (wordBytes 8 G.ev)
  /-- The scalar call's emit arm. -/
  r₂ : CallOutcome
  hpre₂ : s2ScalarValuePre
    [.ptr (TailCarry₂ C).stage.c, .ptr (TailCarry₂ C).stage.tok,
     .ptr (TailCarry₂ C).stage.z] r₁.mem r₁.next
  hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
    [.ptr (TailCarry₂ C).stage.c, .ptr (TailCarry₂ C).stage.tok,
     .ptr (TailCarry₂ C).stage.z] r₁.mem r₁.next = some r₂
  hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 1)
  hev64 : G.ev < 2 ^ 64
  /-- The copy call, at the root-done slot. -/
  r₃ : CallOutcome
  hpre₃ : s2AfterValuePre
    [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
     .ptr C.stage.ctype, .ptr C.stage.cst] r₂.mem r₂.next
  hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
    [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
     .ptr C.stage.ctype, .ptr C.stage.cst] r₂.mem r₂.next = some r₃

/-- **The seam's three call rows transport across the byte's leaf.**  Nothing but the
state's memory and counter appears in the group — the callees read `%tok`, `%z`, `%c` and
the two test cells off the carry and the arguments, and each row is stated at the memory
and the counter the state carries — so the same rows serve every leaf of `if.then413.i`.
The leaves differ in their environment, so this is a cast rather than a definitional
equality, and it is what lets a leaf's producer use the seam's rows once. -/
def HcontSeamCalls.cast {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s s' : State} (hmem : s'.mem = s.mem) (hnext : s'.next = s.next)
    (rows : HcontSeamCalls G C s) : HcontSeamCalls G C s' where
  cA := rows.cA
  rdv := rows.rdv
  r₁ := rows.r₁
  xA := rows.xA
  hpre₁ := by rw [hmem, hnext]; exact rows.hpre₁
  hcall₁ := by rw [hmem, hnext]; exact rows.hcall₁
  hret₁ := rows.hret₁
  hbit0 := rows.hbit0
  hzread := by rw [hmem]; exact rows.hzread
  r₂ := rows.r₂
  hpre₂ := rows.hpre₂
  hcall₂ := rows.hcall₂
  hret₂ := rows.hret₂
  hev64 := rows.hev64
  r₃ := rows.r₃
  hpre₃ := rows.hpre₃
  hcall₃ := rows.hcall₃

/-- **The seam's two leading calls**: the value-position call and the scalar call, at the
memory and counter the first one hands back.  Both arms of the seam share them — the emit
arm (`od_scalar_value` answered `1`) adds `s2_after_value`, and the refusal arm
(`od_scalar_value` answered `0`) adds the refusal record — so this is the part of the group
that is not arm-dependent, stated once.

The kind literal `cA` is here because the first call's argument list is read at the memory
the store of it leaves; the scalar call's answer is *not* constrained: `hret₁` is the
value-position answer's word, and the scalar answer `r₂` carries only its precondition and
its resolution.  Which word it answered is the arm's (`HcontSeamEmit`/`HcontSeamRefuse`). -/
structure HcontSeamMid {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Type where
  /-- The kind literal `if.then413.i`'s `phi` selects, read at its own store. -/
  cA : BitVec 32
  /-- The root-done slot's word, as the first call's argument list carries it. -/
  rdv : BitVec 32
  /-- The value-position call. -/
  r₁ : CallOutcome
  xA : BitVec 32
  hpre₁ : s2ValuePosPre
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
     .ptr C.stage.ctype, .ptr C.stage.cst]
    (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)) s.next
  hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
     .ptr C.stage.ctype, .ptr C.stage.cst]
    (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)) s.next = some r₁
  hret₁ : r₁.ret = .int 32 xA
  /-- The call's zero test: the arm that continues at `if.then425.i`. -/
  hbit0 : evalICmp .eq xA (BitVec.ofNat 32 0) = 0
  /-- The log's base word, read at the post-store memory. -/
  hzread : readBytes
    (writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)) C.stage.z 8 =
      some (wordBytes 8 G.ev)
  /-- The scalar call, at the memory the first one left. -/
  r₂ : CallOutcome
  hpre₂ : s2ScalarValuePre
    [.ptr (TailCarry₂ C).stage.c, .ptr (TailCarry₂ C).stage.tok,
     .ptr (TailCarry₂ C).stage.z] r₁.mem r₁.next
  hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
    [.ptr (TailCarry₂ C).stage.c, .ptr (TailCarry₂ C).stage.tok,
     .ptr (TailCarry₂ C).stage.z] r₁.mem r₁.next = some r₂

/-- **The emit arm's third step.**  The scalar call answered `1` — the token produced a
record — so the walk takes `if.then447.i` and calls `s2_after_value` at the root slot.  This
is the arm the scan tail's three links are stated on. -/
structure HcontSeamEmit {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (mid : HcontSeamMid G C s) : Type where
  /-- The scalar call's emitted answer. -/
  hret₂ : mid.r₂.ret = .int 32 (BitVec.ofNat 32 1)
  hev64 : G.ev < 2 ^ 64

/-- **The refusal arm.**  The scalar call answered `0` — `stage2ScalarValue`'s first arm,
`od_fail`'s record — so the walk leaves `if.then425.i` for `if.then432.i` and calls nothing:
the arm's content is the answer and the record the answer wrote.  `stage2ErrSetMsg` is the
model's refusal record (its `ok` word at `%e`, its offset at `%e + 8` and a null message at
`%e + 16`), so `hmem` names the memory the walk's next block starts from.

The token's position `pos` is the model's own reading of the token record (the scalar
staging's `pos`), which is why the field is data rather than a hypothesis: the refusal's
`%e + 8` word is that number. -/
structure HcontSeamRefuse {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (mid : HcontSeamMid G C s) : Type where
  /-- The scalar call's refused answer. -/
  hret₂ : mid.r₂.ret = .int 32 (BitVec.ofNat 32 0)
  /-- The token's position, the refusal record's offset word. -/
  pos : Nat
  /-- The memory the refusal left. -/
  hmem : mid.r₂.mem = stage2ErrSetMsg mid.r₁.mem C.stage.e pos 0

/-- **The seam's two leading calls transport across the byte's leaf**: the leaves bind cells
only, so the memory and the counter are the seam's and everything stated at them moves. -/
def HcontSeamMid.cast {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s s' : State}
    (hmem : s'.mem = s.mem) (hnext : s'.next = s.next)
    (mid : HcontSeamMid G C s) : HcontSeamMid G C s' where
  cA := mid.cA
  rdv := mid.rdv
  r₁ := mid.r₁
  xA := mid.xA
  hpre₁ := by rw [hmem, hnext]; exact mid.hpre₁
  hcall₁ := by rw [hmem, hnext]; exact mid.hcall₁
  hret₁ := mid.hret₁
  hbit0 := mid.hbit0
  hzread := by rw [hmem]; exact mid.hzread
  r₂ := mid.r₂
  hpre₂ := mid.hpre₂
  hcall₂ := mid.hcall₂

/-- **The emit group, as the shared prefix and its third step.**  `HcontSeamCalls` is the
same data at the same fields; this pair is what lets the two arms share the leading calls
without restating them. -/
def HcontSeamCalls.toMid {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (rows : HcontSeamCalls G C s) : HcontSeamMid G C s where
  cA := rows.cA
  rdv := rows.rdv
  r₁ := rows.r₁
  xA := rows.xA
  hpre₁ := rows.hpre₁
  hcall₁ := rows.hcall₁
  hret₁ := rows.hret₁
  hbit0 := rows.hbit0
  hzread := rows.hzread
  r₂ := rows.r₂
  hpre₂ := rows.hpre₂
  hcall₂ := rows.hcall₂

/-- **The emit group, from the shared prefix, the emit step and the copy call.**  The
third call's precondition and answer are the producer's (`s2_after_value` resolves there and
the copy's byte is the invariant's carried across the scalar call), so the step is the arm's
fact and the call is the contract's. -/
def HcontSeamCalls.ofMid {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (mid : HcontSeamMid G C s) (emit : HcontSeamEmit G C s mid) (r₃ : CallOutcome)
    (hpre₃ : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] mid.r₂.mem mid.r₂.next)
    (hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] mid.r₂.mem mid.r₂.next = some r₃) :
    HcontSeamCalls G C s where
  cA := mid.cA
  rdv := mid.rdv
  r₁ := mid.r₁
  xA := mid.xA
  hpre₁ := mid.hpre₁
  hcall₁ := mid.hcall₁
  hret₁ := mid.hret₁
  hbit0 := mid.hbit0
  hzread := mid.hzread
  r₂ := mid.r₂
  hpre₂ := mid.hpre₂
  hcall₂ := mid.hcall₂
  hret₂ := emit.hret₂
  hev64 := emit.hev64
  r₃ := r₃
  hpre₃ := hpre₃
  hcall₃ := hcall₃

/-- The prefix's literal survives the emit group: the two views are one memory. -/
theorem HcontSeamCalls.toMid_cA {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (rows : HcontSeamCalls G C s) : rows.toMid.cA = rows.cA := rfl

/-- The group's literal survives the two-step view. -/
theorem HcontSeamCalls.ofMid_cA {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    {mid : HcontSeamMid G C s} (emit : HcontSeamEmit G C s mid) (r₃ : CallOutcome)
    (hpre₃ : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] mid.r₂.mem mid.r₂.next)
    (hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] mid.r₂.mem mid.r₂.next = some r₃) :
    (HcontSeamCalls.ofMid mid emit r₃ hpre₃ hcall₃).cA = mid.cA := rfl

/-- The group's root word survives the two-step view. -/
theorem HcontSeamCalls.ofMid_rdv {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    {mid : HcontSeamMid G C s} (emit : HcontSeamEmit G C s mid) (r₃ : CallOutcome)
    (hpre₃ : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] mid.r₂.mem mid.r₂.next)
    (hcall₃ : stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] mid.r₂.mem mid.r₂.next = some r₃) :
    (HcontSeamCalls.ofMid mid emit r₃ hpre₃ hcall₃).rdv = mid.rdv := rfl

#print axioms LeanLLVM.Refinement.WalkScope.HcontSeamMid
#print axioms LeanLLVM.Refinement.WalkScope.HcontSeamEmit
#print axioms LeanLLVM.Refinement.WalkScope.HcontSeamRefuse
#print axioms LeanLLVM.Refinement.WalkScope.HcontSeamMid.cast
#print axioms LeanLLVM.Refinement.WalkScope.HcontSeamCalls.toMid
#print axioms LeanLLVM.Refinement.WalkScope.HcontSeamCalls.ofMid

/-- **A seam's three call rows with the kind literal they store.**  The rows are
`HcontSeamCalls`' — the three callees' preconditions and answers at one seam — and the
literal is separate because it is *about* them: the first call's argument list and the
copy's test are read at `writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)`, so
two seams whose literals differ are two different memories, not one row at two states.

`if.then413.i`'s `phi` selects the literal from its predecessor's edge, and a leaf's
`hval` reads that selection, so the literal a leaf needs is fixed by the edge the leaf
comes from.  A seam group that omitted it could not build a leaf at all: the structure's
`hval` would be an equation between the `phi`'s value and an unconstrained word. -/
structure HcontSeamKind {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (cA0 : BitVec 32) : Type where
  /-- The three callee rows at the seam. -/
  calls : HcontSeamCalls G C s
  /-- The kind literal the seam's store writes: the `phi`'s selected incoming. -/
  hcA : calls.cA = cA0
  /-- **The root slot's word before the kind store**, at the seam's memory: the read the
  copy call's argument list carries, which a leaf's `hroot` is the post-store transport of
  (`classCSeam_rootRead`).  It is `HcontSeamRow.hroot`'s statement at the seam rather than at
  the head, and the same shape `HcontWsRows` uses (`hroot` at the run's `contWsTailStart`):
  one form, two states. -/
  hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)

/-- **A seam's kind-`0` rows with the literal they store**: the two leading calls, the
literal, the root slot's word and the *refusal* arm.  This is `HcontSeamKind`'s twin at the
`if.else405.i` edge, and it is the group that edge can carry: `od_scalar_value` answers `0`
there (`stage2ScalarValue`'s first arm), so the walk leaves for `if.then432.i` and never
reaches `s2_after_value`.  `HcontSeamKind`'s third call is therefore not weakened here but
replaced by the refusal record's memory.

The root word is stated at the seam's own memory, as in `HcontSeamKind`: it is what a
leaf's `hroot` transports across the kind store. -/
structure HcontSeamRefusal {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (cA0 : BitVec 32) : Type where
  /-- The two leading calls at the seam. -/
  mid : HcontSeamMid G C s
  /-- The kind literal the seam's store writes: the `phi`'s selected incoming. -/
  hcA : mid.cA = cA0
  /-- The root slot's word before the kind store. -/
  hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes mid.rdv.toNat 4)
  /-- The refusal arm: the scalar answer and the record it wrote. -/
  refuse : HcontSeamRefuse G C s mid

/-- **The refusal group transports across a leaf's binds.**  The mid moves by
`HcontSeamMid.cast` and the refusal arm's statements name `r₁`/`r₂`, which the cast leaves
alone; the root word is at the state's memory. -/
def HcontSeamRefusal.cast {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s s' : State}
    {cA0 : BitVec 32} (hmem : s'.mem = s.mem) (hnext : s'.next = s.next)
    (rows : HcontSeamRefusal G C s cA0) : HcontSeamRefusal G C s' cA0 where
  mid := rows.mid.cast hmem hnext
  hcA := rows.hcA
  hroot := by rw [hmem]; exact rows.hroot
  refuse :=
    { hret₂ := rows.refuse.hret₂
      pos := rows.refuse.pos
      hmem := rows.refuse.hmem }

/-- **The last entry's seam, at its class**: the value-position answer's two arms, crossed
with the kind literal.  The shape is the same as the continuing seams' — the call's answer
and the literal decide which rows exist — but the last level's seam is *not* one
`HcontSeamCalls`: at `%8 ∈ {126, 127}` the literal is `if.else405.i`'s `0`, and
`hcontSeamCalls_no_kind_zero` proves no three-call group exists there.  So the sum is
stated, and the two refusal arms are named: the scalar call's refusal
(`s2ScalarValue_refused`) and, when `s2_value_pos` itself answers `0`, the first call alone
with the short route through `if.then418.i` and `cleanup474.i`. -/
inductive HlastSeam {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Type
  /-- **`s2_value_pos` answered `0`**: no scalar call is made.  The walk leaves
  `if.then413.i` for `if.then418.i`, stores the entry's position at `%e + 8`, and reaches
  the refusal copy through `cleanup474.i`. -/
  | answerZero (rows : HlastSeamZero G C s) : HlastSeam G C s
  /-- **`s2_value_pos` answered `1` at the literal `0`**: the refusal rows (the two
  leading calls, the answer `0` and `stage2ErrSetMsg`'s record), and the walk leaves for
  `if.then432.i` and the error path. -/
  | answerOneRefuse (rows : HlastSeamRefusal G C s) : HlastSeam G C s
  /-- **`s2_value_pos` answered `1` at a nonzero literal**: the emitting group. -/
  | answerOneEmit (rows : HcontSeamCalls G C s) : HlastSeam G C s

/-- **The seam's rows at every seam**: one `∀`-field each.  The continuing seams are the
run class's own `if.then413.i` — `ContTailStartC C` at the state `contWsTailStart` builds
from the check state's stop and byte — and the last entry's is `TailStartC C` at
`hlastTail`.

The edge decides the field, because the kind literal is `if.then413.i`'s `phi` and both the
`phi`'s value and the memory the first call reads are fixed by it:

* `if.else405.i`'s `0` is the **refusal** seam (`scanRefuse`): `od_scalar_value` answers `0`
  at a zero kind, the walk leaves for `if.then432.i` and no third call exists.  The three
  leaves whose predecessor is that edge — the letters `LetS413`, `LeafBlock56`'s else arm
  `ClsS413F` and `LeafBlock58`'s else arm `HeadS413` — read it
  (`HcontSeamRefusal.cast` moves it to each), and it is the field with no emit row;
* `if.then397.i`'s `9`, `if.then403.i`'s `10` and `LeafBlock58`'s `8` are the three emit
  seams (`scanF`, `scan56True`, `scan58True`), one per leaf, because a cast preserves `cA`
  and the leaf's `hval` pins it.

The last entry's field is the **sum** `HlastSeam`, not one group: `hlastTail`'s literal is
the last entry's byte class, so at `%8 ∈ {126, 127}` it is `if.else405.i`'s `0` and the
three-call group does not exist there (`hcontSeamCalls_no_kind_zero`); the class's rows are
`HlastSeam.answerOneRefuse`'s, and `s2_value_pos`'s own zero answer is the third arm
(`HlastSeamZero`, the short route through `if.then418.i` and `cleanup474.i`).
`HlastClassRows.seam` is where the last level's rows are grouped, at the byte-route tail;
its producer is `hlastSeamRefusal_of_stage` and `hlastSeamZero_of_call`
(`JsonStage2WalkDispatchHlastSupply`).

Every field here has an inhabitant at its leaf: `hcontSeamRefusalOf` for `scanRefuse`
(from the staged words alone, the answer and the record being derived),
`hcontSeamKindOf` for the emit fields (whose extra supply is the single row `hemit`), and
`HlastSeam`'s refusal arm for the last level, which is the arm the class's literal `0`
takes. -/
structure HcontSeamAbi {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- **The `if.else405.i` edge's seam, which is the refusal arm.**  That edge writes the
  literal `0`, and `od_scalar_value` answers `0` at a zero kind (`stage2ScalarValue`'s
  first arm, `stage2ErrSetMsg`), so the walk leaves `if.then425.i` for `if.then432.i` and
  no third call exists: the rows are the two leading calls, the answer `0` and the refusal
  record's memory.  This is the field the three leaves whose predecessor is `if.else405.i`
  read. -/
  scanRefuse : ∀ (C : WalkCarry G) (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32)
    (k : Nat) (x1 : BitVec 8),
    HcontSeamRefusal G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1) (BitVec.ofNat 32 0)
  /-- **The `'f'` leaf's seam**: `FS413`, whose `phi` incoming is `if.then397.i`'s `9`.
  The rows are not any other leaf's: the kind literal is the memory the first call reads, so
  each leaf whose predecessor is not `if.else405.i` has its own. -/
  scanF : ∀ (C : WalkCarry G) (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32)
    (k : Nat) (x1 : BitVec 8),
    HcontSeamKind G (ContTailStartC C)
      (FS413 (contWsSeamS C (wsSlAt G sl b35 ix v k) k x1) x1) (BitVec.ofNat 32 9)
  /-- **`110`'s leaf's seam**: `ClsS413T`, whose `phi` incoming is `if.then403.i`'s `10`. -/
  scan56True : ∀ (C : WalkCarry G) (sl : State) (b35 : UInt8) (ix : BitVec 64)
    (v : BitVec 32) (k : Nat) (x1 : BitVec 8),
    HcontSeamKind G (ContTailStartC C)
      (ClsS413T (contWsSeamS C (wsSlAt G sl b35 ix v k) k x1) x1) (BitVec.ofNat 32 10)
  /-- **`116`'s leaf's seam**: `ClsS58T`, whose `phi` incoming is `LeafBlock58`'s own `8`. -/
  scan58True : ∀ (C : WalkCarry G) (sl : State) (b35 : UInt8) (ix : BitVec 64)
    (v : BitVec 32) (k : Nat) (x1 : BitVec 8),
    HcontSeamKind G (ContTailStartC C)
      (ClsS58T (contWsSeamS C (wsSlAt G sl b35 ix v k) k x1) x1) (BitVec.ofNat 32 8)
  /-- **The last entry's seam, at its class**: the value-position answer's sum
  (`HlastSeam`).  The literal is the last entry's byte class, so the field does not name
  one group: the class's `0` takes the refusal arm, a nonzero literal the emit arm, and
  the call's `0` answer the short refusal at any literal. -/
  last : ∀ (C : WalkCarry G) (s : State) (x : BitVec 8) (inc nep : BitVec 64)
    (v : Nat) (ix : BitVec 64) (b35 : UInt8),
    HlastSeam G (TailStartC C) (hlastTail C s x inc nep v ix b35)

/-! ### The scan arm's three links, from the rows

`emptyTailSeg_of_calls` (`JsonStage2WalkDispatchWitnessHlast`) is the same three links on
the arm where the copy call's test is `ult v v`: the equation `%ee.1.i = %cond350.i` makes
the test's result a `decide`, so no span is claimed.  This is the other arm: the index is
strictly below the bound, and the copy's third link needs the span `cd - ei ≤ C.inner`.
-/

/-- **The seam's log word at the first answer's memory.**  The value-position contract's
post hands back the caller's memory, so the post-store read is the callee's memory's read.
This is what lets a consumer that already holds the three answers state the tail without
re-deriving the record the scalar call appended. -/
theorem HcontSeamCalls.hzread_mem {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (rows : HcontSeamCalls G C s) :
    readBytes rows.r₁.mem C.stage.z 8 = some (wordBytes 8 G.ev) := by
  obtain ⟨r₁', hcall₁', hpost₁, _⟩ :=
    s2ValuePosContract.resolves (next := s.next) rows.hpre₁
  obtain ⟨_, _, _, hmemV₁, _⟩ := hpost₁
  have hr₁ : r₁' = rows.r₁ := Option.some.inj (hcall₁'.symm.trans rows.hcall₁)
  rw [hr₁] at hmemV₁
  rw [hmemV₁]
  exact rows.hzread

/-- **The scan arm's tail at a named record.**  `consumerTailSegAt`
(`JsonStage2WalkPrefixCount`) at `Seg.measure`: the three calls' rows, the record the
scalar call appended, and the seam's own cells.  Every premise is a hypothesis of the
composition's, so this is the composition itself rather than a proof about it. -/
theorem scanTailSeg_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (rows : HcontSeamCalls G C s) (ev : EventRecord) {ei cd : Nat}
    (happ : s2ScalarValueAppend rows.r₁.mem rows.r₂.mem (TailCarry₂ C).stage.z
      ev.encodedBytes)
    (hzreadJ : readBytes rows.r₁.mem C.stage.z 8 = some (wordBytes 8 G.ev))
    (hInv : WalkInv G C s) (hblock : C.block = "if.then413.i")
    {p : String} (reg : String) {op : Operand}
    (hpre : s.pre = some p)
    (hphi : phiIncoming p
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some op)
    (hop : evalOperand (stateAt s.env s) op = some (.int 32 rows.cA))
    (hkind : lookupName s.env "%kind404.i" = some (.ptr (C.stage.tok + 16)))
    (hrd : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)))
    (hread : readBytes
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes rows.cA.toNat 4))
      (G.next0 + 8) 4 = some (natToBytes rows.rdv.toNat 4))
    (hc : lookupName s.env "%c.i" = some (.ptr (TailCarry₂ C).stage.c))
    (ht : lookupName s.env "%t352.i" = some (.ptr (TailCarry₂ C).stage.tok))
    (ho : lookupName s.env "%z" = some (.ptr (TailCarry₂ C).stage.z))
    (htight : C.events.length ≤ C.k) (hklt : C.k < G.nep)
    (hei : lookupName s.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 ei)))
    (hcd : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd)))
    (hinner : cd - ei ≤ C.inner) (hlt2 : ei < cd) (hcd64 : cd < 2 ^ 64) :
    WalkSegment (stage2Calls stage2SubCalls) G C s (TailCarryScan C ev)
      (ScanEntry s rows.r₁ rows.r₂ rows.r₃ ei cd rows.cA rows.rdv rows.xA) 3 :=
  Seg.measure (consumerTailSegAt (G := G) (C := C) (s := s) rows.r₁ rows.r₂ rows.r₃ ev ei cd
    hInv hblock p reg rows.cA op rows.rdv rows.xA hpre hphi hop hkind hrd hread rows.hpre₁
    rows.hcall₁ rows.hret₁ rows.hbit0 hzreadJ hc ht ho rows.hcall₂ happ rows.hret₂
    rows.hev64
    (by
      have h1 := hInv.evlen_le
      have h2 := G.evRoom
      have h3 := G.evcapLt
      omega)
    htight hklt rows.hpre₃ rows.hcall₃ hei hcd hinner hlt2 hcd64)

/-- **The scan arm's tail, from the three calls' rows.**  The record the scalar call
appends is existential in its contract's post, so this theorem *returns* it: the three
contracts are applied at their staged argument lists and the composition is
`scanTailSeg_at` at the record the post names. -/
theorem scanTailSeg_of_calls {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (rows : HcontSeamCalls G C s) {ei cd : Nat}
    (hInv : WalkInv G C s) (hblock : C.block = "if.then413.i")
    {p : String} (reg : String) {op : Operand}
    (hpre : s.pre = some p)
    (hphi : phiIncoming p
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some op)
    (hop : evalOperand (stateAt s.env s) op = some (.int 32 rows.cA))
    (hkind : lookupName s.env "%kind404.i" = some (.ptr (C.stage.tok + 16)))
    (hrd : lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)))
    (hread : readBytes
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes rows.cA.toNat 4))
      (G.next0 + 8) 4 = some (natToBytes rows.rdv.toNat 4))
    (hc : lookupName s.env "%c.i" = some (.ptr (TailCarry₂ C).stage.c))
    (ht : lookupName s.env "%t352.i" = some (.ptr (TailCarry₂ C).stage.tok))
    (ho : lookupName s.env "%z" = some (.ptr (TailCarry₂ C).stage.z))
    (htight : C.events.length ≤ C.k) (hklt : C.k < G.nep)
    (hei : lookupName s.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 ei)))
    (hcd : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd)))
    (hinner : cd - ei ≤ C.inner) (hlt2 : ei < cd) (hcd64 : cd < 2 ^ 64) :
    ∃ ev : EventRecord,
      WalkSegment (stage2Calls stage2SubCalls) G C s (TailCarryScan C ev)
        (ScanEntry s rows.r₁ rows.r₂ rows.r₃ ei cd rows.cA rows.rdv rows.xA) 3 := by
  obtain ⟨r₂', hcall₂', hpost₂, _⟩ :=
    s2ScalarValueContract.resolves (next := rows.r₁.next) rows.hpre₂
  have hr₂ : r₂' = rows.r₂ := Option.some.inj (hcall₂'.symm.trans rows.hcall₂)
  rw [hr₂] at hpost₂
  obtain ⟨⟨_, _, _, _, _, _⟩, happPost⟩ := hpost₂
  obtain ⟨ev, happ₂⟩ := happPost rows.hret₂
  exact ⟨ev, scanTailSeg_at G C s rows ev happ₂ rows.hzread_mem hInv hblock reg hpre hphi hop
    hkind hrd hread hc ht ho htight hklt hei hcd hinner hlt2 hcd64⟩

/-! ### The run class's scan tail, at its own seam

The `.ws`/`.run` classes' `hTail`, at `ContTailStartC C` and `contWsTailStart`: the scan
arm's three links with the seam's two cells (`%ee.1.i` is the stop `k` the seam stored,
`%cond350.i` the lane's word) and the span the class's field leaves. -/

/-- **The continuing run class's scan tail, from the seam's rows.**  `HcontFacts.hTail`'s
and `RunFacts.hTail`'s producer: the class's `heicd` (`k < v.toNat`) and its lane bound
(`v.toNat - ix.toNat ≤ C.inner` with `ix.toNat < k`) are the two numeric facts the scan arm
needs, and the seam's cells are the state's. -/
theorem hcontScanTail_of_calls {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (sl : State)
    (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32) (k : Nat) (x1 : BitVec 8)
    (rows : HcontSeamCalls G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1))
    (hInvT : WalkInv G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1))
    {pT : String} (regT : String) {opT : Operand}
    (hpreT : (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).pre = some pT)
    (hincT : phiIncoming pT
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some opT)
    (hopT : evalOperand
      (stateAt (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).env
        (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1)) opT = some (.int 32 rows.cA))
    (hkindT : lookupName (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).env
      "%kind404.i" = some (.ptr (C.stage.tok + 16)))
    (hrdT : lookupName (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).env
      "%root_done.i" = some (.ptr (G.next0 + 8)))
    (hreadRoot : readBytes
      (writeBytes (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).mem
        (C.stage.tok + 16) (natToBytes rows.cA.toNat 4)) (G.next0 + 8) 4 =
      some (natToBytes rows.rdv.toNat 4))
    (hcT : lookupName (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).env
      "%c.i" = some (.ptr (TailCarry₂ (ContTailStartC C)).stage.c))
    (htT : lookupName (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).env
      "%t352.i" = some (.ptr (TailCarry₂ (ContTailStartC C)).stage.tok))
    (hoT : lookupName (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).env
      "%z" = some (.ptr (TailCarry₂ (ContTailStartC C)).stage.z))
    (htightT : (ContTailStartC C).events.length ≤ (ContTailStartC C).k)
    (hkltT : (ContTailStartC C).k < G.nep)
    (heiT : lookupName (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).env
      "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 k)))
    (hcdT : lookupName (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)))
    (hinner : v.toNat - k ≤ (ContTailStartC C).inner)
    (heicd : k < v.toNat) (hcd64 : v.toNat < 2 ^ 64) :
    ∃ ev : EventRecord,
      WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
        (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1)
        (TailCarryScan (ContTailStartC C) ev)
        (contWsEntry C (wsSlAt G sl b35 ix v k) k x1 x1 rows.r₁ rows.r₂ rows.r₃ k v
          rows.cA rows.rdv rows.xA) 3 :=
  scanTailSeg_of_calls G (ContTailStartC C)
    (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1) rows hInvT rfl regT hpreT hincT
    hopT hkindT hrdT hreadRoot hcT htT hoT htightT hkltT heiT hcdT hinner heicd hcd64

/-! ### The run's rows at a class's check state

`HcontRunFacts` (`JsonStage2WalkRevolution`) is the run class's bundle at an arbitrary check
state, and one of its fields is the tail's counted segment.  The group below is the same
bundle **without that field**: the document's stop, the landing's byte and the scan's
traversal, stated at the check state and at the seam's three answers.  Nothing in it is a
segment and nothing is a bundle: the check state's cells are facts, the landing's reads are
facts and the traversal's rows are the round, the byte read and the byte's class, which
`walkScanRounds457_of_cell` consumes.

The answers are parameters rather than fields because the landing's rows are *about* them —
`contWsEntry` takes the three outcomes and the copy's words — so a structure that carried
its own copies could not be fed the seam's.
-/

/-- **The run's rows at a check state**: `HcontRunFacts` minus its `hTail` field.  The
byte's leaf `ss` is an index as well as the tail's source, because the landing's states are
built from it (`ScanEntry ss …`) and the four cells `ScanEntry`/`Latch462S` do not bind are
the leaf's — so they are fields here and the bundle reads them at the rows. -/
structure HcontRunRows {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (sl : State)
    (ss : State)
    (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32) (k : Nat) (x1 : BitVec 8)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) (cA rdv xA : BitVec 32) : Type where
  /-- The check state's own invariant. -/
  hInv : WalkInv G (ContAC₄ C) sl
  /-- The byte before the entry's end, as the check reads it. -/
  h35 : evalOperand sl (.reg "%35") = some (.int 8 (cont35 b35))
  /-- The entry's index and end. -/
  hidx : lookupName sl.env "%idxprom.i" = some (.int 64 ix)
  hcond : lookupName sl.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))
  hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1
  /-- **The whitespace skip's stop and traversal class.** -/
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
  /-- The entry's first byte's class at the seam, and the byte test's clear arm — the arm
  that leaves `if.end372.i` for `if.else387.i`. -/
  h8c : evalOperand (contWsSeamS C (wsSlAt G sl b35 ix v k) k x1) (.reg "%8") =
    some (.int 8 x1)
  hbit : (evalICmp .eq x1 (BitVec.ofNat 8 45) |||
    evalICmp .ult (x1 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0
  /-- The four cells the leaf carries and `ScanEntry`/`Latch462S` bind nothing of: the
  run's stop, the lane's word and the head's two registers.  The tail's contracts read all
  four at the leaf, so the rows state them instead of peeling them from a named leaf. -/
  hssEe : lookupName ss.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 k))
  hssCond : lookupName ss.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))
  hssInc : lookupName ss.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 1)))
  hssNep : lookupName ss.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep))
  /-- The record the scalar call appended, and the memory it wrote. -/
  happ : s2ScalarValueAppend r₁.mem r₂.mem (TailCarry₂ (ContTailStartC C)).stage.z
    ev.encodedBytes
  /-- The copy call's landing: the byte's address and the byte. -/
  a : Nat
  q : Nat
  bs : List UInt8
  h3S : lookupName (ScanEntry ss r₁ r₂ r₃ k v.toNat cA rdv xA).env "%3" =
      some (.ptr a)
  hpos : ((BitVec.ofNat 64 k).signExtend 64).toNat < 2 ^ 63
  hreadS : readBytes
    (ScanEntry ss r₁ r₂ r₃ k v.toNat cA rdv xA).mem
    (a + ((BitVec.ofNat 64 k).signExtend 64).toNat) 1 = some bs
  hbsS : bytesToNat bs = q
  hloc105 : WalkLocal (ScanC₁₀₅ (TailCarryScan (ContTailStartC C) ev))
    (landRhs457OutAt
      (ScanEntry ss r₁ r₂ r₃ k v.toNat cA rdv xA)
      (BitVec.ofNat 64 k) a q)
  x47 : BitVec 8
  h47 : evalOperand
    (landRhs457OutAt
      (ScanEntry ss r₁ r₂ r₃ k v.toNat cA rdv xA)
      (BitVec.ofNat 64 k) a q) (.reg "%47") = some (.int 8 x47)
  hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1
  hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
  hloc96 : WalkLocal (ScanC₉₆ (TailCarryScan (ContTailStartC C) ev))
    (ScanS₉₆ (ScanEntry ss r₁ r₂ r₃ k v.toNat cA rdv xA)
      (BitVec.ofNat 64 k) a q x47)
  hlatch : WalkLocal { TailCarryScan (ContTailStartC C) ev with block := "while.body462.i" }
    (Latch462S (ScanEntry ss r₁ r₂ r₃ k v.toNat cA rdv xA) (BitVec.ofNat 64 k) a q x47)
  /-- The scan runs inside the entry's span. -/
  hspan : v.toNat ≤ entryPos G (C.k + 1)
  hstart : entryPos G C.k ≤ k
  /-- The traversal's round and the input's totality: `walkScanRounds457_of_cell`'s `hround` and
  `hbyte`.  The round is `scanRoundField`'s (`JsonStage2WalkRevolutionScanRound`); the
  totality's read half is `scanByteField`'s and its class half is the document's. -/
  hround : ∀ (C' : WalkCarry G) (s' : State) (p a : Nat) (bs : List UInt8) (q : Nat)
    (x : BitVec 8), WalkInv G C' s' → C'.block = "while.body462.i" →
    lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
    lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) →
    p + 1 < v.toNat → p + 1 < 2 ^ 63 →
    lookupName (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i").env
      "%3" = some (.ptr a) →
    readBytes s'.mem (a + (p + 1)) 1 = some bs → bytesToNat bs = q →
    evalOperand (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
      "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) →
    evalICmp .slt x (BitVec.ofNat 8 13) = 1 →
    evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 →
    WalkLocal (ScanC₁₀₅ (ScanCLand C'))
      (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
        "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) →
    WalkLocal (ScanC₉₆ (ScanCLand C'))
      (ScanS₉₆ (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
        (BitVec.ofNat 64 (p + 1)) a q x) →
    WalkLocal { ScanCLand C' with block := "while.body462.i" }
      (Latch462S (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
        (BitVec.ofNat 64 (p + 1)) a q x) →
    ∃ (C'' : WalkCarry G) (s'' : State) (j : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C' s' C'' s'' j ∧
      WalkInv G C'' s'' ∧ C''.block = "while.body462.i" ∧ j ≤ stage2ByteAllowance ∧
      lookupName s''.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 (p + 1))) ∧
      lookupName s''.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))
  hbyte : ∀ (C' : WalkCarry G) (s' : State) (p : Nat), WalkInv G C' s' →
    C'.block = "while.body462.i" → k < p + 1 → p + 1 < v.toNat →
    lookupName s'.env "%q.0.i246" = some (.int 64 (BitVec.ofNat 64 p)) →
    lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)) →
    ∃ (a : Nat) (bs : List UInt8) (q : Nat) (x : BitVec 8),
      lookupName (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
        "land.rhs457.i").env "%3" = some (.ptr a) ∧
      readBytes s'.mem (a + (p + 1)) 1 = some bs ∧ bytesToNat bs = q ∧
      evalOperand (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
        "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) (.reg "%47") = some (.int 8 x) ∧
      evalICmp .slt x (BitVec.ofNat 8 13) = 1 ∧
      evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 ∧
      WalkLocal (ScanC₁₀₅ (ScanCLand C'))
        (landRhs457OutAt (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat
          "land.rhs457.i") (BitVec.ofNat 64 (p + 1)) a q) ∧
      WalkLocal (ScanC₉₆ (ScanCLand C'))
        (ScanS₉₆ (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x) ∧
      WalkLocal { ScanCLand C' with block := "while.body462.i" }
        (Latch462S (scanLatchOut s' "%inc463.i" "%exitcond298.not" p v.toNat "land.rhs457.i")
          (BitVec.ofNat 64 (p + 1)) a q x)
  /-- The token record's register at the scan's exit. -/
  htok : ∀ (C' : WalkCarry G) (s' : State), WalkInv G C' s' →
    C'.block = "while.body462.i" → ∃ tok : Nat, lookupName s'.env "%t352.i" = some (.ptr tok)

/-- **The scan tail at the run class's seam, at a named record.**  `scanTailSeg_at` at
`ContTailStartC C` and `contWsTailStart`, with the two cells the seam stores and the span
the class's field leaves. -/
theorem hcontScanTail_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (sl : State)
    (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32) (k : Nat) (x1 : BitVec 8)
    (rows : HcontSeamCalls G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1))
    (ev : EventRecord)
    (happ : s2ScalarValueAppend rows.r₁.mem rows.r₂.mem
      (TailCarry₂ (ContTailStartC C)).stage.z ev.encodedBytes)
    (hInvT : WalkInv G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1))
    {pT : String} (regT : String) {opT : Operand}
    (hpreT : (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).pre = some pT)
    (hincT : phiIncoming pT
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some opT)
    (hopT : evalOperand
      (stateAt (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).env
        (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1)) opT = some (.int 32 rows.cA))
    (hkindT : lookupName (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).env
      "%kind404.i" = some (.ptr (C.stage.tok + 16)))
    (hrdT : lookupName (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).env
      "%root_done.i" = some (.ptr (G.next0 + 8)))
    (hreadRoot : readBytes
      (writeBytes (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).mem
        (C.stage.tok + 16) (natToBytes rows.cA.toNat 4)) (G.next0 + 8) 4 =
      some (natToBytes rows.rdv.toNat 4))
    (hcT : lookupName (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).env
      "%c.i" = some (.ptr (TailCarry₂ (ContTailStartC C)).stage.c))
    (htT : lookupName (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).env
      "%t352.i" = some (.ptr (TailCarry₂ (ContTailStartC C)).stage.tok))
    (hoT : lookupName (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).env
      "%z" = some (.ptr (TailCarry₂ (ContTailStartC C)).stage.z))
    (htightT : (ContTailStartC C).events.length ≤ (ContTailStartC C).k)
    (hkltT : (ContTailStartC C).k < G.nep)
    (heiT : lookupName (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).env
      "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 k)))
    (hcdT : lookupName (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1).env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)))
    (hinner : v.toNat - k ≤ (ContTailStartC C).inner)
    (heicd : k < v.toNat) (hcd64 : v.toNat < 2 ^ 64) :
    WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1)
      (TailCarryScan (ContTailStartC C) ev)
      (contWsEntry C (wsSlAt G sl b35 ix v k) k x1 x1 rows.r₁ rows.r₂ rows.r₃ k v
        rows.cA rows.rdv rows.xA) 3 :=
  scanTailSeg_at G (ContTailStartC C)
    (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1) rows ev happ rows.hzread_mem
    hInvT rfl regT hpreT hincT hopT hkindT hrdT hreadRoot hcT htT hoT htightT hkltT heiT hcdT
    hinner heicd hcd64

/-- **The byte's own leaf below `if.else387.i`, as the run's tail reads it.**  The six
leaves into `if.then413.i` differ in the names they bind and in the kind literal their
`phi` selects; they agree in the carry (`{C with block := "if.then413.i"}`), in the memory
and in the counter.  So the leaf is data: its state, its invariant, its three call rows,
the root slot's word at the memory the first call reads, and the `phi`'s own predecessor and
operand.  The four cells `ScanEntry`/`Latch462S` bind nothing of are the rows'
(`HcontRunRows`), not the leaf's, since a `ScanEntry`'s environment is its source's plus the
tail's six binds. -/
structure HcontRunLeaf {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : Type where
  /-- The leaf's endpoint: `if.then413.i`'s state. -/
  ss : State
  /-- The endpoint's invariant, which the class's span produces. -/
  hInv : WalkInv G (ContTailStartC C) ss
  /-- The tail's three call rows at the endpoint. -/
  calls : HcontSeamCalls G (ContTailStartC C) ss
  /-- The root slot's word at the memory the first call reads.  The kind store is inside the
  token record and the slot is outside it, so this is `walkReadBytes_rootSlot_of_tokStore`'s
  transport of the head state's read. -/
  hroot : readBytes (writeBytes ss.mem (C.stage.tok + 16) (natToBytes calls.cA.toNat 4))
    (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)
  /-- The carry's two bounds, which the tail's contracts read. -/
  htight : (ContTailStartC C).events.length ≤ (ContTailStartC C).k
  hklt : (ContTailStartC C).k < G.nep
  /-- The `phi`'s predecessor, its operand, the operand's value and the `phi` itself: the
  leaf's own edge, and the kind literal it selects. -/
  pT : String
  hpre : ss.pre = some pT
  op : Operand
  hphi : phiIncoming pT
    [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
     ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
     ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
     ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
     ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some op
  hval : evalOperand (stateAt ss.env ss) op = some (.int 32 calls.cA)

/-- **The scan tail at the byte's own leaf.**  `hcontScanTail_at`'s statement at the leaf
rather than at the class-C seam: the source is `leaf.ss`, the target `ScanEntry leaf.ss …`,
and every other premise is the leaf's or the rows'. -/
theorem hcontScanTailAt_leaf {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (leaf : HcontRunLeaf G C) (k : Nat) (v : BitVec 32) (ev : EventRecord)
    (happ : s2ScalarValueAppend leaf.calls.r₁.mem leaf.calls.r₂.mem
      (TailCarry₂ (ContTailStartC C)).stage.z ev.encodedBytes)
    (hkindT : lookupName leaf.ss.env "%kind404.i" = some (.ptr (C.stage.tok + 16)))
    (hrdT : lookupName leaf.ss.env "%root_done.i" = some (.ptr (G.next0 + 8)))
    (hcT : lookupName leaf.ss.env "%c.i" = some (.ptr (TailCarry₂ (ContTailStartC C)).stage.c))
    (htT : lookupName leaf.ss.env "%t352.i" =
      some (.ptr (TailCarry₂ (ContTailStartC C)).stage.tok))
    (hoT : lookupName leaf.ss.env "%z" = some (.ptr (TailCarry₂ (ContTailStartC C)).stage.z))
    (heiT : lookupName leaf.ss.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 k)))
    (hcdT : lookupName leaf.ss.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat)))
    (hinner : v.toNat - k ≤ (ContTailStartC C).inner)
    (heicd : k < v.toNat) :
    WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C) leaf.ss
      (TailCarryScan (ContTailStartC C) ev)
      (ScanEntry leaf.ss leaf.calls.r₁ leaf.calls.r₂ leaf.calls.r₃ k v.toNat leaf.calls.cA
        leaf.calls.rdv leaf.calls.xA) 3 :=
  scanTailSeg_at G (ContTailStartC C) leaf.ss leaf.calls ev happ leaf.calls.hzread_mem
    leaf.hInv rfl leaf.pT leaf.hpre leaf.hphi leaf.hval hkindT hrdT leaf.hroot hcT htT hoT
    leaf.htight leaf.hklt heiT hcdT hinner heicd (by have := v.isLt; omega)

/-- **The run class's seam, as a state group.**  The invariant at `contWsTailStart` and the
cells the tail's three calls read: the predecessor and the `phi`'s kind, the five static
registers, the root word across the kind store, the two test cells and the carry's two
bounds.

**Why a group.**  The bundle's `hTail` is stated at this seam, so deriving it from the
three call rows used to need the seam's invariant, which was obtained from the bundle's own
tail (`hcontRunFacts_of_contFacts` feeding `contWsRunF`) — a circle through the bundle's
shape, not its mathematics: `contWsRunF` never reads the tail.  `hcontWsSeam_of_body`
produces this group from the run's *body* (`HcontRunBody`, `contWsRunBody`) and the class-C
span, so the invariant and the cells are state consequences and the tail follows
(`hcontScanTail_of_seam`). -/
structure HcontWsSeam {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (sl : State)
    (b : HcontRunBody G C sl)
    (calls : HcontSeamCalls G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1)) : Type where
  /-- The invariant at the seam, from the run's segment and the byte's span. -/
  hInv : WalkInv G (ContTailStartC C)
    (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1)
  /-- The `phi`'s predecessor, its operand and the operand's value.  The predecessor is
  fixed: the class-C span's `if.else405.i` edge. -/
  hpre : (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1).pre =
    some "if.else405.i"
  hphi : phiIncoming "if.else405.i"
    [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
     ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
     ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
     ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
     ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] =
    some (.imm (.int 32 (BitVec.ofNat 32 0)))
  hop : evalOperand
    (stateAt (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1).env
      (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1))
    (.imm (.int 32 (BitVec.ofNat 32 0))) = some (.int 32 calls.cA)
  /-- The five static registers the three calls read. -/
  hkind : lookupName (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1).env
    "%kind404.i" = some (.ptr ((ContTailStartC C).stage.tok + 16))
  hrd : lookupName (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1).env
    "%root_done.i" = some (.ptr (G.next0 + 8))
  hc : lookupName (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1).env
    "%c.i" = some (.ptr (TailCarry₂ (ContTailStartC C)).stage.c)
  ht : lookupName (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1).env
    "%t352.i" = some (.ptr (TailCarry₂ (ContTailStartC C)).stage.tok)
  ho : lookupName (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1).env
    "%z" = some (.ptr (TailCarry₂ (ContTailStartC C)).stage.z)
  /-- The root slot's word at the memory the first call reads. -/
  hreadRoot : readBytes
    (writeBytes (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1).mem
      ((ContTailStartC C).stage.tok + 16) (natToBytes calls.cA.toNat 4)) (G.next0 + 8) 4 =
    some (natToBytes calls.rdv.toNat 4)
  /-- The copy call's two test cells: the run's stop and the lane's word. -/
  hei : lookupName (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1).env
    "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 b.k))
  hcd : lookupName (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1).env
    "%cond350.i" = some (.int 64 (BitVec.ofNat 64 b.v.toNat))
  hcd64 : b.v.toNat < 2 ^ 64
  /-- The carry's two bounds the tail's contracts read. -/
  htight : (ContTailStartC C).events.length ≤ (ContTailStartC C).k
  hklt : (ContTailStartC C).k < G.nep

/-- **The run class's seam, from the run's body.**  The run's segment is `contWsRunBody`'s,
the byte's span is `walkHeadChainCSeg`'s at the entry's first byte (the class-C route), and
the cells are the seam's own peels.  The bundle's tail is not an input anywhere. -/
noncomputable def hcontWsSeam_of_body {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (b : HcontRunBody G C sl) (hk : C.k + 1 < G.nep)
    (calls : HcontSeamCalls G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1))
    (hc110 : evalICmp .slt b.x1 (BitVec.ofNat 8 110) = 0)
    (hc116 : evalICmp .slt b.x1 (BitVec.ofNat 8 116) = 0)
    (hceq116 : evalICmp .eq b.x1 (BitVec.ofNat 8 116) = 0)
    (hcA : calls.cA = BitVec.ofNat 32 0)
    (hroot : readBytes
      (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1).mem
      (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)) :
    HcontWsSeam G C sl b calls := by
  -- the run, from its own rows, and its endpoint invariant
  let hrun := contWsRunBody G C sl b hk
  have hsegRun : WalkSegment (stage2Calls stage2SubCalls) G (ContAC₄ C) sl (ContSeamC C)
      (contWsSeamS C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1) hrun.choose :=
    hrun.choose_spec.2.1
  have hcondSl : lookupName (wsSlAt G sl b.b35 b.ix b.v b.k).env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 b.v.toNat)) := hrun.choose_spec.2.2
  -- the byte's span to the class-C target
  have hspan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C)
      (contWsSeamS C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1) (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1) 5 :=
    walkHeadChainCSeg (G := G) (C := ContSeamC C)
      (s := contWsSeamS C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1)
      hsegRun.inv' rfl b.h8c hc110 hc116 hceq116
  have hInvT : WalkInv G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1) :=
    hspan.measure.inv'
  refine
    { hInv := hInvT
      hpre := by simp only [contWsTailStart, HeadS413, HeadS405]
      hphi := by decide
      hop := ?_
      hkind := hInvT.regs ("%kind404.i", .ptr ((ContTailStartC C).stage.tok + 16))
        (by simp [walkStaticRegs])
      hrd := hInvT.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs])
      hc := hInvT.regs ("%c.i", .ptr (TailCarry₂ (ContTailStartC C)).stage.c)
        (by simp [walkStaticRegs])
      ht := hInvT.regs ("%t352.i", .ptr (TailCarry₂ (ContTailStartC C)).stage.tok)
        (by simp [walkStaticRegs])
      ho := hInvT.regs ("%z", .ptr (TailCarry₂ (ContTailStartC C)).stage.z)
        (by simp [walkStaticRegs])
      hreadRoot := by
        rw [walkReadBytes_rootSlot_of_tokStore (C := ContTailStartC C) (off := 16) (len := 4)
          (v := natToBytes calls.cA.toNat 4) (by decide) (natToBytes_length _ _)]
        exact hroot
      hei := by
        simp only [contWsTailStart, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62,
          contWsSeamS, seamS, seamFin, stateAt, cells, State.bind]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact lookupName_cons_self _ _ _
      hcd := by
        simp only [contWsTailStart, HeadS413, HeadS405, HeadS58, HeadS60, HeadS62,
          contWsSeamS, seamS, seamFin, stateAt, cells, State.bind]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact hcondSl
      hcd64 := by have := b.v.isLt; omega
      htight := b.hInv.events_le_of_tight
        (walkEmitC_of_not_contains (b := "NodeBlock41") (by decide))
      hklt := by show C.k < G.nep; omega }
  · rw [hcA]
    simp only [evalOperand, Const.toValue]

/-- **The run class's tail, from the seam group.**  `hcontScanTail_at` at the group's own
invariant and cells: every premise is a field or the class's own `heicd`, so the tail is a
consequence of the group and the three calls, not of a bundle. -/
theorem hcontScanTail_of_seam {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (sl : State)
    (b : HcontRunBody G C sl)
    (calls : HcontSeamCalls G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1))
    (seam : HcontWsSeam G C sl b calls) (ev : EventRecord)
    (happ : s2ScalarValueAppend calls.r₁.mem calls.r₂.mem
      (TailCarry₂ (ContTailStartC C)).stage.z ev.encodedBytes) :
    WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1)
      (TailCarryScan (ContTailStartC C) ev)
      (contWsEntry C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1 calls.r₁ calls.r₂
        calls.r₃ b.k b.v calls.cA calls.rdv calls.xA) 3 :=
  hcontScanTail_at G C sl b.b35 b.ix b.v b.k b.x1 calls ev happ seam.hInv
    (pT := "if.else405.i") "if.else405.i" (opT := .imm (.int 32 (BitVec.ofNat 32 0)))
    seam.hpre seam.hphi seam.hop seam.hkind seam.hrd
    seam.hreadRoot seam.hc seam.ht seam.ho seam.htight seam.hklt seam.hei seam.hcd
    (by show b.v.toNat - b.k ≤ C.inner
        have hbud := b.hClass.2.2.2.2.1
        have hik := b.hClass.2.2.2.1
        omega)
    b.heicd (by have := b.v.isLt; omega)

/-- **`HcontRunFacts` from the run's rows and the seam's calls.**  Every field but the
tail's segment is the rows'; the tail is `hcontScanTail_at` at the record the rows name, so
the bundle's one segment enters as the composition's result and not as a field of the
group. -/
noncomputable def hcontRunFacts_of_rows {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (leaf : HcontRunLeaf G C)
    (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32) (k : Nat) (x1 : BitVec 8)
    (ev : EventRecord)
    (rows : HcontRunRows G C sl leaf.ss b35 ix v k x1 leaf.calls.r₁ leaf.calls.r₂
      leaf.calls.r₃ ev leaf.calls.cA leaf.calls.rdv leaf.calls.xA) :
    HcontRunFacts G C sl := by
  have hinner : v.toNat - k ≤ (ContTailStartC C).inner := by
    have hinn : (ContTailStartC C).inner = C.inner := rfl
    have hik := rows.hClass.2.2.2.1
    have hsub := rows.hClass.2.2.2.2.1
    omega
  exact
  { hInv := rows.hInv
    b35 := b35
    h35 := rows.h35
    ix := ix
    hidx := rows.hidx
    v := v
    hcond := rows.hcond
    hugt := rows.hugt
    k := k
    x1 := x1
    hClass := rows.hClass
    heicd := rows.heicd
    h8c := rows.h8c
    hbit := rows.hbit
    ss := leaf.ss
    hssEe := rows.hssEe
    hssCond := rows.hssCond
    hssInc := rows.hssInc
    hssNep := rows.hssNep
    r₁ := leaf.calls.r₁
    r₂ := leaf.calls.r₂
    r₃ := leaf.calls.r₃
    ev := ev
    cA := leaf.calls.cA
    rdv := leaf.calls.rdv
    xA := leaf.calls.xA
    hTail := hcontScanTailAt_leaf G C leaf k v ev rows.happ
      (leaf.hInv.regs ("%kind404.i", .ptr ((ContTailStartC C).stage.tok + 16))
        (by simp [walkStaticRegs]))
      (leaf.hInv.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs]))
      (leaf.hInv.regs ("%c.i", .ptr (TailCarry₂ (ContTailStartC C)).stage.c)
        (by simp [walkStaticRegs]))
      (leaf.hInv.regs ("%t352.i", .ptr (TailCarry₂ (ContTailStartC C)).stage.tok)
        (by simp [walkStaticRegs]))
      (leaf.hInv.regs ("%z", .ptr (TailCarry₂ (ContTailStartC C)).stage.z)
        (by simp [walkStaticRegs]))
      rows.hssEe rows.hssCond hinner rows.heicd
    a := rows.a
    q := rows.q
    bs := rows.bs
    h3S := rows.h3S
    hpos := rows.hpos
    hreadS := rows.hreadS
    hbsS := rows.hbsS
    hloc105 := rows.hloc105
    x47 := rows.x47
    h47 := rows.h47
    hbit47 := rows.hbit47
    hws47 := rows.hws47
    hloc96 := rows.hloc96
    hlatch := rows.hlatch
    hspan := rows.hspan
    hstart := rows.hstart
    hround := rows.hround
    hbyte := rows.hbyte
    htok := rows.htok }

/-! ### The run's bundle at a class's check state, from its rows and its seam

`hcontRunFacts_of_rows` takes the rows and the seam's cells separately; a class supplies
them as two groups: `HcontRunRows` at the check state and `HcontWsSeam` at the seam the
class's own span reaches.  This joins them, so the bundle's one segment is the tail the
cells produce and nothing enters as an assumed segment. -/

/-- **A class's check state**: its prefix's endpoint and the shared four links to
`NodeBlock41`. -/
abbrev contRunCheck {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (q5 : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8) :
    State :=
  contLandOut (G := G) (contMidS C q5 inc nep ep v ix) v.toNat b35

/-- The seam the run's chain reaches: `if.else387.i`'s state at the run's stop.  The
check state's byte is `b35`; the record's byte, the run's start and its bound are the
body's (`bb35`, `bix`, `bv`). -/
abbrev contRunSeamS {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (q5 : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8)
    (bb35 : UInt8) (bix : BitVec 64) (bv : BitVec 32) (k : Nat) (x1 : BitVec 8) : State :=
  contWsSeamS C (wsSlAt G (contRunCheck G C q5 inc nep ep v ix b35) bb35 bix bv k) k x1

/-- The tail's start: the byte's own leaf leaves `if.then413.i`. -/
abbrev contRunTailS {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (q5 : State)
    (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8)
    (bb35 : UInt8) (bix : BitVec 64) (bv : BitVec 32) (k : Nat) (x1 : BitVec 8) : State :=
  contWsTailStart C (wsSlAt G (contRunCheck G C q5 inc nep ep v ix b35) bb35 bix bv k) k x1 x1

/-- **The class-C else leaf, from the seam group.**  The seam's invariant, its three call
rows, its root word and its `phi` — `if.else405.i`'s edge, whose kind literal is `0` — are
the leaf's, so a row stated at the class-C else leaf needs no new leaf data.  This is the
instance `HcontRunRow`'s rows are written at; a row at another leaf supplies its own
producer. -/
noncomputable def hcontRunLeaf_of_seam {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (sl : State) (b : HcontRunBody G C sl)
    (calls : HcontSeamCalls G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1))
    (seam : HcontWsSeam G C sl b calls) : HcontRunLeaf G C where
  ss := contWsTailStart C (wsSlAt G sl b.b35 b.ix b.v b.k) b.k b.x1 b.x1
  hInv := seam.hInv
  calls := calls
  hroot := seam.hreadRoot
  htight := seam.htight
  hklt := seam.hklt
  pT := "if.else405.i"
  hpre := seam.hpre
  op := Operand.imm (.int 32 (BitVec.ofNat 32 0))
  hphi := seam.hphi
  hval := seam.hop

/-- **`HcontRunFacts` from the run's rows and the byte's leaf.**  The rows are the check
state's and the landing's, and the leaf is the byte's own: its invariant, its three call
rows and its `phi`.  The one numeric fact the tail needs beside them is the lane's bound at
the run's stop, which is the rows' class (`v - k ≤ inner` from `v - ix ≤ inner` and
`ix < k`).  So the bundle's tail is `hcontScanTailAt_leaf`'s at the leaf, and no segment is
an input. -/
noncomputable def hcontRunFacts_of_seam {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (q5 : State) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32) (ix : BitVec 64)
    (b35 : UInt8)
    (b : HcontRunBody G C (contRunCheck G C q5 inc nep ep v ix b35))
    (leaf : HcontRunLeaf G C) (ev : EventRecord)
    (rows : HcontRunRows G C (contRunCheck G C q5 inc nep ep v ix b35) leaf.ss
      b.b35 b.ix b.v b.k b.x1 leaf.calls.r₁ leaf.calls.r₂ leaf.calls.r₃ ev leaf.calls.cA
      leaf.calls.rdv leaf.calls.xA) :
    HcontRunFacts G C (contRunCheck G C q5 inc nep ep v ix b35) :=
  hcontRunFacts_of_rows G C (contRunCheck G C q5 inc nep ep v ix b35) leaf
    b.b35 b.ix b.v b.k b.x1 ev rows

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.scanTailSeg_at
#print axioms LeanLLVM.Refinement.WalkScope.scanTailSeg_of_calls
#print axioms LeanLLVM.Refinement.WalkScope.hcontScanTail_of_calls
#print axioms LeanLLVM.Refinement.WalkScope.hcontScanTail_at
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunFacts_of_rows
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunFacts_of_seam
#print axioms LeanLLVM.Refinement.WalkScope.hcontScanTailAt_leaf
#print axioms LeanLLVM.Refinement.WalkScope.hcontRunLeaf_of_seam
#print axioms LeanLLVM.Refinement.WalkScope.hcontWsSeam_of_body
#print axioms LeanLLVM.Refinement.WalkScope.HcontSeamRefusal
#print axioms LeanLLVM.Refinement.WalkScope.HcontSeamRefusal.cast
#print axioms LeanLLVM.Refinement.WalkScope.hcontScanTail_of_seam

end WalkScope
end LeanLLVM.Refinement
