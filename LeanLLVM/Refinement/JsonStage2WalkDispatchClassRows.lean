/-
# The payload's per-class rows, as document facts

`HcontPayload` (`JsonStage2WalkDispatchSupply`) carries the rows the continuing head
reaches without a class: the openers' root word and value-position call, the standalone
string's lane and two calls, the default arm's document row, and the traversal's visits.
The classes the residual table names beside those take rows that are not in that payload:
the byte before the entry's end with its class, the entry's lane and its order, the
whitespace stop with its per-index facts, and the log's two words.

This module states those rows as **one group per class**, in the same shape as the groups
already there: a `∀`-field over the invariant's head states, each field a fact about the
document (read at the state's own memory) or about a call's argument list.  No group holds
an arm or a bundle, and none reads a clause of `WalkInv` as a premise beyond the head state
the row is stated at.  One row holds a *segment* — `HcontDeepRow`'s merge route — and it says
so where it is written: that segment is the arm's own route rather than something the arm
establishes.  The class-C rows hold no span either: `c56TrueSpan` … `c58ElseSpan` compose it
from the head chain's `inv'` and the byte's own bits.

## The classes whose row is a document fact alone

`HcontCleanupDoc` is the scan-free class's document row: the next entry's position word,
its read at the head's own memory, the bound's compare and the byte before the entry's end
with its three pivot bits.  It is *produced* for free from the payload's `defaultLane` row
(`hcontCleanupDoc_of_lane`): the two documents' rows are the same document's, and the only
work is the head chain's own two rewrites — the increment's word (`cont_inc_toNat`) and the
index's spelling (`contIx` is `BitVec.ofNat 64 (entryPos G C.k)` by definition).  So the
class the table marks *document* is reached by the row already carried, and the arm's
producer takes it beside the tail.

`HcontArm.cleanup` is then built at that row and the seam's three call rows
(`hcontArm_cleanup_of_rows`, `JsonStage2WalkDispatchSeamRows`): the seventeen-link chain,
the seam's invariant and its five environment cells are theorems there, and the root
slot's word crosses the seam with `contTailStart_rootRead`, which takes the word the head
state holds — `hcontArm_cleanup_of_rows` is stated at an arbitrary `rdv0`, so the class is
total over the slot's values and not only at `0`.

## The groups this module states

* `HcontCleanupDoc` — the scan-free class's document row, produced from `defaultLane`;
* `HcontSeamRow` — **a class's seam as one row**: the three callee rows at the seam the
  class's own chain reaches, the kind literal that seam's store writes, and the root slot's
  word as the first call reads it.  One structure serves every class whose tail is the
  three calls, because what differs between them is the seam state and the literal;
* `HcontDeepRow` — the positive-depth opener's route: the merge's counted segment with its
  endpoint, or the refusal's witness;
* `HcontRunRow` — the run class's row: the class's prefix and the shared four's cells at
  their endpoint, the check state's rows, the run's body and the seam's state group.  Its
  arm follows from it (`hcontArm_run_of_row`), the one segment below `if.else387.i` being
  the head byte's own leaf;
* `HlastClassDoc`/`HlastClassRows` — the last entry's last byte's class with the seam's
  three calls at its tail start.

The payloads that carry them are `HcontClassRows` and `HlastClassRows`, and their groups
are what the class case's branches read.

## What the groups do not carry

Every group here is a row: a document read, a call's argument list, a set of class bits.
None carries an arm, and none carries a bundle (`HcontFacts`, `HcontCleanupFacts`,
`HcontScalarFacts`, `RunFacts`, `HstringFacts`, `HlastResidue`, `HlastFacts`).  The one
input a class's *arm* needs beside its rows is the invariant at the seam state the tail
starts from — `hInvT` in `hcontTail_of_calls`/`hcontScanTail_at`, `hInvS` in
`scTailByte_of_calls` (`JsonStage2WalkDispatchSegments`).  That state is further along the
walk than the head, so its invariant is not a consequence of `WalkInv` at the head alone:
the seam's block, its extended environment and the token record its step writes are all
new.  It is a head chain's `inv'` rather than a row, and each of the three (the high-byte
route's `ContTailStartC`, the scalar route's `scSeamByte`, the last entry's `TailStartC`) is
produced in `JsonStage2WalkHcontSeamInv` (`contTailStartInv_of_cleanup`,
`scSeamInv_of_scalar`, `hlastTailInv_of_facts`) — so a class's arm is `rows + the seam's
chain`, and the seam between the two is named once per class here rather than hidden in a
row.

The positive-depth string opener is the same kind of seam, and it is closed:
`HcontClass.stringOpener` is the byte test alone and `HcontArm.twoEntry` takes
`C.sp = 0`, so at positive depth `land.lhs.true.i`'s depth test and the marker
bytes at `%sp - 1` select `if.end245.i`'s merge or `if.then249.i`'s refusal.
Those two states are `HcontArm.stringOpenAboveZeroMerge` and
`.stringOpenAboveZeroRefuse` (`JsonStage2WalkDispatchHcontStringDeep`), and each
arm is the class's row plus the chain it carries — the merge's counted segment
to `cleanup478.i`, the refusal's `WalkRefuseAt` — so the class has an arm at both
depths and this module owes it no further row.

## The run class's row

The run class (the one-entry class whose document byte is whitespace) has its own group,
`HcontRunRow`.  Its arm is `HcontArm.run (f : RunFacts G C s)`, and the row is *not* a
bundle: it is the class's prefix to `sw.default.i` with the shared four's cells at that
endpoint, the check state's rows (`HcontRunRows`), the run's body there and the byte's leaf
(`HcontRunLeaf`).  `hcontRunFacts_of_seam` (`JsonStage2WalkDispatchSeams`) joins the last
two into `HcontRunFacts` — its tail is `hcontScanTailAt_leaf`'s at the leaf — and
`runFacts_of_defaultClass` places that bundle after the class's prefix, so the whole
`RunFacts` follows from the row.  The one segment the arm takes beside the row is the
byte's own leaf below `if.else387.i` (`lettersSpan`, `fSpan`, the four class-C spans), and
the class case composes it from the head byte's bits rather than the row holding it.  The
leaf is the row's argument, so every leaf's cell is in the case: the six producers are
`hcontRunLeaf_letters` … `_58Else` (`JsonStage2WalkDispatchClassCase`).  What the leaf's
own producers do *not* supply is its three call answers and the landing built on them —
those are the payload's tail rows (`runTail`), and the row is `hcontRunRow_of_rows`'
(`JsonStage2WalkDispatchRunRow`).
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchSupply
import LeanLLVM.Refinement.JsonStage2WalkDispatchSeams
import LeanLLVM.Refinement.JsonStage2WalkDispatchDefaultLane
import LeanLLVM.Refinement.JsonStage2WalkDispatchRunHead
import LeanLLVM.Refinement.JsonStage2WalkHcontWsScalar

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The class's document row -/

/-- **The class's document row**: the next entry's position word and the read at the
head's own memory, the bound's compare against this entry's index, and the byte before the
entry's end with its route.  The same document fact as `HcontDefaultRow`
(`JsonStage2WalkDispatchSupply`), at the two spellings the producers read: the word at
`contAS₅`'s memory and `%inc.i`'s own value, the compare against the index term the lookup
carries.  The route is the byte's (`HcontByteRoute`), not one asserted leaf: all three
non-whitespace leaves reach `if.end372.i` without a run. -/
structure HcontCleanupDoc {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  /-- The next entry's position word. -/
  v : BitVec 32
  /-- Its read, at the head's memory and the increment's own address. -/
  hread : readBytes (contAS₅ s (hlastByte G C) (hlastIncV C) (hlastNepV G)).mem
    (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4)
  /-- The word is no further than the next entry's position. -/
  hspan : v.toNat ≤ entryPos G (C.k + 1)
  /-- The bound's compare: the entry is not empty. -/
  hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat)
    (BitVec.ofNat 64 (entryPos G C.k)) = 1
  /-- The byte before the entry's end and its route below `if.else387.i`. -/
  hb : HcontByteRoute (cont35 (contB35 G v))

/-- **The class's document row, from the payload's default row.**  The payload's
`lane.defaultLane` states the same document at the head state's memory and the header's
increment; the producers read it at `cond.true345.i`'s memory and `%inc.i`'s word.  The
memory is the state's (every state between the head and the check binds registers only),
the word's value is `cont_inc_toNat`'s, and the index is `contIx`'s own spelling.  The
caller names the byte's route — the three non-whitespace classes — because the whitespace
byte is the run class's, not this one's. -/
noncomputable def hcontCleanupDoc_of_lane {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hk : C.k + 1 < G.nep) (r : HcontDefaultRow G C s)
    (hb : HcontByteRoute (cont35 (contB35 G r.v))) :
    HcontCleanupDoc G C s := by
  obtain ⟨v, hread0, _hv1, hvle, hugt0, _hclass⟩ := r
  have hmem : (contAS₅ s (hlastByte G C) (hlastIncV C) (hlastNepV G)).mem = s.mem := rfl
  refine ⟨v, ?_, hvle, ?_, hb⟩
  · rw [hmem, cont_inc_toNat G C hk]
    exact hread0
  · exact hugt0

/-! ### A class's seam, as one row

Every one of the continuing level's one-entry classes ends its tail at a seam: three
callee rows at a state the class's own chain reaches, the kind literal that state's store
writes, and the root slot's word as the first call reads it.  The three are one group
because the arm reads them together, and the seam state is a parameter: it is the chain's
endpoint, not the head's block, so the group is stated at the class's own reachable state.

The group holds no arm, no bundle and no `WalkInv`: `calls` is the three calls' argument
lists with their outcomes, `hcA` is the store's literal, and `hroot` is
`readBytes` of the head's own memory at the slot the first call reads. -/
structure HcontSeamRow {m0 : Mem} (G : WalkGeom m0) (s : State) (Cp : WalkCarry G)
    (sp : State) (cA0 : BitVec 32) : Type where
  /-- The three callee rows at the seam. -/
  calls : HcontSeamCalls G Cp sp
  /-- The kind literal the seam's `if.then413.i` store writes. -/
  hcA : calls.cA = cA0
  /-- The root slot's word at the head state, which the first call reads. -/
  hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes calls.rdv.toNat 4)

/-! ### The positive-depth opener's route row

The byte `34` at a positive depth leaves `if.then219.i` for `land.lhs.true.i`, and the two
stack bytes at `%sp - 1` select `if.end245.i`'s `phi`: the merge's route to
`cleanup478.i`, or `if.then249.i`'s refusal.  The class's own facts are derived (the byte
from `cont_reg8`, the two stack bytes from the carry's maps, the call's staging from
`HcontOpenCall`), so what the class's row is is the route: the merge's counted segment with
its endpoint, or the refusal's witness.  A `Type`-valued inductive rather than a
disjunction, because the arm's producer eliminates it. -/
inductive HcontDeepRow {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Type
  /-- The merge's route: the counted segment to `cleanup478.i` and the cells the merge's
  `phi` reads there. -/
  | merge (Cd : WalkCarry G) (sd : State) (p k2 : Nat) (nepv : BitVec 64)
      (hseg : WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p)
      (hblock : Cd.block = "cleanup478.i") (hkC : Cd.k = C.k)
      (prev : String) (hprev : prev = "if.then330.i" ∨ prev = "if.else334.i")
      (hpre : sd.pre = some prev)
      (hinc : lookupName sd.env "%inc208.i" = some (.int 64 (BitVec.ofNat 64 k2)))
      (hnepv : lookupName sd.env "%nep" = some (.int 64 nepv))
      (hadvance : C.k < k2) (hcap : k2 ≤ nepv.toNat)
      (hprice : p + 2 ≤ stage2EntryAllowance * (k2 - C.k) +
        stage2ByteAllowance * (entryPos G k2 - entryPos G C.k)) : HcontDeepRow G C s
  /-- The refusal's route: `if.then249.i`'s witness, as every refusing route states it. -/
  | refuse (href : WalkRefuseAt (stage2Calls stage2SubCalls) G C s) : HcontDeepRow G C s

/-! ### The run class's row, and its arm

The run class is the one-entry class whose document byte is whitespace: the skip runs, the
token's end is the run's stop, the copy call's test is true, and the scan is entered so the
merge follows its exit.  Its arm is `HcontArm.run (f : RunFacts G C s)`.

The row is the class's evidence, not the bundle: the prefix segment to `sw.default.i` and
the shared four's cells at its endpoint (the ten numbers `runFacts_of_defaultClass` reads),
the check state's rows at `NodeBlock41` (`HcontRunRows`), the run's body there
(`HcontRunBody`), and the seam's state group (`HcontWsSeam`) with its three calls.  Both
groups are state data — a document's cells and a set of call rows — and neither is an arm,
a bundle or a segment. -/
structure HcontRunRow {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Type where
  /-- The class's prefix endpoint: `sw.default.i`'s state. -/
  q5 : State
  nq : Nat
  hPrefix : WalkSegment (stage2Calls stage2SubCalls) G C s (HeadAC₄ C) q5 nq
  hnq : nq ≤ 4
  /-- The count test's two words and its outcome at the endpoint. -/
  inc : BitVec 64
  nep : BitVec 64
  hinc : evalOperand q5 (.reg "%inc.i") = some (.int 64 inc)
  hnep : evalOperand q5 (.reg "%nep") = some (.int 64 nep)
  hnext : evalICmp .ult inc nep = 1
  /-- The next entry's position word, its read and the bound's compare. -/
  ep : Nat
  h5 : lookupName (contSwOut q5 inc nep).env "%5" = some (.ptr ep)
  hi63 : inc.toNat < 2 ^ 63
  v : BitVec 32
  hread : readBytes (contSwOut q5 inc nep).mem (ep + inc.toNat * 4) 4 =
    some (natToBytes v.toNat 4)
  /-- The entry's index and the two token-record pointers the check stores. -/
  ix : BitVec 64
  hidx : lookupName (contSwOut q5 inc nep).env "%idxprom.i" = some (.int 64 ix)
  htok : lookupName (contSwOut q5 inc nep).env "%t352.i" = some (.ptr C.stage.tok)
  hgap : lookupName (contSwOut q5 inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20))
  hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1
  /-- The byte before the entry's end, read at the whitespace check. -/
  b35 : UInt8
  hread35 : readBytes (contMidS C q5 inc nep ep v ix).mem ((G.b - 1) + v.toNat) 1 =
    some [b35]
  /-- The run's own rows at the check state: its stop, its class and its span. -/
  b : HcontRunBody G C (contRunCheck G C q5 inc nep ep v ix b35)
  /-- **The byte's own leaf below `if.else387.i`.**  The class reaches `if.then413.i`
  through one of six leaves, and they differ in the environment they bind and in the kind
  literal the `phi` selects; the tail's three calls, the landing and the scan's entry are
  stated at whichever leaf the class's own bits select.  So the leaf is the row's data. -/
  leaf : HcontRunLeaf G C
  /-- The record the tail's scalar call appends. -/
  ev : EventRecord
  /-- The check state's rows: the cells, the landing's reads and the traversal, at the
  leaf's own three answers. -/
  rows : HcontRunRows G C (contRunCheck G C q5 inc nep ep v ix b35) leaf.ss
    b.b35 b.ix b.v b.k b.x1 leaf.calls.r₁ leaf.calls.r₂ leaf.calls.r₃ ev leaf.calls.cA
    leaf.calls.rdv leaf.calls.xA

/-- The run class's seam state, from a row's own fields. -/
abbrev HcontRunRow.seamS {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (row : HcontRunRow G C s) : State :=
  contRunSeamS G C row.q5 row.inc row.nep row.ep row.v row.ix row.b35
    row.b.b35 row.b.ix row.b.v row.b.k row.b.x1

/-- The leaf's endpoint, from a row's own fields: the tail's source and the landing's
base. -/
abbrev HcontRunRow.tailS {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (row : HcontRunRow G C s) : State :=
  row.leaf.ss

/-- **The run class's arm, from its row.**  The bundle is `hcontRunFacts_of_seam`'s at the
check state, placed after the class's prefix and the shared four by
`runFacts_of_defaultClass`; the byte's own span below `if.else387.i` is the one segment the
arm takes beside the row, and the class case composes it from the head byte's bits.  The
span ends at the leaf's endpoint `row.tailS`, whose invariant is the span's own, so the
producer takes no state fact the class does not have. -/
noncomputable def hcontArm_run_of_row {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep) (row : HcontRunRow G C s) {nS : Nat}
    (hSpan : Seg (stage2Calls stage2SubCalls) G (ContSeamC C) row.seamS
      (ContTailStartC C) row.tailS nS)
    (hnS : nS ≤ 5) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .run (runFacts_of_defaultClass G C s hInv hblock row.q5 row.nq row.hPrefix row.hnq
    row.hinc row.hnep row.hnext row.h5 row.hi63 row.hread row.hidx row.htok row.hgap row.hugt
    row.hread35
    (hcontRunFacts_of_seam G C row.q5 row.inc row.nep row.ep row.v row.ix row.b35
      row.b row.leaf row.ev row.rows)
    hk hSpan hnS)

/-! ### The plain-value class's whitespace run

`HcontScalarWsRow` is the numeral route's whitespace cell: the plain-value prefix's
document cells, the byte's class with the run's stop, the seam's own cells and invariant,
and the seam's three call rows with the scan's landing.  The arm's producer joins the last
two into the tail with `scanTailSeg_at`, so the segment is a consequence of the rows and
not a field.  It is `HcontRunRow`'s shape at `HcontScalarWsFacts`'s states: the run's body
enters as the document's class and the stop's per-index facts, and the seam's state group
as the invariant and the cells. -/

/-- **The numeral route's whitespace row**: the bundle's document fields with the seam's
three call rows in place of the tail's segment. -/
structure HcontScalarWsRow {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  /-- The plain-value prefix: the head's byte and its four pivots, the counts and the
  lane. -/
  x : BitVec 8
  h8 : evalOperand s (.reg "%8") = some (.int 8 x)
  hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1
  h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0
  h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1
  hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0
  hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
    evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1
  inc : BitVec 64
  nep : BitVec 64
  hinc : evalOperand (scS₄ s x) (.reg "%inc.i") = some (.int 64 inc)
  hnep : evalOperand (scS₄ s x) (.reg "%nep") = some (.int 64 nep)
  hnext : evalICmp .ult inc nep = 1
  ep : Nat
  v : BitVec 32
  h5 : lookupName (scS₅ s x inc nep).env "%5" = some (.ptr ep)
  hi63 : inc.toNat < 2 ^ 63
  hread : readBytes (scS₅ s x inc nep).mem (ep + inc.toNat * 4) 4 =
    some (natToBytes v.toNat 4)
  ix : BitVec 64
  hidx5 : lookupName (scS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix)
  hidxS : lookupName s.env "%idxprom.i" = some (.int 64 ix)
  htok5 : lookupName (scS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok)
  hgap5 : lookupName (scS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20))
  hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat) ix = 1
  b35 : UInt8
  hread35 : readBytes (sEnd C s x inc nep ep v ix).mem ((G.b - 1) + v.toNat) 1 =
    some [b35]
  hx : x = hlastByte G C
  /-- The whitespace skip's stop, its byte class and its per-index facts. -/
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
  heicd : k < v.toNat
  hspan : v.toNat ≤ entryPos G (C.k + 1)
  /-- The seam's own cells: its byte, the token's end pointer, the bound and the root
  slot's word — state facts at the run's stop, as `HcontRunRows` states its own. -/
  h8m : evalOperand (scWsSeam C (scWsSl G C s x inc nep ep v ix b35 k) k x) (.reg "%8") =
    some (.int 8 x)
  hendm : lookupName (scWsSeam C (scWsSl G C s x inc nep ep v ix b35 k) k x).env "%end.i" =
    some (.ptr (C.stage.tok + 8))
  hcdm : lookupName (scWsSeam C (scWsSl G C s x inc nep ep v ix b35 k) k x).env
    "%cond350.i" = some (.int 64 (BitVec.ofNat 64 v.toNat))
  hInvSeam : WalkInv G (HeadC₄₁₃ (ContAC₇ C))
    (scWsSeam C (scWsSl G C s x inc nep ep v ix b35 k) k x)
  /-- The seam's three call rows, with the record the scalar call appended. -/
  calls : HcontSeamCalls G (HeadC₄₁₃ (ContAC₇ C))
    (scWsSeam C (scWsSl G C s x inc nep ep v ix b35 k) k x)
  hcA : calls.cA = BitVec.ofNat 32 7
  ev : EventRecord
  happ : s2ScalarValueAppend calls.r₁.mem calls.r₂.mem
    (TailCarry₂ (HeadC₄₁₃ (ContAC₇ C))).stage.z ev.encodedBytes
  /-- The copy call's test: the root slot's word at the seam's own memory. -/
  hrootm : readBytes
    (writeBytes (scWsSeam C (scWsSl G C s x inc nep ep v ix b35 k) k x).mem
      (C.stage.tok + 16) (natToBytes calls.cA.toNat 4)) (G.next0 + 8) 4 =
    some (natToBytes calls.rdv.toNat 4)
  /-- The scan's landing, at the scan's entry. -/
  a : Nat
  q : Nat
  bs : List UInt8
  h3S : lookupName
    (scWsEntry C (scWsSl G C s x inc nep ep v ix b35 k) k x v calls.r₁ calls.r₂ calls.r₃
      calls.cA calls.rdv calls.xA).env "%3" = some (.ptr a)
  hpos : ((BitVec.ofNat 64 k).signExtend 64).toNat < 2 ^ 63
  hreadS : readBytes
    (scWsEntry C (scWsSl G C s x inc nep ep v ix b35 k) k x v calls.r₁ calls.r₂ calls.r₃
      calls.cA calls.rdv calls.xA).mem
    (a + ((BitVec.ofNat 64 k).signExtend 64).toNat) 1 = some bs
  hbsS : bytesToNat bs = q
  hloc105 : WalkLocal (ScanC₁₀₅ (TailCarryScan (HeadC₄₁₃ (ContAC₇ C)) ev))
    (landRhs457OutAt
      (scWsEntry C (scWsSl G C s x inc nep ep v ix b35 k) k x v calls.r₁ calls.r₂ calls.r₃
        calls.cA calls.rdv calls.xA) (BitVec.ofNat 64 k) a q)
  x47 : BitVec 8
  h47 : evalOperand
    (landRhs457OutAt
      (scWsEntry C (scWsSl G C s x inc nep ep v ix b35 k) k x v calls.r₁ calls.r₂ calls.r₃
        calls.cA calls.rdv calls.xA) (BitVec.ofNat 64 k) a q) (.reg "%47") =
    some (.int 8 x47)
  hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1
  hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
  hloc96 : WalkLocal (ScanC₉₆ (TailCarryScan (HeadC₄₁₃ (ContAC₇ C)) ev))
    (ScanS₉₆ (scWsEntry C (scWsSl G C s x inc nep ep v ix b35 k) k x v calls.r₁ calls.r₂
      calls.r₃ calls.cA calls.rdv calls.xA) (BitVec.ofNat 64 k) a q x47)
  hlatch : WalkLocal
    { TailCarryScan (HeadC₄₁₃ (ContAC₇ C)) ev with block := "while.body462.i" }
    (scWsLatch C (scWsSl G C s x inc nep ep v ix b35 k) k x v calls.r₁ calls.r₂ calls.r₃
      calls.cA calls.rdv calls.xA (BitVec.ofNat 64 k) a q x47)
  /-- The visits' totality: the document's byte at every index the scan visits. -/
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

/-- **The whitespace-run arm, from its row.**  The tail is `scanTailSeg_at`'s at the
seam's own calls, the cells and the record the scalar call appended — so the segment is
the composition's and no field of the row is one.  The bundle is then the row's fields
beside that tail. -/
noncomputable def hcontArm_scalarRun_of_row {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (_hInv : WalkInv G C s) (_hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep) (row : HcontScalarWsRow G C s) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .scalarRun
    { x := row.x
      h8 := row.h8
      hlt91 := row.hlt91
      h44 := row.h44
      h58 := row.h58
      hne44 := row.hne44
      hbit := row.hbit
      inc := row.inc
      nep := row.nep
      hinc := row.hinc
      hnep := row.hnep
      hnext := row.hnext
      ep := row.ep
      v := row.v
      h5 := row.h5
      hi63 := row.hi63
      hread := row.hread
      ix := row.ix
      hidx5 := row.hidx5
      hidxS := row.hidxS
      htok5 := row.htok5
      hgap5 := row.hgap5
      hugt := row.hugt
      b35 := row.b35
      hread35 := row.hread35
      hx := row.hx
      k := row.k
      hClass := row.hClass
      heicd := row.heicd
      hspan := row.hspan
      h8m := row.h8m
      hendm := row.hendm
      r₁ := row.calls.r₁
      r₂ := row.calls.r₂
      r₃ := row.calls.r₃
      ev := row.ev
      cA := row.calls.cA
      rdv := row.calls.rdv
      xA := row.calls.xA
      hTail :=
        scanTailSeg_at (G := G) (C := HeadC₄₁₃ (ContAC₇ C))
          (s := scWsSeam C (scWsSl G C s row.x row.inc row.nep row.ep row.v row.ix row.b35
            row.k) row.k row.x)
          row.calls row.ev row.happ (HcontSeamCalls.hzread_mem row.calls) row.hInvSeam
          rfl (p := "if.end372.i") "if.end372.i"
          (op := Operand.imm (.int 32 (BitVec.ofNat 32 7)))
          (by
            rw [scWsSeam_pre C
              (scWsSl G C s row.x row.inc row.nep row.ep row.v row.ix row.b35 row.k) row.k
              row.x]
            rw [scWsSl_pc C s row.x row.inc row.nep row.ep row.v row.ix row.b35
              row.hClass.2.2.2.1])
          (by decide) (by rw [row.hcA]; rfl)
          (row.hInvSeam.regs ("%kind404.i", .ptr (C.stage.tok + 16))
            (by simp [walkStaticRegs]))
          (row.hInvSeam.regs ("%root_done.i", .ptr (G.next0 + 8))
            (by simp [walkStaticRegs]))
          row.hrootm
          (row.hInvSeam.regs ("%c.i",
            .ptr (TailCarry₂ (HeadC₄₁₃ (ContAC₇ C))).stage.c) (by simp [walkStaticRegs]))
          (row.hInvSeam.regs ("%t352.i",
            .ptr (TailCarry₂ (HeadC₄₁₃ (ContAC₇ C))).stage.tok) (by simp [walkStaticRegs]))
          (row.hInvSeam.regs ("%z",
            .ptr (TailCarry₂ (HeadC₄₁₃ (ContAC₇ C))).stage.z) (by simp [walkStaticRegs]))
          (row.hInvSeam.events_le_of_tight
            (walkEmitC_of_not_contains (b := "if.then413.i") (by decide)))
          (by show C.k < G.nep; omega)
          (scWsSeam_ee C _ row.k row.x) row.hcdm
          (by
            have hik : row.ix.toNat < row.k := row.hClass.2.2.2.1
            have hsub : row.v.toNat - row.ix.toNat ≤ C.inner := row.hClass.2.2.2.2.1
            have hinn : (HeadC₄₁₃ (ContAC₇ C)).inner = C.inner := rfl
            show row.v.toNat - row.k ≤ (HeadC₄₁₃ (ContAC₇ C)).inner
            omega)
          row.heicd (by have := row.v.isLt; omega)
      a := row.a
      q := row.q
      bs := row.bs
      h3S := row.h3S
      hpos := row.hpos
      hreadS := row.hreadS
      hbsS := row.hbsS
      hloc105 := row.hloc105
      x47 := row.x47
      h47 := row.h47
      hbit47 := row.hbit47
      hws47 := row.hws47
      hloc96 := row.hloc96
      hlatch := row.hlatch
      hbyte := row.hbyte }

/-! ### The payload's per-class groups -/

/-! ### The run class's document rows

Two groups, both about the document and neither about the run's execution: the whitespace
skip's **class** (its per-index run, its stop and the stop's place inside the entry) and
the run's **tail rows** (the landing's byte and the scan's traversal, at the check state and
the byte's leaf).  They are separated because they are read at different points: the class
fixes `k`, which is what the check state and the tail are stated at, so the tail group takes
the body as an argument rather than choosing `k` again.

**What the payload's own rows already supply, and what these add.**  `HcontDefaultRow`
carries the entry's lane and, in its `hclass`, the *class* of the byte before the entry's
end — at `.wsByte` that is `wsStop G (r.v.toNat - 1)`, one byte's fact.  The skip runs from
the entry's index until its first whitespace byte, so the stop and the per-index run are
what the one-byte class cannot give; `HcontRunSkip` is exactly that, and it is guarded by
the one-byte class the payload already carries.  `HcontRunTail` is the group
`HcontRunRows` names — the landing's reads and the traversal's `hround`/`hbyte` — which is
the input's content at the scan's own span and is not derivable from the invariant.

**Neither group carries a segment, a bundle or an arm**, and neither chooses a state: the
skip group is stated at the head state (its terms are `contIx G C` and `r.v`, both functions
of the head), and the tail group at the check state the class's prefix and the shared four
build, with the byte's leaf as its index. -/

/-- **The whitespace skip's class at a continuing head.**  `k` is the stop: every index from
this entry's position to `k` continues the token, the byte at `k` stops it, and `k` is above
the entry's position.

The byte before the entry's end being whitespace is the caller's guard — it is the
payload's `HcontDefaultRow.hclass` at `.wsByte`, and the class case destructures that
disjunct — so this group does not restate it.  `k < r.v.toNat` is *not* a field: it follows
from the stop being inside the entry, which the per-index run and the one-byte class force
(`cont_heicd` is that argument at the bundle that carries it). -/
structure HcontRunSkip {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (r : HcontDefaultRow G C s) : Type where
  /-- The skip's stop. -/
  k : Nat
  /-- Every index from this entry's position to the stop continues the token. -/
  hrun : ∀ q, (contIx G C).toNat ≤ q → q < k → wsCont G q
  /-- The byte at the stop is whitespace. -/
  hstop : wsStop G k
  /-- The stop is above the entry's position. -/
  hik : (contIx G C).toNat < k
  /-- **The entry's span is inside the component's budget.**  This is the one conjunct
  `WalkInv` cannot supply: `inner_cap` bounds `C.inner` above, and the walk asserts the
  invariant at mid-scan states where the component is being spent down.  At the loop head it
  is the refill's — `walkSeed` and the back edge both set `inner := walkInnerCap G`, and
  `v.toNat - entryPos G C.k ≤ G.n` by the stream's order (`walkLoopHead_inner_pos`).  It is
  the same conjunct `HcontRunBody.hClass` carries and the first visit's `ScanEntered` reads. -/
  hinner : r.v.toNat - (contIx G C).toNat ≤ C.inner

/-- **The run's tail rows, at the class's check state and the byte's leaf.**  The landing's
byte and its three reads, the scan's traversal `hround`/`hbyte`, and the four cells the
leaf's state does not bind — `HcontRunRows`' content — with the record the scalar call
appends existentially, because the record is the call's post's and not a choice.

The body is an argument: its `k` is the skip's, so the group does not restate the skip's
class.  The consumer is `hcontRunRow_of_rows`, which places it in `HcontRunRow` after the
row's head part. -/
structure HcontRunTail {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (r : HcontDefaultRow G C s) (q5 : State) (leaf : HcontRunLeaf G C)
    (b : HcontRunBody G C (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
      (contIx G C) (contB35 G r.v))) : Type where
  /-- The record the tail's scalar call appends. -/
  ev : EventRecord
  /-- The landing and the traversal, at the leaf's own three answers. -/
  rows : HcontRunRows G C (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
      (contIx G C) (contB35 G r.v)) leaf.ss b.b35 b.ix b.v b.k b.x1
    leaf.calls.r₁ leaf.calls.r₂ leaf.calls.r₃ ev leaf.calls.cA leaf.calls.rdv leaf.calls.xA

/-- **The continuing payload's class rows**: the rows the residual table names beside
`HcontPayload`'s, one group per class of `HcontClass`.  Each field is guarded by its
class's own states — the head state's invariant and continuing guard where the class's
chain is composed from the payload's document row, and the class's own premises where the
producer reads them — so no field is stated at "every head".

The fields are the producers' remaining argument lists:

* `cleanup` — the scan-free class's document row, produced from the payload's own
  `defaultLane` (`hcontCleanupDoc_of_lane`), so it costs no new supply;
* `cleanupRow` — the same class's seam row, at `contTailStart`'s own state; its root slot's
  word is the state's, which the arm's producer takes freely (`rdv0`);
* `scalar` — the plain-value class's seam row, at the seam `scTailByte_of_calls` reads
  (`scSeamByte … pre.hb`, whose cells are the class's own peels);
* `letters`, `fLetter` — the default arm's scan-free classes' seam rows, at the seams
  `LetS413` and `FS413` that their head chains reach;
* `c56True`, `c56Else`, `c58True`, `c58Else` — the class-C span's four leaves' seam rows,
  at the four named seam states (`ClsS413T`/`ClsS413F`/`ClsS58T`/`HeadS413`);
* `deep` — the positive-depth opener's route row (`HcontDeepRow`): the merge's counted
  segment and endpoint, or the refusal's witness, named as the arm's own segment;
* `runSkip` — the whitespace skip's class (`HcontRunSkip`): the per-index run, the stop and
  its place in the entry, at a continuing head whose next entry's last byte is whitespace;
* `runTail` — the run's tail rows (`HcontRunTail`): the landing's byte, its reads and the
  traversal's two `∀`s, at the check state the class's prefix builds and the byte's leaf,
  with the appended record; the body it is stated at is `hcontRunBody_of_skip`'s;
* `run` — the run class's arm from a row, which the class case feeds with
  `hcontRunRow_of_rows` at the leaf the head byte's bits select;
* `seam` — the seams `HcontSeamAbi` names: the `if.else405.i` edge's refusal group and the
  four emit groups (each inhabited at its leaf);
* `refuseSeg` — the kind-`0` edge's refusal route as a segment, with the slow scan's stop
  named; the arm it feeds is `HcontArm.badToken`.

The run class's leaf is an argument of both producers rather than a field of the payload:
the segment below `if.else387.i` belongs to the head byte's class, and the case's branch
composes it (`hcontArm_run_of_class`). -/
structure HcontClassRows {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- The default-value class's document row (`126`/`127` at a continuing head), at the
  payload's default row and the byte's own route: the three non-whitespace leaves all
  reach the seam without a run. -/
  cleanup : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → (r : HcontDefaultRow G C s) →
    HcontByteRoute (cont35 (contB35 G r.v)) → HcontCleanupDoc G C s
  /-- The default-value class's seam row: the three callee rows at the byte route's tail
  start, whose kind literal is `if.else405.i`'s `0`.  Its root slot's word is the state's
  own, so the arm is total over the slot's values (`hcontArm_cleanup_of_rows` takes
  `rdv0` freely). -/
  cleanupRow : ∀ (C : WalkCarry G) (s : State) (doc : HcontCleanupDoc G C s),
    HcontSeamRow G s (ContTailStartC C)
      (contTailStartByte C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
        (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C) doc.hb)
      (BitVec.ofNat 32 0)
  /-- The plain-value class's seam row, at the class's own prefix and the document byte's
  route: the producer's remaining argument, with the prefix's values fixing the seam
  state. -/
  scalar : ∀ (C : WalkCarry G) (s : State) (pre : HcontScalarPrefix G C s),
    HcontSeamRow G s (HeadC₄₁₃ (ContAC₇ C))
      (scSeamByte (sLand C s pre.x pre.inc pre.nep pre.ep pre.v pre.ix pre.b35)
        pre.v.toNat pre.x C.stage.tok pre.b35 pre.hb)
      (BitVec.ofNat 32 7)
  /-- **The plain-value class's whitespace-run row**: `.value` × `wsByte`, the cell the
  route-carrying `scalar` row cannot reach (its `pre.hb` is the three non-whitespace
  leaves).  The row is `HcontScalarWsRow`'s — the prefix's document cells, the byte's
  class with the run's stop, the seam's own cells and invariant, and the seam's three
  calls — and its producer is `hcontArm_scalarRun_of_row`, which builds the tail from the
  calls. -/
  scalarRun : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → HcontScalarWsRow G C s
  /-- The letters class's seam row: the head chain's endpoint's seam `LetS413`, whose
  kind literal is `if.end372.i`'s `0`. -/
  letters : ∀ (C : WalkCarry G) (s : State) {x : BitVec 8} (ch : HcontHeadChain G C s x),
    HcontSeamRow G s (HeadC₄₁₃ (LetC₄₀₅ ch.Cm)) (LetS413 ch.sm x) (BitVec.ofNat 32 0)
  /-- The `'f'` leaf's seam row: the head chain's endpoint's seam `FS413`, whose kind
  literal is `if.then397.i`'s `9`. -/
  fLetter : ∀ (C : WalkCarry G) (s : State) {x : BitVec 8} (ch : HcontHeadChain G C s x),
    HcontSeamRow G s (FC₄₁₃ ch.Cm) (FS413 ch.sm x) (BitVec.ofNat 32 9)
  /-- `110`'s leaf seam: `LeafBlock56`'s true arm, kind `10`. -/
  c56True : ∀ (C : WalkCarry G) (s : State) {x : BitVec 8} (ch : HcontHeadChain G C s x),
    HcontSeamRow G s ({ ClsC₄₀₃ ch.Cm with block := "if.then413.i" }) (ClsS413T ch.sm x)
      (BitVec.ofNat 32 10)
  /-- `111 … 115`'s leaf seam: `LeafBlock56`'s else arm, kind `0`. -/
  c56Else : ∀ (C : WalkCarry G) (s : State) {x : BitVec 8} (ch : HcontHeadChain G C s x),
    HcontSeamRow G s (HeadC₄₁₃ (ClsC₄₀₅ ch.Cm)) (ClsS413F ch.sm x) (BitVec.ofNat 32 0)
  /-- `116`'s leaf seam: `LeafBlock58` itself, kind `8`. -/
  c58True : ∀ (C : WalkCarry G) (s : State) {x : BitVec 8} (ch : HcontHeadChain G C s x),
    HcontSeamRow G s ({ HeadC₅₈ ch.Cm with block := "if.then413.i" }) (ClsS58T ch.sm x)
      (BitVec.ofNat 32 8)
  /-- `117 … 125`'s leaf seam: `LeafBlock58`'s else arm, kind `0`. -/
  c58Else : ∀ (C : WalkCarry G) (s : State) {x : BitVec 8} (ch : HcontHeadChain G C s x),
    HcontSeamRow G s (HeadC₄₁₃ ch.Cm) (HeadS413 ch.sm x) (BitVec.ofNat 32 0)
  /-- The positive-depth opener's route row: the merge's segment and endpoint, or the
  refusal's witness, at the class's own state. -/
  deep : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1 →
    C.sp ≠ 0 → HcontDeepRow G C s
  /-- **The whitespace skip's class**, at the class's own continuing head: the stop `k`, the
  per-index run and the stop's place above the entry's position.  Its guard is the payload's
  own one-byte class — `HcontDefaultRow.hclass` at `.wsByte`, i.e.
  `wsStop G (r.v.toNat - 1)` — so the group is stated where the run class's document byte is
  whitespace and nowhere else.  Its consumer is `hcontRunBody_of_skip`
  (`JsonStage2WalkDispatchRunRow`), which reads `k` and the run and derives the stop's place
  in the entry from them and the one-byte class (`cont_heicd`). -/
  runSkip : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → (r : HcontDefaultRow G C s) → wsStop G (r.v.toNat - 1) →
    HcontRunSkip G C s r
  /-- **The run's tail rows**, at the check state the class's prefix builds and the byte's
  leaf: the landing's byte and its three reads, the scan's traversal `hround`/`hbyte` and the
  record the scalar call appends.

  **The body is an argument**, because its `k` is the skip's: the case supplies it from
  `hcontRunBody_of_skip` and this group states the rows at it, so no second `k` enters the
  payload.  The prefix enters as the class's own endpoint `q5` and its invariant, and the
  memory tie `q5.mem = s.mem` is what makes the landing's reads the head state's — the
  default arm's prefix binds registers only.  Its consumer is `hcontRunRow_of_rows`. -/
  runTail : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → (r : HcontDefaultRow G C s) → wsStop G (r.v.toNat - 1) →
    (q5 : State) → WalkInv G (HeadAC₄ C) q5 → q5.mem = s.mem →
    (leaf : HcontRunLeaf G C) →
    (b : HcontRunBody G C (contRunCheck G C q5 (hlastIncV C) (hlastNepV G) G.ep r.v
      (contIx G C) (contB35 G r.v))) →
    HcontRunTail G C s r q5 leaf b
  /-- **The run class's arm, from a row**: the row joined to `RunFacts` at the class's
  prefix, with the byte's own leaf below `if.else387.i` as the arm's span.  The row is
  `hcontRunRow_of_rows`' at the class's prefix, `runSkip`'s stop and `runTail`'s rows. -/
  run : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → (row : HcontRunRow G C s) → ∀ {nS : Nat},
    Seg (stage2Calls stage2SubCalls) G (ContSeamC C) row.seamS (ContTailStartC C)
      row.tailS nS → nS ≤ 5 →
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s)
  /-- The seam's rows, at the run class's seams: the `if.else405.i` edge's refusal group
  (`scanRefuse`) and the four emit groups.  The kind literal each field fixes is part of
  the memory the first call reads, so the edge decides which field a leaf can read
  (`JsonStage2WalkDispatchRunRow`'s table).  Every field is inhabited at its leaf. -/
  seam : HcontSeamAbi G
  /-- **The kind-`0` refusal route, as a segment.**  From a head state whose byte is on
  `if.else405.i`'s edge to the refusal copy: `if.then413.i`'s value-position call,
  `if.then425.i`'s scalar call (answer `0`), `if.then432.i`, the slow scan
  (`cond.end.i96` / `land.rhs.i103` ⟲ `while.body.i104`), `while.end.i`, `if.end.i97`,
  `if.else.i`, `NodeBlock83`'s pivots, `if.else43.i`'s refusal store and `cleanup474.i`
  into `if.then`.

  **The scan's interior is named, not assumed.**  Its stop is the first position at or after
  the entry's start whose byte is whitespace (`9`, `10`, `13`, `32`) or the token's bound
  (`%cond.i`, written by `cond.end.i96`), and the loop's cell `%40` is the read that decides
  it.  A token may carry whitespace inside — a string's interior is not whitespace-free —
  and that is the case the route states as its *stop*: the scan halts there and the walk
  continues from `while.end.i` exactly as it does at the bound, so the arm needs no
  "the interior is non-whitespace" premise for the token.

  The row is the arm's premise, as `twoEntry`'s segment is; every link it names is proved in
  `JsonStage2Walk*` (`if_then413_i`, `if_then425_i_refuse`, `if_then432_i`, `land_rhs_i103`,
  `while_end_i`, `if_end_i97`, `if_else_i`, `NodeBlock83`, `LeafBlock75`/`77`/`79`,
  `if_else43_i`, `cleanup474_i`). -/
  refuseSeg : ∀ (C : WalkCarry G) (s : State) (x : BitVec 8),
    WalkInv G C s → C.block = walkLoopHead → C.k + 1 < G.nep →
    evalOperand s (.reg "%8") = some (.int 8 x) →
    (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 →
    evalICmp .eq x (BitVec.ofNat 8 102) = 0 →
    evalICmp .eq x (BitVec.ofNat 8 110) = 0 →
    evalICmp .eq x (BitVec.ofNat 8 116) = 0 →
    ∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p ∧
      Cd.block = "if.then" ∧
      (∃ k, k ≤ G.n ∧ readBytes sd.mem (Cd.stage.e + 8) 8 = some (wordBytes 8 k)) ∧
      Cd.eoff ≤ G.n ∧
      p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
        stage2ByteAllowance * (G.n - entryPos G C.k)

/-- **The kind-`0` edge's arm, from the class row.**  The refusal route is the row's
(`refuseSeg`), and the answer `0` and the record the scalar call wrote are
`HcontSeamAbi.scanRefuse`'s — `s2ScalarValue_refused` derives them from the zero kind, so
nothing here supplies an answer.  The byte facts are the head class's: the tag bit clear
and the byte outside the three literal pivots. -/
theorem hcontArm_badToken_of_row {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hc : HcontClassRows G) (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep) {x : BitVec 8}
    (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0)
    (hne110 : evalICmp .eq x (BitVec.ofNat 8 110) = 0)
    (hne116 : evalICmp .eq x (BitVec.ofNat 8 116) = 0) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  obtain ⟨Cd, sd, p, seg, hblk, hword, herr, hprice⟩ :=
    hc.refuseSeg C s x hInv hblock hk h8 hbit hne102 hne110 hne116
  exact ⟨HcontArm.badToken h8 hbit hne102 hne110 hne116 Cd sd p seg hblk hword herr
    hprice⟩

/-- **The continuing class rows hold what the payload holds.**  The default-value class's
document row is `defaultLane`'s, so a payload with the default row and the seam's calls
already carries it: this is the group's producer from the payload's own fields, and it says
the class the table marks *document* costs no new supply. -/
noncomputable def hcontClassRows_cleanup_of_payload {m0 : Mem} {G : WalkGeom m0}
    (hp : HcontPayload G) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hb : HcontByteRoute (cont35 (contB35 G ((hp.lane.defaultLane C s hInv hblock hk).v)))) :
    HcontCleanupDoc G C s :=
  hcontCleanupDoc_of_lane hk (hp.lane.defaultLane C s hInv hblock hk) hb

/-! ### The last entry's last byte, with its seam

`HlastTailLane` (`JsonStage2WalkDispatchSupply`) is the last byte's class; the payload
carries it as `lane.tail`.  The last level's seam is the **sum** `HlastSeam`
(`JsonStage2WalkDispatchSeams`): the value-position answer's two arms crossed with the
kind literal.  At `%8 ∈ {126, 127}` the literal is `if.else405.i`'s `0` and the three-call
group does not exist (`hcontSeamCalls_no_kind_zero`), so the class's rows are
`HlastSeam.answerOneRefuse`'s — the two leading calls and the derived refusal answer and
record — with `HlastSeam.answerZero` naming the other answer.  The producer is
`JsonStage2WalkDispatchHlastSupply`'s. -/

/-- **The last entry's document row**: the last byte's route, one group.  It is
`HlastTailLane`'s content, which the payload's `lane.tail` states at the high-byte route's
two conditions. -/
abbrev HlastClassDoc {m0 : Mem} (G : WalkGeom m0) : Type :=
  ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    ¬ (C.k + 1 < G.nep) →
    evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0 →
    evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0 → HlastTailLane G

/-- **The last entry's class rows**: the last byte's document row and the last level's
seam, at the route the document's byte selects. -/
structure HlastClassRows {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- The last byte's class (`126`/`127` at the exhausted count). -/
  tail : HlastClassDoc G
  /-- **The last level's seam**, at the byte route's tail: `HlastSeam`'s sum.  The literal
  the seam's store writes is the byte's class, so the class's `0` takes
  `HlastSeam.answerOneRefuse` and `s2_value_pos`'s own `0` answer takes
  `HlastSeam.answerZero`; a nonzero literal takes the emit arm.  The state is
  `hlastTailByte … hb` (the routed tail, whose memory differs from `hlastTail`'s at the
  token record), so this is not `HcontSeamAbi.last`'s instance — that field is stated at
  `hlastTail`, and the producer here is `hlastSeamRefusal_of_stage` /
  `hlastSeamZero_of_call` (`JsonStage2WalkDispatchHlastSupply`). -/
  seam : ∀ (C : WalkCarry G) (s : State) (x : BitVec 8) (inc nep : BitVec 64)
    (v : Nat) (ix : BitVec 64) (b35 : UInt8)
    (hb : HcontByteRoute (head35 b35)),
    HlastSeam G (TailStartC C) (hlastTailByte C s x inc nep v ix b35 hb)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_badToken_of_row

#print axioms LeanLLVM.Refinement.WalkScope.hcontCleanupDoc_of_lane
#print axioms LeanLLVM.Refinement.WalkScope.hcontClassRows_cleanup_of_payload
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_run_of_row

end WalkScope
end LeanLLVM.Refinement
