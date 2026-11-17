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
document (read at the state's own memory) or about a call's argument list.  It holds no
`WalkSegment`, no arm and no bundle, and it reads no clause of `WalkInv` as a premise of a
group beyond the head state the row is stated at.

## The classes whose row is a document fact alone

`HcontCleanupDoc` is the scan-free class's document row: the next entry's position word,
its read at the head's own memory, the bound's compare and the byte before the entry's end
with its three pivot bits.  It is *produced* for free from the payload's `defaultLane` row
(`hcontCleanupDoc_of_lane`): the two documents' rows are the same document's, and the only
work is the head chain's own two rewrites — the increment's word (`cont_inc_toNat`) and the
index's spelling (`contIx` is `BitVec.ofNat 64 (entryPos G C.k)` by definition).  So the
class the table marks *document* is reached by the row already carried, and the arm's
producer takes it beside the tail.

`HcontArm.cleanup` is then built at that row and the tail's three calls'
(`hcontArm_cleanup_of_doc`, through `hcontArm_cleanup_of_staging`).  The tail itself is
`emptyTailSeg_of_calls`'s, whose remaining input is the tail-start state's invariant
(`hInvT`) — a `WalkInv` at a state further along the walk, which no document row and no
clause of the head state's invariant supplies.  It is not a row either: it is the head
chain's own `inv'`, and `JsonStage2WalkDispatchSeamRows`'s `hcontSpan17_of_doc` derives the
chain from the document row alone (`contTailStartInv_of_doc`), so the class's arm is
`hcontArm_cleanup_of_rows` — the row, the lane's root word and the seam's three call rows,
with the seam's cells and the root slot's word produced beside them.
`hcontArm_cleanup_of_calls` states the same list at the cells explicitly, so the seam is
named once.

## The groups this module states

* `HcontCleanupDoc` — the scan-free class's document row, produced from `defaultLane`;
* `HcontWsDoc` — the run class's document row: the stop and its per-index facts, the byte
  before the entry's end and the seam's own reads, at the check state's numbers and at the
  three calls' answers.  Its fields are `HcontFacts`'s document conjuncts and its traversal
  group, which is the table's `.ws` row;
* `HcontRunRow` — the same rows as `HcontRunRows` (`JsonStage2WalkDispatchSeams`), which is
  already the segment-free shape, at the seam's calls;
* `HlastTailDoc` — the last entry's last byte's class with its three calls' argument lists,
  which is `HlastTailLane` beside `HlastHighByteAbi` (`JsonStage2WalkDispatchSupply`).

The payloads that carry them are `HcontClassRows` and `HlastClassRows`, and their groups
are the ones the two bundle theorems consume.

## What the groups do not carry

Every group here is a row: a document read, a call's argument list, a set of class bits.
None carries a `WalkSegment`, an arm, or a `WalkInv`.  The one input a class's *arm* needs
beside its rows is the invariant at the seam state the tail starts from — `hInvT` in
`hcontTail_of_calls`/`hcontScanTail_at`, `hInvS` in `scContTail_of_calls`
(`JsonStage2WalkDispatchSegments`).  That state is further along the walk than the head, so
its invariant is not a consequence of `WalkInv` at the head alone: the seam's block, its
extended environment and the token record its step writes are all new.  It is a head
chain's `inv'` rather than a row, and each of the three (the high-byte route's
`ContTailStartC`, the scalar route's `scSeamS`, the last entry's `TailStartC`) is produced
in `JsonStage2WalkHcontSeamInv` (`contTailStartInv_of_cleanup`, `scSeamInv_of_scalar`,
`hlastTailInv_of_facts`) — so a class's arm is `rows + the seam's chain`, and the seam
between the two is named once per class here rather than hidden in a row.

The positive-depth string opener is the same kind of seam, and it is closed:
`HcontClass.stringOpener` is the byte test alone and `HcontArm.twoEntry` takes
`C.sp = 0`, so at positive depth `land.lhs.true.i`'s depth test and the marker
bytes at `%sp - 1` select `if.end245.i`'s merge or `if.then249.i`'s refusal.
Those two states are `HcontArm.stringOpenAboveZeroMerge` and
`.stringOpenAboveZeroRefuse` (`JsonStage2WalkDispatchHcontStringDeep`), and each
arm is the class's row plus the chain it carries — the merge's counted segment
to `cleanup478.i`, the refusal's `WalkRefuseAt` — so the class has an arm at both
depths and this module owes it no further row.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchSupply
import LeanLLVM.Refinement.JsonStage2WalkDispatchSeams
import LeanLLVM.Refinement.JsonStage2WalkDispatchDefaultLane

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The scan-free class's document row -/

/-- **The scan-free class's document row**: the next entry's position word and the read at
the head's own memory, the bound's compare against this entry's index, and the byte before
the entry's end with its three scan-free pivot bits.  The same document fact as
`HcontDefaultRow` (`JsonStage2WalkDispatchSupply`), at the two spellings the producers read:
the word at `contAS₅`'s memory and `%inc.i`'s own value, the compare against the index term
the lookup carries. -/
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
  /-- The byte before the entry's end is above `13` (`\r`). -/
  hb13 : evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 13) = 0
  /-- It is below `32`, the whitespace range's upper bound. -/
  hb32 : evalICmp .slt (cont35 (contB35 G v)) (BitVec.ofNat 8 32) = 1
  /-- It is not `13`: the three bits are the scan-free class's own. -/
  hbne13 : evalICmp .eq (cont35 (contB35 G v)) (BitVec.ofNat 8 13) = 0

/-- **The scan-free class's document row, from the payload's default row.**  The payload's
`lane.defaultLane` states the same document at the head state's memory and the header's
increment; the producers read it at `cond.true345.i`'s memory and `%inc.i`'s word.  The
memory is the state's (every state between the head and the check binds registers only),
the word's value is `cont_inc_toNat`'s, and the index is `contIx`'s own spelling. -/
noncomputable def hcontCleanupDoc_of_lane {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hk : C.k + 1 < G.nep) (hLane : HcontLane G) : HcontCleanupDoc G C s := by
  obtain ⟨v, hread0, _hv1, hvle, hugt0, hb13, hb32, hbne13⟩ :=
    hLane.defaultLane C s hInv hblock hk
  have hmem : (contAS₅ s (hlastByte G C) (hlastIncV C) (hlastNepV G)).mem = s.mem := rfl
  refine ⟨v, ?_, hvle, ?_, hb13, hb32, hbne13⟩
  · rw [hmem, cont_inc_toNat G C hk]
    exact hread0
  · exact hugt0

/-! ### The scan-free class's arm, at that row and the tail -/

/-- **The scan-free continuing arm, from its document row and its tail.**  The row is
`HcontCleanupDoc`'s and the tail is `emptyTailSeg_of_calls`'s at the class's own seam; the
class's bits are the payload's (`defaultValueHigh`'s two) and the staging producer is
`hcontArm_cleanup_of_staging`.  Nothing here names a memory the walk has not written: the
tail is the argument. -/
noncomputable def hcontArm_cleanup_of_doc {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (doc : HcontCleanupDoc G C s)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) {cA rdv xA : BitVec 32}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
      (contTailStart C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v (contIx G C)
        (contB35 G doc.v) (hlastByte G C) (hlastByte G C))
      (TailCarryEnd (ContTailStartC C) ev)
      (contCleanupEnd C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v (contIx G C)
        (contB35 G doc.v) (hlastByte G C) (hlastByte G C) r₁ r₂ r₃ cA rdv xA) 3) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  hcontArm_cleanup_of_staging G C s hInv hk hlt125 hne125 doc.hread doc.hspan doc.hugt
    doc.hb13 doc.hb32 doc.hbne13 r₁ r₂ r₃ ev hTail

/-! ### The run class's document row

The run class's row is the whitespace stop's: the skip runs to `k`, the token's end is `k`,
and the copy call's test `k < v` is true, so the extra-token scan is entered.  The rows are
the document's (the stop and its per-index facts, the byte before the entry's end, the
entry's span) and the seam's reads at the three answers.  `HcontRunRows`
(`JsonStage2WalkDispatchSeams`) is this row's shape already: it is the bundle minus its
tail, so this group is its name for the payload's own vocabulary. -/

/-- **The run class's document row**: the check state's cells, the whitespace stop with its
per-index facts, the entry's span, the landing's byte and its reads, and the traversal's
round, guard and byte totality — at the seam's three answers.  A `∀`-field per class is the
payload's shape, so this is the row and not a bundle: `hTail` is absent by construction. -/
abbrev HcontRunRow {m0 : Mem} (G : WalkGeom m0) : Type :=
  ∀ (C : WalkCarry G) (sl : State) (b35 : UInt8) (ix : BitVec 64) (v : BitVec 32)
    (k : Nat) (x1 : BitVec 8)
    (calls : HcontSeamCalls G (ContTailStartC C)
      (contWsTailStart C (wsSlAt G sl b35 ix v k) k x1 x1))
    (ev : EventRecord),
    HcontRunRows G C sl b35 ix v k x1 calls.r₁ calls.r₂ calls.r₃ ev calls.cA calls.rdv
      calls.xA

/-- **The plain-value route's three calls at its own seam**: the scalar class's row, which
is `HcontSeamCalls` at `scSeamS` — the state `JsonStage2WalkHcontScalar` names and
`scContTail_of_calls` (`JsonStage2WalkDispatchSegments`) reads its invariant at. -/
abbrev HcontScalarRow {m0 : Mem} (G : WalkGeom m0) : Type :=
  ∀ (C : WalkCarry G) (s : State) (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat)
    (v : BitVec 32) (ix : BitVec 64) (b35 : UInt8),
    HcontSeamCalls G (HeadC₄₁₃ (ContAC₇ C)) (scSeamS C s x inc nep ep v ix b35)

/-- **The default arm's scan-free classes' three calls**: one group at the letters route's
seam, which is `LetS413` at the head chain's endpoint `if.else387.i`.  `fLetter` reads the
same seam from `FC₄₁₃`'s state, and `classC` reads it after its byte's own span. -/
abbrev HcontLettersRow {m0 : Mem} (G : WalkGeom m0) : Type :=
  ∀ {Cm : WalkCarry G} {sm : State} (x : BitVec 8),
    HcontSeamCalls G (HeadC₄₁₃ (LetC₄₀₅ Cm)) (LetS413 sm x)

/-! ### The payload's per-class groups -/

/-- **The continuing payload's class rows**: the document rows the residual table names
beside `HcontPayload`'s, one group per class.  `cleanup` is produced from the payload's own
`defaultLane` (`hcontCleanupDoc_of_lane`); `run` is the whitespace stop's row; the seam's
three calls are `HcontSeamAbi`'s, one instance per seam the classes read. -/
structure HcontClassRows {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- The scan-free class's document row (`126`/`127` at a continuing head). -/
  cleanup : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → HcontCleanupDoc G C s
  /-- The run class's document row, at the seam's own calls. -/
  run : HcontRunRow G
  /-- The plain-value class's three calls at its own seam. -/
  scalar : HcontScalarRow G
  /-- The default arm's scan-free classes' three calls at the letters route's seam. -/
  letters : HcontLettersRow G
  /-- The seam's three calls, at the run class's seam and the last entry's. -/
  seam : HcontSeamAbi G

/-- **The continuing class rows hold what the payload holds.**  The scan-free class's
document row is `defaultLane`'s, so a payload with the default row and the seam's calls
already carries it: this is the group's producer from the payload's own fields, and it says
the class the table marks *document* costs no new supply. -/
noncomputable def hcontClassRows_cleanup_of_payload {m0 : Mem} {G : WalkGeom m0}
    (hp : HcontPayload G) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep) :
    HcontCleanupDoc G C s :=
  hcontCleanupDoc_of_lane hInv hblock hk hp.lane

/-! ### The last entry's last byte, with its three calls

`HlastTailLane` (`JsonStage2WalkDispatchSupply`) is the last byte's class and
`HlastHighByteAbi` is the three calls at its argument lists; the payload already carries
both.  What the last level's remaining classes read is the same pair at the last entry's
seam — the `.scalar` route's three calls there — so the group below names the seam's calls
at the last entry's tail start, which is `HcontSeamAbi.last`'s instance. -/

/-- **The last entry's document row**: the last byte's class, one group.  It is
`HlastTailLane`'s content, which the payload's `lane.tail` states at the high-byte route's
two conditions. -/
abbrev HlastClassDoc {m0 : Mem} (G : WalkGeom m0) : Type :=
  ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    ¬ (C.k + 1 < G.nep) →
    evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0 →
    evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0 → HlastTailLane G

/-- **The last entry's class rows**: the last byte's document row and the seam's three
calls at the last entry's tail start. -/
structure HlastClassRows {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- The last byte's class (`126`/`127` at the exhausted count). -/
  tail : HlastClassDoc G
  /-- The seam's three calls at the last entry's tail start, for the `.scalar` route and
  the `.run` class beside it. -/
  seam : ∀ (C : WalkCarry G) (s : State) (x : BitVec 8) (inc nep : BitVec 64)
    (v : Nat) (ix : BitVec 64) (b35 : UInt8),
    HcontSeamCalls G (TailStartC C) (hlastTail C s x inc nep v ix b35)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontCleanupDoc_of_lane
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_cleanup_of_doc
#print axioms LeanLLVM.Refinement.WalkScope.hcontClassRows_cleanup_of_payload

end WalkScope
end LeanLLVM.Refinement
