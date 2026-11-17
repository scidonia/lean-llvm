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
`scContTail_of_calls` (`JsonStage2WalkDispatchSegments`).  That state is further along the
walk than the head, so its invariant is not a consequence of `WalkInv` at the head alone:
the seam's block, its extended environment and the token record its step writes are all
new.  It is a head chain's `inv'` rather than a row, and each of the three (the high-byte
route's `ContTailStartC`, the scalar route's `scSeamS`, the last entry's `TailStartC`) is
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
endpoint, the check state's rows (`HcontRunRows`), the run's body there and the seam's state
group (`HcontWsSeam`).  `hcontRunFacts_of_seam` (`JsonStage2WalkDispatchSeams`) joins the
last two into `HcontRunFacts` — its tail is `hcontScanTail_at`'s at the rows' own stop — and
`runFacts_of_defaultClass` places that bundle after the class's prefix, so the whole
`RunFacts` follows from the row.  The one segment the arm still takes beside the row is the
byte's own leaf below `if.else387.i` (the class-C span, `lettersSpan`, `fSpan`), and the
class case composes it from the head byte's bits rather than the row holding it.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchSupply
import LeanLLVM.Refinement.JsonStage2WalkDispatchSeams
import LeanLLVM.Refinement.JsonStage2WalkDispatchDefaultLane
import LeanLLVM.Refinement.JsonStage2WalkDispatchRunHead

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
the word's value is `cont_inc_toNat`'s, and the index is `contIx`'s own spelling.  This is
the class's own row: it takes the row and the scan-free disjunct, so it is stated only at
the states whose byte the class names. -/
noncomputable def hcontCleanupDoc_of_lane {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (hk : C.k + 1 < G.nep) (r : HcontDefaultRow G C s)
    (hf : HcontScanFree G r.v) :
    HcontCleanupDoc G C s := by
  obtain ⟨v, hread0, _hv1, hvle, hugt0, _hclass⟩ := r
  obtain ⟨hb13, hb32, hbne13⟩ := hf
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
    (.scanFree doc.hb13 doc.hb32 doc.hbne13) r₁ r₂ r₃ ev hTail

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
  /-- The record the tail's scalar call appends. -/
  ev : EventRecord
  /-- The seam's three calls, at the tail's start. -/
  calls : HcontSeamCalls G (ContTailStartC C)
    (contRunTailS G C q5 inc nep ep v ix b35 b.b35 b.ix b.v b.k b.x1)
  /-- The check state's rows: the cells, the landing's reads and the traversal. -/
  rows : HcontRunRows G C (contRunCheck G C q5 inc nep ep v ix b35)
    b.b35 b.ix b.v b.k b.x1 calls.r₁ calls.r₂ calls.r₃ ev calls.cA calls.rdv calls.xA
  /-- The seam's state group: its invariant, its cells and the root word across the kind
  store. -/
  seam : HcontWsSeam G C (contRunCheck G C q5 inc nep ep v ix b35) b calls

/-- The run class's seam state, from a row's own fields. -/
abbrev HcontRunRow.seamS {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (row : HcontRunRow G C s) : State :=
  contRunSeamS G C row.q5 row.inc row.nep row.ep row.v row.ix row.b35
    row.b.b35 row.b.ix row.b.v row.b.k row.b.x1

/-- The tail's start, from a row's own fields. -/
abbrev HcontRunRow.tailS {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (row : HcontRunRow G C s) : State :=
  contRunTailS G C row.q5 row.inc row.nep row.ep row.v row.ix row.b35
    row.b.b35 row.b.ix row.b.v row.b.k row.b.x1

/-- **The run class's arm, from its row.**  The bundle is `hcontRunFacts_of_seam`'s at the
check state, placed after the class's prefix and the shared four by
`runFacts_of_defaultClass`; the byte's own span below `if.else387.i` is the one segment the
arm takes beside the row, and the class case composes it from the head byte's bits. -/
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
      row.b row.ev row.calls row.rows row.seam)
    hk hSpan hnS)

/-! ### The payload's per-class groups -/

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
* `scalar` — the plain-value class's seam row, at the seam `scContTail_of_calls` reads
  (`scSeamS`, whose cells are the class's own peels);
* `letters`, `fLetter` — the default arm's scan-free classes' seam rows, at the seams
  `LetS413` and `FS413` that their head chains reach;
* `c56True`, `c56Else`, `c58True`, `c58Else` — the class-C span's four leaves' seam rows,
  at the four named seam states (`ClsS413T`/`ClsS413F`/`ClsS58T`/`HeadS413`);
* `deep` — the positive-depth opener's route row (`HcontDeepRow`): the merge's counted
  segment and endpoint, or the refusal's witness, named as the arm's own segment;
* `run` — the run class's row (`HcontRunRow`) and the byte's own span below
  `if.else387.i`, which the class case composes from the head byte's bits;
* `seam` — the two seams `HcontSeamAbi` names.

The run class's field takes the byte's leaf as an argument rather than holding it: the
segment belongs to the head byte's class, and the case's branch composes it
(`hcontArm_run_of_class`). -/
structure HcontClassRows {m0 : Mem} (G : WalkGeom m0) : Type where
  /-- The scan-free class's document row (`126`/`127` at a continuing head), at the
  payload's default row and the scan-free disjunct. -/
  cleanup : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → (r : HcontDefaultRow G C s) → HcontScanFree G r.v →
    HcontCleanupDoc G C s
  /-- The scan-free class's seam row: the three callee rows at `contTailStartOfDoc`, whose
  kind literal is `if.else405.i`'s `0`.  Its root slot's word is the state's own, so the
  arm is total over the slot's values (`hcontArm_cleanup_of_rows` takes `rdv0` freely). -/
  cleanupRow : ∀ (C : WalkCarry G) (s : State) (doc : HcontCleanupDoc G C s),
    HcontSeamRow G s (ContTailStartC C)
      (contTailStart C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep doc.v
        (contIx G C) (contB35 G doc.v) (hlastByte G C) (hlastByte G C))
      (BitVec.ofNat 32 0)
  /-- The plain-value class's seam row, at the class's own prefix: the producer's remaining
  argument, with the prefix's values fixing the seam state. -/
  scalar : ∀ (C : WalkCarry G) (s : State) (pre : HcontScalarPrefix G C s),
    HcontSeamRow G s (HeadC₄₁₃ (ContAC₇ C))
      (scSeamS C s pre.x pre.inc pre.nep pre.ep pre.v pre.ix pre.b35)
      (BitVec.ofNat 32 7)
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
  /-- **The run class's row**: the class's prefix and check state with the seam's group,
  and the byte's own leaf below `if.else387.i` as the arm's span. -/
  run : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → (row : HcontRunRow G C s) → ∀ {nS : Nat},
    Seg (stage2Calls stage2SubCalls) G (ContSeamC C) row.seamS (ContTailStartC C)
      row.tailS nS → nS ≤ 5 →
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s)
  /-- The seam's three calls, at the run class's seam and the last entry's. -/
  seam : HcontSeamAbi G

/-- **The continuing class rows hold what the payload holds.**  The scan-free class's
document row is `defaultLane`'s, so a payload with the default row and the seam's calls
already carries it: this is the group's producer from the payload's own fields, and it says
the class the table marks *document* costs no new supply. -/
noncomputable def hcontClassRows_cleanup_of_payload {m0 : Mem} {G : WalkGeom m0}
    (hp : HcontPayload G) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hf : HcontScanFree G ((hp.lane.defaultLane C s hInv hblock hk).v)) :
    HcontCleanupDoc G C s :=
  hcontCleanupDoc_of_lane hk (hp.lane.defaultLane C s hInv hblock hk) hf

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
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_run_of_row

end WalkScope
end LeanLLVM.Refinement
