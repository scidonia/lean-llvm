/-
The no-event walk's completion, from the premises a dispatch supplies.

`JsonStage2NoEventWalkTraverse` proves the loop finishes from the seed's run to the
post-read head `NodeBlock5`, the head's premise there (`Stage2NoEventWalkHead`) and
one step per head visit; this module states the premises that step is written
against, produces them from the record's precondition and the staging, and turns
them into the walk's obligation.

**Two layers, because they answer different questions.**

* `Stage2NoEventWalkExit` and `Stage2NoEventWalkRows` are the dispatch's data: the
  terminal route's own evidence — the acceptance's three stores or the refusal
  family's registers — the prefix trace, the counts and the report, and the row that
  either closes a count-class cycle to the next head or takes a terminal route.  They
  are assumed, never proved here, exactly as the certified walk's class groups are:
  the terminal arms' own runs (`JsonStage2NoEventWalkTerminal`) are what a producer
  reads to fill them.
* `Stage2NoEventWalkPremises` is the `WalkPremises`-shaped statement the completion
  consumes: at every staging the record admits, a carry and a head state, the seed's
  conclusion at `EntryState`, the seed run to the head, the invariant and its read
  facts there, and the step.

`stage2NoEventWalkPremises_of_rows` builds the second from the first and the lane's
already-proved seed (`stage2NoEventWalkInv_seed`, `stage2NoEventWalkSeedRun`), so the
only data the dispatch still owes is the rows.  `stage2NoEventWalkObligation_of_premises`
derives both conjuncts of `Satisfies` — completion and the post at every behaviour —
and takes no post rule beside the premises: the flush and terminal branches carry the
boundary at their own outcomes, and `runFuel_outcome_unique` carries it to every
behaviour of the run.

**The gap is a parameter of the premises and the obligation, and the seed route is the
default model's.**  `stage2NoEventWalkSeedRun` is stated at an arbitrary selection; the
flush route is proved at `stage2NoEventCalls stage2GapRecover` (`JsonStage2NoEventWalk-
Segment`'s flush lemmas), which is the tree's model of `od_gap_recover` and the record's
own default.  So `stage2NoEventWalkPremises_of_rows` produces the premises at that
selection, while `stage2NoEventWalkObligation_of_premises` is stated at any selection a
premises statement names.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkTraverse
import LeanLLVM.Refinement.JsonStage2NoEventWalkSeed
import LeanLLVM.Refinement.JsonEventBridge

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### The dispatch's data

The terminal route's evidence is the three terminal arms' supply: the acceptance's
three-word reading at the route's post-block endpoint (`Stage2NoEventWalkAcceptAcc K' sT`
for the last entry's carry `K'`: `%tokens.8`, `%terms.8`, `%arena.10`), the parse
relation and the fold facts the acceptance's boundary needs (`Stage2NoEvent K.bs K'.arena
obs toks`, the count `K'.tok` and the sum `K'.terms`), the run equality to that endpoint
(`Stage2NoEventWalkRunTo`, no invariant there), the run to the return and its price at
the head's `K`, and the report at `K'`.  The row starts at a head state;
the evidence sits at the post-block `sT` the route's run reaches, where the stores are
visible and the in-block cells remain in the env.

`Stage2NoEventWalkAcceptAcc`'s names are the loop-exit merge's, not the head's:
`%tokens.8`, `%terms.8` and `%arena.10` are bound at `if.end545` (and `%idxprom.lcssa`
at its `scalar` arms), so the acceptance's reading belongs at the post-block endpoint
and cannot be a fact of `NodeBlock5`.  The head's carried counts are its own `phi` names
(`%tokens.0.ph1408`, `%terms.0.ph1407`, `%arena.0.ph1406`), which the invariant does not
state either; the step's producers read them.  The loop's `Stage2NoEventWalkAcc` is not
inhabitable at a head (F2), which is why the exit carries the three-word reading and the
refusal its own family's registers. -/

/-- **A run to a post-block endpoint.**  The counted segment's run equality
without `inv'`: `sT` is the route's **post-block** state, where the terminal
block's stores are visible and its in-block cells (the `errStore` offset phi, the
`%ei520.0.ph` phi, the `%err` read-back) remain in the env, but no invariant is
claimed there.  The plain `Segment` tie is not used: `inv'`'s `walkFrame` requires
silence at the four output words, and every terminal block writes them inside the
route. -/
def Stage2NoEventWalkRunTo (calls : Calls) (s : State) (sT : State) : Prop :=
  ∃ j, ∀ n, runFuel calls (j + n) stage2NoEventBody s =
    runFuel calls n stage2NoEventBody sT

/-- **The `%ei520.0.ph` phi's incoming operand**, per edge of the literal chain:
`%sub524` on the not-taken/other edges, one of the `0…4` immediates, or `%ln.0`
for `for.end.i` (the fixture `:1122-1131`).  Which edge the route takes is the
terminal lane's; this is the shape its evidence names. -/
inductive Stage2NoEventWalkEi520Incoming : Type
  /-- The not-taken/other edges: `%sub524`'s value. -/
  | sub524 (v : Nat)
  /-- One of the `0…4` immediates. -/
  | imm (i : Nat)
  /-- `%ln.0` for `for.end.i`. -/
  | ln (v : Nat)

/-- **The incoming operand's value.** -/
def Stage2NoEventWalkEi520Incoming.value : Stage2NoEventWalkEi520Incoming → Nat
  | .sub524 v => v
  | .imm i => i
  | .ln v => v

/-- **A refusal route's evidence at its own terminal state.**  The five refusal
shapes read different registers/words, so the evidence is route-indexed:

* **`zeroStore`**: the four output pointers, the route's own offset word `eoff`
  and its read-back at the refusal record (`readBytes s.mem K.err 8 = some
  (wordBytes 8 eoff)`), with `eoff ≤ K.n` and `eoff < 2^64`.  The per-entry
  sources are the entries' own index or `n` word (`if.then12`'s
  `%idxprom.lcssa1108`, `if.then38`'s `%idxprom.lcssa1110`,
  `if.then68`/`if.then105`/`if.then297`/`if.then321`/`if.then372`'s `%n`, and
  the rest's `%idxprom…`/`%conv…` values).
* **`errStore`** (`cleanup.thread`, `cleanup287.thread`): the offset source
  operand and word, the **in-block offset phi** at the post-block state
  (`%conv130.sink` or `%idxprom.lcssa1109.lcssa.sink`, whose cell remains in the
  env), and the `lifetime.end` **operand pointer** (`%outn` for
  `cleanup.thread`, `%outn205` for `cleanup287.thread`).  There is no
  `%lifetime.end` register: the callee is a void `callVoid` and binds nothing;
  the predecessors carry the zeros.
* **`gapElse`** (`if.else510`): the four output pointers, the `%off` slot, the
  `od_gap_recover` call's outcome `hrc`, its read-back `hv` at the refusal record,
  the call's frame `hGapFrame`, the token index `idx` (`%idxprom.lcssa`), and the
  addend-free `eoff = idx` with the bounds.
* **`gapNumber`** (`cleanup491.thread`): the same pointers/`%off`/`hrc`/`hv`/
  frame, `idx`, the `%ei` pointer (`K.next0 + 24`) and the error word's read in
  the route's memory (`readBytes hrc.mem (K.next0 + 24) 8 = some (wordBytes 8
  errOff)`; the helper writes only the record at `e`, so the alloca slot is
  untouched across the call), the addend `errOff` (`num_fast_el1`'s error
  offset), and `eoff = errOff + idx` with the bounds.
* **`gapLiteral`** (`if.then527`): the same pointers/`%off`/`hrc`/`hv`/frame,
  `idx`, the literal chain's `%ei520.0.ph` value `ei520` with its **provenance**
  (`Stage2NoEventWalkEi520Incoming`: `%sub524`, one of the `0…4` immediates, or
  `%ln.0`; **not always `0`**), and `eoff = ei520 + idx` with the bounds.

`%idxprom.lcssa` is its own value in each gap shape and is never equated with
`eoff`.  Each gap shape's `hGapFrame` is over
`stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
(stage2NoEventRunRegions … ++ [(K.next0, K.nextEnd − K.next0)])` — the pre-call
frame alone fails at the post-block `sT`, where the stores are visible
(`stage2NoEventBoundary_refusal`'s shape).  `%ei520.0.ph` is a field of
`gapLiteral` only.  Each constructor's fields are exactly the registers/words its
step reads.  The per-route construction — which block reaches which shape — is the
terminal tier's. -/
inductive Stage2NoEventWalkRefusalEvidence (K : Stage2NoEventWalkCarry) (s : State) :
    Prop
  /-- The zero-store family: the three zero stores and the route's word at `*err`. -/
  | zeroStore (eoff : Nat) :
      lookupName s.env "%tokens_out" = some (.ptr K.tokensOut) →
      lookupName s.env "%values_out" = some (.ptr K.valuesOut) →
      lookupName s.env "%sum_out" = some (.ptr K.sumOut) →
      lookupName s.env "%err" = some (.ptr K.err) →
      readBytes s.mem K.err 8 = some (wordBytes 8 eoff) →
      eoff ≤ K.n →
      eoff < 2 ^ 64 →
      Stage2NoEventWalkRefusalEvidence K s
  /-- The err-store family: the in-block offset phi and the `lifetime.end`
  operand. -/
  | errStore (w : Nat) (op : Operand) (p : Nat) (src : String) :
      evalOperand s op = some (.int 64 (BitVec.ofNat 64 w)) →
      w < 2 ^ 64 →
      (src = "%conv130.sink" ∨ src = "%idxprom.lcssa1109.lcssa.sink") →
      lookupName s.env src = some (.int 64 (BitVec.ofNat 64 w)) →
      (lookupName s.env "%outn" = some (.ptr p) ∨
        lookupName s.env "%outn205" = some (.ptr p)) →
      lookupName s.env "%err" = some (.ptr K.err) →
      Stage2NoEventWalkRefusalEvidence K s
  /-- The gap family's addend-free shape (`if.else510`): `eoff = idx`. -/
  | gapElse (hrc : CallOutcome) (eoff idx : Nat) :
      lookupName s.env "%tokens_out" = some (.ptr K.tokensOut) →
      lookupName s.env "%values_out" = some (.ptr K.valuesOut) →
      lookupName s.env "%sum_out" = some (.ptr K.sumOut) →
      lookupName s.env "%err" = some (.ptr K.err) →
      lookupName s.env "%off" = some (.ptr (K.e + 8)) →
      lookupName s.env "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 idx)) →
      readBytes hrc.mem (K.e + 8) 8 = some (wordBytes 8 eoff) →
      UnchangedOutside s.mem hrc.mem
        (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
          (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
            [(K.next0, K.nextEnd - K.next0)])) →
      eoff = idx →
      eoff ≤ K.n →
      eoff < 2 ^ 64 →
      Stage2NoEventWalkRefusalEvidence K s
  /-- The gap family's number shape (`cleanup491.thread`): `eoff = errOff + idx`,
  with the `%ei` pointer and the error word's read. -/
  | gapNumber (hrc : CallOutcome) (eoff idx errOff : Nat) :
      lookupName s.env "%tokens_out" = some (.ptr K.tokensOut) →
      lookupName s.env "%values_out" = some (.ptr K.valuesOut) →
      lookupName s.env "%sum_out" = some (.ptr K.sumOut) →
      lookupName s.env "%err" = some (.ptr K.err) →
      lookupName s.env "%off" = some (.ptr (K.e + 8)) →
      lookupName s.env "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 idx)) →
      lookupName s.env "%ei" = some (.ptr (K.next0 + 24)) →
      readBytes hrc.mem (K.next0 + 24) 8 = some (wordBytes 8 errOff) →
      readBytes hrc.mem (K.e + 8) 8 = some (wordBytes 8 eoff) →
      UnchangedOutside s.mem hrc.mem
        (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
          (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
            [(K.next0, K.nextEnd - K.next0)])) →
      eoff = errOff + idx →
      eoff ≤ K.n →
      eoff < 2 ^ 64 →
      Stage2NoEventWalkRefusalEvidence K s
  /-- The gap family's literal shape (`if.then527`): `eoff = ei520 + idx`, with
  the `%ei520.0.ph` phi's provenance. -/
  | gapLiteral (hrc : CallOutcome) (eoff idx ei520 : Nat)
      (src : Stage2NoEventWalkEi520Incoming) :
      lookupName s.env "%tokens_out" = some (.ptr K.tokensOut) →
      lookupName s.env "%values_out" = some (.ptr K.valuesOut) →
      lookupName s.env "%sum_out" = some (.ptr K.sumOut) →
      lookupName s.env "%err" = some (.ptr K.err) →
      lookupName s.env "%off" = some (.ptr (K.e + 8)) →
      lookupName s.env "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 idx)) →
      lookupName s.env "%ei520.0.ph" = some (.int 64 (BitVec.ofNat 64 ei520)) →
      src.value = ei520 →
      readBytes hrc.mem (K.e + 8) 8 = some (wordBytes 8 eoff) →
      UnchangedOutside s.mem hrc.mem
        (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
          (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
            [(K.next0, K.nextEnd - K.next0)])) →
      eoff = ei520 + idx →
      eoff ≤ K.n →
      eoff < 2 ^ 64 →
      Stage2NoEventWalkRefusalEvidence K s

/-- **An acceptance's facts, at the parse's trace.**  The record trace the parse's
tokens determine for this document and arena, the relation at the parser's
tokens, the identity `obs = consumeRecords`, the record widths, the used-extent
clause on the reported events, and the parser's token tie.  The trace, its
relation, its widths and its extent clause are **derived from the parse**:
`JsonStage2NoEventWalkRecordSupplyOfParse` produces them at every accepting parse
(`stage2NoEventWalkRecordsSupply_of_parse`), and
`stage2NoEventWalkReferenceFacts_iff_supply` shows the facts are exactly that
supply plus `obs` and `toks`.  What the relation does not supply — as
`stage2NoEvent_str_len_free` shows — is the read-back: `obs` is not a function of
`(bs, arena, toks)`, so the facts may not be quantified over derivations.
Stated at the acceptance's own `(bs, arena, obs, toks, t)`, so the walk's witnesses
select it.

The declaration lives here, beside the exit that carries it, because the exit's
accept constructor names it and `JsonStage2NoEventWalkReference` imports this
module: the reference module's transfer chain and its row bundle read it from this
definition. -/
structure Stage2NoEventWalkReferenceFacts (bs arena : List UInt8)
    (obs : List ConsumerEvent) (toks : List Token) (t : Tape) : Type where
  /-- A record trace the parse's tokens determine (not necessarily the one a
  reference run emits).  **derived from the parse**. -/
  rs : List EventRecord
  /-- The record trace is the document's relation at the parser's tokens.
  **derived from the parse**. -/
  records : Stage2Records bs arena rs toks
  /-- The walk's report is the record trace read back by the consumer.
  **the reference's choice of read-back**. -/
  consume : obs = consumeRecords bs arena rs
  /-- Every record fits the field widths its bytes are written at.
  **derived from the parse**. -/
  bounded : ∀ r ∈ rs, r.Bounded
  /-- Every reported string's body lies inside the source it names.
  **derived from the parse**, at the read-back the acceptance names. -/
  within : ∀ e ∈ obs, e.BodiesWithin bs arena
  /-- The parser's tape carries exactly the tokens the relation is at.
  **derived from the parse** (definitional once `toks` is the tape's token list). -/
  tokens : t.tokens = toks

/-- **The reference parser refuses the document.**  **carried data**: the
deployment boundary's parse.  Every refusal shape is admitted — `parseBytes`
rejects with `.inputTooLong`, `.depthExceeded`, `.outOfCapacity` and `.invalid`
(`Parse.lean`), and a reference run that observes any of them must be able to
supply this; the verdict word is zero at all four (`Stage2NoEventWalkReferenceWord`
maps every `.error` to `0`). -/
def Stage2NoEventWalkParseRefusal (bs : List UInt8) : Prop :=
  ∃ e, parseBytes Limits.default (ByteString.literal bs) = .error e

/-- **An acceptance's reference data, as the producer consumes it.**  The tape,
the parse equality at it, the observations and the tokens the acceptance names,
the relation at them, the two count equations, and the facts at them.  The tape,
the parse and the trace are the parse's
(`JsonStage2NoEventWalkRecordSupplyOfParse`).  What the deployment supplies is the
reference's own data: the two count equations — the walk's counted-token and term
registers against the trace — and the read-back identity `obs = consumeRecords`
that places them at the observations.  They are not derived from `Stage2NoEvent`
(the read-back's `len` is free above the decoded slice, and
`countsTieDoc_terms_two_derivations` separates two arena-bound derivations' term
sums), so a producer is given them rather than proving them.  Indexed by the head's
and the acceptance's carries, so a producer takes it at the witnesses its route
reports. -/
def Stage2NoEventWalkReferenceAccept (K K' : Stage2NoEventWalkCarry) : Type :=
  Σ (t : Tape) (obs : List ConsumerEvent) (toks : List Token),
    (Stage2NoEvent K.bs K'.arena obs toks ∧ obs.length = K'.tok ∧
      K'.terms = (obs.map ConsumerEvent.terms).sum ∧
      parseBytes Limits.default (ByteString.literal K.bs) = .ok t) ×'
    Stage2NoEventWalkReferenceFacts K.bs K'.arena obs toks t

/-- **A refusal's reference data, as the producer consumes it.**  The observations
and tokens the head's trace names, the relation at them, the two count equations,
and the reference parser's verdict on the document.  **entirely carried data**:
the refusal's trace is a `Prop` that cannot supply the exit's `Type` fields, so the
observations, the tokens, the relation's witnesses, the two counts and the verdict
all come from the deployment boundary. -/
def Stage2NoEventWalkReferenceRefuse (K : Stage2NoEventWalkCarry) : Type :=
  Σ (obs : List ConsumerEvent) (toks : List Token),
    (Stage2NoEvent K.bs K.arena obs toks ∧ obs.length = K.tok ∧
      K.terms = (obs.map ConsumerEvent.terms).sum) ×'
    Stage2NoEventWalkParseRefusal K.bs

/-- **A terminal route's evidence at its post-block endpoint**, route-specific.  Both
constructors carry the run equality to the post-block endpoint `sT`
(`Stage2NoEventWalkRunTo`, no invariant there), the credit, the verdict, the
returned memory and the run, the prefix trace the walk has consumed, and the
walk's report at the returned memory.  The evidence is stated at `sT`, where the
terminal block's stores are visible and its in-block cells remain in the env.
The acceptance reads its three stores there; the refusal carries its own
family's registers.  The old single-`Acc` field is gone: `%idxprom.lcssa` is defined on the
number route only and the three count words on the value route only, so no one
accumulator is inhabitable at every route's terminal state.

The exit is **data**, not a proof: a terminal route's witnesses (`K'`, the report's
tokens and the parser's tape) are what a consumer of the walk theorem reads, so the
type lives in `Type`.  The acceptance carries the reference's facts at its own
witnesses (`Stage2NoEventWalkReferenceFacts`) — the parse's trace, the reference's
read-back and its counts — and the refusal carries the reference parser's verdict
on the head's document; the trace is the parse's, while the read-back, the counts
and the refusal's verdict are **carried data** the producer takes from the
deployment boundary, never invents. -/
inductive Stage2NoEventWalkExit (calls : Calls) (mem : Mem) (F : Nat)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) : Type
  /-- The accepted arm: verdict one, the last entry's carry `K'`, the three
  stores' reading at the post-block state, the trace (the head's prefix plus the
  last entry's event), and the boundary.  The head's `K` stays the index for the
  price and the boundary; the report's numbers are `K'`'s.  The parser's tape,
  the parse equality at it, and the reference run's facts at
  `(K.bs, K'.arena, obs, toks)` are the acceptance's carried data.  The equality
  is a field and not a hypothesis over the facts type: the facts' only tape
  field is `t.tokens = toks`, so a facts value re-indexes at any tape with the
  same token list and no statement about the open structure can pin the tape. -/
  | accept (K' : Stage2NoEventWalkCarry) (q : Nat) (m : Mem) (sT : State)
      (route : Stage2NoEventWalkRunTo calls s sT)
      (cost : q ≤ stage2NoEventWalkPotential K k + F)
      (run : runFuel calls (q + 2) stage2NoEventBody s =
        some (.ret (some (.int 64 1)) m))
      (htok : K.tok < K'.tok) (ha12 : K'.a12 = K.a12) (hn0 : K'.next0 = K.next0)
      (acc : Stage2NoEventWalkAcceptAcc K' sT)
      (obs : List ConsumerEvent) (toks : List Token)
      (rel : Stage2NoEvent K.bs K'.arena obs toks)
      (obsLen : obs.length = K'.tok)
      (termsEq : K'.terms = (obs.map ConsumerEvent.terms).sum)
      (report : Stage2NoEventRun K'.a12 mem m)
      (bound : stage2NoEventBoundary K'.a12 mem K'.next0 m (.int 64 1))
      (t : Tape)
      (parsed : parseBytes Limits.default (ByteString.literal K.bs) = .ok t)
      (facts : Stage2NoEventWalkReferenceFacts K.bs K'.arena obs toks t) :
      Stage2NoEventWalkExit calls mem F K k s
  /-- The refused arm: verdict zero, the route's own evidence, the walk's trace,
  the supplied relation witnesses, and the boundary at the refusal's memory.

  The trace is carried although it is a `Prop` — its content that the flat
  fields do not already give is the arena bound (`Stage2NoEventArenaBound`) —
  and the witnesses are supplied alongside it rather than read from it, because a
  `Prop` inductive's data cannot be eliminated into this `Type`.  Nothing ties
  the two witnesses to each other; the parser's verdict on the document is the
  refusal's carried data. -/
  | refuse (q : Nat) (m : Mem) (sT : State)
      (route : Stage2NoEventWalkRunTo calls s sT)
      (cost : q ≤ stage2NoEventWalkPotential K k + F)
      (run : runFuel calls (q + 2) stage2NoEventBody s =
        some (.ret (some (.int 64 0)) m))
      (ev : Stage2NoEventWalkRefusalEvidence K sT)
      (trace : Stage2NoEventWalkTrace K)
      (obs : List ConsumerEvent) (toks : List Token)
      (rel : Stage2NoEvent K.bs K.arena obs toks)
      (obsLen : obs.length = K.tok)
      (termsEq : K.terms = (obs.map ConsumerEvent.terms).sum)
      (report : Stage2NoEventRun K.a12 mem m)
      (bound : stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0))
      (refused : Stage2NoEventWalkParseRefusal K.bs) :
      Stage2NoEventWalkExit calls mem F K k s

/-- **The dispatch's row at a head**, as data: either the count class's
cycle-closing priced head segment to the next head — the segment carries the
target's `Head` and `Trace`, and the three static numbers do not move — or a
terminal route with its evidence.  Which side is taken is the entry's own class,
so the field is one value of this type and not a per-class table. -/
inductive Stage2NoEventWalkRow (calls : Calls) (mem : Mem) (F : Nat)
    (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) : Type
  /-- The count class's cycle-closing segment to the next head. -/
  | cont (K' : Stage2NoEventWalkCarry) (k' : Nat) (s' : State) (p : Nat)
      (seg : Stage2NoEventWalkHeadPricedSegment calls mem K k s K' k' s' p)
      (hnep : K'.nep = K.nep) (ha12 : K'.a12 = K.a12) (hn0 : K'.next0 = K.next0)
      (hlt : k < k') (hk'lt : k' < K.nep) :
      Stage2NoEventWalkRow calls mem F K k s
  /-- The terminal route, with its evidence. -/
  | terminal (exit : Stage2NoEventWalkExit calls mem F K k s) :
      Stage2NoEventWalkRow calls mem F K k s

/-- **The dispatch's rows at a head.**  From a head — the invariant, the
parameters, the index below the entry count and the head block's read values —
one row: the continuing class's priced segment or a terminal route. -/
structure Stage2NoEventWalkRows (calls : Calls) (mem : Mem) (F : Nat) where
  /-- The row at a head, given the walk's accumulated output evidence there: a
  continuing row's priced segment carries the target's trace, which is the
  source's stepped by the class's own event, so the producer needs the source
  trace.  The trace is not a field of `Stage2NoEventWalkHead`, which is a state
  fact about the head block's read. -/
  row : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State),
    Stage2NoEventWalkHead K mem k s →
    Stage2NoEventWalkTrace K →
    Stage2NoEventWalkRow calls mem F K k s

/-- **The step, from the row.**  The continuing side is the row's priced head
segment with its three static equalities (the target's `Head` and `Trace` ride in
the segment); the terminal side cases the route-specific exit, whose verdict and
boundary are its own. -/
theorem stage2NoEventWalkStep_of_rows {calls : Calls} {mem : Mem} {F : Nat}
    (h : Stage2NoEventWalkRows calls mem F) :
    Stage2NoEventWalkStep calls mem F := by
  intro K k s hhead htrace
  cases h.row K k s hhead htrace with
  | cont K' k' s' p seg hnep ha12 hn0 hlt hk'lt =>
      exact Or.inl ⟨K', k', s', p, seg, hnep, ha12, hn0, hlt, hk'lt⟩
  | terminal exit =>
      cases exit with
      | accept K' q m sT route cost run htok ha12 hn0 acc obs toks rel obsLen termsEq report bound _ _ =>
          exact Or.inr ⟨q, 1, m, cost, run, by rw [← ha12, ← hn0]; exact bound⟩
      | refuse q m sT route cost run ev _ obs toks rel obsLen termsEq report bound _ =>
          exact Or.inr ⟨q, 0, m, cost, run, bound⟩

/-! ### F1's row corollary

The state `JsonStage2NoEventWalkHead`'s F1 witness exhibits is outside the new
premise — the head's read is absent — and no row is inhabitable there either: a
continuing row would need an index strictly between zero and the entry count, and
a terminal row a return the undefined step never produces.  So the old statement,
a row at every state the invariant admits at `NodeBlock5`, is refutable. -/

/-- **No row at the `%3`-less state.** -/
theorem stage2NoEventWalkF1_notRow (calls : Calls) (F : Nat) :
    ¬ Nonempty (Stage2NoEventWalkRow calls stage2NoEventWalkF1Mem F
      stage2NoEventWalkF1K 0 stage2NoEventWalkF1S) := by
  rintro ⟨row⟩
  cases row with
  | cont K' k' s' p seg hnep ha12 hn0 hlt hk'lt =>
      have hk1 : stage2NoEventWalkF1K.nep = 1 := by decide
      omega
  | terminal exit =>
      cases exit with
      | accept K' q m sT route cost run htok ha12 hn0 acc obs toks rel obsLen termsEq report bound _ _ =>
          rw [show q + 2 = (q + 1) + 1 from by omega] at run
          rw [stage2NoEventWalkF1_noRet (stage2NoEventWalkF1_step calls) (q + 1)] at run
          cases run
      | refuse q m sT route cost run ev _ obs toks rel obsLen termsEq report bound _ =>
          rw [show q + 2 = (q + 1) + 1 from by omega] at run
          rw [stage2NoEventWalkF1_noRet (stage2NoEventWalkF1_step calls) (q + 1)] at run
          cases run

/-- **F1's `¬ Rows` corollary**: the pre-fix statement — a row at every state the
invariant admits at `NodeBlock5` with the index at zero and a nonempty entry
stream — is refutable by the witness above. -/
theorem stage2NoEventWalkF1_notRows (calls : Calls) (F : Nat) :
    ¬ (∀ (K : Stage2NoEventWalkCarry) (s : State),
        Stage2NoEventWalkInv K stage2NoEventWalkF1Mem s →
        s.pc = "NodeBlock5" →
        lookupName s.env "%k.0.ph1404" = some (.int 64 (BitVec.ofNat 64 0)) →
        0 < K.nep →
        Nonempty (Stage2NoEventWalkRow calls stage2NoEventWalkF1Mem F K 0 s)) := by
  intro h
  refine stage2NoEventWalkF1_notRow calls F ?_
  apply h stage2NoEventWalkF1K stage2NoEventWalkF1S stage2NoEventWalkF1_inv rfl ?_ ?_
  · show lookupName [("%k.0.ph1404", Value.int 64 (BitVec.ofNat 64 0))] "%k.0.ph1404"
        = some (.int 64 (BitVec.ofNat 64 0))
    rw [lookupName_cons_self]
  · decide

/-! ### The empty entry stream's route -/

/-- **The flush route at the memory and cursor it is used at.**  The entry block's true
arm, the three zero stores and the document's length, inside the record's finalisation
allowance, with the record's boundary at the returned memory.  The boundary is part of
the supply because the route leaves the loop: no step states it, so the flush is the one
non-step branch of the completion and its post is read here.

The form is the certified `WalkFlushAt`'s, with the boundary added: `nep = 0` implies a
run of at most the allowance at the entry state.  The state is the one the premises
name, so the route is read at the caller's own staging. -/
def Stage2NoEventWalkFlushAt (calls : Calls) (mem : Mem) (next : Nat)
    (a12 : List Value) (stk e c d : Nat) (nep : Nat) (K : Stage2NoEventWalkCarry) :
    Prop :=
  nep = 0 →
    ∃ (q : Nat) (m : Mem), q ≤ stage2NoEventFinalisationAllowance ∧
      runFuel calls q stage2NoEventBody
        (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) =
        some (.ret (some (.int 64 0)) m) ∧
      stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0)

/-! ### The premises -/

/-- **What a dispatch supplies, and nothing else.**  At every staging the record
admits: a carry whose static numbers are the argument list's and the four staged
objects' (the seed's own conclusion), the invariant at the entry state, and either the
empty stream's flush or a nonempty stream's seed run to `NodeBlock5` with the invariant
and its read facts there and the loop's step.

The loop branch's run is the seed producer's statement at exactly the head it reports:
`pc = "NodeBlock5"`, `%k.0.ph1404 = 0`, the invariant at the head, and the three reads
the head's first lane and document byte make — `Inv.entries`, `Inv.inside` and
`Inv.doc`, at the staging's memory `mem` (the invariant's fields are stated there, and
the head's run keeps them by its frame), named here as the loop's own input so a
producer need not unfold the invariant to see what it hands the dispatch.  The carry's
field equalities are the seed's conclusion, including `K.xj = K.next0`; the initial
readings are the seed's, so the terminal's post is read at the readings the loop has
moved, not at these.

The `Step` is the counted loop's interface (`JsonStage2NoEventWalkTraverse`): the
continuing branch is a priced segment to the next head, the terminal branch completes
inside the head's credit plus `F`.  The premise names `F = 27`, so the seed's three
steps and the finalisation's two fit the record's `32` (`3 + 27 + 2 = 32`). -/
def Stage2NoEventWalkPremises (gap : Calls := stage2GapRecover) (stk e c d : Nat) : Prop :=
  ∀ (a12 : List Value) (mem : Mem) (next : Nat),
    Γ_stage2_noevent.pre a12 mem next →
    stage2NoEventStagedPre a12 mem next stk e c d →
    ∃ (K : Stage2NoEventWalkCarry),
      K.a12 = a12 ∧ K.stk = stk ∧ K.e = e ∧ K.c = c ∧ K.d = d ∧
      K.next0 = next ∧ K.xj = K.next0 ∧
      K.tok = 0 ∧ K.terms = 0 ∧ K.arena = [] ∧
      Stage2NoEventWalkInv K mem
        (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) ∧
      ((K.nep = 0 ∧
          Stage2NoEventWalkFlushAt (stage2NoEventCalls gap) mem next a12 stk e c d
            K.nep K) ∨
        (0 < K.nep ∧
          ∃ (sHead : State),
            (∀ n, runFuel (stage2NoEventCalls gap) (3 + n) stage2NoEventBody
                (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) =
              runFuel (stage2NoEventCalls gap) n stage2NoEventBody sHead) ∧
            Stage2NoEventWalkHead K mem 0 sHead ∧
            Stage2NoEventWalkTrace K ∧
            readLanes32 mem K.ep K.nep = some K.ent ∧
            (∀ q ∈ K.ent, q < K.n) ∧
            readBytes mem K.b K.n = some K.bs ∧
            Stage2NoEventWalkStep (stage2NoEventCalls gap) mem 27))

/-- **The record's budget carries the finalisation allowance.**  The empty stream's
route costs at most the allowance, and the record's budget is at least it at every
argument list: the ABI list's three read counts are the only terms subtracted from
the two counted charges, so the allowance's `32` is a lower bound. -/
theorem stage2NoEventBudget_ge_finalisation {a12 : List Value} {mem : Mem}
    {b n ep nep xp nxp scratch scratchcap tokensOut valuesOut sumOut err : Nat}
    (hargs : a12 = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
      .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
      .ptr scratch, .int 64 (BitVec.ofNat 64 scratchcap), .ptr tokensOut,
      .ptr valuesOut, .ptr sumOut, .ptr err])
    (hnLt : n < 2 ^ 64) (hneLt : nep < 2 ^ 64) (hnxLt : nxp < 2 ^ 64) :
    stage2NoEventFinalisationAllowance ≤ stage2NoEventBudget a12 mem := by
  rw [hargs]
  simp only [stage2NoEventBudget, stage2NoEventEntryAllowance,
    stage2NoEventByteAllowance, stage2NoEventPositionAllowance,
    stage2NoEventFinalisationAllowance, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hnLt, Nat.mod_eq_of_lt hneLt, Nat.mod_eq_of_lt hnxLt]
  omega

/-! ### The premises from the record and the rows

The seed's conclusion is `JsonStage2NoEventWalkInv`'s, and the run to the head is
`JsonStage2NoEventWalkSeed`'s.  Both are at the entry state the staging names; the only
fact the seed does not hand back is `1 ≤ K.b`, which is the record's and is recovered
from the two decompositions of the argument list (`stage2NoEventAbiList_eq`).  The
flush route is the segment module's, at the default selection. -/

/-- **The premises from the row bundle.**  The zero branch is the flush route read at
the seed's invariant and parameters; the nonempty branch is the seed run, whose head is
the seed producer's, with the step derived from the row. -/
theorem stage2NoEventWalkPremises_of_rows {stk e c d : Nat}
    (hrows : ∀ (a12 : List Value) (mem : Mem) (next : Nat),
      Γ_stage2_noevent.pre a12 mem next →
      stage2NoEventStagedPre a12 mem next stk e c d →
      Stage2NoEventWalkRows (stage2NoEventCalls stage2GapRecover) mem 27) :
    Stage2NoEventWalkPremises stage2GapRecover stk e c d := by
  intro a12 mem next hpre hstaged
  -- the seed's carry and invariant
  obtain ⟨K, hK12, hKstk, hKe, hKc, hKd, hKn0, hKxj, hKtok, hKterms, hKarena,
    hInvEntry⟩ := stage2NoEventWalkInv_seed hpre hstaged
  -- the record's own witnesses, for `1 ≤ b`
  have hpre' := hpre
  obtain ⟨b, n, ep, nep, xp, nxp, scratch, scratchcap, tokensOut, valuesOut,
    sumOut, err, bs, ent, hargs, hdoc, hb1, htail, hentries, horder, hinside, hesc,
    hscratchBytes, hscratchRoom, htokB, hvalB, hsumB, herrB, hmaxDoc, hnLt, hscLt,
    hneLt, hnxLt, hsep, hwater⟩ := hpre'
  -- the two decompositions of the argument list are one list
  have hAbiPre : Stage2NoEventAbiList b n ep nep xp nxp scratch scratchcap tokensOut
      valuesOut sumOut err = a12 := by
    simpa only [Stage2NoEventAbiList] using hargs.symm
  have hAbiInv : Stage2NoEventAbiList K.b K.n K.ep K.nep K.xp K.nxp K.scratch
      K.scratchcap K.tokensOut K.valuesOut K.sumOut K.err = K.a12 := by
    simpa only [Stage2NoEventAbiList] using hInvEntry.args_eq.symm
  have hAbi : Stage2NoEventAbiList b n ep nep xp nxp scratch scratchcap tokensOut
      valuesOut sumOut err =
      Stage2NoEventAbiList K.b K.n K.ep K.nep K.xp K.nxp K.scratch K.scratchcap
        K.tokensOut K.valuesOut K.sumOut K.err := by
    rw [hAbiPre, ← hK12, hAbiInv]
  obtain ⟨hbK, -⟩ := stage2NoEventAbiList_eq hAbi hnLt hInvEntry.nLt hscLt
    hInvEntry.scratchcapLt hneLt hInvEntry.nepLt hnxLt hInvEntry.nxpLt
  have hb1K : 1 ≤ K.b := hbK ▸ hb1
  have hKxj0 : K.xj = K.next0 := by rw [hKn0]; exact hKxj
  -- the parameters at the entry state, at the seed's carry
  have hpar : Stage2NoEventWalkParams K
      (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) := by
    simpa only [stage2NoEventEntryState, ← hK12, ← hKstk, ← hKe, ← hKc, ← hKd]
      using stage2NoEventEntry_params (K := K) (mem := mem) (next := next)
        hInvEntry.args_eq
  refine ⟨K, hK12, hKstk, hKe, hKc, hKd, hKn0, hKxj0, hKtok, hKterms, hKarena,
    hInvEntry, ?_⟩
  by_cases hzero : K.nep = 0
  · -- the empty entry stream: the entry block's true arm and the flush
    have hflush := stage2NoEventWalkFlushRoute (K := K) (mem := mem)
      (s := EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next)
      hInvEntry hpar rfl (by simpa [EntryState] using hKn0.symm) hKxj0 hb1K hzero
    refine Or.inl ⟨hzero, ?_⟩
    intro _
    obtain ⟨m, hrun, hb⟩ := hflush
    exact ⟨stage2NoEventFlushSteps, m, stage2NoEventFlushSteps_le_finalisation,
      hrun, hb⟩
  · -- entries left: the seed's run to the post-read head
    have hseed := stage2NoEventWalkSeedRun (gap := stage2GapRecover) (K := K) (mem := mem)
      (s0 := EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next)
      hInvEntry hpar rfl (by simpa [EntryState] using hKn0.symm) hb1K
      (Nat.pos_of_ne_zero hzero) hKtok hKterms hKarena
    obtain ⟨sHead, -, -, hrun, hHead, htrace, -⟩ := hseed
    refine Or.inr ⟨Nat.pos_of_ne_zero hzero, sHead, hrun, hHead, htrace, ?_, ?_, ?_, ?_⟩
    · exact hHead.inv.entries
    · exact hHead.inv.inside
    · exact hHead.inv.doc
    · exact stage2NoEventWalkStep_of_rows (hrows a12 mem next hpre hstaged)

/-! ### A fixed post at the completion's outcome carries to every behaviour -/

/-- **The post at the run's outcome carries to every behaviour.**  A completion at any
fuel pins the run's outcome; a behaviour at another fuel is the same outcome or the
undefined one, and the undefined outcome is excluded by the completion.  The post is the
record's, not a rule of its own: it is stated at the outcome the completion reaches. -/
theorem stage2NoEventPost_of_completion {calls : Calls} {args : List Value} {mem : Mem}
    {next : Nat} {sE : State} {B : Nat} {oGood : Outcome}
    (hcom : runFuel calls B stage2NoEventBody sE = some oGood)
    (hgood : Γ_stage2_noevent.post args mem next oGood) :
    ∀ o, BehFromState calls stage2NoEventBody sE o →
      Γ_stage2_noevent.post args mem next o := by
  intro o hbeh
  rcases hbeh with ⟨n, hn⟩ | ⟨n, hn⟩
  · have hEq : oGood = Outcome.ub := (runFuel_outcome_unique hn hcom).symm
    rw [hEq] at hgood
    exact hgood.elim
  · have hEq := runFuel_outcome_unique hn hcom
    rw [hEq]
    exact hgood

/-! ### The obligation

`Satisfies`'s two conjuncts are the completion at the record's budget and the post at
every behaviour.  The premises give both routes; the budget identity is the record's
own (`Γ_stage2_noevent_at` reads the twelve-slot prefix, and the adapter appends the
four staging objects), and the post is the boundary at the completion's outcome. -/

/-- **The walk's obligation, from the premises.**  No post rule beside the premises: the
flush carries its boundary and the step's terminal branch carries its own, and
`stage2NoEventPost_of_completion` carries that one outcome to every behaviour of the
run.  The zero branch's budget is the finalisation allowance, which
`stage2NoEventBudget` carries at every argument list; the nonempty branch's is
`potential + 32`, bounded by `32·nep + 8·n + 32` and that by the record's budget. -/
theorem stage2NoEventWalkObligation_of_premises {gap : Calls} {stk e c d : Nat}
    (h : Stage2NoEventWalkPremises gap stk e c d) :
    Stage2NoEventWalkObligation gap stk e c d := by
  intro args mem next hpre
  obtain ⟨a12, rfl, hpre12, hstaged⟩ := hpre
  obtain ⟨K, hK12, hKstk, hKe, hKc, hKd, hKn0, hKxj, hKtok, hKterms,
    hKarena, hInvEntry, hbr⟩ := h a12 mem next hpre12 hstaged
  have hlen : a12.length = 12 := stage2NoEventPre_length hpre12
  have htake : (stage2NoEventArgs a12 stk e c d).take 12 = a12 :=
    stage2NoEventArgs_take12 a12 hlen stk e c d
  have hbudget : (Γ_stage2_noevent_at stk e c d).budget
      (stage2NoEventArgs a12 stk e c d) mem = stage2NoEventBudget a12 mem := by
    change Γ_stage2_noevent.budget
      (List.take 12 (stage2NoEventArgs a12 stk e c d)) mem = stage2NoEventBudget a12 mem
    rw [htake]
    rfl
  -- the ABI witnesses the budget's lower bound reads
  obtain ⟨b, n, ep, nep, xp, nxp, scratch, scratchcap, tokensOut, valuesOut,
    sumOut, err, bs, ent, hargs, hdoc12, hb1, htail, hentries, horder, hinside,
    hesc, hscratchBytes, hscratchRoom, htokB, hvalB, hsumB, herrB, hmaxDoc, hnLt,
    hscLt, hneLt, hnxLt, hsep, hwater⟩ := hpre12
  refine ⟨?_, ?_⟩
  · rcases hbr with ⟨hzero, hflush⟩ | ⟨hpos, sHead, hseed, hHead, htrace,
      hentries, hinside, hdoc, hstep⟩
    · -- the empty entry stream
      obtain ⟨q, m, hq, hrun, hb⟩ := hflush hzero
      have hqbudget : q ≤ stage2NoEventBudget a12 mem :=
        le_trans hq (stage2NoEventBudget_ge_finalisation hargs hnLt hneLt hnxLt)
      exact ⟨some (.int 64 0), m, by
        rw [hbudget]
        exact runFuel_mono_le hqbudget hrun⟩
    · -- entries left: the seed run, the loop, and the budget
      obtain ⟨q, v, m, hq, hrun, hb⟩ :=
        stage2NoEventWalkLoopFinishes hstep K 0 sHead hHead htrace
      have hcost : 3 + (q + 2) ≤ stage2NoEventBudget a12 mem := by
        have hpot := stage2NoEventWalkPotential_le K 0
        have hble := stage2NoEventWalkBudget_le (mem := mem) (s := sHead) hHead.inv
        rw [hK12] at hble
        omega
      have htotal : runFuel (stage2NoEventCalls gap) (3 + (q + 2)) stage2NoEventBody
          (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) =
          some (.ret (some (.int 64 v)) m) := by
        rw [hseed (q + 2)]
        exact hrun
      exact ⟨some (.int 64 v), m, by
        rw [hbudget]
        exact runFuel_mono_le hcost htotal⟩
  · intro o hbeh
    change Γ_stage2_noevent.post
      (List.take 12 (stage2NoEventArgs a12 stk e c d)) mem next o
    rw [htake]
    rcases hbr with ⟨hzero, hflush⟩ | ⟨hpos, sHead, hseed, hHead, htrace,
      hentries, hinside, hdoc, hstep⟩
    · -- the flush's boundary at the completion's outcome
      obtain ⟨q, m, hq, hrun, hb⟩ := hflush hzero
      have hqbudget : q ≤ stage2NoEventBudget a12 mem :=
        le_trans hq (stage2NoEventBudget_ge_finalisation hargs hnLt hneLt hnxLt)
      have hcom : runFuel (stage2NoEventCalls gap) (stage2NoEventBudget a12 mem)
          stage2NoEventBody
          (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) =
          some (.ret (some (.int 64 0)) m) :=
        runFuel_mono_le hqbudget hrun
      have hgood : Γ_stage2_noevent.post a12 mem next
          (.ret (some (.int 64 0)) m) := by
        show stage2NoEventBoundary a12 mem next m (.int 64 0)
        simpa only [hK12, hKn0] using hb
      exact stage2NoEventPost_of_completion hcom hgood o hbeh
    · -- the terminal branch's boundary at the completion's outcome
      obtain ⟨q, v, m, hq, hrun, hb⟩ :=
        stage2NoEventWalkLoopFinishes hstep K 0 sHead hHead htrace
      have hcost : 3 + (q + 2) ≤ stage2NoEventBudget a12 mem := by
        have hpot := stage2NoEventWalkPotential_le K 0
        have hble := stage2NoEventWalkBudget_le (mem := mem) (s := sHead) hHead.inv
        rw [hK12] at hble
        omega
      have htotal : runFuel (stage2NoEventCalls gap) (3 + (q + 2)) stage2NoEventBody
          (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) =
          some (.ret (some (.int 64 v)) m) := by
        rw [hseed (q + 2)]
        exact hrun
      have hcom : runFuel (stage2NoEventCalls gap) (stage2NoEventBudget a12 mem)
          stage2NoEventBody
          (EntryState stage2NoEventBody (stage2NoEventArgs a12 stk e c d) mem next) =
          some (.ret (some (.int 64 v)) m) :=
        runFuel_mono_le hcost htotal
      have hgood : Γ_stage2_noevent.post a12 mem next
          (.ret (some (.int 64 v)) m) := by
        show stage2NoEventBoundary a12 mem next m (.int 64 v)
        simpa only [hK12, hKn0] using hb
      exact stage2NoEventPost_of_completion hcom hgood o hbeh

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkF1_notRow
#print axioms stage2NoEventWalkF1_notRows
#print axioms stage2NoEventWalkStep_of_rows
#print axioms stage2NoEventWalkPremises_of_rows
#print axioms stage2NoEventPost_of_completion
#print axioms stage2NoEventWalkObligation_of_premises

end LeanLLVM.Refinement
