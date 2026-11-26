/-
The no-event walk's trace, read off the walk's own run.

`Stage2NoEventWalkRows` takes the walk's accumulated output evidence
(`Stage2NoEventWalkTrace K`) at every head, and `Stage2NoEventWalkReferenceRun_spec`
takes it at the head it starts from.  This module settles where that predicate
comes from, and where it cannot come from.

**What the trace carries.**  `Stage2NoEventWalkTrace K` binds the event list
(`obs`), the reference parser's token list (`toks`), the derivation
(`Stage2NoEvent K.bs K.arena obs toks`), the two count equations
(`obs.length = K.tok`, `K.terms = (obs.map ConsumerEvent.terms).sum`) and the
arena bound.  Its data are the relation's witnesses; the count equations are the
pair `Stage2NoEventWalkCountsTie` names.  `Stage2NoEventWalkTrace_iff_report`
states the whole of it as an equivalence: a trace is a flat report
(relation, length, sum) plus the arena bound, and nothing else.

**The run does not store it.**  The walk's weight is three reading words —
`%tokens.8`, `%terms.8` and `%arena.10` — and the document and arena bytes; it
stores no event and no token.  The three words are counts
(`Stage2NoEventWalkHead.tokensPhi`, `…termsPhi`, `…arenaPhi`), and the arena's
*list* is not pinned by them: the head carries its length (`…alenPhi`) and the
invariant its byte sum (`Stage2NoEventWalkInv.arenaEq`), not its bytes.  So the
relation's witnesses are not read back off a returned state, and the trace is not
implied by the document's shape either: an empty document with a nonzero token
register inhabits no trace (`stage2NoEventWalkTrace_not_of_bs_nil`).  The trace is
the loop's induction invariant: each route extends it by one relation step
(`Stage2NoEventWalkTrace.step`) and each segment carries the result
(`Stage2NoEventWalkHeadSegment.trace'`).

**Where a theorem consumes it, it is already earned.**

* the **seed** — the carry the body is entered at has `tok = 0`, `terms = 0`,
  `arena = []`, so the empty relation inhabits the trace
  (`Stage2NoEventWalkTrace.of_zeros`) and the row at the seed head needs no trace
  from its caller (`stage2NoEventWalkSeedRow`).  This is the only head a consumer
  of `Rows` reaches from outside the loop;
* the **acceptance** — the run's own report is a `Stage2NoEvent` at the
  acceptance's own `obs` and `toks`, the two count equations are the trace's, and
  the carried reference facts' extent clause implies the arena bound
  (`stage2NoEventWalkArenaBound_of_within`), so the trace at the acceptance's
  carry is rebuilt from the exit (`stage2NoEventWalkTrace_of_accept`), not
  supplied;
* the **refusal** — the exit carries the trace itself, and its content beyond the
  flat report is the arena bound, which the refusal's carried data has no clause
  for, so it stays a field
  (`stage2NoEventWalkExit_trace` cases both arms).

**What a caller of `Rows` supplies.**  A builder of the bundle supplies its four
class producers.  A consumer of the reference run
(`stage2NoEventWalkReferenceRun_spec`) supplies `hrows` and the seed head; it
**no longer supplies the trace**: at the seed it is `of_zeros`, at an interior
head the preceding segment's `trace'`, and at a terminal the exit's own report.
No theorem here deletes the trace parameter from `Stage2NoEventWalkRows.row`: the
trace is genuine induction data (the events are not stored), so the parameter is
how the loop passes its own accumulation from one head to the next — not how a
deployment supplies one.  Deleting it would require the body to store the
event and token lists, which it does not; the only stored reading is the pair of
count words (and the arena's length and byte sum).

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkPremises

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR

/-! ### The arena bound from the carried extent clause

The reference facts carry `within : ∀ e ∈ obs, e.BodiesWithin bs arena`, the
used-extent clause on the reported events.  The trace's arena bound is its
clear-bit half: a string event's arena field plus its length ends inside the
arena the trace was read at.  This is the one field of the accept arm's carried
data the trace needs beyond the flat report. -/

/-- **The extent clause implies the arena bound.**  `BodiesWithin` splits on the
field's top bit; on the arena side it is exactly `Stage2NoEventArenaBound`'s
conclusion at the same event. -/
theorem stage2NoEventWalkArenaBound_of_within {bs arena : List UInt8}
    {obs : List ConsumerEvent}
    (h : ∀ e ∈ obs, e.BodiesWithin bs arena) :
    Stage2NoEventArenaBound arena obs := by
  intro e he htag hbelow
  have hb := h e he htag
  rw [if_pos hbelow] at hb
  exact hb

/-! ### The trace at a flat report

`Stage2NoEventWalkTrace` is, field for field, the report a route already has: a
derivation at the carry's document and arena, its length and term sum at the
carry's two registers, and the arena bound.  Stating the constructor at a report
is what lets both arms below hand it the run's own witnesses. -/

/-- **A flat report is the trace.** -/
theorem stage2NoEventWalkTrace_of_report {K : Stage2NoEventWalkCarry}
    {obs : List ConsumerEvent} {toks : List Token}
    (rel : Stage2NoEvent K.bs K.arena obs toks)
    (hlen : obs.length = K.tok)
    (hsum : K.terms = (obs.map ConsumerEvent.terms).sum)
    (hbound : Stage2NoEventArenaBound K.arena obs) :
    Stage2NoEventWalkTrace K :=
  Stage2NoEventWalkTrace.intro obs toks rel hlen hsum hbound

/-- **The trace is a flat report and a bound, and nothing else.**  The forward
direction reads the inductive's witnesses; the backward direction is
`stage2NoEventWalkTrace_of_report`.  So where a `Prop` cannot carry data (the
refusal's `Type` exit), the trace's content is the report the exit already binds
plus the arena bound. -/
theorem Stage2NoEventWalkTrace_iff_report {K : Stage2NoEventWalkCarry} :
    Stage2NoEventWalkTrace K ↔
      ∃ (obs : List ConsumerEvent) (toks : List Token),
        Stage2NoEvent K.bs K.arena obs toks ∧ obs.length = K.tok ∧
          K.terms = (obs.map ConsumerEvent.terms).sum ∧
          Stage2NoEventArenaBound K.arena obs := by
  constructor
  · intro h
    cases h with
    | intro obs toks rel hlen hsum hbound =>
        exact ⟨obs, toks, rel, hlen, hsum, hbound⟩
  · rintro ⟨obs, toks, rel, hlen, hsum, hbound⟩
    exact stage2NoEventWalkTrace_of_report rel hlen hsum hbound

/-! ### The acceptance's trace, from the run's report

The accept exit's constructor binds the run, the post-block state's three stored
words, the report `(obs, toks, rel, obsLen, termsEq)` and the reference facts at
the same witnesses.  Its `acc` names `K'.tok` and `K'.terms` as the two count
words the post block stored, and `obsLen`/`termsEq` are exactly the trace's two
equations at them.  So the acceptance does not need a trace supplied beside it:
the trace at its carry is the report it already carries. -/

/-- **The acceptance's trace is the run's own report.**  The relation, the two
count equations and the facts' extent clause inhabit the trace with `obs` as the
event list and the facts' `toks` as the token list — the list the exit reports,
not a supplied one.

The carry is the acceptance's readings at the **head's** document: the exit's
`rel` is stated at `K.bs` (the document the head read) while `obsLen`/`termsEq`
are at `K'.tok`/`K'.terms` (the post block's stored words), so the trace those
fields make is the one indexed by the readings `K'` carries and the document the
run read.  The row producers build `K'` by moving only the reading registers, so
there `K'.bs = K.bs` and this is the trace at `K'` itself. -/
theorem stage2NoEventWalkTrace_of_accept {K K' : Stage2NoEventWalkCarry}
    {obs : List ConsumerEvent} {toks : List Token} {t : Tape}
    (rel : Stage2NoEvent K.bs K'.arena obs toks)
    (hlen : obs.length = K'.tok)
    (hsum : K'.terms = (obs.map ConsumerEvent.terms).sum)
    (facts : Stage2NoEventWalkReferenceFacts K.bs K'.arena obs toks t) :
    Stage2NoEventWalkTrace { K' with bs := K.bs } :=
  Stage2NoEventWalkTrace.intro obs toks rel hlen hsum
    (stage2NoEventWalkArenaBound_of_within facts.within)

/-- **At the acceptance's own carry, once its document word is the head's.**  The
row producers build `K'` from `K` by moving only the reading registers, so the
identification is `rfl` there; this is the form a consumer uses to read the
trace at the carry the acceptance names. -/
theorem stage2NoEventWalkTrace_of_accept_self {K K' : Stage2NoEventWalkCarry}
    {obs : List ConsumerEvent} {toks : List Token} {t : Tape}
    (hbs : K'.bs = K.bs)
    (rel : Stage2NoEvent K.bs K'.arena obs toks)
    (hlen : obs.length = K'.tok)
    (hsum : K'.terms = (obs.map ConsumerEvent.terms).sum)
    (facts : Stage2NoEventWalkReferenceFacts K.bs K'.arena obs toks t) :
    Stage2NoEventWalkTrace K' :=
  Stage2NoEventWalkTrace.intro obs toks (hbs.symm ▸ rel) hlen hsum
    (stage2NoEventWalkArenaBound_of_within facts.within)

/-- **Every exit either derives its trace or carries it.**  On the accept arm the
trace the exit's fields make is `stage2NoEventWalkTrace_of_accept`'s, at the
acceptance's readings over the head's document; on the refuse arm the exit
carries the trace itself.  Either way a consumer of the walk's terminal reads the
trace out of the exit, never as an extra supply. -/
theorem stage2NoEventWalkExit_trace {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (h : Stage2NoEventWalkExit calls mem F K k s) :
    (∃ K' : Stage2NoEventWalkCarry, Stage2NoEventWalkTrace K') ∨
      Stage2NoEventWalkTrace K := by
  cases h with
  | accept K' q m sT route cost run htok ha12 hn0 acc obs toks rel obsLen termsEq
      report bound t parsed facts =>
      exact Or.inl ⟨_, stage2NoEventWalkTrace_of_accept rel obsLen termsEq facts⟩
  | refuse q m sT route cost run ev trace obs toks rel obsLen termsEq report bound
      refused =>
      exact Or.inr trace

/-! ### The seed's trace, and the row it fills

The body is entered with the three readings at zero and the arena empty.  At that
carry the empty relation inhabits the trace whatever the document and the entry
stream are, so the row bundle's `row` at the seed head takes no trace from its
caller. -/

/-- **The zero carry's trace.**  With `tok = 0`, `terms = 0` and `arena = []`, the
empty derivation is a trace: `obs = []`, `toks = []`, and both count equations and
the arena bound hold vacuously. -/
theorem Stage2NoEventWalkTrace.of_zeros {K : Stage2NoEventWalkCarry}
    (htok : K.tok = 0) (hterms : K.terms = 0) (_harena : K.arena = []) :
    Stage2NoEventWalkTrace K :=
  Stage2NoEventWalkTrace.intro [] [] Stage2NoEvent.nil
    (by rw [htok]; rfl) (by rw [hterms]; rfl) (by intro e he; simp at he)

/-- **The row at the seed head needs no trace.**  `Stage2NoEventWalkRows.row`
takes the walk's accumulated evidence; at the index-zero head of a carry whose
readings are the seed's, that evidence is `of_zeros`'s, so a caller of the bundle
reaches the first row without supplying one. -/
noncomputable def stage2NoEventWalkSeedRow {calls : Calls} {mem : Mem} {F : Nat}
    (hrows : Stage2NoEventWalkRows calls mem F)
    {K : Stage2NoEventWalkCarry} {s : State}
    (hhead : Stage2NoEventWalkHead K mem 0 s)
    (htok : K.tok = 0) (hterms : K.terms = 0) (harena : K.arena = []) :
    Stage2NoEventWalkRow calls mem F K 0 s :=
  hrows.row K 0 s hhead (Stage2NoEventWalkTrace.of_zeros htok hterms harena)

/-! ### The obstruction: the events are not stored

The trace's witnesses are the relation's, and the walk writes none of them.  The
sharpest small instance is the empty document: no derivation at `bs = []` can
produce an event (every event row binds a byte at the token's start), so a
nonzero token register there is not a trace's.  This is why the trace cannot be a
read-back of a run: the count word on its own does not determine, and is not
determined by, the events the relation names.

The two cells that are not recoverable are therefore named here:

* the **event list** `obs` and the **token list** `toks` — the relation's
  witnesses, which the walk never writes; the three stored words are counts, and
  the count equations are carried data (`Stage2NoEventWalkCountsTie`);
* the **arena list** `K.arena` — the head pins its length and the invariant its
  byte sum, not its bytes, so even the arena bound is not a read-back.

The trace stays a parameter of `Stage2NoEventWalkRows.row`.  What changes is who
fills it: `of_zeros` at the seed, the preceding segment's `trace'` along the
loop, and the exit's own report at a terminal. -/

/-- **An empty document carries no event.**  Every non-separator row binds a byte
at the token's start, and `[]` has none; the two separators carry no event and
the empty row none either. -/
theorem stage2NoEvent_nil_of_bs_nil {arena : List UInt8} :
    ∀ {obs : List ConsumerEvent} {toks : List Token},
      Stage2NoEvent [] arena obs toks → obs = [] := by
  intro obs toks h
  induction h with
  | nil => rfl
  | comma _ ih => exact ih
  | colon _ ih => exact ih
  | openBrace hbyte hspan h ih => simp at hbyte
  | closeBrace hbyte hspan h ih => simp at hbyte
  | openBracket hbyte hspan h ih => simp at hbyte
  | closeBracket hbyte hspan h ih => simp at hbyte
  | trueTag hbytes hspan h ih => simp at hbytes
  | falseTag hbytes hspan h ih => simp at hbytes
  | nullTag hbytes hspan h ih => simp at hbytes
  | number hread hspan hlexeme h ih =>
      unfold StrtodReader.reader at hread
      rw [← hlexeme] at hread
      simp at hread
  | strPlain hquote hspan hcode h ih => simp at hquote
  | strArena hquote hspan hcode hbelow harena h ih => simp at hquote

/-- **The empty document admits no trace at a nonzero count.** -/
theorem stage2NoEventWalkTrace_not_of_bs_nil {K : Stage2NoEventWalkCarry}
    (hbs : K.bs = []) (htok : K.tok ≠ 0) : ¬ Stage2NoEventWalkTrace K := by
  rintro ⟨obs, toks, rel, hlen, -, -⟩
  have hrel : Stage2NoEvent [] K.arena obs toks := hbs ▸ rel
  have hemp : obs = [] := stage2NoEvent_nil_of_bs_nil hrel
  rw [hemp] at hlen
  exact htok hlen.symm

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkArenaBound_of_within
#print axioms stage2NoEventWalkTrace_of_report
#print axioms Stage2NoEventWalkTrace_iff_report
#print axioms stage2NoEventWalkTrace_of_accept
#print axioms stage2NoEventWalkTrace_of_accept_self
#print axioms stage2NoEventWalkExit_trace
#print axioms Stage2NoEventWalkTrace.of_zeros
#print axioms stage2NoEventWalkSeedRow
#print axioms stage2NoEvent_nil_of_bs_nil
#print axioms stage2NoEventWalkTrace_not_of_bs_nil

end LeanLLVM.Refinement
