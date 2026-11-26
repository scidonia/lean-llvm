/-
The reference's two supplies, and which side proves what.

`Stage2NoEventWalkExit` carries the reference's data on both arms: `accept` binds a
tape, the parse equality at it and the reference facts
(`Stage2NoEventWalkReferenceFacts`), and `refuse` binds the parser's verdict
(`Stage2NoEventWalkParseRefusal`).  The accept arm's data is the tree's:
`JsonStage2NoEventWalkRecordSupplyOfParse` proves `Stage2NoEventWalkRecordsSupply`
at every `parseBytes … = .ok t`, and `Stage2NoEventAdmitted.referenceRecords` gives
`Stage2NoEventReferenceRecords` at every admitted document.  The refusal arm's is
not — its verdict belongs only to documents the reference refuses — so this module
states exactly what a producer of either must have, proves what follows from the
tree about them, and says which part is whose.

**The accept supply reduces to one record trace, and the parse determines it.**
`parseBytes` is a function, so a document has at most one tape
(`stage2NoEventWalkParsed_unique`), and the tape it returns is the document's own:
`t.input` is the bytes and `decodeTape` reads the accepted value
(`stage2NoEventWalkParsed_tape`).  The facts' tape field is then not an obligation
of its own — its only content, `t.tokens = toks`, holds definitionally once `toks`
is the tape's token list — and `stage2NoEventWalkReferenceFacts_iff_supply` proves
the facts are exactly `Stage2NoEventWalkRecordsSupply` plus those two
identifications.  The four remaining fields — the trace `rs`, the relation
`Stage2Records bs arena rs t.tokens` at the tape's own tokens, the record widths
`∀ r ∈ rs, r.Bounded`, and the extent clause
`∀ e ∈ consumeRecords bs arena rs, e.BodiesWithin bs arena` — are produced by
`records_exists` (`JsonStage2NoEventWalkRecordSupplyOfParse`) from the parse's
tokens under the strengthened `TokenBytes`: the witness is a relation-satisfying
trace, with plain-form strings (`EventRecord.str false`), that the parse's tokens
determine, not necessarily a trace a particular reference run emits.  The choice
of witness is harmless: the transfer chain's `value` is a theorem at every facts
value at the same document, so every such trace yields the same
`scalarCanonValueOfBytes`.  What remains the deployment's is the two count
equations, `obs.length = K'.tok` and `K'.terms = (obs.map ConsumerEvent.terms).sum`
(`JsonStage2NoEventWalkCountsTie`): the tree does not compute the walk's two
registers from the document — its invariant carries only `K.tok ≤ K.n`
(`Stage2NoEventWalkInv.tokLe`) and its count is only an over-count
(`Stage2NoEventWalkCount_iff`) — so at a chosen supply, where
`obs = consumeRecords bs arena rs`, the equations compare those registers against
the trace's own data.  The bounded witness `countsTieDoc_terms_two_derivations`
separates two *derivations* with `obs` free, not two values at one supply: it
shows the relation alone fixes neither the read-back nor its term sum.  The
reduction below proves that no *further* reference data is hidden behind them.

**The refusal arm's carried data is the whole `Stage2NoEventWalkReferenceRefuse`.**
The exit's `refuse` also holds the walk's trace, but a `Prop` trace cannot supply
the exit's `Type` fields: the relation's witnesses, the two count equations and
the parser's verdict are all carried from the boundary, as `ReferenceRefuse`'s own
docstring and the terminal producers' say.  What this module adds is that at an
**admitted** document that verdict is refutable — admission carries a successful
parse and the parser is a function — so the two arms are exclusive there, and the
refusal supply belongs only to documents the reference refuses.

**What is proved here.**  The parse tie (`stage2NoEventWalkParsed_unique`,
`stage2NoEventWalkParsed_tape`); the reduction of the facts and of the acceptance
to the records supply (`stage2NoEventWalkReferenceFacts_iff_supply`,
`stage2NoEventWalkReferenceAccept_iff`); the transfer chain read at the supply
(`Stage2NoEventWalkRecordsSupply.value`, `Stage2NoEventWalkAcceptSupply.value`);
and the exclusivity at the admitted domain (`Stage2NoEventAdmitted.not_parseRefusal`,
`…referenceWord_eq_one`, `…referenceRecords_iff`, `…refuseSupply_not`,
`…tape_tied`).

**What the deployment proves.**  On the accept arm: nothing beyond the two count
equations.  The trace, its relation, its widths and its extent clause are the
parse's own (`stage2NoEventWalkRecordsSupply_of_parse`), and the facts' `obs` and
`toks` are the read-back and the tape's tokens; the equations `obs.length = K'.tok`
and `K'.terms = (obs.map ConsumerEvent.terms).sum` compare the walk's registers
against that derived data, and `JsonStage2NoEventWalkCountsTie` shows they are the
deployment's: the counted-token register is not computed by the tree (its invariant
carries only `K.tok ≤ K.n`, `Stage2NoEventWalkInv.tokLe`; its count only
`Stage2NoEventWalkCount_iff`), and the relation does not fix the read-back — the
bounded witness `countsTieDoc_terms_two_derivations` gives two arena-bound
derivations at one `(bs, arena, toks)`, with `obs` free, of equal length and
different sums.  At a chosen supply, where `obs = consumeRecords bs arena rs`, the
term sum is determined, and the equation compares the walk's term register against
the trace's own `(rs.map EventRecord.terms).sum`.  On the refusal arm:
the whole `ReferenceRefuse` — the relation's witnesses, the counts and the parser's
error.  The run, its price, the boundary, the terminal witnesses and the row are
the walk's.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkReference
import LeanLLVM.Refinement.JsonStage2NoEventAdmission
import LeanLLVM.JSON.Correct

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR

/-! ### The accept supply

The one data structure the accept route's reference data reduces to.  It is indexed
by the document and the acceptance's arena — the exit's own `K.bs` and `K'.arena` —
and by the tape the reference parser returned, so a producer that builds it at the
document's own parse cannot place it anywhere else. -/

/-- **A record trace at a document's parse.**  The trace, the relation
at the tape's own token list, the record widths, and the reported strings' extent
clause.  `JsonStage2NoEventWalkRecordSupplyOfParse` produces this for every accepted
document: `stage2NoEventWalkRecordsSupply_of_parse` builds the trace from the
parse's own tokens under the strengthened `TokenBytes` (plain-form strings,
`EventRecord.str false`), so the supply is a relation-satisfying trace the parse
determines, not necessarily the trace a particular reference run emits.  The choice
between such traces is harmless: the transfer chain's `value` holds at every facts
value at the same document, so each yields the same `scalarCanonValueOfBytes`.
What the tokens do not determine is the two count equations, which
`JsonStage2NoEventWalkCountsTie` classifies. -/
structure Stage2NoEventWalkRecordsSupply (bs arena : List UInt8) (t : Tape) : Type where
  /-- A record trace the parse's tokens determine at this document and
  arena. -/
  rs : List EventRecord
  /-- The trace is the document's relation at the parser's own tokens. -/
  records : Stage2Records bs arena rs t.tokens
  /-- Every record fits the field widths its bytes are written at. -/
  bounded : ∀ r ∈ rs, r.Bounded
  /-- Every reported string's body lies inside the source it names. -/
  within : ∀ e ∈ consumeRecords bs arena rs, e.BodiesWithin bs arena

namespace Stage2NoEventWalkRecordsSupply

/-- **The relation at the consumer's own events.**  The supply's trace read by
`Stage2Records.toNoEvent` is a `Stage2NoEvent` at the tape's tokens, with the
observations chosen as the consumer's read-back.  This is the exit's `rel` field at
the supply's witnesses. -/
theorem relation {bs arena : List UInt8} {t : Tape}
    (s : Stage2NoEventWalkRecordsSupply bs arena t) :
    Stage2NoEvent bs arena (consumeRecords bs arena s.rs) t.tokens :=
  Stage2Records.toNoEvent s.records

/-- **The facts, from the supply.**  The acceptance's `obs` is the consumer's
read-back of `rs` and its `toks` the tape's own token list, so `consume` and
`tokens` are definitional and the four real fields are the supply's. -/
def facts {bs arena : List UInt8} {t : Tape}
    (s : Stage2NoEventWalkRecordsSupply bs arena t) :
    Stage2NoEventWalkReferenceFacts bs arena (consumeRecords bs arena s.rs) t.tokens t :=
  { rs := s.rs
    records := s.records
    consume := rfl
    bounded := s.bounded
    within := s.within
    tokens := rfl }

/-- **The transfer chain at the supply.**  At one acceptance — the parser's equality
at the tape plus the supply's records — the emitted stream's value is
`scalarCanonValueOfBytes` at the document.  This is
`stage2NoEventWalkReference_valueOfEvents` with the facts the supply builds, so a
producer that proves the supply has proved the value equation's premises and
nothing more. -/
theorem value {bs arena : List UInt8} {t : Tape}
    (s : Stage2NoEventWalkRecordsSupply bs arena t)
    (hparse : parseBytes Limits.default (ByteString.literal bs) = .ok t) :
    (eventsOfBytes bs (s.rs.map EventRecord.encodedBytes).flatten arena).bind
        valueOfEvents = scalarCanonValueOfBytes bs :=
  stage2NoEventWalkReference_valueOfEvents s.facts hparse

end Stage2NoEventWalkRecordsSupply

/-- **The facts, read backwards.**  Every facts value's tape field is the relation
of its record trace at the tape's own tokens: the acceptance's `toks` is not an
independent choice. -/
def Stage2NoEventWalkReferenceFacts.toSupply {bs arena : List UInt8}
    {obs : List ConsumerEvent} {toks : List Token} {t : Tape}
    (f : Stage2NoEventWalkReferenceFacts bs arena obs toks t) :
    Stage2NoEventWalkRecordsSupply bs arena t :=
  { rs := f.rs
    records := by rw [f.tokens]; exact f.records
    bounded := f.bounded
    within := by rw [← f.consume]; exact f.within }

/-- **The facts are the supply plus the tie.**  Any facts value is a supply at its
own tape (`toSupply`), and a supply at a tape determines the facts once the
acceptance's `obs` is the consumer's read-back and its `toks` the tape's tokens.
So the facts hide nothing beyond the four fields of
`Stage2NoEventWalkRecordsSupply`. -/
theorem stage2NoEventWalkReferenceFacts_iff_supply {bs arena : List UInt8}
    {obs : List ConsumerEvent} {toks : List Token} {t : Tape} :
    Nonempty (Stage2NoEventWalkReferenceFacts bs arena obs toks t) ↔
      ∃ s : Stage2NoEventWalkRecordsSupply bs arena t,
        obs = consumeRecords bs arena s.rs ∧ toks = t.tokens := by
  constructor
  · rintro ⟨f⟩
    exact ⟨f.toSupply, f.consume, f.tokens.symm⟩
  · rintro ⟨s, hobs, htoks⟩
    have hrec : Stage2Records bs arena s.rs toks := by rw [htoks]; exact s.records
    have hwith : ∀ e ∈ obs, e.BodiesWithin bs arena := by rw [hobs]; exact s.within
    exact ⟨s.rs, hrec, hobs, s.bounded, hwith, htoks.symm⟩

/-- **The accept route's reference-side supply.**  The parser's verdict at the
document and the record trace the parse determines at that tape.  This is everything
`Stage2NoEventWalkExit.accept` binds beyond the walk's own evidence: the tape, the
parse equality at it, and the facts (which the records supply determines, at the
observations and tokens it names).  A producer reads the records from
`stage2NoEventWalkRecordsSupply_of_parse`; the counts are the deployment's. -/
structure Stage2NoEventWalkAcceptSupply (K K' : Stage2NoEventWalkCarry) : Type where
  /-- The tape the reference parser returned at the head's document. -/
  t : Tape
  /-- The parse equality at that tape. -/
  parsed : parseBytes Limits.default (ByteString.literal K.bs) = .ok t
  /-- The record trace the parse determines at the acceptance's arena and that tape. -/
  recordsSupply : Stage2NoEventWalkRecordsSupply K.bs K'.arena t

namespace Stage2NoEventWalkAcceptSupply

/-- **The acceptance's facts, from the supply.** -/
def facts {K K' : Stage2NoEventWalkCarry}
    (s : Stage2NoEventWalkAcceptSupply K K') :
    Stage2NoEventWalkReferenceFacts K.bs K'.arena
      (consumeRecords K.bs K'.arena s.recordsSupply.rs) s.t.tokens s.t :=
  s.recordsSupply.facts

/-- **The acceptance's relation, from the supply.**  The exit's `rel` field at
`obs := consumeRecords …` and `toks := t.tokens`. -/
theorem relation {K K' : Stage2NoEventWalkCarry}
    (s : Stage2NoEventWalkAcceptSupply K K') :
    Stage2NoEvent K.bs K'.arena
      (consumeRecords K.bs K'.arena s.recordsSupply.rs) s.t.tokens :=
  s.recordsSupply.relation

/-- **The value equation at the acceptance's own witnesses.** -/
theorem value {K K' : Stage2NoEventWalkCarry}
    (s : Stage2NoEventWalkAcceptSupply K K') :
    (eventsOfBytes K.bs
        (s.recordsSupply.rs.map EventRecord.encodedBytes).flatten K'.arena).bind
      valueOfEvents = scalarCanonValueOfBytes K.bs :=
  s.recordsSupply.value s.parsed

end Stage2NoEventWalkAcceptSupply

/-- **The acceptance's reference data, reduced to the supply.**  The producer's
interface `Stage2NoEventWalkReferenceAccept` is the record supply plus the two
count equations `obs.length = K'.tok` and
`K'.terms = (obs.map ConsumerEvent.terms).sum`, read at the consumer's read-back of
the supply's trace.

The counts are the deployment's, not the walk's, and the two are oriented
differently: `obs.length = K'.tok` puts the observation list (the read-back of the
supply's trace) on the left and the walk's counted-token register on the right,
while `K'.terms = (obs.map ConsumerEvent.terms).sum` puts the walk's term register
on the left and the observation sum on the right.  The tree carries both in
`ReferenceAccept` (`JsonStage2NoEventWalkPremises`), every accept exit destructures
them from that data (`…RowsContainerZero`), and nothing in the tree computes the
walk's stored words.  What the reduction shows is therefore that the accept arm
carries no *further* reference data beyond the supply and these two equations. -/
theorem stage2NoEventWalkReferenceAccept_iff (K K' : Stage2NoEventWalkCarry) :
    Nonempty (Stage2NoEventWalkReferenceAccept K K') ↔
      ∃ s : Stage2NoEventWalkAcceptSupply K K',
        (consumeRecords K.bs K'.arena s.recordsSupply.rs).length = K'.tok ∧
        K'.terms =
          ((consumeRecords K.bs K'.arena s.recordsSupply.rs).map
            ConsumerEvent.terms).sum := by
  constructor
  · rintro ⟨⟨t, obs, toks, h, f⟩⟩
    obtain ⟨rel, obsLen, termsEq, parsed⟩ := h
    refine ⟨⟨t, parsed, f.toSupply⟩, ?_, ?_⟩
    · rw [show (f.toSupply).rs = f.rs from rfl, ← f.consume]
      exact obsLen
    · rw [show (f.toSupply).rs = f.rs from rfl, ← f.consume]
      exact termsEq
  · rintro ⟨s, hlen, hterms⟩
    exact ⟨⟨s.t, consumeRecords K.bs K'.arena s.recordsSupply.rs, s.t.tokens,
      ⟨s.recordsSupply.relation, hlen, hterms, s.parsed⟩, s.recordsSupply.facts⟩⟩

/-! ### The parse tie

The parser is a function, and its tape is the document's own.  Both are the tree's
own theorems at the reference parser, restated here at the walk's vocabulary. -/

/-- **The reference's parse is unique at a document.**  `parseBytes` is a function,
so two accepting outcomes at the same bytes carry the same tape.  This is what
fixes a producer's `parsed` field: whichever tape it writes, it is the one the
parser returns at `bs`. -/
theorem stage2NoEventWalkParsed_unique {bs : List UInt8} {t t' : Tape}
    (h : parseBytes Limits.default (ByteString.literal bs) = .ok t)
    (h' : parseBytes Limits.default (ByteString.literal bs) = .ok t') : t' = t := by
  rw [h] at h'
  exact (ParseResult.ok.inj h').symm

/-- **The tape the parser returns is the document's own.**  Its input is the bytes
parsed and `decodeTape` reads the accepted value out of it: the tape carries no
meaning the document does not, so the only data the records supply adds is the
record trace. -/
theorem stage2NoEventWalkParsed_tape {bs : List UInt8} {t : Tape}
    (h : parseBytes Limits.default (ByteString.literal bs) = .ok t) :
    t.input = ByteString.literal bs ∧
      ∃ v : LeanLLVM.JSON.Value, decodeTape t = some v ∧
        ValidDocument (ByteString.literal bs) v := by
  obtain ⟨v, hdec, hin, hval⟩ :=
    decodeTape_correct Limits.default (ByteString.literal bs) t h
  exact ⟨hin, v, hdec, hval⟩

/-- **An accept supply carries the parse's only tape.**  Any other accepting
outcome at the same document is this supply's tape, so a producer's `parsed` field
is fixed by the parser, not chosen. -/
theorem Stage2NoEventWalkAcceptSupply.tape_eq {K K' : Stage2NoEventWalkCarry}
    (s : Stage2NoEventWalkAcceptSupply K K') {t0 : Tape}
    (h0 : parseBytes Limits.default (ByteString.literal K.bs) = .ok t0) : s.t = t0 :=
  (stage2NoEventWalkParsed_unique (bs := K.bs) s.parsed h0).symm

/-- **The accept supply's tape is the domain's.**  At an admitted document the
domain names the parse (existentially), and uniqueness makes it the tape any
accept supply carries: the tape is the parser's, not a choice.  The tie is the
parser's (`Stage2NoEventWalkAcceptSupply.tape_eq`, `…tape_tied`), and uniqueness
means the domain's existential and the supply's tape agree without further data. -/
theorem Stage2NoEventWalkAcceptSupply.tape_tied {bs : List UInt8}
    {K K' : Stage2NoEventWalkCarry}
    (hK : K.bs = bs) (s : Stage2NoEventWalkAcceptSupply K K') {t0 : Tape}
    (h0 : parseBytes Limits.default (ByteString.literal bs) = .ok t0) : s.t = t0 := by
  have hp : parseBytes Limits.default (ByteString.literal K.bs) = .ok t0 := by
    rw [hK]; exact h0
  exact s.tape_eq hp

/-! ### The refusal supply

The parser's verdict, at the document.  The refusal arm's carried data is the
whole `Stage2NoEventWalkReferenceRefuse` — the relation's witnesses, the two count
equations and the verdict — because the walk's trace is a `Prop` and cannot supply
the exit's `Type` fields; this section proves about the verdict itself that it
cannot hold at an admitted document. -/

/-- **The failure of the reference's parse.**  This is the verdict part of the
refusal arm's carried data: every refusal shape is admitted — `parseBytes` rejects
with `.inputTooLong`, `.depthExceeded`, `.outOfCapacity` and `.invalid` — and the
reference's word is zero at all four
(`stage2NoEventWalkReferenceWord_of_error`). -/
theorem Stage2NoEventAdmitted.not_parseRefusal {bs : List UInt8}
    (h : Stage2NoEventAdmitted bs) : ¬ Stage2NoEventWalkParseRefusal bs := by
  intro hr
  obtain ⟨t, ht⟩ := h.referenceAccepts
  obtain ⟨e, he⟩ := hr
  rw [he] at ht
  exact ParseResult.noConfusion ht

/-- **The reference's word at an admitted document is one.**  The domain's parse
existence and the parser's function-ness fix the acceptance, so the walk's read of
the reference's verdict is the accepted one. -/
theorem Stage2NoEventAdmitted.referenceWord_eq_one {bs : List UInt8}
    (h : Stage2NoEventAdmitted bs) :
    Stage2NoEventWalkReferenceWord bs = 1 := by
  obtain ⟨t, ht⟩ := h.referenceAccepts
  exact stage2NoEventWalkReferenceWord_of_ok ht

/-- **The accept arm's record obligation at a document.**  The parse of `bs`
determines a record trace at the parser's own tape for the arena: this is
`Stage2NoEventWalkRecordsSupply`, stated without naming the tape.
`JsonStage2NoEventWalkRecordSupplyOfParse` proves it from an accepting parse
(`stage2NoEventWalkRecordsSupply_of_parse`), so it is the tree's statement, not a
deployment obligation. -/
def Stage2NoEventReferenceRecords (bs arena : List UInt8) : Prop :=
  ∃ t : Tape, parseBytes Limits.default (ByteString.literal bs) = .ok t ∧
    Nonempty (Stage2NoEventWalkRecordsSupply bs arena t)

/-- **At an admitted document the obligation is at the domain's tape.**  Every
accepting tape at `bs` is the same tape, so the records obligation holds at one if
and only if it holds at every parse of the document; the domain inherits it at the
tape admission names. -/
theorem Stage2NoEventAdmitted.referenceRecords_iff {bs arena : List UInt8}
    (h : Stage2NoEventAdmitted bs) :
    Stage2NoEventReferenceRecords bs arena ↔
      ∀ t : Tape, parseBytes Limits.default (ByteString.literal bs) = .ok t →
        Nonempty (Stage2NoEventWalkRecordsSupply bs arena t) := by
  constructor
  · rintro ⟨t, ht, hs⟩ t' ht'
    have hEq : t' = t := stage2NoEventWalkParsed_unique (bs := bs) ht ht'
    rw [hEq]
    exact hs
  · intro hall
    obtain ⟨t, ht⟩ := h.referenceAccepts
    exact ⟨t, ht, hall t ht⟩

/-- **The refusal supply cannot be produced at an admitted document.**  The
refusal's carried verdict is refutable there, so only the accept arm exists at the
admitted domain; the refusal arm's supply belongs to documents the reference itself
refuses, where `Stage2NoEventAdmitted` does not hold. -/
theorem Stage2NoEventAdmitted.refuseSupply_not {bs : List UInt8}
    (h : Stage2NoEventAdmitted bs) {K : Stage2NoEventWalkCarry} (hK : K.bs = bs) :
    ¬ Nonempty (Stage2NoEventWalkReferenceRefuse K) := by
  rintro ⟨x⟩
  obtain ⟨obs, toks, -, href⟩ := x
  exact h.not_parseRefusal (hK ▸ href)

/-! ### Axiom footprints -/

#print axioms Stage2NoEventWalkRecordsSupply.relation
#print axioms Stage2NoEventWalkRecordsSupply.facts
#print axioms Stage2NoEventWalkRecordsSupply.value
#print axioms Stage2NoEventWalkReferenceFacts.toSupply
#print axioms stage2NoEventWalkReferenceFacts_iff_supply
#print axioms Stage2NoEventWalkAcceptSupply.facts
#print axioms Stage2NoEventWalkAcceptSupply.relation
#print axioms Stage2NoEventWalkAcceptSupply.value
#print axioms stage2NoEventWalkReferenceAccept_iff
#print axioms Stage2NoEventWalkAcceptSupply.tape_eq
#print axioms stage2NoEventWalkParsed_unique
#print axioms stage2NoEventWalkParsed_tape
#print axioms Stage2NoEventWalkAcceptSupply.tape_tied
#print axioms Stage2NoEventAdmitted.not_parseRefusal
#print axioms Stage2NoEventAdmitted.referenceWord_eq_one
#print axioms Stage2NoEventAdmitted.referenceRecords_iff
#print axioms Stage2NoEventAdmitted.refuseSupply_not

end LeanLLVM.Refinement
