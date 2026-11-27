/-
The pipeline's residual rows: what the run still owes, and what it no longer does.

`ParserRows` (`JsonPipelineParserHalf`) is the pipeline's last hypothesis at one
outcome: the verdict word's meaning, the accepted run's relation to the parser's
tokens, and the refusal word's policy.  Each of its three clauses has content the
run's own ingredients determine, and this module proves the determinations:

* **the trace row, at the walk's own geometry.**  `JsonStage2WalkGeneral`'s
  `walkTraceRow_of_quoteSteps` produces a carry whose events are the walk's
  `WalkTraceRow` over the parser's tokens; `stage2Records_of_generalRow` composes
  it with `emittedStream_of_row` (`JsonStage2WalkAlignment`), so the record trace,
  its byte-level relation `Stage2EventRel` and the stream's decoded skeleton are
  *theorems* at the general document rather than a supplied relation.  The
  entry-level spelling is `stage2EventRel_of_walkTraceRow`: the row and the
  stream's flattening give the relation, with no `Stage2Records` constructor in
  the statement.
* **the accepting trace, at the outcome.**  `ParserHalfResidual` states the
  accepted branch with `WalkTraceRow` and the stream read in place of
  `Stage2Records`; `parserHalfRows_of_residual` then produces `ParserRows`'
  accepted clause through `emittedStream_of_row`, and
  `refusalOffset_of_parseOk` supplies the accepted document's refusal policy
  from the same tape and the stage's passed UTF-8 test.
* **the refusal bit and offset.**  The verdict word's `0` direction is
  `verdictWord_zero_iff`'s from the run's bit and the parser's refusal, and the
  refusal row is the family's: `RefusalRoute` names the four document shapes the
  walk's refusing arms reach, and `refusalOffset_of_route` reads the parser's
  own refusal at each into `RefusalOffset` (`refusalOffset_allSpace`,
  `refusalOffset_spacePrefix_closeBracket`, `..._closeBrace`,
  `refusalOffset_quote`).  `refusalPolicy_of_route` lifts that to the stored
  word: a producer that knows each stored word's route shape gets
  `RefusalOffsetPolicy` rather than assuming it.

# The residual, exactly

`ParserRowsResidual` is the whole obligation that remains: the document the
arguments name, the run's verdict bit, the parser's answer at that document, the
two reads, and — on acceptance — the walk's row and the stage's passed UTF-8
test.  It is *not* `ParserRows` restated and it is *not* a weakening:

* `parserRows_of_residual` derives `ParserRows` from it, so the row's word
  clauses, its accepted relation and its refusal policy are all produced;
* `residual_of_evidence` shows stage two's standing
  `Stage2OutcomeEvidence` (`JsonStage2Hsem`) already supplies it — the evidence's
  `Stage2Records` conjunct is the walk's row by
  `stage2Records_iff_forall₂` — so the residual adds no obligation the tree does
  not already carry;
* `evidence_of_residual` shows the converse, and `residual_iff_evidence` is the
  equivalence: the residual is the evidence with the record trace named as the
  walk's row.  What changed is that the row is no longer assumed at the outcome:
  `JsonStage2WalkGeneral` proves it from the walk's alignment, its per-token
  steps and its seed, and `stage2Records_of_generalRow` reads the relation back.

`pipeline_satisfies_of_residual` is the whole chain at the specification:
`Γ_pipeline stage2EventRel tab base` follows from the units' record, the staging,
the run and the residual, with every clause between the residual and the post
produced here rather than assumed.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonPipelineParserHalf
import LeanLLVM.Refinement.JsonStage2WalkGeneral
import LeanLLVM.Refinement.JsonStage2WalkRefusalOffset
import LeanLLVM.Refinement.JsonStage2WalkRefusalOffsetBracket
import LeanLLVM.Refinement.JsonStage2WalkRefusalOffsetBrace
import LeanLLVM.Refinement.JsonStage2WalkRefusalOffsetQuote

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonUtf8IR

/-! ### The walk's row at the parser's relation

`WalkTraceRow` is the pointwise relation over the parser's token list with the
separators removed (`JsonStage2WalkAlignment`), and `emittedStream_of_row` turns
it plus the stream's flattening into the three clauses the accepted branch
consumes.  The reading below names the middle clause on its own, which is the
shape `ParserRows` asks for. -/

/-- **The row gives the byte-level relation.**  A trace related record for record
to the parser's tokens, and the event stream that is its encoding, are
`Stage2EventRel` at those tokens.  No `Stage2Records` constructor is named: the
relation is read off the walk's row. -/
theorem stage2EventRel_of_walkTraceRow {bs arena : List UInt8} {t : Tape}
    {rs : List EventRecord} {evs : List UInt8}
    (hrow : WalkTraceRow bs arena t rs)
    (hev : evs = (rs.map EventRecord.encodedBytes).flatten) :
    Stage2EventRel bs arena evs t.tokens :=
  (emittedStream_of_row hrow hev).2.1

/-! ### The general row produces the relation

The general document's row (`walkTraceRow_of_quoteSteps`) is the carry whose
events the row relates to the tokens.  Composed with `emittedStream_of_row`, it
gives what stage two's accepted boundary needs — the record trace, the
byte-level relation and the decoded skeleton — at any tape and geometry the
quote-inclusive staging supplies, so the trace is a theorem at the document and
not a supplied relation. -/

/-- **The general row's trace evidence.**  At a tape and geometry
`WalkAlignQuoted` relates, with a step at every token index and the seed's
correspondence, the walk's final carry has the whole document's row and
`emittedStream_of_row` reads it as the record trace, the byte-level relation and
the stream's skeleton. -/
theorem stage2Records_of_generalRow {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {arena : List UInt8} {C₀ : WalkCarry G}
    (hal : WalkAlignQuoted G t)
    (hstep : ∀ (j : Nat) (C : WalkCarry G), j < t.tokens.length →
      WalkTracePrefixAt G arena t C j → ∃ C', WalkTraceStepAt G arena t C C' j)
    (hk₀ : C₀.k = 0) (hpre₀ : WalkTracePrefixAt G arena t C₀ 0) :
    ∃ C : WalkCarry G,
      C.k = G.nep ∧
      Stage2Records G.bs arena C.events t.tokens ∧
      Stage2EventRel G.bs arena
        ((C.events.map EventRecord.encodedBytes).flatten) t.tokens ∧
      parseSkeleton ((C.events.map EventRecord.encodedBytes).flatten) =
        C.events.map EventRecord.tagVal := by
  obtain ⟨C, hk, hrow⟩ := walkTraceRow_of_quoteSteps hal hstep hk₀ hpre₀
  obtain ⟨hrecs, hrel, hskel⟩ := emittedStream_of_row hrow rfl
  exact ⟨C, hk, hrecs, hrel, hskel⟩

/-! ### The refusing routes' offsets

`RefusalOffset` splits by the stage that owns the refusal: a UTF-8-invalid
document refuses at its end, and a UTF-8-valid one at the parser's position
(`JsonPipelineSpec`).  The walk's refusing arms reach four document shapes — the
flush route's whitespace-only document, the depth-zero closing bracket and
closing brace, and the unterminated string — and each is the parser-side premise
of one theorem in the refusal-offset family.  `RefusalRoute` is those shapes as
one predicate, at the offset each route stores, and the two readings below turn
it into the row: the offset first (`refusalOffset_of_route`), then the policy at
the stored word (`refusalPolicy_of_route`). -/

/-- **The four document shapes the walk's refusals reach, at the stored offset.**
The flush route's whitespace-only document and its length; the depth-zero
closing bracket and brace, each after a whitespace prefix, at the prefix's
length; and the unterminated string, whose body carries no closing quote, control
byte, malformed escape or invalid sequence, at the opening quote's position. -/
def RefusalRoute (bs : List UInt8) (e : Nat) : Prop :=
  ((∀ b ∈ bs, IsSpaceB b = true) ∧ e = bs.length) ∨
  (∃ pre rest : List UInt8,
      bs = pre ++ (0x5D :: rest) ∧
      (∀ b ∈ pre, IsSpaceB b = true) ∧ e = pre.length) ∨
  (∃ pre rest : List UInt8,
      bs = pre ++ (0x7D :: rest) ∧
      (∀ b ∈ pre, IsSpaceB b = true) ∧ e = pre.length) ∨
  (∃ pre body : List UInt8,
      bs = pre ++ (0x22 :: body) ∧
      (∀ b ∈ pre, IsSpaceB b = true) ∧
      (∀ b ∈ body, IsQuoteBodyByte b) ∧ e = pre.length)

/-- **A route shape's offset is the parser's.**  Each of the family's four
theorems is one case, at the document the shape names and the offset the route
stored.  The input bound and the stage's passed UTF-8 test are the two premises
every walk route carries; the flush route needs no valid-prefix premise for its
own clause. -/
theorem refusalOffset_of_route {bs : List UInt8} {e : Nat}
    (hbound : bs.length ≤ Limits.default.maxInput)
    (hutf8 : utf8WinPrefix (utf8Window bs bs.length (pipelineBlocks bs.length)))
    (h : RefusalRoute bs e) :
    RefusalOffset bs e := by
  rcases h with ⟨hws, rfl⟩ | ⟨pre, rest, rfl, hws, rfl⟩ |
    ⟨pre, rest, rfl, hws, rfl⟩ | ⟨pre, body, rfl, hws, hbody, rfl⟩
  · exact refusalOffset_allSpace hbound hws
  · exact refusalOffset_spacePrefix_closeBracket hws hbound hutf8
  · exact refusalOffset_spacePrefix_closeBrace hws hbound hutf8
  · exact refusalOffset_quote hws hbody hbound hutf8

/-- **The refusal policy from the routes.**  A producer that reads each word the
caller's refusal slot holds and knows the route shape that stored it gets
`RefusalOffsetPolicy` — the third conjunct `ParserRows` asks for — from the
family, rather than assuming the policy at the outcome. -/
theorem refusalPolicy_of_route {bs : List UInt8} {m : Mem} {err : Nat}
    (hbound : bs.length ≤ Limits.default.maxInput)
    (hutf8 : utf8WinPrefix (utf8Window bs bs.length (pipelineBlocks bs.length)))
    (hroute : ∀ e : Nat, readBytes m err 8 = some (wordBytes 8 e) →
      RefusalRoute bs e) :
    RefusalOffsetPolicy bs m err :=
  fun e hread => refusalOffset_of_route hbound hutf8 (hroute e hread)

/-! ### The residual at one document

The residual is `ParserHalfRows` with each clause's derivable part removed: the
word row is not named (the run's bit and the parser's answer are), the accepted
relation is not named (the walk's row and the stream read are), and the accepted
document's refusal policy is not named (the stage's passed UTF-8 test is).  The
refused document's policy stays, because the outcome does not name which route
stored the word; `refusalPolicy_of_route` is how a producer that does know the
route discharges it. -/

/-- **What the run still owes at one document.**  On acceptance: the bit, the
parser's tape, the arena and event reads, the walk's row, the staged arena
cursor (`mem`'s `ndst` slot, read at the starting memory), the extent the trace
accounts for from it, and the stage's passed UTF-8 test.  On refusal: the bit,
the parser's refusal and the policy at the caller's slot. -/
def ParserHalfResidual (bs : List UInt8) (verdict : BitVec 64) (mem m : Mem)
    (dst ev err ndst : Nat) (ndst' nev' : Nat) : Prop :=
  (verdict = 1 ∧
    ∃ (t : Tape) (rs : List EventRecord) (arena : List UInt8) (ndst0 : Nat),
      parseBytes Limits.default (ByteString.literal bs) = .ok t ∧
      readBytes m dst ndst' = some arena ∧
      readBytes m ev nev' = some ((rs.map EventRecord.encodedBytes).flatten) ∧
      WalkTraceRow bs arena t rs ∧
      readBytes mem ndst 8 = some (wordBytes 8 ndst0) ∧
      ndst' = ndst0 + arenaExtent rs ∧
      utf8WinPrefix (utf8Window bs bs.length (pipelineBlocks bs.length))) ∨
  (verdict = 0 ∧
    (¬ ∃ t : Tape, parseBytes Limits.default (ByteString.literal bs) = .ok t) ∧
    RefusalOffsetPolicy bs m err)

/-- **The residual gives the rows at the document.**  The word row is the
parser's answer at the run's bit; the accepted clause is the walk's row read
through `emittedStream_of_row`, at the arena and the stream the run's reads name;
and the accepted document's policy is `refusalOffset_of_parseOk`'s, from the tape
and the stage's passed test.  The refused branch's policy is the residual's own,
and its accepted clause is vacuous at the bit. -/
theorem parserHalfRows_of_residual {bs : List UInt8} {verdict : BitVec 64}
    {mem m : Mem} {dst ev err ndst ndst' nev' : Nat}
    (h : ParserHalfResidual bs verdict mem m dst ev err ndst ndst' nev') :
    ParserHalfRows stage2EventRel bs verdict m dst ev err ndst' nev' := by
  rcases h with ⟨hv, t, rs, arena, ndst0, hparse, hdst, hev, hrow, -, -, hutf8⟩ |
    ⟨hv, hno, hpol⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [hv]
      exact verdictWord_one_iff.mpr ⟨t, hparse⟩
    · intro _
      exact ⟨t, arena, (rs.map EventRecord.encodedBytes).flatten, hparse, hdst, hev,
        (emittedStream_of_row hrow rfl).2.1⟩
    · intro e _
      exact refusalOffset_of_parseOk hparse hutf8
  · refine ⟨?_, ?_, hpol⟩
    · rw [hv]
      exact verdictWord_zero_iff.mpr hno
    · intro h1
      rw [hv] at h1
      exact absurd h1 (by decide)

/-! ### The residual at the outcome

The residual is indexed by the outcome exactly as `ParserRows` and
`Stage2OutcomeEvidence` are, so the producer is asked only at outcomes an
execution produces.  Its match is `ParserRows`' match: the document is the one
the length argument and the starting memory name, and the verdict, the returned
memory and the three slots are the outcome's own fields. -/

/-- **What the run still owes at one outcome.** -/
def ParserRowsResidual (base : Nat) (args : List Value)
    (mem : Mem) (ndst' nev' : Nat) (o : Outcome) : Prop :=
  match o, args with
  | .ret (some (.int 64 verdict)) m,
    [.ptr _, .int 64 n, .ptr _, .ptr _, .ptr _, .ptr _, .int 64 _, .ptr _, .ptr _,
     .int 64 _, .ptr _, .ptr _, .ptr dst, .int 64 _, .ptr ndst, .ptr ev, .int 64 _,
     .ptr _, .ptr err, .int 64 _] =>
      ∃ bs : List UInt8,
        n.toNat = bs.length ∧
        readBytes mem base n.toNat = some bs ∧
        ParserHalfResidual bs verdict mem m dst ev err ndst ndst' nev'
  | _, _ => False

/-- **The residual gives the pipeline's rows at the outcome.** -/
theorem parserRows_of_residual {base : Nat} {args : List Value} {mem : Mem}
    {ndst' nev' : Nat} {o : Outcome}
    (h : ParserRowsResidual base args mem ndst' nev' o) :
    ParserRows stage2EventRel base args mem ndst' nev' o := by
  unfold ParserRowsResidual at h
  unfold ParserRows
  split at h
  · obtain ⟨bs, hlen, hread, hres⟩ := h
    exact ⟨bs, hlen, hread, parserHalfRows_of_residual hres⟩
  · exact h.elim

/-! ### The evidence supplies the residual, and nothing else

`Stage2OutcomeEvidence` (`JsonStage2Hsem`) is the standing producer's statement
at an outcome.  Its accepted branch carries `Stage2Records bs arena rs t.tokens`,
which `stage2Records_iff_forall₂` reads as the walk's row; the rest of the branch
is unchanged.  So the residual is no new obligation, and the converse holds too:
the two predicates differ only in how the record trace is spelled. -/

/-- **Stage two's evidence supplies the residual.**  The accepted branch's
`Stage2Records` is the walk's row (`stage2Records_iff_forall₂`), its
`evs = (rs.map …).flatten` is the residual's pinned read, and its staged cursor
and extent equation are the residual's own; the refused branch is unchanged. -/
theorem residual_of_evidence {base : Nat} {args : List Value} {mem : Mem}
    {ndst' nev' : Nat} {o : Outcome}
    (h : Stage2OutcomeEvidence base args mem ndst' nev' o) :
    ParserRowsResidual base args mem ndst' nev' o := by
  unfold Stage2OutcomeEvidence at h
  unfold ParserRowsResidual
  split at h
  · obtain ⟨bs, hlen, hread, hcase⟩ := h
    refine ⟨bs, hlen, hread, ?_⟩
    rcases hcase with
      ⟨hv, hutf8, t, rs, arena, evs, hparse, hdst, hev, hrecs, hrel,
        ndst0, hndst0read, hndst0eq⟩ |
      ⟨hv, hpol, hno⟩
    · refine Or.inl ⟨hv, t, rs, arena, ndst0, hparse, hdst, ?_, ?_,
        hndst0read, hndst0eq, hutf8⟩
      · rw [hrecs] at hev
        exact hev
      · exact stage2Records_iff_forall₂.mp hrel
    · exact Or.inr ⟨hv, hno, hpol⟩
  · exact h.elim

/-- **The residual supplies stage two's evidence.**  The accepted branch's row
is `Stage2Records` by `Stage2Records.of_forall₂`, and its pinned stream read is
that branch's `evs` at the flattening; the refused branch is unchanged. -/
theorem evidence_of_residual {base : Nat} {args : List Value} {mem : Mem}
    {ndst' nev' : Nat} {o : Outcome}
    (h : ParserRowsResidual base args mem ndst' nev' o) :
    Stage2OutcomeEvidence base args mem ndst' nev' o := by
  unfold ParserRowsResidual at h
  unfold Stage2OutcomeEvidence
  split at h
  · obtain ⟨bs, hlen, hread, hcase⟩ := h
    refine ⟨bs, hlen, hread, ?_⟩
    rcases hcase with
      ⟨hv, t, rs, arena, ndst0, hparse, hdst, hev, hrow, hndst0read,
        hndst0eq, hutf8⟩ |
      ⟨hv, hno, hpol⟩
    · refine Or.inl ⟨hv, hutf8, t, rs, arena,
        (rs.map EventRecord.encodedBytes).flatten, hparse, hdst, hev, rfl, ?_,
        ndst0, hndst0read, hndst0eq⟩
      exact Stage2Records.of_forall₂ hrow
    · exact Or.inr ⟨hv, hpol, hno⟩
  · exact h.elim

/-- **The residual is the standing evidence, at the walk's row.**  Neither
predicate is stronger: the difference is the record trace's spelling, and
`stage2Records_iff_forall₂` is the equivalence between the two spellings. -/
theorem residual_iff_evidence {base : Nat} {args : List Value} {mem : Mem}
    {ndst' nev' : Nat} {o : Outcome} :
    ParserRowsResidual base args mem ndst' nev' o ↔
      Stage2OutcomeEvidence base args mem ndst' nev' o :=
  ⟨evidence_of_residual, residual_of_evidence⟩

/-! ### The specification from the residual

`pipeline_satisfies_of_parserRows` takes the rows at each outcome the run
produces; with `parserRows_of_residual` the same theorem takes the residual.  The
staging, the run and the extent record are consumed only to index the residual,
so the record's post follows from the units' record and the run's own facts. -/

/-- **The pipeline's specification from the units' record and the residual.** -/
theorem pipeline_satisfies_of_residual {calls : Calls} {f : Function}
    {tab base : Nat}
    (hunits : Satisfies calls f (Γ_pipeline_units tab base))
    (hres : ∀ (args : List Value) (mem : Mem) (next : Nat) (o : Outcome)
      (ndst' nev' : Nat),
      pipelineStaging tab base args mem →
      BehFromState calls f (EntryState f args mem next) o →
      pipelineOutputExtents args o ndst' nev' →
      ParserRowsResidual base args mem ndst' nev' o) :
    Satisfies calls f (Γ_pipeline stage2EventRel tab base) :=
  pipeline_satisfies_of_parserRows hunits
    (fun args mem next o ndst' nev' hst hbeh hext =>
      parserRows_of_residual (hres args mem next o ndst' nev' hst hbeh hext))

/-! ### Axiom footprints

The trace composition is `emittedStream_of_row`'s and the general row's; the
refusal readings are the family's; the residual's derivations are the parser's
parity theorems and `refusalOffset_of_parseOk`.  Every declaration stays inside
the development's ceiling, `[propext, Quot.sound]`, measured rather than
assumed. -/

/-- info: 'LeanLLVM.Refinement.stage2EventRel_of_walkTraceRow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2EventRel_of_walkTraceRow

/-- info: 'LeanLLVM.Refinement.stage2Records_of_generalRow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Records_of_generalRow

/-- info: 'LeanLLVM.Refinement.RefusalRoute' does not depend on any axioms -/
#guard_msgs in
#print axioms RefusalRoute

/-- info: 'LeanLLVM.Refinement.refusalOffset_of_route' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalOffset_of_route

/-- info: 'LeanLLVM.Refinement.refusalPolicy_of_route' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalPolicy_of_route

/-- info: 'LeanLLVM.Refinement.ParserHalfResidual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ParserHalfResidual

/-- info: 'LeanLLVM.Refinement.parserHalfRows_of_residual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parserHalfRows_of_residual

/-- info: 'LeanLLVM.Refinement.ParserRowsResidual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ParserRowsResidual

/-- info: 'LeanLLVM.Refinement.parserRows_of_residual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parserRows_of_residual

/-- info: 'LeanLLVM.Refinement.residual_of_evidence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms residual_of_evidence

/-- info: 'LeanLLVM.Refinement.evidence_of_residual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evidence_of_residual

/-- info: 'LeanLLVM.Refinement.residual_iff_evidence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms residual_iff_evidence

/-- info: 'LeanLLVM.Refinement.pipeline_satisfies_of_residual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_satisfies_of_residual

end LeanLLVM.Refinement
