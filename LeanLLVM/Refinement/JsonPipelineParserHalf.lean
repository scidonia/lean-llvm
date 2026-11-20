/-
`ParserHalfForOutcome`, characterized: the verdict word's meaning and the three
rows the run owes.

`ParserHalfForOutcome` (`JsonPipelineRefine`) is the assembled pipeline's last
hypothesis: the run's verdict word, its returned memory and the caller's slots
identify the reference parser's answer for the document the arguments name.  This
module states what that identification *is* — `VerdictWord`, the ABI's two words
against `parseBytes`'s two constructors — and then shows that the predicate is
exactly three rows over the run (`ParserHalfRows`), with the parser-side content
of its accepted clause **redundant in both directions**:

* `parserHalf_of_rows`: from the rows, `ParserHalf`'s accepted clause gains the
  tape's input, its decoded value, its validity and its span discipline through
  `decodeTape_correct` and `tape_valid` — the parser's own theorems, not an
  assumption about the run;
* `rows_of_parserHalf`: from `ParserHalf`, each row is one of its conjuncts with
  the derived content dropped.

So `parserHalf_iff_rows` is an equivalence, not a sufficient condition: the
residual is the same obligation with nothing carried that the parser's
correctness theorems already give, and nothing dropped that they do not.

# The rows

At the document `bs`, the verdict `verdict` and the returned memory `m`:

1. **the word** — `VerdictWord bs verdict`: the ABI's word is `1` exactly where
   `parseBytes Limits.default` returns `.ok`, and `0` exactly where it refuses
   (`verdictWord_iff_twoSided` splits the equivalence into the two directions a
   per-route proof discharges, one per verdict the run returns; `verdictWord_unique`
   says the word is the document's, so an outcome cannot supply two readings);
2. **the trace** — on `verdict = 1`, the arena and event reads the record's
   extents name, related by `eventRel` to the tokens of the parser's own tape;
3. **the refusal word** — every word the caller's refusal slot holds is
   `RefusalOffset`'s (`JsonPipelineSpec`), the policy at the document.

`ParserRows` lifts the three to the run's outcome exactly as
`ParserHalfForOutcome` lifts `ParserHalf`, and `parserHalfForOutcome_iff_rows`
carries the equivalence there.  `pipeline_satisfies_of_parserRows` is
`pipeline_satisfies_of_parser` with the characterization applied, so the
specification `Γ_pipeline eventRel tab base` follows from the units' record and
the three rows — at a **general** `eventRel`, which is the shape the record is
stated at.  `parserRows_of_evidence` is stage two's evidence
(`JsonStage2Hsem`'s `Stage2OutcomeEvidence`) read at `stage2EventRel`: the rows are
no stronger than what that producer supplies, and `pipeline_satisfies_of_evidence`
is the whole chain in one application.

**Each value of the word has its parser theorem.**  At `1` an accepted tape is
`parseRef_complete`'s from a `ValidDocument` witness (`verdictWord_one_of_valid`);
at `0` the absence of such a witness refutes acceptance through `parseRef_sound`
(`verdictWord_zero_of_noValid`).  So a per-route proof never has to run the parser:
it supplies the witness or its absence, and the two theorems give the word.

**The theorem at a document.**  `verdictWord_one_of_valid` is applied at `[]` — the
two-entry container the walk's trace row covers (`row_openCloseBracket`) — so the
accepting route's hypotheses are discharged from the document's bytes: the
`ValidDocument` witness at `.array []`, the input's length, and the value's depth
and token count (`emptyArrayValid`, `emptyArrayInput`, `emptyArrayDepth`,
`emptyArrayTokens`), with the word (`emptyArrayWord`) and the parser's tape
(`emptyArrayParses`) both named there.

**What is not here, and why.**  The rows are not proved of any execution: the
word row and the trace row are the walk's answer (its `refusal` bit and its
emitted stream at the parser's token boundaries), and the refusal row is the
offset each refusing path stores.  `LeanLLVM/Refinement/JsonStage2Hsem.lean`
produces them from stage two's evidence; the walk's own trace row
(`WalkTraceRow`, `JsonStage2WalkAlignment`) is the row still owed, and it is the
statement that the walk's `C.events` are the parser's tokens' records.  Nothing
in this module assumes its conclusion, and no clause of the rows repeats a fact
the parser's theorems supply.
-/
import LeanLLVM.Refinement.JsonStage2Hsem

set_option autoImplicit false
set_option maxRecDepth 16000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The parser's two answers

`parseBytes` returns `ParseResult`, which has exactly two constructors, so at
every document the parser either returns a tape or an error — the two answers the
verdict word's two values stand for. -/

/-- The parser accepts the document: it returns a tape. -/
def ParserAccepts (bs : List UInt8) : Prop :=
  ∃ t : Tape, parseBytes Limits.default (ByteString.literal bs) = .ok t

/-- The parser refuses the document: it returns an error, at whichever of the
four constructors applies. -/
def ParserRefuses (bs : List UInt8) : Prop :=
  ∃ e : ParseError, parseBytes Limits.default (ByteString.literal bs) = .error e

/-- **Every document gets one of the two answers.**  `ParseResult` has no third
constructor, so a run whose verdict is `0` says the parser refused and is not
leaving open a document on which the parser did something else. -/
theorem parserAccepts_or_refuses (bs : List UInt8) :
    ParserAccepts bs ∨ ParserRefuses bs := by
  rcases h : parseBytes Limits.default (ByteString.literal bs) with t | e
  · exact Or.inl ⟨t, h⟩
  · exact Or.inr ⟨e, h⟩

/-- A refusal is not an acceptance: the two constructors are disjoint. -/
theorem parserRefuses_not_accepts {bs : List UInt8} (h : ParserRefuses bs) :
    ¬ ParserAccepts bs := by
  obtain ⟨e, he⟩ := h
  rintro ⟨t, ht⟩
  rw [he] at ht
  exact ParseResult.noConfusion ht

/-! ### The verdict word's meaning

`pipeline.h:55-57`: the return is `1` for acceptance and `0` for refusal.  The
predicate below is that sentence at the parser's own vocabulary, and it is
exactly the first conjunct of `ParserHalf`. -/

/-- **The verdict word's meaning**: the ABI's word is `1` exactly where the
reference parser accepts the document. -/
def VerdictWord (bs : List UInt8) (verdict : BitVec 64) : Prop :=
  verdict = 1 ↔ ParserAccepts bs

/-- **The equivalence, as the two directions a per-route proof discharges.**  A
run's post states the word's two values (`verdict = 0 ∨ verdict = 1`), and at
that dichotomy the equivalence is: acceptance on `1` and a refusal on `0`.  Each
is one route's row — the accepting route's and the refusing route's — so neither
has to reason about the word the other returns. -/
theorem verdictWord_iff_twoSided {bs : List UInt8} {verdict : BitVec 64}
    (h : verdict = 0 ∨ verdict = 1) :
    VerdictWord bs verdict ↔
      ((verdict = 1 → ParserAccepts bs) ∧ (verdict = 0 → ParserRefuses bs)) := by
  constructor
  · intro hw
    refine ⟨hw.1, ?_⟩
    intro h0
    rcases parserAccepts_or_refuses bs with hac | hrf
    · exfalso
      have h1 : verdict = 1 := hw.2 hac
      rw [h0] at h1
      exact absurd h1 (by decide)
    · exact hrf
  · rintro ⟨h1, h0⟩
    refine ⟨h1, ?_⟩
    intro hac
    rcases h with hz | ho
    · exact absurd hac (parserRefuses_not_accepts (h0 hz))
    · exact ho

/-- **The word is the document's.**  Two verdicts the post admits and the
parser's answer both identify are the same word: the acceptance equivalence pins
each, so an outcome cannot carry two readings of one document. -/
theorem verdictWord_unique {bs : List UInt8} {v w : BitVec 64}
    (hv : VerdictWord bs v) (hw : VerdictWord bs w)
    (hv0 : v = 0 ∨ v = 1) (hw0 : w = 0 ∨ w = 1) : v = w := by
  rcases hv0 with hv0 | hv0 <;> rcases hw0 with hw0 | hw0
  · rw [hv0, hw0]
  · exfalso
    have hacc : ParserAccepts bs := hw.1 hw0
    have h1 : v = 1 := hv.2 hacc
    rw [hv0] at h1
    exact absurd h1 (by decide)
  · exfalso
    have hacc : ParserAccepts bs := hv.1 hv0
    have h1 : w = 1 := hw.2 hacc
    rw [hw0] at h1
    exact absurd h1 (by decide)
  · rw [hv0, hw0]

/-! ### Each value of the word, and the parser theorem that settles it

`verdictWord_iff_twoSided` splits the equivalence by the word's value; the four
theorems below name what closes each half *from the parser's side*, so a route
proof does not have to run `parseBytes` itself:

* at `1`, an accepted tape — `parseRef_complete` produces one from a `ValidDocument`
  witness within the parser's limits (`verdictWord_one_of_valid`), and the word
  simply *is* the parser's acceptance (`verdictWord_one_iff`);
* at `0`, the absence of a text of the accepted language — `parseRef_sound`'s
  first conjunct turns any accepting tape into such a text, so its absence is a
  refutation of acceptance (`verdictWord_zero_of_noValid`), and the word is the
  parser's refusal (`verdictWord_zero_iff`). -/

/-- The word at `1` is the parser's acceptance. -/
theorem verdictWord_one_iff {bs : List UInt8} :
    VerdictWord bs 1 ↔ ParserAccepts bs :=
  ⟨fun h => h.1 rfl, fun h => ⟨fun _ => h, fun _ => rfl⟩⟩

/-- The word at `0` is the parser's refusal. -/
theorem verdictWord_zero_iff {bs : List UInt8} :
    VerdictWord bs 0 ↔ ¬ ParserAccepts bs := by
  constructor
  · intro hw hac
    have h1 : (0 : BitVec 64) = 1 := hw.2 hac
    exact absurd h1 (by decide)
  · intro hno
    exact ⟨fun h1 => absurd h1 (by decide), fun hac => absurd hac hno⟩

/-- **An accepted document's word, from the parser's completeness theorem.**  A
text of the accepted language within the parser's three limits is parsed to a
tape, so the word row holds at `1` without any fact about the run. -/
theorem verdictWord_one_of_valid {bs : List UInt8} {v : LeanLLVM.JSON.Value}
    (hvalid : ValidDocument (ByteString.literal bs) v)
    (hinput : bs.length ≤ Limits.default.maxInput)
    (hdepth : v.depth ≤ Limits.default.maxDepth)
    (htokens : v.tokenCount ≤ Limits.default.maxTokens) :
    VerdictWord bs 1 := by
  obtain ⟨t, ht, -, -⟩ := parseRef_complete Limits.default
    (ByteString.literal bs) v hvalid hinput hdepth htokens
  exact ⟨fun _ => ⟨t, ht⟩, fun _ => rfl⟩

/-- **A document with no interpretation's word, from the parser's soundness
theorem.**  `parseRef_sound` gives every accepted tape a `ValidDocument` witness
for its input, so a document no interpretation satisfies cannot be accepted, and
the word row holds at `0`. -/
theorem verdictWord_zero_of_noValid {bs : List UInt8}
    (h : ¬ ∃ v : LeanLLVM.JSON.Value, ValidDocument (ByteString.literal bs) v) :
    VerdictWord bs 0 := by
  refine ⟨fun h1 => absurd h1 (by decide), fun hac => ?_⟩
  obtain ⟨t, ht⟩ := hac
  obtain ⟨-, v, hvalid, -⟩ := (parseRef_sound Limits.default (ByteString.literal bs)).1 t ht
  exact (h ⟨v, hvalid⟩).elim

/-! ### The rows at one document, verdict and memory

The three conjuncts of `ParserHalf`, minus what the parser's theorems supply for
an accepted document: the tape's input, its decoded value, that value's validity
and the tape's span discipline.  The middle conjunct therefore names the reads and
the relation only, and `eventRel` stays a parameter (as it is in `ParserHalf`). -/

/-- **The three rows.**  The verdict word, the accepted run's relation to the
parser's tokens at the record's two extents, and the refusal word's policy. -/
def ParserHalfRows (eventRel : EventStreamRel) (bs : List UInt8)
    (verdict : BitVec 64) (m : Mem) (dst ev err ndst' nev' : Nat) : Prop :=
  VerdictWord bs verdict ∧
    (verdict = 1 →
      ∃ (t : Tape) (arena evs : List UInt8),
        parseBytes Limits.default (ByteString.literal bs) = .ok t ∧
        readBytes m dst ndst' = some arena ∧
        readBytes m ev nev' = some evs ∧
        eventRel bs arena evs t.tokens) ∧
    (∀ e : Nat, readBytes m err 8 = some (wordBytes 8 e) → RefusalOffset bs e)

/-- **The rows are the whole of `ParserHalf`'s non-derived content.**  The
accepted clause's four extra conjuncts are `decodeTape_correct`'s and
`tape_valid`'s at the tape the row names: the tape's input is the document, its
decode is a value the accepted language assigns to that document, and the tape's
spans check out.  So the row asks the run for the two buffers and the relation,
and the parser's correctness theorem supplies the meaning. -/
theorem parserHalf_of_rows {eventRel : EventStreamRel} {bs : List UInt8}
    {verdict : BitVec 64} {m : Mem} {dst ev err ndst' nev' : Nat}
    (h : ParserHalfRows eventRel bs verdict m dst ev err ndst' nev') :
    ParserHalf eventRel bs verdict m dst ev err ndst' nev' := by
  obtain ⟨hword, hacc, hpol⟩ := h
  refine ⟨hword, ?_, hpol⟩
  intro hv
  obtain ⟨t, arena, evs, hparse, hdst, hev, hrel⟩ := hacc hv
  obtain ⟨v, hdec, hin, hvalid⟩ :=
    decodeTape_correct Limits.default (ByteString.literal bs) t hparse
  refine ⟨t, v, arena, evs, hparse, hin, hdec, hdst, hev, hrel,
    (tape_valid t v hdec).1, ?_⟩
  rw [← hin]
  exact (tape_valid t v hdec).2

/-- **And nothing in `ParserHalf` is stronger than the rows.**  Each row is one of
the predicate's conjuncts: the word is its first, the trace its accepted clause
with the derived fields dropped, the policy its third.  With `parserHalf_of_rows`
this makes the rows and `ParserHalf` interderivable, so the residual neither
strengthens nor weakens the obligation the pipeline's bridge carries. -/
theorem rows_of_parserHalf {eventRel : EventStreamRel} {bs : List UInt8}
    {verdict : BitVec 64} {m : Mem} {dst ev err ndst' nev' : Nat}
    (h : ParserHalf eventRel bs verdict m dst ev err ndst' nev') :
    ParserHalfRows eventRel bs verdict m dst ev err ndst' nev' := by
  obtain ⟨hword, hacc, hpol⟩ := h
  refine ⟨hword, ?_, hpol⟩
  intro hv
  obtain ⟨t, v, arena, evs, hparse, _, _, hdst, hev, hrel, _, _⟩ := hacc hv
  exact ⟨t, arena, evs, hparse, hdst, hev, hrel⟩

/-- **The characterization.**  The residual is `ParserHalf` with its
parser-derived content dropped, and therefore the same obligation. -/
theorem parserHalf_iff_rows {eventRel : EventStreamRel} {bs : List UInt8}
    {verdict : BitVec 64} {m : Mem} {dst ev err ndst' nev' : Nat} :
    ParserHalf eventRel bs verdict m dst ev err ndst' nev' ↔
      ParserHalfRows eventRel bs verdict m dst ev err ndst' nev' :=
  ⟨rows_of_parserHalf, parserHalf_of_rows⟩

/-! ### The rows at the run's outcome

`ParserRows` is `ParserHalfForOutcome`'s match with the three rows in place of
`ParserHalf`: the document is the one the length argument and the starting memory
name, and the verdict, the returned memory and the three slots are the outcome's
own fields. -/

/-- **The rows at one outcome of the run.** -/
def ParserRows (eventRel : EventStreamRel) (base : Nat) (args : List Value)
    (mem : Mem) (ndst' nev' : Nat) (o : Outcome) : Prop :=
  match o, args with
  | .ret (some (.int 64 verdict)) m,
    [.ptr _, .int 64 n, .ptr _, .ptr _, .ptr _, .ptr _, .int 64 _, .ptr _, .ptr _,
     .int 64 _, .ptr _, .ptr _, .ptr dst, .int 64 _, .ptr _, .ptr ev, .int 64 _,
     .ptr _, .ptr err, .int 64 _] =>
      ∃ bs : List UInt8,
        n.toNat = bs.length ∧
        readBytes mem base n.toNat = some bs ∧
        ParserHalfRows eventRel bs verdict m dst ev err ndst' nev'
  | _, _ => False

/-- **The rows at the outcome give the parser half.** -/
theorem parserHalfForOutcome_of_rows {eventRel : EventStreamRel} {base : Nat}
    {args : List Value} {mem : Mem} {ndst' nev' : Nat} {o : Outcome}
    (h : ParserRows eventRel base args mem ndst' nev' o) :
    ParserHalfForOutcome eventRel base args mem ndst' nev' o := by
  unfold ParserRows at h
  unfold ParserHalfForOutcome
  split at h
  · obtain ⟨bs, hlen, hread, hrows⟩ := h
    exact ⟨bs, hlen, hread, parserHalf_of_rows hrows⟩
  · exact h.elim

/-- **The parser half at the outcome is the rows.**  `parserHalfForOutcome`'s
match is `ParserRows`' match, so the characterization lifts pointwise. -/
theorem rows_of_parserHalfForOutcome {eventRel : EventStreamRel} {base : Nat}
    {args : List Value} {mem : Mem} {ndst' nev' : Nat} {o : Outcome}
    (h : ParserHalfForOutcome eventRel base args mem ndst' nev' o) :
    ParserRows eventRel base args mem ndst' nev' o := by
  unfold ParserHalfForOutcome at h
  unfold ParserRows
  split at h
  · obtain ⟨bs, hlen, hread, hhalf⟩ := h
    exact ⟨bs, hlen, hread, rows_of_parserHalf hhalf⟩
  · exact h.elim

/-- **The characterization, at the outcome.**  The pipeline's last hypothesis is
the three rows and nothing else. -/
theorem parserHalfForOutcome_iff_rows {eventRel : EventStreamRel} {base : Nat}
    {args : List Value} {mem : Mem} {ndst' nev' : Nat} {o : Outcome} :
    ParserHalfForOutcome eventRel base args mem ndst' nev' o ↔
      ParserRows eventRel base args mem ndst' nev' o :=
  ⟨rows_of_parserHalfForOutcome, parserHalfForOutcome_of_rows⟩

/-! ### The specification from the rows

`pipeline_satisfies_of_parser` takes the parser half at each outcome the run
produces; with the characterization the same theorem takes the rows instead, so
the record's post follows from the units' record and the row bundle — at a
general `eventRel`, the shape `Γ_pipeline` is stated at. -/

/-- **The pipeline's specification from the units' record and the rows.** -/
theorem pipeline_satisfies_of_parserRows {calls : Calls} {f : Function}
    {eventRel : EventStreamRel} {tab base : Nat}
    (hunits : Satisfies calls f (Γ_pipeline_units tab base))
    (hrows : ∀ (args : List Value) (mem : Mem) (next : Nat) (o : Outcome)
      (ndst' nev' : Nat),
      pipelineStaging tab base args mem →
      BehFromState calls f (EntryState f args mem next) o →
      pipelineOutputExtents args o ndst' nev' →
      ParserRows eventRel base args mem ndst' nev' o) :
    Satisfies calls f (Γ_pipeline eventRel tab base) :=
  pipeline_satisfies_of_parser hunits
    (fun args mem next o ndst' nev' hst hbeh hext =>
      parserHalfForOutcome_of_rows (hrows args mem next o ndst' nev' hst hbeh hext))

/-! ### The rows are inhabited by stage two's evidence

`Stage2OutcomeEvidence` (`JsonStage2Hsem`) is what the stage-2 boundary supplies at
a run's outcome; it is stated at `stage2EventRel` and carries the trace as the
record list `Stage2Records` relates to the tape's tokens.  The rows name the
relation `eventRel` and not the record list, so the evidence supplies them; this
is the bridge between the two producers' vocabularies, not a new obligation. -/

/-- **The evidence supplies the rows.**  The accepted branch's word row is the
equivalence at `1`, its trace row the evidence's own tape and relation
(`stage2EventRel_of_records`), and its policy the accept path's
(`refusalOffset_of_parseOk`, which needs the stage's passed test — the evidence's
own `utf8WinPrefix`).  The refused branch's word row is the equivalence at `0` by
the parser's refusal, its trace row vacuous, and its policy the evidence's. -/
theorem parserRows_of_evidence {base : Nat} {args : List Value} {mem : Mem}
    {ndst' nev' : Nat} {o : Outcome}
    (h : Stage2OutcomeEvidence base args mem ndst' nev' o) :
    ParserRows stage2EventRel base args mem ndst' nev' o := by
  unfold Stage2OutcomeEvidence at h
  unfold ParserRows
  split at h
  · obtain ⟨bs, hlen, hread, hcase⟩ := h
    refine ⟨bs, hlen, hread, ?_⟩
    rcases hcase with
      ⟨hv, hutf8, t, rs, arena, evs, hparse, hdst, hev, hrecs, hrel⟩ |
      ⟨hv, hpol, hno⟩
    · refine ⟨⟨fun _ => ⟨t, hparse⟩, fun _ => hv⟩, ?_, ?_⟩
      · intro _
        exact ⟨t, arena, evs, hparse, hdst, hev,
          stage2EventRel_of_records hrecs hrel⟩
      · intro e _
        exact refusalOffset_of_parseOk hparse hutf8
    · refine ⟨⟨?_, fun hac => absurd hac hno⟩, ?_, hpol⟩
      · intro h1
        rw [hv] at h1
        exact absurd h1 (by decide)
      · intro h1
        rw [hv] at h1
        exact absurd h1 (by decide)
  · exact h.elim

/-- **The pipeline's specification from stage two's evidence.**  The evidence's
producer is `JsonStage2Hsem`'s; this theorem is its statement at the terminal
bridge, so the chain from the walk's evidence to `Γ_pipeline` is one application
rather than a re-derivation at each consumer. -/
theorem pipeline_satisfies_of_evidence {calls : Calls} {f : Function}
    {tab base : Nat}
    (hunits : Satisfies calls f (Γ_pipeline_units tab base))
    (hev : ∀ (args : List Value) (mem : Mem) (next : Nat) (o : Outcome)
      (ndst' nev' : Nat),
      pipelineStaging tab base args mem →
      BehFromState calls f (EntryState f args mem next) o →
      pipelineOutputExtents args o ndst' nev' →
      Stage2OutcomeEvidence base args mem ndst' nev' o) :
    Satisfies calls f (Γ_pipeline stage2EventRel tab base) :=
  pipeline_satisfies_of_parserRows hunits
    (fun args mem next o ndst' nev' hst hbeh hext =>
      parserRows_of_evidence (hev args mem next o ndst' nev' hst hbeh hext))

/-! ### The rows are inhabited

Two documents, one the parser accepts and one it refuses, at a memory holding the
arena's and the event stream's single byte and nothing at the refusal slot.  The
accepted document's tape comes from `parseRef_complete` at the accepted
language's own witness; the refused one's refusal is `parseBytes`'s
byte-order-mark branch.  So neither the word row nor the trace row is a predicate
no document can meet, and the refusal row is discharged by the slot's absence.

The relation is the one-byte report: the arena and the event stream are the bytes
the memory holds at the two extents the rows are stated at. -/

/-- The `null` document's accepted-language witness: the value `null` at the
four-byte literal span. -/
theorem nullValid :
    ValidDocument (ByteString.literal nullDoc) (.null : LeanLLVM.JSON.Value) :=
  ⟨⟨0, 4, by decide, ValueAt.null (by unfold HasPrefix; decide), by decide⟩,
    charPolicy_null⟩

/-- The memory the two instances are stated at: the arena's byte at `8`, the
event stream's at `16`, and nothing at the refusal slot `24`. -/
def demoMem : Mem := [(8, 0x07), (16, 0x01)]

/-- **An accepting instance.**  The parser returns a tape for `null`, so the word
row holds at `1`; the trace row is that tape with the memory's two bytes; and the
refusal slot holds no word, so the policy is vacuous. -/
theorem nullRows :
    ParserHalfRows (fun _ _ _ _ => True) nullDoc 1 demoMem 8 16 24 1 1 := by
  obtain ⟨t, ht, -, -⟩ := parseRef_complete Limits.default
    (ByteString.literal nullDoc) (.null : LeanLLVM.JSON.Value) nullValid
    (by decide) (by decide) (by decide)
  refine ⟨⟨fun _ => ⟨t, ht⟩, fun _ => rfl⟩, ?_, ?_⟩
  · intro _
    exact ⟨t, [0x07], [0x01], ht, by decide, by decide, trivial⟩
  · intro e h
    have hnone : readBytes demoMem 24 8 = none := by decide
    rw [hnone] at h
    cases h

/-- A byte-order mark, which `parseBytes` refuses at its own branch. -/
def bomDoc : List UInt8 := [0xEF, 0xBB, 0xBF]

/-- The parser's refusal at the byte-order mark. -/
theorem bomRefused :
    parseBytes Limits.default (ByteString.literal bomDoc) =
      .error (.invalid .byteOrderMark) := by
  decide

/-- The byte-order mark is not accepted: the refusal constructor settles it. -/
theorem bomNoParse : ¬ ParserAccepts bomDoc := by
  rintro ⟨t, h⟩
  rw [bomRefused] at h
  exact ParseResult.noConfusion h

/-- **A refusing instance.**  The word row holds at `0` because the parser refuses
the document, the trace row is vacuous on the refusing verdict, and the refusal
slot again holds no word. -/
theorem bomRows :
    ParserHalfRows (fun _ _ _ _ => True) bomDoc 0 demoMem 8 16 24 1 1 := by
  refine ⟨⟨fun h1 => absurd h1 (by decide),
    fun hac => absurd hac bomNoParse⟩, ?_, ?_⟩
  · intro h1
    exact absurd h1 (by decide)
  · intro e h
    have hnone : readBytes demoMem 24 8 = none := by decide
    rw [hnone] at h
    cases h

/-! ### The accepted container document `[]`

The two instances above are a scalar and a refusal.  The smallest *container
document* the walk's trace rows cover is `[]`: `JsonStage2WalkRowSteps`'
`row_openCloseBracket` is the row at a `DelimiterLastDocument G 0x5B 0x5D`, whose
bytes are `G.bs = [0x5B, 0x5D]` (`DelimiterLastDocument.bs`).  At those bytes the
word's accepted value is `verdictWord_one_of_valid`'s, and its hypotheses are all
about the document: the accepting route supplies the value, the depth, the token
count and the input's length, and the theorem is the word.  Nothing in the route
reads a run or runs the parser.

Every hypothesis is proved from the bytes rather than assumed: the grammar's
`array` production at `0` with the empty body at the byte after the opener and
the closing bracket at `1`; the policy, vacuous on the empty element list; and the
three limits, which the value's measures and the input's length make `1`, `2` and
`2`.  The parser's tape is named as well (`emptyArrayParses`), so the word is not
the only reading of the document here — it is the reading the accepted language
gives. -/

/-- The document `[]`. -/
def emptyArrayDoc : List UInt8 := [0x5B, 0x5D]

/-- **The accepted-language witness at `[]`.**  `RfcText` is the grammar's
`array` production: the opener at `0`, the empty body at `1`, the closing bracket
at `1`, and the text ending at `2`.  `Policy` has no element to check. -/
theorem emptyArrayValid :
    ValidDocument (ByteString.literal emptyArrayDoc) (.array ([] : List LeanLLVM.JSON.Value)) := by
  have hclose : (ByteString.literal emptyArrayDoc)[1]? = some 0x5D := by decide
  have hskip : skipFrom (ByteString.literal emptyArrayDoc) (0 + 1) = 1 := by decide
  refine ⟨⟨0, 2, by decide, ?_, by decide⟩, ?_⟩
  · have hb : ArrBody .rfc (ByteString.literal emptyArrayDoc)
        (skipFrom (ByteString.literal emptyArrayDoc) (0 + 1)) [] 1 := by
      rw [hskip]
      exact ArrBody.empty hclose
    exact ValueAt.array (i := 0) (k := 1) (vs := []) (by decide) hb (by decide)
  · exact (charPolicy_array []).mpr (by simp)

/-- The input limit at `[]`: two bytes. -/
theorem emptyArrayInput : emptyArrayDoc.length ≤ Limits.default.maxInput := by
  decide

/-- The depth limit at `[]`: the empty array is one level. -/
theorem emptyArrayDepth :
    (Value.array ([] : List LeanLLVM.JSON.Value)).depth ≤ Limits.default.maxDepth := by
  decide

/-- The token limit at `[]`: the two container tokens. -/
theorem emptyArrayTokens :
    (Value.array ([] : List LeanLLVM.JSON.Value)).tokenCount ≤ Limits.default.maxTokens := by
  decide

/-- **The word at `[]`, through the parser's completeness theorem.**  The four
document facts above are exactly `verdictWord_one_of_valid`'s hypotheses, so the
accepted route's word row is one application. -/
theorem emptyArrayWord : VerdictWord emptyArrayDoc 1 :=
  verdictWord_one_of_valid emptyArrayValid emptyArrayInput emptyArrayDepth
    emptyArrayTokens

/-- **The parser's own answer at `[]`**: the tape `parseRef_complete` produces,
its input, and its decode.  The word above and this tape are the same document's,
so the accepting route's witness and the parser's reading agree by construction
rather than by a second argument. -/
theorem emptyArrayParses :
    ∃ t : Tape,
      parseBytes Limits.default (ByteString.literal emptyArrayDoc) = .ok t ∧
      t.input = ByteString.literal emptyArrayDoc ∧
      decodeTape t = some (.array ([] : List LeanLLVM.JSON.Value)) :=
  parseRef_complete Limits.default (ByteString.literal emptyArrayDoc)
    (.array ([] : List LeanLLVM.JSON.Value)) emptyArrayValid emptyArrayInput emptyArrayDepth
    emptyArrayTokens

/-- The acceptance `VerdictWord`'s `1` stands for, read from that tape. -/
theorem emptyArrayAccepts : ParserAccepts emptyArrayDoc := by
  obtain ⟨t, ht, -, -⟩ := emptyArrayParses
  exact ⟨t, ht⟩

/-- The same acceptance read back from the word (`verdictWord_one_iff`), so the
word row and the tape are one answer at this document. -/
theorem emptyArrayWord_accepts : ParserAccepts emptyArrayDoc :=
  verdictWord_one_iff.mp emptyArrayWord

/-! ### Axiom footprints

The parser-side content is `decodeTape_correct`'s and `tape_valid`'s; the
characterization itself is definitional plus those two.  Every declaration sits at
the development's ceiling, `[propext, Quot.sound]`, measured rather than assumed.
-/

/-- info: 'LeanLLVM.Refinement.ParserAccepts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ParserAccepts

/-- info: 'LeanLLVM.Refinement.ParserRefuses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ParserRefuses

/-- info: 'LeanLLVM.Refinement.parserAccepts_or_refuses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parserAccepts_or_refuses

/-- info: 'LeanLLVM.Refinement.parserRefuses_not_accepts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parserRefuses_not_accepts

/-- info: 'LeanLLVM.Refinement.VerdictWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms VerdictWord

/-- info: 'LeanLLVM.Refinement.verdictWord_iff_twoSided' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms verdictWord_iff_twoSided

/-- info: 'LeanLLVM.Refinement.verdictWord_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms verdictWord_unique

/-- info: 'LeanLLVM.Refinement.ParserHalfRows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ParserHalfRows

/-- info: 'LeanLLVM.Refinement.parserHalf_of_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parserHalf_of_rows

/-- info: 'LeanLLVM.Refinement.rows_of_parserHalf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rows_of_parserHalf

/-- info: 'LeanLLVM.Refinement.ParserRows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ParserRows

/-- info: 'LeanLLVM.Refinement.parserHalfForOutcome_of_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parserHalfForOutcome_of_rows

/-- info: 'LeanLLVM.Refinement.rows_of_parserHalfForOutcome' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rows_of_parserHalfForOutcome

/-- info: 'LeanLLVM.Refinement.pipeline_satisfies_of_parserRows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_satisfies_of_parserRows

/-- info: 'LeanLLVM.Refinement.parserRows_of_evidence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parserRows_of_evidence

/-- info: 'LeanLLVM.Refinement.pipeline_satisfies_of_evidence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_satisfies_of_evidence

/-- info: 'LeanLLVM.Refinement.nullValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nullValid

/-- info: 'LeanLLVM.Refinement.demoMem' does not depend on any axioms -/
#guard_msgs in
#print axioms demoMem

/-- info: 'LeanLLVM.Refinement.nullRows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nullRows

/-- info: 'LeanLLVM.Refinement.bomDoc' does not depend on any axioms -/
#guard_msgs in
#print axioms bomDoc

/-- info: 'LeanLLVM.Refinement.bomRefused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bomRefused

/-- info: 'LeanLLVM.Refinement.bomNoParse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bomNoParse

/-- info: 'LeanLLVM.Refinement.bomRows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bomRows

/-- info: 'LeanLLVM.Refinement.emptyArrayDoc' does not depend on any axioms -/
#guard_msgs in
#print axioms emptyArrayDoc

/-- info: 'LeanLLVM.Refinement.emptyArrayValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms emptyArrayValid

/-- info: 'LeanLLVM.Refinement.emptyArrayInput' does not depend on any axioms -/
#guard_msgs in
#print axioms emptyArrayInput

/-- info: 'LeanLLVM.Refinement.emptyArrayDepth' does not depend on any axioms -/
#guard_msgs in
#print axioms emptyArrayDepth

/-- info: 'LeanLLVM.Refinement.emptyArrayTokens' does not depend on any axioms -/
#guard_msgs in
#print axioms emptyArrayTokens

/-- info: 'LeanLLVM.Refinement.emptyArrayWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms emptyArrayWord

/-- info: 'LeanLLVM.Refinement.emptyArrayParses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms emptyArrayParses

/-- info: 'LeanLLVM.Refinement.emptyArrayAccepts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms emptyArrayAccepts

/-- info: 'LeanLLVM.Refinement.emptyArrayWord_accepts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms emptyArrayWord_accepts

/-- info: 'LeanLLVM.Refinement.verdictWord_one_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms verdictWord_one_iff

/-- info: 'LeanLLVM.Refinement.verdictWord_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms verdictWord_zero_iff

/-- info: 'LeanLLVM.Refinement.verdictWord_one_of_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms verdictWord_one_of_valid

/-- info: 'LeanLLVM.Refinement.verdictWord_zero_of_noValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms verdictWord_zero_of_noValid

end LeanLLVM.Refinement
