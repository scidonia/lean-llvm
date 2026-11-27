/-
The release theorem's remaining number-extent assumption, stated as a named
premise.

The release target is one Lean call `valueOf doc` that terminates, returns the
reference parser's canonical value or its parse error, and is competitive with
native.  Its event route ends at
`JsonEventBridgeFinal.eventsOfBytes_valueOfEvents_scalar`, whose `hrel :
Stage2Records bs arena rs toks` is built from the walk's number arm.  That arm's
number record takes, as its first premise, that the span the stage-1 scanner
hands to `num_fast_el1` is the grammar token's extent.  Most of that premise is a
theorem about the decoder — `JsonNumberPremises.parse_number_maximal_run` — and
what the walk alone cannot supply is one equation; this module states that
equation as an assumption of the release theorem, and proves its consumer.

## What is no longer assumed

`TokenBytes`'s number row names `numRunFrom`'s run: the decoder's number guard
sets `lex := numRunFrom bs i` and emits the span `⟨i, i + lex.length⟩`, and
`decodeTokenBytes_aux` carries that equality into the per-token predicate.  So
`JsonNumberPremises.tape_number_maximal_run` proves, from `decodeTape` and the
tape's token list, that the span's bytes are the maximal run; its parse-facing
form `parse_number_maximal_run` (and `parse_number_maximal_run_literal`) states it
for a document `parseBytes` accepts, and `tape_number_start_le_stop` gives the
span's well-formedness.  The maximal-run half of the extent is therefore a
theorem, not a hypothesis, and this module does not restate it.

## The assumption

`NumberExtentAssumed bs sp q` is the release theorem's assumption-list entry for
one number token.  `sp` is the parser's span for the token, `q` the stop the
stage-1 scalar scan reports for it, and `bs` the document.  Its single field is

* `stop_eq` — the scan's stop is the span's stop, so the scanner hands over the
  whole token rather than a stopping point of its own.

That is the emitter/staging piece: `q` is a walk value read from the staged lane
table, the tape's `sp.stop` is the decoder's, and joining them is what the
alignment and the stage-1 emitter owe.  `NumberExtentAssumed.ofExtent` records
that every whole extent implies the assumption (`bs` is retained as a parameter so
the release theorem's assumption list keeps its shape); the converse,
`.toExtent_of_tape`, composes the assumption with the decoder's theorems above.

## The consumer

`numberArmPremises_of_extentAssumed` is the connection, as a theorem.  Given a
document (`decodeTape t = some v`, `t.input = ByteString.literal bs`), a number
token of its tape, the assumption at that token with the scan's stop, and the
walk's lane being the span's start, it yields the number arm's five premises as
one existential: the slice the walk reads, a `StrtodReader.reader` witness at
it, that decimal's well-formedness, the stop equation `q = lane + lex.length`,
and the payload equality `numFastEmitted … = strtodSpec …`.  These are precisely
`JsonStage2NoEventWalkDispatchValueArmsB.stage2NoEventWalkValueNumber`'s `hlex`,
`hread`, `hwf`, `hstop` and `hslice`, and the event arm's span/lexeme and `hev`
data through `JsonStage2WalkRowArms.payloadRevolution_number_arm`.  The extent it
passes to the arm is `hassume.toExtent_of_tape …`, whose maximal-run conjunct is
`tape_number_maximal_run` and whose well-formedness conjunct is
`tape_number_start_le_stop`: the assumption supplies `stop_eq` and nothing else.
`numberArmPremises_of_parseAssumed` is the same consumer from a `parseBytes`
acceptance, reading the run through `parse_number_maximal_run_literal`.

## The discharge path

The stop equation is not derivable from the tree's current definitions.
`WalkAlign` (`LeanLLVM/Refinement/JsonStage2WalkAlignment.lean:313`) pins each
token's *start* to `entryPos G k` and the next entry to the next token's start;
it never states that the next entry is the current token's *stop*.  The clause to
add is `WalkAlignStops`, defined in `JsonNumberPremises`: for every token with a
successor, the successor's entry position is the token's stop.  It belongs as a
further conjunct of `WalkAlign` in `LeanLLVM/Refinement/JsonStage2WalkAlignment.lean`
— at the token-start reading, which is the stream exactly when no token is a
string; under `WalkAlignQuoted` the clause is read at the number's start lane
rather than at a token index.  Whether the staged stream places an entry at the
digit-run end of a number — rather than only at the next structural or scalar
byte — is exactly the emitter question below.

Initialising the clause is the stage-1 emitter's job, and that is the part the
tree does not have.  `WalkGeom.entries`
(`LeanLLVM/Refinement/JsonStage2WalkScopeGeom.lean:21`, field `entries` at line
70) reads the staged lane table; `entryPos` (same file, line 891) is a lane
read.  The stage-1 emitter that fills those lanes (`entryMask64`'s lanes,
`JsonEntSpec`) has no Lean semantics anywhere in the tree, and what it produces
is entry *positions*, not extents.  Discharging the assumption therefore needs
the emitter's *stop* side — the statement that the lane after a number's start
lane is the run's stop — and that side would have to be **proved** (a body proof
of the emitter, composed with `parseValue`'s token list) or **measured** (an
identity or a capture of the emitted object bound to `decodeTape`'s tokens).
Only then does `WalkAlign` plus the decoder's spans give `NumberExtentAssumed`
at every number token.  The last token is outside `WalkAlignStops`: its stop is
the scalar scan's `q`, obtained from the document, and joining it to the tape is
the final piece of the same discharge.

## What it is not

This module does not prove the stop equation, and nothing in it should be read as
a claim that the tree does.  `NumberExtentAssumed` is a *hypothesis* of the
release theorem — the same kind of named premise as its compiler and ABI steps —
not a theorem about the scanner, the emitter, or `WalkAlign`.  The maximal-run
half is not part of it: that is `JsonNumberPremises.parse_number_maximal_run`, a
theorem about the decoder.  The companion accumulator premise is stated
separately; this module is the extent half alone.
-/
import LeanLLVM.Refinement.JsonNumberPremises

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.StrtodRefine
open ByteString

/-! ### The assumption

The release theorem's assumption-list entry at one number token: the walk's stop
is the tape token's stop, and nothing else. -/

/-- **The release theorem's remaining number-extent assumption.**  At the number
token `sp` of the document `bs`, with the stage-1 scalar scan's stop `q`, the scan
stops at the span's stop.  The maximal-run half of the extent is the decoder's
(`JsonNumberPremises.tape_number_maximal_run`), so it is not a field. -/
structure NumberExtentAssumed (bs : List UInt8) (sp : Span) (q : Nat) : Prop where
  /-- The scan's stop is the token's. -/
  stop_eq : q = sp.stop

/-- Every whole extent implies the narrowed assumption. -/
theorem NumberExtentAssumed.ofExtent {bs : List UInt8} {sp : Span} {q : Nat}
    (h : NumberTokenExtentAt bs sp q) : NumberExtentAssumed bs sp q :=
  ⟨h.stop_eq⟩

/-- **The assumption plus the decoder's theorems is the extent.**  The maximal-run
conjunct is `tape_number_maximal_run` and the well-formedness conjunct is
`tape_number_start_le_stop`; the assumption supplies `stop_eq`. -/
theorem NumberExtentAssumed.toExtent_of_tape {t : Tape} {v : JSON.Value}
    {bs : List UInt8} {sp : Span} {q : Nat}
    (h : NumberExtentAssumed bs sp q) (hdec : decodeTape t = some v)
    (hin : t.input = ByteString.literal bs) (htok : Token.number sp ∈ t.tokens) :
    NumberTokenExtentAt bs sp q :=
  ⟨tape_number_start_le_stop hdec hin htok, h.stop_eq,
    tape_number_maximal_run hdec hin htok⟩

/-- **The assumption plus a `parseBytes` acceptance is the extent.**  The
maximal-run conjunct is `parse_number_maximal_run_literal` at the document's byte
list; the decoder's equation comes from `decodeTape_correct`. -/
theorem NumberExtentAssumed.toExtent_of_parse {l : Limits} {t : Tape}
    {bs : List UInt8} {sp : Span} {q : Nat}
    (h : NumberExtentAssumed bs sp q)
    (hparse : parseBytes l (ByteString.literal bs) = .ok t)
    (htok : Token.number sp ∈ t.tokens) :
    NumberTokenExtentAt bs sp q := by
  obtain ⟨v, hdec, hin, -⟩ := decodeTape_correct l (ByteString.literal bs) t hparse
  exact ⟨tape_number_start_le_stop hdec hin htok, h.stop_eq,
    parse_number_maximal_run_literal hparse htok⟩

/-! ### The consumer

The wrapper the release theorem uses: the document's facts plus the assumption
at its number token give the number arm's five premises. -/

/-- **Supplying the assumption at a document yields the number arm's five
premises.**  `hdec` and `hin` make `t` the document's tape; `htok` selects a
number token; `hassume` is the release theorem's assumption at that token with
the scan's stop; `hlane` places the walk's lane at the span's start.  The
conclusion is `numberArmPremises_of_extent`'s: the slice, a reader witness, its
well-formedness, the stop equation and the payload equality. -/
theorem numberArmPremises_of_extentAssumed {t : Tape} {v : JSON.Value}
    {bs : List UInt8} {sp : Span} {q lane : Nat}
    (hdec : decodeTape t = some v) (hin : t.input = ByteString.literal bs)
    (htok : Token.number sp ∈ t.tokens) (hassume : NumberExtentAssumed bs sp q)
    (hlane : lane = sp.start) :
    ∃ (lex : List UInt8) (d : Decimal),
      (bs.drop lane).take (q - lane) = lex ∧
        StrtodReader.reader (ByteString.literal lex) = some d ∧
          d.wellFormed ∧
            q = lane + lex.length ∧
              (numFastEmitted (ByteString.literal lex)).toBits =
                (strtodSpec d).toBits :=
  numberArmPremises_of_extent hdec hin htok
    (hassume.toExtent_of_tape hdec hin htok) hlane

/-- **Supplying the assumption at a parsed document yields the five premises.**
The same wrapper from a `parseBytes` acceptance: `decodeTape_correct` supplies the
decoder equation, and the extent's maximal-run conjunct is
`parse_number_maximal_run_literal`. -/
theorem numberArmPremises_of_parseAssumed {l : Limits} {t : Tape}
    {bs : List UInt8} {sp : Span} {q lane : Nat}
    (hparse : parseBytes l (ByteString.literal bs) = .ok t)
    (htok : Token.number sp ∈ t.tokens) (hassume : NumberExtentAssumed bs sp q)
    (hlane : lane = sp.start) :
    ∃ (lex : List UInt8) (d : Decimal),
      (bs.drop lane).take (q - lane) = lex ∧
        StrtodReader.reader (ByteString.literal lex) = some d ∧
          d.wellFormed ∧
            q = lane + lex.length ∧
              (numFastEmitted (ByteString.literal lex)).toBits =
                (strtodSpec d).toBits := by
  obtain ⟨v, hdec, hin, -⟩ := decodeTape_correct l (ByteString.literal bs) t hparse
  exact numberArmPremises_of_extentAssumed hdec hin htok hassume hlane

/-! ### Axiom footprints -/

#print axioms NumberExtentAssumed.ofExtent
#print axioms NumberExtentAssumed.toExtent_of_tape
#print axioms NumberExtentAssumed.toExtent_of_parse
#print axioms numberArmPremises_of_extentAssumed
#print axioms numberArmPremises_of_parseAssumed

end LeanLLVM.Refinement
