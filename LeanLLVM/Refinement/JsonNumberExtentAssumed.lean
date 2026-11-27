/-
The release theorem's remaining number-extent assumption, stated as a named
premise.

The release target is one Lean call `valueOf doc` that terminates, returns the
reference parser's canonical value or its parse error, and is competitive with
native.  Its event route ends at
`JsonEventBridgeFinal.eventsOfBytes_valueOfEvents_scalar`, whose `hrel :
Stage2Records bs arena rs toks` is built from the walk's number arm.  That arm's
number record takes, as its first premise, that the slice the walk hands to
`num_fast_el1` is the grammar token's extent.  Most of that premise is a
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
walk's scalar scan reports for it, and `bs` the document.  Its single field is

* `stop_eq` — the scan's stop is the span's stop, so the scanner hands over the
  whole token rather than a stopping point of its own.

That is the staging piece: `q` is the stage-2 scan's stop over the staged
document, the tape's `sp.stop` is the decoder's, and joining them is what the
scan's whitespace rule and the document's gaps owe — not the entry table, which
places run starts (`JsonStage2WalkStopsGap`).  `NumberExtentAssumed.ofExtent`
records that every whole extent implies the assumption (`bs` is retained as a
parameter so the release theorem's assumption list keeps its shape); the
converse, `.toExtent_of_tape`, composes the assumption with the decoder's
theorems above.

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

## The discharge path, and why the recorded stop clause is not it

The stop equation is not derivable from the tree's definitions, and the clause an
earlier reading of this module recorded — `WalkAlignStops` in
`JsonNumberPremises`, a conjunct saying the successor entry is the token's stop —
is not merely unproved: it is false.  `WalkAlign` already forces the byte at
every entry to announce a token class (`WalkAlign.class`), and no whitespace byte
has a class.  A token followed by whitespace ends on a whitespace byte, so its
stop cannot be the successor entry.  `[1 ,2]` is a valid document at which
`WalkAlign` holds and `WalkAlignStops` fails: the entry stream is
`[0, 1, 3, 4, 5]`, the first number's stop is `2`, and its successor entry is the
comma at `3`.  `JsonStage2WalkStopsGap` proves the refutation
(`WalkAlign.not_stops_of_isSpace`) and the corrected clause.

The stage-1 model confirms the shape rather than repairing it: `JsonEntSpec`'s
`entry_mask_eq` makes an entry bit an unescaped quote, a delimiter outside a
string, or a scalar run's first lane, and `positionsOf` turns those into
positions.  Nothing in that definition names a run's last lane, so the emitter
can supply neither the false clause nor the true one.

What the stop equation needs is the document's gap: between a token's stop and
the walk's `%cond` bound the bytes are whitespace.  `JsonStage2WalkStopsGap`
states that clause (`StopToEntrySpace`, `WalkAlignGaps`) and proves its consumers:
`stop_eq_of_gap_loop` and `stop_eq_of_gap_direct` derive the scan's stop, and
`numberExtentAssumed_of_gap_loop`/`_direct` yield `NumberExtentAssumed` itself.
The residue is the clause's initialisation, and it is the parser's rather than
the emitter's: `parseBytes` skips whitespace between tokens (`spaceRun_all`,
`skipFrom_space`, which `TapeCorrect`'s decoder proof already uses), but the tape
predicates record only `checkSpans`'s `prev ≤ s.start` and each token's own bytes
(`TokenBytes`).  A theorem that a parse-accepted tape's inter-token gaps are
whitespace is the exact missing premise.

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
