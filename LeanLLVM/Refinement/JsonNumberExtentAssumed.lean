/-
The release theorem's number-extent assumption, stated as a named premise.

The release target is one Lean call `valueOf doc` that terminates, returns the
reference parser's canonical value or its parse error, and is competitive with
native.  Its event route ends at
`JsonEventBridgeFinal.eventsOfBytes_valueOfEvents_scalar`, whose `hrel :
Stage2Records bs arena rs toks` is built from the walk's number arm.  That arm's
number record takes, as its first premise, that the span the stage-1 scanner
hands to `num_fast_el1` is the grammar token's extent.  The premise is not
derived by the walk; this module states it as an assumption of the release
theorem, in the form the theorem's assumption list cites, and proves its
consumer.

`JsonNumberPremises` states the same fact as `NumberTokenExtentAt` and proves
what the tape and reader alone allow.  This module adds the release-side
packaging: a structure whose fields are exactly those three clauses, the wrapper
from it plus a document to the number arm's five premises, and the discharge
path in prose.  It changes no definition and restates no theorem: the proofs
below are the premises module's lemmas under the assumption's name.

## The assumption

`NumberExtentAssumed bs sp q` is the release theorem's assumption list entry for
one number token.  `sp` is the parser's span for the token, `q` the stop the
stage-1 scalar scan reports for it, and `bs` the document.  The three fields are
exactly the extent clauses:

* `start_le_stop` — the span is well formed;
* `stop_eq` — the scan's stop is the span's stop, so the scanner hands over the
  whole token rather than a stopping point of its own;
* `slice` — the document bytes at the span are the maximal `NumConstituent` run
  `numRunFrom` from the span's start, so the token is RFC 8259 §6's number and
  not merely a prefix `numLexB` accepts.

Together they say the scanner hands over precisely the grammar token's extent.
`NumberExtentAssumed.toExtent` and `.ofExtent` identify the structure with
`NumberTokenExtentAt`, so the memory of the assumption is the premises module's
statement and nothing narrower.

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
data through `JsonStage2WalkRowArms.payloadRevolution_number_arm`.  The body of
the wrapper is `numberArmPremises_of_extent` applied to `hassume.toExtent`; the
assumption is what the call site supplies, not something the wrapper finds.

## The discharge path

The extent is not derivable from the tree's current definitions.  `WalkAlign`
(`LeanLLVM/Refinement/JsonStage2WalkAlignment.lean:313`) pins each token's
*start* to `entryPos G k` and the next entry to the next token's start; it never
states that the next entry is the current token's *stop*.  The clause to add is
`WalkAlignStops`, defined in `JsonNumberPremises`: for every token with a
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
Only then does `WalkAlign` plus `decodeTape`'s spans give `NumberExtentAssumed`
at every number token.  The last token is outside `WalkAlignStops`: its stop is
the scalar scan's `q`, obtained from the document, and joining it to the tape is
the final piece of the same discharge.

## What it is not

This module does not prove the extent, and nothing in it should be read as a
claim that the tree does.  `NumberExtentAssumed` is a *hypothesis* of the release
theorem — the same kind of named premise as its compiler and ABI steps — not a
theorem about the scanner, the emitter, or `WalkAlign`.  It is not derivable
from `decodeTape`, from `WalkAlign`, or from any emitted body in the tree, and
`WalkAlignStops` is only a *proposed* clause here: the alignment in this
checkout does not carry it.  The companion accumulator premise is stated
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

The release theorem's assumption-list entry at one number token, with the
premises module's statement recovered by a projection. -/

/-- **The release theorem's number-extent assumption.**  At the number token
`sp` of the document `bs`, with the stage-1 scalar scan's stop `q`, the scanner
hands over precisely the grammar token's extent: the span is well formed, the
scan stops at the span's stop, and the span's bytes are the maximal number run
from its start.  The three fields are exactly `NumberTokenExtentAt`'s clauses,
named so the release theorem's assumption list can cite one. -/
structure NumberExtentAssumed (bs : List UInt8) (sp : Span) (q : Nat) : Prop where
  /-- The span is well formed. -/
  start_le_stop : sp.start ≤ sp.stop
  /-- The scan's stop is the token's. -/
  stop_eq : q = sp.stop
  /-- The span holds the maximal number run. -/
  slice : (bs.drop sp.start).take (sp.stop - sp.start) =
    (numRunFrom (ByteString.literal bs) sp.start).data.toList

/-- The assumption is the premises module's `NumberTokenExtentAt`. -/
theorem NumberExtentAssumed.toExtent {bs : List UInt8} {sp : Span} {q : Nat}
    (h : NumberExtentAssumed bs sp q) : NumberTokenExtentAt bs sp q :=
  ⟨h.start_le_stop, h.stop_eq, h.slice⟩

/-- The premises module's statement is the assumption; the two are the same
proposition. -/
theorem NumberExtentAssumed.ofExtent {bs : List UInt8} {sp : Span} {q : Nat}
    (h : NumberTokenExtentAt bs sp q) : NumberExtentAssumed bs sp q :=
  ⟨h.1, h.2.1, h.2.2⟩

/-- The assumption and the premises module's definition are equivalent. -/
theorem NumberExtentAssumed.extent_iff {bs : List UInt8} {sp : Span} {q : Nat} :
    NumberExtentAssumed bs sp q ↔ NumberTokenExtentAt bs sp q :=
  ⟨NumberExtentAssumed.toExtent, NumberExtentAssumed.ofExtent⟩

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
  numberArmPremises_of_extent hdec hin htok hassume.toExtent hlane

/-! ### Axiom footprints -/

#print axioms NumberExtentAssumed.toExtent
#print axioms NumberExtentAssumed.ofExtent
#print axioms NumberExtentAssumed.extent_iff
#print axioms numberArmPremises_of_extentAssumed

end LeanLLVM.Refinement
