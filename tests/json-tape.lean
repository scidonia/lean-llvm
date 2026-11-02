/-
The tape scenario: hand-built tapes, none produced by the parser, decoded
against their own input.

A tape is source-backed: a token names a span and the meaning is read from the
bytes the span indexes.  A tape whose span does not point at the bytes its
token kind denotes, whose tokens leave a non-whitespace gap, or whose spans
overlap is not valid, however plausible its token kinds look.  `decodeTape`
returns `none` for a tape it cannot read; `spansWellFormed` decides the span
discipline alone.

Elaborated by `nix develop -c lake env lean tests/json-tape.lean`.  A `#guard`
that does not hold stops elaboration with a nonzero exit status; nothing
outside the elaborated program is written.
-/
import LeanLLVM

namespace JsonTapeScenario

open LeanLLVM.JSON

/-! ### The affirmative control: a tape that spells `[1]` -/

def correctTape : Tape :=
  { input := [0x5B, 0x31, 0x5D],
    tokens := [
      .punct .openBracket ⟨0, 1⟩,
      .number ⟨1, 2⟩,
      .punct .closeBracket ⟨2, 3⟩ ] }

#guard decodeTape correctTape = some (.array [.number [0x31]])
#guard spansWellFormed correctTape = true

/-- A correct two-element array tape: `[1,2]`, the affirmative control for the
comma path.  Without it, a decoder that refused every multi-element array would
satisfy every comma refusal below. -/
def correctTwoElemsTape : Tape :=
  { input := [0x5B, 0x31, 0x2C, 0x32, 0x5D],
    tokens := [
      .punct .openBracket ⟨0, 1⟩,
      .number ⟨1, 2⟩,
      .punct .comma ⟨2, 3⟩,
      .number ⟨3, 4⟩,
      .punct .closeBracket ⟨4, 5⟩ ] }

#guard decodeTape correctTwoElemsTape =
  some (.array [.number [0x31], .number [0x32]])
#guard spansWellFormed correctTwoElemsTape = true

/-- A correct string tape: one string token over `"a"`.  Without it, a decoder
that refused every string would satisfy every string refusal below. -/
def correctStringTape : Tape :=
  { input := [0x22, 0x61, 0x22], tokens := [.string ⟨0, 3⟩] }

#guard decodeTape correctStringTape = some (.string [0x61])
#guard spansWellFormed correctStringTape = true

/-- A correct object tape: `{"a":1}`, with the colon token's span naming the
byte between the name and the value. -/
def correctObjectTape : Tape :=
  { input := [0x7B, 0x22, 0x61, 0x22, 0x3A, 0x31, 0x7D],
    tokens := [
      .punct .openBrace ⟨0, 1⟩,
      .string ⟨1, 4⟩,
      .punct .colon ⟨4, 5⟩,
      .number ⟨5, 6⟩,
      .punct .closeBrace ⟨6, 7⟩ ] }

#guard decodeTape correctObjectTape = some (.object [([0x61], .number [0x31])])
#guard spansWellFormed correctObjectTape = true

/- The colon token's span is the byte between the name and the value, so the
object tape is not the same tokens with the separator unchecked. -/
#guard
  match correctObjectTape.tokens with
  | [.punct .openBrace _, .string _, .punct .colon s, .number _,
      .punct .closeBrace _] =>
      decide (s = ⟨4, 5⟩ ∧ correctObjectTape.input.get? 4 = some 0x3A)
  | _ => false

/-! ### A separator is a token and a byte -/

/-- The object's colon token removed: the separator is a token the tape must
carry, so the name and the value do not become adjacent members. -/
def objectMissingColon : Tape :=
  { input := [0x7B, 0x22, 0x61, 0x22, 0x3A, 0x31, 0x7D],
    tokens := [
      .punct .openBrace ⟨0, 1⟩,
      .string ⟨1, 4⟩,
      .number ⟨5, 6⟩,
      .punct .closeBrace ⟨6, 7⟩ ] }

#guard decodeTape objectMissingColon = none

/-- The colon token one byte late: its span names the value byte, not the colon
at the cursor the name leaves. -/
def objectShortColon : Tape :=
  { input := [0x7B, 0x22, 0x61, 0x22, 0x3A, 0x31, 0x7D],
    tokens := [
      .punct .openBrace ⟨0, 1⟩,
      .string ⟨1, 4⟩,
      .punct .colon ⟨5, 6⟩,
      .number ⟨5, 6⟩,
      .punct .closeBrace ⟨6, 7⟩ ] }

#guard decodeTape objectShortColon = none

/-- Tokens for `[1,2]` laid over `[1x2]`: every span is in bounds, the comma
token sits between two number tokens, and the byte at its cursor is `x`, not a
comma.  The byte is the only thing the decoder can refuse. -/
def commaWithoutCommaByte : Tape :=
  { input := [0x5B, 0x31, 0x78, 0x32, 0x5D],
    tokens := [
      .punct .openBracket ⟨0, 1⟩,
      .number ⟨1, 2⟩,
      .punct .comma ⟨2, 3⟩,
      .number ⟨3, 4⟩,
      .punct .closeBracket ⟨4, 5⟩ ] }

#guard decodeTape commaWithoutCommaByte = none
#guard spansWellFormed commaWithoutCommaByte = true

/-! ### A token whose span does not point at its bytes -/

/-- A number token spanning text that is not a number lexeme.  The span is in
the input and well formed, so only the decoder's reading of the bytes rejects
it. -/
def numberOverText : Tape :=
  { input := [0x61, 0x62, 0x63],
    tokens := [.number ⟨0, 3⟩] }

#guard decodeTape numberOverText = none
#guard spansWellFormed numberOverText = true

/-- A string token whose span stops one byte before the closing quote.  The
span is non-empty, in order and inside the input, so `spansWellFormed` accepts
it; the decoder rejects it because the span does not cover the literal. -/
def stringShortSpan : Tape :=
  { input := [0x22, 0x61, 0x62, 0x22],
    tokens := [.string ⟨0, 3⟩] }

#guard decodeTape stringShortSpan = none
#guard spansWellFormed stringShortSpan = true

/-- A string token over `a"`: the one span is in bounds and well formed, and
the byte at its start is `a`, not the opening quote.  Only the opening-quote
check can refuse it, so the tape separates a string's span from its bytes. -/
def stringMissingOpenQuote : Tape :=
  { input := [0x61, 0x22], tokens := [.string ⟨0, 2⟩] }

#guard decodeTape stringMissingOpenQuote = none
#guard spansWellFormed stringMissingOpenQuote = true

/-- A string token over `"\uDEAD"`.  RFC 8259 §8.2 admits the unpaired escape,
so the bytes are an RFC text; the decoder's character discipline is the strict
reading, so the tape does not decode.  This is the tape-level face of `Policy`. -/
def unpairedSurrogateTape : Tape :=
  { input := [0x22, 0x5C, 0x75, 0x44, 0x45, 0x41, 0x44, 0x22],
    tokens := [.string ⟨0, 8⟩] }

#guard decodeTape unpairedSurrogateTape = none
#guard spansWellFormed unpairedSurrogateTape = true

/-- An opening-bracket token over a brace: the span is one byte as punctuation
requires, and the byte is the wrong punctuation. -/
def bracketOverBrace : Tape :=
  { input := [0x7B],
    tokens := [.punct .openBracket ⟨0, 1⟩] }

#guard decodeTape bracketOverBrace = none

/-! ### A gap that is not whitespace -/

/-- Tokens for `[]` laid over `[1]`: the closing bracket is not at the cursor
the opening bracket leaves, and the byte between them is not whitespace. -/
def emptyArrayOverOne : Tape :=
  { input := [0x5B, 0x31, 0x5D],
    tokens := [.punct .openBracket ⟨0, 1⟩, .punct .closeBracket ⟨2, 3⟩] }

#guard decodeTape emptyArrayOverOne = none

/-- The same token kinds over `[ ]`, where the gap is whitespace: the control
for the previous case. -/
def emptyArrayOverSpace : Tape :=
  { input := [0x5B, 0x20, 0x5D],
    tokens := [.punct .openBracket ⟨0, 1⟩, .punct .closeBracket ⟨2, 3⟩] }

#guard decodeTape emptyArrayOverSpace = some (.array [])

/-! ### The whole input is consumed -/

/-- A token for `1` over `1 2`: the input is not consumed apart from
whitespace, because a second value follows. -/
def numberOverTwoValues : Tape :=
  { input := [0x31, 0x20, 0x32],
    tokens := [.number ⟨0, 1⟩] }

#guard decodeTape numberOverTwoValues = none

/-- A token for `1` over ` 1 `: surrounding whitespace is admitted, so the same
token list decodes. -/
def numberSurrounded : Tape :=
  { input := [0x20, 0x31, 0x20],
    tokens := [.number ⟨1, 2⟩] }

#guard decodeTape numberSurrounded = some (.number [0x31])

/-! ### `spansWellFormed` decides the span discipline alone -/

/-- Two number tokens whose spans overlap: the second starts before the first
stops.  The token kinds alone would not show it. -/
def overlappingSpans : Tape :=
  { input := [0x31, 0x32, 0x33],
    tokens := [.number ⟨0, 2⟩, .number ⟨1, 3⟩] }

#guard spansWellFormed overlappingSpans = false

/- The correct tape's spans are in order, non-empty and inside the input, so
the same predicate accepts them; the two tapes are distinguished by the span
discipline and not by their token kinds. -/
#guard spansWellFormed correctTape = true

/-- No tokens: the span predicate holds vacuously, and the decoder refuses the
tape because the input is not consumed. -/
def emptyTokenList : Tape :=
  { input := [0x31], tokens := [] }

#guard decodeTape emptyTokenList = none
#guard spansWellFormed emptyTokenList = true

end JsonTapeScenario
