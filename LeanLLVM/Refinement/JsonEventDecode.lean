/-
The event stream's decoders: events to a value, and tokens to a value.

`valueOfEvents` is the computable decoder over the consumer's event list, and
`parseValueT` is the same reading over the reference tape's tokens, which is the
object the event decoder is compared with.  Both are here, with the canonical
number rendering `bitsLexeme`, because they are code: the transfer theorem and
the canonicalisation of source lexemes are in `JsonEventValue` and `JsonCanon`,
which import this module.  A program that decodes an event stream therefore does
not import the stage-2 walk's specification or the strtod tiers.
-/
import LeanLLVM.JSON
import LeanLLVM.JSON.Strtod
import LeanLLVM.Refinement.JsonConsumerEvent

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-- The lexeme a number event's payload renders: its eight bytes, little-endian. -/
def bitsLexeme (bits : Nat) : List UInt8 := bitsBytes bits

/-! ### The event decoder

A recursive descent over the consumer's events.  Commas and colons are absent
from the stream, so a container is opened by its tag and closed by the matching
end tag, with values back to back.  The parser is fuelled: every step spends one
unit, so the recursion is structural on the fuel and the definition needs no
well-founded measure.  `valueOfEvents` supplies the one bound that matters, the
stream's own length. -/

mutual

/-- One value at the head of the event list, with the events after it. -/
def parseValueF : Nat → List ConsumerEvent → Option (JSON.Value × List ConsumerEvent)
  | 0, _ => none
  | _, [] => none
  | f + 1, e :: es =>
      match e.tag with
      | 1 =>
          match parseMembersF f es with
          | some (ms, rest) => some (.object ms, rest)
          | none => none
      | 3 =>
          match parseElemsF f es with
          | some (vs, rest) => some (.array vs, rest)
          | none => none
      | 5 => some (.string e.cps, es)
      | 6 => some (.string e.cps, es)
      | 7 => some (.number (ByteString.literal (bitsLexeme e.payload)), es)
      | 8 => some (.bool true, es)
      | 9 => some (.bool false, es)
      | 10 => some (.null, es)
      | _ => none

/-- Array elements, back to back, closed by `T_ARR_END` (consumed here). -/
def parseElemsF : Nat → List ConsumerEvent → Option (List JSON.Value × List ConsumerEvent)
  | 0, _ => none
  | _, [] => none
  | f + 1, e :: es =>
      if e.tag = 4 then some ([], es)
      else
        match parseValueF f (e :: es) with
        | some (v, rest) =>
            match parseElemsF f rest with
            | some (vs, rest') => some (v :: vs, rest')
            | none => none
        | none => none

/-- Object members, back to back, closed by `T_OBJ_END` (consumed here); a member
is a key event followed by a value.  At a member-key position a string event is
the key whatever its tag says: the position decides the role, and the emitter's
`T_KEY`/`T_STR` flag is an annotation the stream's consumer does not need to
trust.  Both tags are therefore accepted here, and `parseValueF` likewise accepts
either at a value position, so a key-flagged or value-flagged string record reads
the same at either position. -/
def parseMembersF : Nat → List ConsumerEvent →
    Option (List (List Nat × JSON.Value) × List ConsumerEvent)
  | 0, _ => none
  | _, [] => none
  | f + 1, e :: es =>
      if e.tag = 2 then some ([], es)
      else if e.tag = 5 ∨ e.tag = 6 then
        match es with
        | [] => none
        | v :: vs =>
            match parseValueF f (v :: vs) with
            | some (val, rest) =>
                match parseMembersF f rest with
                | some (ms, rest') => some ((e.cps, val) :: ms, rest')
                | none => none
            | none => none
      else none

end

/-- **The event stream read as a JSON value.**  A value is accepted when it
consumes the whole stream; a prefix (a refusing run's stream) or an ill-formed
list decodes to `none`.  A number's payload is rendered canonically
(`bitsLexeme`); strings carry the consumer's code points. -/
def valueOfEvents (evs : List ConsumerEvent) : Option JSON.Value :=
  match parseValueF (evs.length + 1) evs with
  | some (v, rest) => if rest = [] then some v else none
  | none => none

/-! ### The token-level structural decoder

The reference reading of the same tokens, with the tape's own lexemes: a number's
span bytes are its lexeme, and a string's body is read at its span.  This is the
object the event decoder is compared against.  The parser is fuelled like the
event decoder; `decodeTape` is the recursive-descent decoder the tape already
carries. -/

mutual

/-- One value at the head of a tape's token list, with the tokens after it. -/
def parseValueTB (bs : Bytes) : Nat → List JSON.Token →
    Option (JSON.Value × List JSON.Token)
  | 0, _ => none
  | _, [] => none
  | f + 1, tok :: rest =>
      match tok with
      | .null _ => some (.null, rest)
      | .bool b _ => some (.bool b, rest)
      | .number s => some (.number ((bs.drop s.start).take (s.stop - s.start)), rest)
      | .string s =>
          match scanCharsEnd bs (s.start + 1) 0 with
          | .ok (cs, _) => some (.string cs, rest)
          | .error _ => none
      | .punct .openBracket _ =>
          match parseElemsTB bs f rest with
          | some (vs, rest') => some (.array vs, rest')
          | none => none
      | .punct .openBrace _ =>
          match parseMembersTB bs f rest with
          | some (ms, rest') => some (.object ms, rest')
          | none => none
      | _ => none

/-- Array elements at a token list, closed by `]` (consumed here). -/
def parseElemsTB (bs : Bytes) : Nat → List JSON.Token →
    Option (List JSON.Value × List JSON.Token)
  | 0, _ => none
  | _, [] => none
  | _ + 1, .punct .closeBracket _ :: rest => some ([], rest)
  | f + 1, tok :: rest =>
      match parseValueTB bs f (tok :: rest) with
      | some (v, rest') =>
          match rest' with
          | .punct .comma _ :: rest'' =>
              match parseElemsTB bs f rest'' with
              | some (vs, r) => some (v :: vs, r)
              | none => none
          | .punct .closeBracket _ :: rest'' => some ([v], rest'')
          | _ => none
      | none => none

/-- Object members at a token list, closed by `}` (consumed here); a member is a
string key, a colon and a value. -/
def parseMembersTB (bs : Bytes) : Nat → List JSON.Token →
    Option (List (List Nat × JSON.Value) × List JSON.Token)
  | 0, _ => none
  | _, [] => none
  | _ + 1, .punct .closeBrace _ :: rest => some ([], rest)
  | f + 1, .string s :: rest =>
      match scanCharsEnd bs (s.start + 1) 0 with
      | .error _ => none
      | .ok (cs, _) =>
          match rest with
          | .punct .colon _ :: rest1 =>
              match rest1 with
              | [] => none
              | v :: vs =>
                  match parseValueTB bs f (v :: vs) with
                  | some (val, rest') =>
                      match rest' with
                      | .punct .comma _ :: rest'' =>
                          match parseMembersTB bs f rest'' with
                          | some (ms, r) => some ((cs, val) :: ms, r)
                          | none => none
                      | .punct .closeBrace _ :: rest'' => some ([(cs, val)], rest'')
                      | _ => none
                  | none => none
          | _ => none
  | _ + 1, _ :: _ => none

end

/-- **The token-level structural decoder.**  The value the tape's tokens spell,
with the tape's own input read through the spans: number lexemes from their
bytes, string bodies from their spans, containers from the token sequence. -/
def parseValueT (t : JSON.Tape) : Option JSON.Value :=
  match parseValueTB t.input (t.tokens.length + 1) t.tokens with
  | some (v, []) => some v
  | _ => none

end LeanLLVM.Refinement
