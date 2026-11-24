/-
The no-event consumer's event stream read as a JSON value.

`JsonStage2NoEvent` projects the certified stage-2 trace onto the caller's
vocabulary: `consumeRecords` replaces each `EventRecord` by the `ConsumerEvent`
the consumer reads from it.  What that module states is the stream's *content* —
token and value counts, the arena byte sum, and the sum — and a refusal policy.
It names the decoded value only as `decodeTape t`, the reference tape's own
decoding, and leaves open what a consumer that wants a **value** reads from the
events.  This module is that entry: `valueOfEvents` is a computable decoder over
the event list, and `valueOfEvents_consumeRecords` transfers it to the parser's
value after canonicalising the reference's number lexemes, conditionally on the
two decoder bridges `hE` and `hT` that the entry separates from the decoder
itself.

# The number arm is lossy, and the accepted value is the canonicalised one

`LeanLLVM.JSON.Value.number` carries the document's **source lexeme**
(`Value.number (lexeme : Bytes)`), while `ConsumerEvent.number` carries only
`strtodSpec d`'s bits: the record's eight payload bytes are an IEEE 754 binary64,
not the bytes that spelled it.  Many lexemes denote one binary64 — `1.0` and
`1.00` are one value — so no decoder can recover the lexeme from the stream
alone, and an equality with `decodeTape t` cannot hold on every trace.

The decoder renders a number's payload canonically (`bitsLexeme`, the eight
payload bytes), and the transfer theorem concludes the equality *after*
canonicalising the reference's number lexemes: `canonValue` reads a lexeme with
`StrtodReader.reader`, converts it with `strtodSpec`, and renders the result with
`bitsLexeme`.  That is the fast path's accepted number behaviour: an accepted
number is its binary64 value, and the canonical rendering of that value is the
eight bytes the event carries.  This is not a uniqueness
claim over traces — many lexemes share one rendering, as they share one value —
and a lexeme the reader refuses has no rendering, so the canonicalisation is
`none` there and an accepted document whose number lexeme the reader refuses
cannot satisfy `hE`.

# The transfer is hypothesis application

`hE` carries the event decoder to the canonicalised token decoder at this
trace's own facts, `hT` carries the token decoder to `decodeTape`, and the
conclusion is those two rewritten in sequence.  No decoder is proved here, and
neither bridge is a vacuous premise: each relates two different decoders of the
same document, and the `hE`/`hT` split names where a proof of the bridge belongs.

# The canonicalisation's domain is a premise, not a fallback

`hcanon` names the domain the event-side bridge is stated under: every number
lexeme of the value `decodeTape t` returns is one `StrtodReader.reader` accepts,
so `canonValue` succeeds on that value.  It is a premise of the theorem and the
last premise `EventsParseValue` binds, so the transfer consumes it; it is not a
silent assumption.  Discharging it rests with the entry's own proof:
`decodeTape_correct` and the accepted
document's `ValidDocument` give the number grammar the reader reads, hence the
decoded value's number lexemes are readable.

A fallback — returning the lexeme unchanged where the reader refuses — would be
worse than a missing premise.  The event side renders `bitsLexeme bits`, the
reference side would keep the source bytes, and the equality would fail exactly
on the documents the fallback touched, silently.  The canonicalisation therefore
stays `Option`-valued, and the theorem states the condition under which it is
defined instead of manufacturing a value where there is none.

The decoder is `def`, not `noncomputable`: its recursion is fuelled, so no
`Classical.choice` enters the value or the theorem.  Its axiom footprint is
`[propext, Quot.sound]`; a future `noncomputable` edit would widen it, which is
why the pin records the narrower line.

There is no `sorry`, `admit` or `native_decide`; the axiom pin is in
`LeanLLVMTest/Refinement.lean`.
-/
import LeanLLVM.Refinement.JsonStage2NoEvent
import LeanLLVM.JSON
import LeanLLVM.StrtodReader

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The canonical number rendering and the canonicalisation

The payload's own eight bytes: `strtodSpec`'s bits little-endian, exactly what the
record carries.  A consumer that wants the lexeme reads the document's span
instead; this rendering is what makes the event list a total function of the
events.

`canonValue` is the other direction, over the reference's `Value`: it replaces
each number's source lexeme by that lexeme's canonical rendering.  The reading is
`StrtodReader.reader` — the emitted scanner's own decomposition — the conversion
is `strtodSpec`, and the rendering is `bitsLexeme`.  A lexeme the reader refuses
has no rendering, so `canonValue` is `Option`-valued and fails loudly there
rather than leaving the lexeme in place as if it had been canonicalised. -/

/-- The lexeme a number event's payload renders: its eight bytes, little-endian. -/
def bitsLexeme (bits : Nat) : List UInt8 := bitsBytes bits

/-- **The canonical rendering of a source lexeme.**  Read the lexeme with the
emitted scanner's reader, convert it to binary64 with `strtodSpec`, and render
that value's payload bytes.  `none` when the reader refuses the lexeme: an
unreadable lexeme has no value, hence no canonical rendering. -/
def canonLexeme (lexeme : Bytes) : Option Bytes :=
  (StrtodReader.reader lexeme).map fun d =>
    ByteString.literal (bitsLexeme (strtodSpec d).toBits)

mutual

/-- **Canonicalise a value's number lexemes.**  Structure, keys, order, strings
and literals are unchanged; each number's lexeme becomes its canonical rendering,
and a lexeme with no rendering makes the whole value `none`. -/
def canonValue : JSON.Value → Option JSON.Value
  | .null => some .null
  | .bool b => some (.bool b)
  | .string cs => some (.string cs)
  | .number lexeme => (canonLexeme lexeme).map .number
  | .array elems => (canonValues elems).map .array
  | .object members => (canonMembers members).map .object

/-- Elementwise canonicalisation, order preserved. -/
def canonValues : List JSON.Value → Option (List JSON.Value)
  | [] => some []
  | v :: vs => canonValue v >>= fun v' => (canonValues vs).map fun vs' => v' :: vs'

/-- Memberwise canonicalisation, keys and order preserved. -/
def canonMembers : List (List Nat × JSON.Value) →
    Option (List (List Nat × JSON.Value))
  | [] => some []
  | (k, v) :: ms =>
      canonValue v >>= fun v' => (canonMembers ms).map fun ms' => (k, v') :: ms'

end

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
is a key event (`T_KEY`) followed by a value. -/
def parseMembersF : Nat → List ConsumerEvent →
    Option (List (List Nat × JSON.Value) × List ConsumerEvent)
  | 0, _ => none
  | _, [] => none
  | f + 1, e :: es =>
      if e.tag = 2 then some ([], es)
      else if e.tag = 5 then
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

/-! ### The transfer theorem

The event stream's value is the tape's value, canonicalised, once the two decoders
are bridged: the event decoder agrees with the canonicalised token decoder
(`hE`), and the token decoder agrees with the tape's own recursive-descent
decoder (`hT`).  Those two are the module's named bridges; the theorem applies
them and rewrites, so the number arm's loss is accounted for by the
canonicalisation on the conclusion's right-hand side rather than by a premise. -/

/-- **The event-side bridge.**  At this trace, given the record relation, the
parse, the token-list tie and that the decoded value's number lexemes all have a
canonical rendering, the event decoder agrees with the token decoder after the
token decoder's number lexemes are canonicalised.  Stated at the trace's own
facts rather than as a bare function equality: the premises are arguments, so a
proof of it is a proof about this document, not a composition of two unrelated
functions. -/
def EventsParseValue (bs arena : List UInt8) (rs : List EventRecord)
    (toks : List JSON.Token) (t : JSON.Tape) : Prop :=
  Stage2Records bs arena rs toks →
  parseBytes Limits.default (ByteString.literal bs) = .ok t →
  t.tokens = toks →
  (∀ v, decodeTape t = some v → (canonValue v).isSome) →
  valueOfEvents (consumeRecords bs arena rs) = (parseValueT t).bind canonValue

/-- **The event stream projects to the parser's canonicalised value**, by
applying the two decoder bridges.  `hcanon` is the domain condition the
event-side bridge is stated under: every number lexeme of the value the tape
decodes is one the reader accepts.  `hE` is the event-side bridge over this
trace's facts and `hcanon`, and `hT` is the token decoder's agreement with
`decodeTape`; the conclusion's right-hand side canonicalises the reference
value's number lexemes with `canonValue`, which is where the number arm's lossy
rendering is accounted for.  Each premise is a statement about a different
object, and none is the conclusion. -/
theorem valueOfEvents_consumeRecords {bs : List UInt8} {arena : List UInt8}
    {rs : List EventRecord} {toks : List JSON.Token} {t : JSON.Tape}
    (hrec : Stage2Records bs arena rs toks)
    (hparse : parseBytes Limits.default (ByteString.literal bs) = .ok t)
    (htoks : t.tokens = toks)
    (hcanon : ∀ v, decodeTape t = some v → (canonValue v).isSome)
    (hE : EventsParseValue bs arena rs toks t)
    (hT : parseValueT t = decodeTape t) :
    valueOfEvents (consumeRecords bs arena rs) = (decodeTape t).bind canonValue := by
  rw [hE hrec hparse htoks hcanon, hT]

end LeanLLVM.Refinement
