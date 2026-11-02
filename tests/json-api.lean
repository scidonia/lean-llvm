/-
The API scenario: the reference parser's public entrypoint, observed from
outside as a client observes it.

The base language is RFC 8259's grammar, and `Policy` is the character
restriction on top of it.  Accepted documents are compared through `decodeTape`,
so an accepted parse is checked against the value the bytes spell rather than
against a parser-private structure.  Refusals are checked as `invalid`; a
refusal whose reason is `Policy` names that reason, because the input is an RFC
text and the policy is what narrows it.  Each resource outcome is checked as
itself: a document that fits the syntax but exceeds a bound is not reported as a
syntax fault, and a syntax fault stays `invalid` under a bound that admits the
input.

Elaborated by `nix develop -c lake env lean tests/json-api.lean`.  A `#guard`
that does not hold stops elaboration with a nonzero exit status; nothing
outside the elaborated program is written.
-/
import LeanLLVM

namespace JsonApiScenario

open LeanLLVM.JSON

/-- The bytes of an ASCII document. -/
def docBytes (s : String) : ByteArray := s.toUTF8

/-- A byte array from literal byte values, for inputs that are not text. -/
def rawBytes (bs : List Nat) : ByteArray :=
  ByteArray.mk (bs.map UInt8.ofNat).toArray

/-- The proof layer's byte string, for the semantic names. -/
def rawList (bs : List Nat) : Bytes := bs.map UInt8.ofNat

/-- A string literal around a raw byte payload, with the quotation marks supplied
here so a case names only the payload it means. -/
def stringWith (payload : List Nat) : ByteArray :=
  rawBytes (0x22 :: payload ++ [0x22])

/-- A document parses and decodes to the expected value. -/
def accepts (input : ByteArray) (v : Value) : Bool :=
  match parseDocument Limits.default input with
  | .ok t => decide (t.input = input.toList ∧ decodeTape t = some v)
  | .error _ => false

/-- A document is refused as `invalid`, whatever the reason. -/
def refuses (input : ByteArray) : Bool :=
  match parseDocument Limits.default input with
  | .error (.invalid _) => true
  | _ => false

/-- A document is refused as `invalid` with a reason the predicate selects. -/
def refusesWith (input : ByteArray) (p : Reject → Bool) : Bool :=
  match parseDocument Limits.default input with
  | .error (.invalid r) => p r
  | _ => false

/-- The reason RFC 8259 §8.2 admits and `Policy` refuses. -/
def isUnpairedSurrogate : Reject → Bool
  | .unpairedSurrogate _ => true
  | _ => false

/-- The reason RFC 7493 §2.1's character constraint supplies. -/
def isNoncharacter : Reject → Bool
  | .noncharacter _ => true
  | _ => false

/-! ### Accepted documents decode to the value their bytes spell -/

#guard
  match parseDocument Limits.default (docBytes "null") with
  | .ok t =>
      decide (t.input = (docBytes "null").toList ∧ decodeTape t = some .null)
  | .error _ => false

#guard
  match parseDocument Limits.default (docBytes "true") with
  | .ok t =>
      decide (t.input = (docBytes "true").toList ∧
        decodeTape t = some (.bool true))
  | .error _ => false

/- A repeated key is kept, in order, as two members; no map is built. -/
#guard accepts (docBytes "{\"a\":1,\"a\":2}") (.object [([0x61], .number [0x31]), ([0x61], .number [0x32])])

/- A lexeme longer than a machine word is kept as bytes, exactly. -/
#guard accepts (docBytes "123456789012345678901234567890") (.number (docBytes "123456789012345678901234567890").toList)

/- Whitespace around the elements and around the document is accepted. -/
#guard accepts (docBytes "[ 1 , 2 ]") (.array [.number [0x31], .number [0x32]])

#guard accepts (docBytes " 1 ") (.number [0x31])

/-! ### Refused documents are `invalid` -/

/- A leading zero has no derivation in the number grammar. -/
#guard
  match parseDocument Limits.default (docBytes "01") with
  | .error (.invalid _) => true
  | _ => false

#guard
  match parseDocument Limits.default (docBytes "-") with
  | .error (.invalid _) => true
  | _ => false

/- A second top-level value is trailing data, not part of the document. -/
#guard
  match parseDocument Limits.default (docBytes "1 2") with
  | .error (.invalid _) => true
  | _ => false

/- An escaped high surrogate without a low half is refused by policy. -/
#guard
  match parseDocument Limits.default (docBytes "\"\\uD800\"") with
  | .error (.invalid _) => true
  | _ => false

#guard
  match parseDocument Limits.default (rawBytes [0xEF, 0xBB, 0xBF, 0x31]) with
  | .error (.invalid .byteOrderMark) => true
  | _ => false

/-! ### The RFC 8259 grammar, clause by clause

Each accepted case decodes to the value its bytes spell; each refused case is
`invalid`.  Where `Policy` is the reason, the reason is named, because those
inputs are RFC texts that the policy narrows rather than non-texts.
-/

/- RFC 3629 §4: the nine `UTF8-char` alternatives, sampled at their boundary
sequences. -/
#guard accepts (stringWith [0xC3, 0xA9]) (.string [0xE9])
#guard accepts (stringWith [0xE2, 0x82, 0xAC]) (.string [0x20AC])
#guard accepts (stringWith [0xF0, 0x90, 0x8D, 0x88]) (.string [0x10348])
#guard accepts (stringWith [0xF0, 0x90, 0x80, 0x80]) (.string [0x10000])
#guard accepts (stringWith [0xF4, 0x8F, 0xBF, 0xBD]) (.string [0x10FFFD])

#guard refuses (stringWith [0x80])
#guard refuses (stringWith [0xC3])
#guard refuses (stringWith [0xE2, 0x82])
#guard refuses (stringWith [0xC0, 0xAF])
#guard refuses (stringWith [0xE0, 0x80, 0xAF])
#guard refuses (stringWith [0xED, 0xA0, 0x80])
#guard refuses (stringWith [0xED, 0xBF, 0xBF])
#guard refuses (stringWith [0xF4, 0x90, 0x80, 0x80])
#guard refuses (stringWith [0xF8, 0x88, 0x80, 0x80, 0x80])
#guard refuses (stringWith [0xFF])

/- §7's `unescaped` is `%x20-21 / %x23-5B / %x5D-10FFFF`: DEL is admitted, and
a raw control character below `0x20` is not. -/
#guard accepts (stringWith [0x7F]) (.string [0x7F])
#guard refuses (stringWith [0x00])
#guard refuses (stringWith [0x1F])
#guard refuses (stringWith [0x09])
#guard refuses (stringWith [0x0A])

/- §2's `ws` is space, tab, LF and CR, on both sides of every structural
character. -/
#guard accepts
  (rawBytes [0x7B, 0x09, 0x0D, 0x0A, 0x20, 0x22, 0x61, 0x22,
    0x09, 0x3A, 0x0A, 0x31, 0x0D, 0x7D])
  (.object [([0x61], .number [0x31])])
#guard refuses (rawBytes [0x0C, 0x31])
#guard refuses (rawBytes [0x31, 0x0B])
#guard refuses (rawBytes [0x7B, 0x0C, 0x22, 0x61, 0x22, 0x3A, 0x31, 0x7D])

/- §6's `number` grammar: the four shapes, the leading-zero rule, and no
`NaN`/`Infinity`/hex extension. -/
#guard accepts (docBytes "-0") (.number [0x2D, 0x30])
#guard accepts (docBytes "1E+3") (.number [0x31, 0x45, 0x2B, 0x33])
#guard accepts (docBytes "-1.5E-7")
  (.number [0x2D, 0x31, 0x2E, 0x35, 0x45, 0x2D, 0x37])
#guard accepts (docBytes "1.25e10")
  (.number [0x31, 0x2E, 0x32, 0x35, 0x65, 0x31, 0x30])
#guard refuses (docBytes "+1")
#guard refuses (docBytes ".5")
#guard refuses (docBytes "1.")
#guard refuses (docBytes "1e")
#guard refuses (docBytes "NaN")
#guard refuses (docBytes "0x10")
#guard refuses (docBytes "--1")

/- §7's surrogate-pair rule, and RFC 7493 §2.1's own legal example: a high
escape followed by a low escape is one code point, and the raw encoding agrees. -/
#guard accepts (docBytes "\"\\uD834\\uDD1E\"") (.string [0x1D11E])
#guard accepts (stringWith [0xF0, 0x9D, 0x84, 0x9E]) (.string [0x1D11E])
#guard accepts (docBytes "\"\\uD800\\uDEAD\"") (.string [0x102AD])

/- RFC 7493 §2.1's character constraint is `Policy`, and it names its reason:
an unpaired escape is RFC-legal but refused, and a noncharacter is refused. -/
#guard refusesWith (docBytes "\"\\uDEAD\"") isUnpairedSurrogate
#guard refusesWith (docBytes "\"\\uD800\"") isUnpairedSurrogate
#guard refusesWith (docBytes "\"\\uFDD0\"") isNoncharacter
#guard refusesWith (docBytes "\"\\uFFFE\"") isNoncharacter
#guard refusesWith (docBytes "\"\\uFFFF\"") isNoncharacter
#guard refusesWith (stringWith [0xEF, 0xB7, 0x90]) isNoncharacter
#guard refusesWith (stringWith [0xEF, 0xBF, 0xBE]) isNoncharacter
/- U+10FFFF is a valid encoding and a noncharacter: `n % 0x10000 = 0xFFFF` is
the supplementary branch of the predicate, and the well-formed surrogate pair
that encodes the same code point takes the pair path to the same refusal. -/
#guard refusesWith (stringWith [0xF4, 0x8F, 0xBF, 0xBF]) isNoncharacter
#guard refusesWith (stringWith [0xF0, 0x9F, 0xBF, 0xBE]) isNoncharacter
#guard refusesWith (docBytes "\"\\uDBFF\\uDFFF\"") isNoncharacter

/- The replacement character is a scalar and is not a noncharacter. -/
#guard accepts (docBytes "\"\\uFFFD\"") (.string [0xFFFD])

/- A repeated name is preserved in order, at any position. -/
#guard accepts (docBytes "{\"a\":1,\"b\":2,\"a\":3}")
  (.object [([0x61], .number [0x31]), ([0x62], .number [0x32]),
    ([0x61], .number [0x33])])

/-! ### The two readings

`RfcText` and `Policy` are separate: the bytes of `"\uDEAD"` spell a text RFC
8259 §8.2 admits, and `Policy` is what refuses the reading.  `ValidDocument` is
their conjunction, and a successful parse yields one. -/

/-- §8.2's unpaired escape: an RFC text whose reading `Policy` refuses. -/
example : ∃ v : Value,
    RfcText (rawList [0x22, 0x5C, 0x75, 0x44, 0x45, 0x41, 0x44, 0x22]) v ∧
      ¬ Policy v := by
  refine ⟨.string [0xDEAD], ?_, ?_⟩
  · unfold RfcText TextAt
    refine ⟨0, 8, by decide, ?_, by decide⟩
    refine ValueAt.string ?_
    unfold StringAt
    refine ⟨by decide, [], ?_, by decide⟩
    refine StrChars.cons ?_ StrChars.nil
    exact StrChar.escLone rfl (by decide) (by decide)
  · unfold Policy Value.charPolicy
    intro h
    exact absurd (h 0xDEAD (by simp)).1 (by decide)

/-- A successful parse yields a `ValidDocument`: the accepted language, not just
a tape. -/
example (t : Tape) (h : parseBytes Limits.default (rawList [0x31]) = .ok t) :
    ∃ v : Value, ValidDocument (rawList [0x31]) v := by
  obtain ⟨_, hrest⟩ :=
    (parseRef_sound Limits.default (rawList [0x31])).1 t h
  obtain ⟨v, hvalid, _⟩ := hrest
  exact ⟨v, hvalid⟩

/-! ### A bound is reported as its own outcome, never as a syntax fault -/

#guard
  match parseDocument Limits.default (docBytes "[1]") with
  | .ok _ => true
  | _ => false

/- The same input under a length bound that excludes it. -/
#guard
  match parseDocument { Limits.default with maxInput := 2 } (docBytes "[1]") with
  | .error .inputTooLong => true
  | _ => false

#guard
  match parseDocument { Limits.default with maxDepth := 1 } (docBytes "[[1]]") with
  | .error .depthExceeded => true
  | _ => false

#guard
  match parseDocument { Limits.default with maxTokens := 4 } (docBytes "[1,2]") with
  | .error .outOfCapacity => true
  | _ => false

/- A syntax fault stays `invalid` under a length bound that admits the input,
and under a depth or capacity bound that could not have excluded it. -/
#guard
  match parseDocument { Limits.default with maxInput := 2 } (docBytes "01") with
  | .error (.invalid _) => true
  | _ => false

#guard
  match parseDocument { Limits.default with maxDepth := 0 } (docBytes "01") with
  | .error (.invalid _) => true
  | _ => false

#guard
  match parseDocument { Limits.default with maxTokens := 0 } (docBytes "01") with
  | .error (.invalid _) => true
  | _ => false

end JsonApiScenario
