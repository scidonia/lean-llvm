/-
The JSON checks: the policy fixtures, the parser fixtures, the tape-level
decoder rows, the renderer's own fixtures, and the axiom pins.

Each group pairs its refusals with an affirmative control, so a detector that
never accepts (or a decoder that never refuses) cannot pass the row it is meant
to justify.  The bytes are written with `rawBytes` where the case is a byte
sequence rather than text, so the escape rules of the host language cannot be
confused with the escape rules under test.
-/
import LeanLLVM
import JsonMain

namespace LeanLLVMTest.Json

open LeanLLVM.JSON

/-- The bytes of an ASCII document. -/
def ascii (s : String) : Bytes := s.toUTF8.toList

/-- A byte string from literal byte values. -/
def rawBytes (bs : List Nat) : Bytes := bs.map UInt8.ofNat

/-! ### Number grammar (RFC 8259 §6) -/

#guard numLexB (ascii "0")
#guard numLexB (ascii "-0")
#guard numLexB (ascii "1")
#guard numLexB (ascii "-1")
#guard numLexB (ascii "42")
#guard numLexB (ascii "123456789012345678901234567890")
#guard numLexB (ascii "1.5")
#guard numLexB (ascii "-0.0")
#guard numLexB (ascii "0.5")
#guard numLexB (ascii "1e3")
#guard numLexB (ascii "1E+3")
#guard numLexB (ascii "1e-3")
#guard numLexB (ascii "1.25e10")
#guard numLexB (ascii "-1.5E-7")

#guard !numLexB (ascii "01")
#guard !numLexB (ascii "-")
#guard !numLexB (ascii "+1")
#guard !numLexB (ascii ".5")
#guard !numLexB (ascii "1.")
#guard !numLexB (ascii "1e")
#guard !numLexB (ascii "1e+")
#guard !numLexB (ascii "1.e5")
#guard !numLexB (ascii "1.2.3")
#guard !numLexB (ascii "NaN")
#guard !numLexB (ascii "Infinity")
#guard !numLexB (ascii "--1")
#guard !numLexB (ascii "0x10")

/-! ### Escapes (RFC 8259 §7)

`scanChars` takes the body after the opening quote and returns the remainder
after the closing quote. -/

#guard scanChars (rawBytes [0x5C, 0x22, 0x22]) = .ok ([0x22], [])
#guard scanChars (rawBytes [0x5C, 0x5C, 0x22]) = .ok ([0x5C], [])
#guard scanChars (rawBytes [0x5C, 0x2F, 0x22]) = .ok ([0x2F], [])
#guard scanChars (rawBytes [0x5C, 0x62, 0x5C, 0x66, 0x5C, 0x6E, 0x5C, 0x72,
    0x5C, 0x74, 0x22]) = .ok ([8, 12, 10, 13, 9], [])
#guard scanChars (rawBytes [0x5C, 0x75, 0x30, 0x30, 0x30, 0x30, 0x22]) =
  .ok ([0], [])
#guard scanChars (rawBytes [0x5C, 0x75, 0x30, 0x30, 0x65, 0x39, 0x22]) =
  .ok ([0xE9], [])

#guard scanChars (rawBytes [0x5C, 0x71, 0x22]) = .error (.badEscape 0)
#guard scanChars (rawBytes [0x5C, 0x75, 0x31, 0x32, 0x22]) = .error .ended
#guard scanChars (rawBytes [0x5C, 0x75, 0x5A, 0x5A, 0x5A, 0x5A, 0x22]) =
  .error (.badEscape 2)
#guard scanChars (rawBytes [0x61, 0x62, 0x63, 0x5C]) = .error .ended

/-! ### Strict UTF-8 (RFC 3629 §4) -/

#guard scanChars (rawBytes [0xC3, 0xA9, 0x22]) = .ok ([0xE9], [])
#guard scanChars (rawBytes [0xE2, 0x82, 0xAC, 0x22]) = .ok ([0x20AC], [])
#guard scanChars (rawBytes [0xF0, 0x90, 0x8D, 0x88, 0x22]) = .ok ([0x10348], [])
#guard scanChars (rawBytes [0xF0, 0x90, 0x80, 0x80, 0x22]) = .ok ([0x10000], [])
#guard scanChars (rawBytes [0xF4, 0x8F, 0xBF, 0xBD, 0x22]) = .ok ([0x10FFFD], [])

#guard scanChars (rawBytes [0x80, 0x22]) = .error (.badUTF8 0)
#guard scanChars (rawBytes [0xC3]) = .error .ended
#guard scanChars (rawBytes [0xE2, 0x82]) = .error .ended
#guard scanChars (rawBytes [0xC0, 0xAF, 0x22]) = .error (.badUTF8 0)
#guard scanChars (rawBytes [0xE0, 0x80, 0xAF, 0x22]) = .error (.badUTF8 0)
#guard scanChars (rawBytes [0xED, 0xA0, 0x80, 0x22]) = .error (.badUTF8 0)
#guard scanChars (rawBytes [0xED, 0xBF, 0xBF, 0x22]) = .error (.badUTF8 0)
#guard scanChars (rawBytes [0xF4, 0x90, 0x80, 0x80, 0x22]) = .error (.badUTF8 0)
#guard scanChars (rawBytes [0xF8, 0x88, 0x80, 0x80, 0x80, 0x22]) =
  .error (.badUTF8 0)
#guard scanChars (rawBytes [0xFF, 0x22]) = .error (.badUTF8 0)

/-! ### `unescaped` ranges (RFC 8259 §7) -/

#guard scanChars (rawBytes [0x7F, 0x22]) = .ok ([0x7F], [])
#guard scanChars (rawBytes [0x00, 0x22]) = .error (.controlCharacter 0)
#guard scanChars (rawBytes [0x1F, 0x22]) = .error (.controlCharacter 0)
#guard scanChars (rawBytes [0x09, 0x22]) = .error (.controlCharacter 0)
#guard scanChars (rawBytes [0x0A, 0x22]) = .error (.controlCharacter 0)

/-! ### Surrogate pairs and unpaired escapes (RFC 8259 §7, §8.2; RFC 7493 §2.1) -/

#guard scanChars (rawBytes [0x5C, 0x75, 0x44, 0x38, 0x33, 0x34,
    0x5C, 0x75, 0x44, 0x44, 0x31, 0x45, 0x22]) = .ok ([0x1D11E], [])
#guard scanChars (rawBytes [0xF0, 0x9D, 0x84, 0x9E, 0x22]) = .ok ([0x1D11E], [])
#guard scanChars (rawBytes [0x5C, 0x75, 0x44, 0x38, 0x30, 0x30,
    0x5C, 0x75, 0x44, 0x45, 0x41, 0x44, 0x22]) = .ok ([0x102AD], [])

#guard scanChars (rawBytes [0x5C, 0x75, 0x44, 0x45, 0x41, 0x44, 0x22]) =
  .error (.unpairedSurrogate 0)
#guard scanChars (rawBytes [0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x22]) =
  .error (.unpairedSurrogate 0)
#guard scanChars (rawBytes [0x5C, 0x75, 0x44, 0x43, 0x30, 0x30, 0x22]) =
  .error (.unpairedSurrogate 0)
#guard scanChars (rawBytes [0x5C, 0x75, 0x44, 0x38, 0x30, 0x30,
    0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x22]) = .error (.unpairedSurrogate 0)
#guard scanChars (rawBytes [0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x61, 0x22]) =
  .error (.unpairedSurrogate 0)
#guard scanChars (rawBytes [0x5C, 0x75, 0x44, 0x43, 0x30, 0x30,
    0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x22]) = .error (.unpairedSurrogate 0)

/-! ### Noncharacters (RFC 7493 §2.1) -/

#guard scanChars (rawBytes [0x5C, 0x75, 0x46, 0x46, 0x46, 0x44, 0x22]) =
  .ok ([0xFFFD], [])
#guard scanChars (rawBytes [0x5C, 0x75, 0x46, 0x44, 0x44, 0x30, 0x22]) =
  .error (.noncharacter 0)
#guard scanChars (rawBytes [0x5C, 0x75, 0x46, 0x46, 0x46, 0x45, 0x22]) =
  .error (.noncharacter 0)
#guard scanChars (rawBytes [0x5C, 0x75, 0x46, 0x46, 0x46, 0x46, 0x22]) =
  .error (.noncharacter 0)
#guard scanChars (rawBytes [0x5C, 0x75, 0x44, 0x42, 0x46, 0x46,
    0x5C, 0x75, 0x44, 0x46, 0x46, 0x46, 0x22]) = .error (.noncharacter 0)
#guard scanChars (rawBytes [0xEF, 0xB7, 0x90, 0x22]) = .error (.noncharacter 0)
#guard scanChars (rawBytes [0xEF, 0xBF, 0xBE, 0x22]) = .error (.noncharacter 0)
#guard scanChars (rawBytes [0xF4, 0x8F, 0xBF, 0xBF, 0x22]) = .error (.noncharacter 0)
#guard scanChars (rawBytes [0xF0, 0x9F, 0xBF, 0xBE, 0x22]) = .error (.noncharacter 0)

/-! ### The two readings: RFC 8259's grammar and our policy

`RfcText` admits §8.2's unpaired escape; `Policy` refuses its reading.  Both
witnesses are proofs, not sampled cases. -/

/-- §8.2's unpaired escape: an RFC text whose reading `Policy` refuses. -/
example : ∃ v : Value,
    RfcText (rawBytes [0x22, 0x5C, 0x75, 0x44, 0x45, 0x41, 0x44, 0x22]) v ∧
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

/-- The strict reading of the same bytes is the pair `\uD800\uDEAD`, one code
point, so the narrow reading is not the RFC one. -/
example : StrictText (rawBytes [0x22, 0x5C, 0x75, 0x44, 0x38, 0x30, 0x30,
    0x5C, 0x75, 0x44, 0x45, 0x41, 0x44, 0x22]) (.string [0x102AD]) := by
  unfold StrictText TextAt
  refine ⟨0, 14, by decide, ?_, by decide⟩
  refine ValueAt.string ?_
  unfold StringAt
  refine ⟨by decide, [], ?_, by decide⟩
  refine StrChars.cons ?_ StrChars.nil
  exact StrChar.escPair (hi := 0xD800) (lo := 0xDEAD)
    (hhi := by decide) (hlo := by decide) (hh := by decide) (hl := by decide)
    (hc := by decide) (hm := by decide)

/-! ### Mask regression (the packed-mask idiom, carried forward from the seam) -/

/-- The subtraction idiom: it looks like the packed mask but reports the byte
before a zero byte as a zero byte too. -/
def subtractIdiom (x : BitVec 64) : BitVec 64 :=
  let m := x ^^^ 0x2C2C2C2C2C2C2C2C
  (m - 0x0101010101010101) &&& ~~~m &&& 0x8080808080808080

#guard LeanLLVM.Vellum.swar 0x0000000000002D2C = 0x80
#guard LeanLLVM.Vellum.spec 0x0000000000002D2C = 0x80
#guard subtractIdiom 0x0000000000002D2C = 0x8080

/-! ### Parser fixtures

`parseBytes` at the default limits, observed through `decodeTape`, so an
accepted document is compared with the value its bytes spell. -/

def parses (input : Bytes) (v : Value) : Bool :=
  match parseBytes Limits.default input with
  | .ok t => decide (decodeTape t = some v)
  | .error _ => false

def refuses (input : Bytes) : Bool :=
  match parseBytes Limits.default input with
  | .error (.invalid _) => true
  | _ => false

def refusesWith (input : Bytes) (p : Reject → Bool) : Bool :=
  match parseBytes Limits.default input with
  | .error (.invalid r) => p r
  | _ => false

def parsesWith (l : Limits) (input : Bytes) (v : Value) : Bool :=
  match parseBytes l input with
  | .ok t => decide (decodeTape t = some v)
  | .error _ => false

/-- The error a parse reports; `outOfCapacity` is a sentinel no `ok` result is
read through, because every row below that uses it also asserts the verdict. -/
def errorWith (l : Limits) (input : Bytes) : ParseError :=
  match parseBytes l input with
  | .ok _ => .outOfCapacity
  | .error e => e

def isInvalid : ParseError → Bool
  | .invalid _ => true
  | _ => false

/-! #### Literals -/

#guard parses (ascii "null") .null
#guard parses (ascii "true") (.bool true)
#guard parses (ascii "false") (.bool false)
#guard refuses (ascii "nul")
#guard refuses (ascii "tru")
#guard refuses (ascii "True")
#guard refuses (ascii "NULL")

/-! #### Documents -/

#guard parses (ascii "0") (.number [0x30])
#guard parses (ascii "\"a\"") (.string [0x61])
#guard parses (ascii "[]") (.array [])
#guard parses (ascii "{}") (.object [])
#guard parses (ascii "[1,2]") (.array [.number [0x31], .number [0x32]])
#guard parses (ascii "{\"a\":1,\"a\":2}")
  (.object [([0x61], .number [0x31]), ([0x61], .number [0x32])])
#guard parses (ascii "{\"a\":1,\"b\":2,\"a\":3}")
  (.object [([0x61], .number [0x31]), ([0x62], .number [0x32]),
    ([0x61], .number [0x33])])
#guard parses (ascii "{\"\":0}") (.object [([], .number [0x30])])
#guard parses (ascii "{\"a\":{\"b\":[true,null]}}")
  (.object [([0x61], .object [([0x62], .array [.bool true, .null])])])
#guard parses (ascii "[ 1 , 2 ]") (.array [.number [0x31], .number [0x32]])
#guard parses (ascii "{\"a\" : 1}") (.object [([0x61], .number [0x31])])
#guard parses (ascii " 1 ") (.number [0x31])
#guard parses (rawBytes [0x09, 0x0D, 0x0A, 0x20, 0x31, 0x20, 0x0A])
  (.number [0x31])

/-! #### Trailing data -/

#guard refuses (ascii "1 2")
#guard refuses (ascii "1,")
#guard refuses (rawBytes [0x6E, 0x75, 0x6C, 0x6C, 0x00])
#guard refuses (ascii "[1]]")
#guard refuses (ascii "}:")
#guard parses (ascii " 1 ") (.number [0x31])

/-! #### Separators and closers, each with its control -/

#guard refuses (ascii "[1,]")
#guard parses (ascii "[1]") (.array [.number [0x31]])
#guard refuses (ascii "{\"a\":1,}")
#guard parses (ascii "{\"a\":1}") (.object [([0x61], .number [0x31])])
#guard refuses (ascii "[1 2]")
#guard parses (ascii "[1,2]") (.array [.number [0x31], .number [0x32]])
#guard refuses (ascii "{\"a\" 1}")
#guard refuses (ascii "{\"a\":1 \"b\":2}")
#guard refuses (ascii "[1,,2]")

/-! #### Byte-order mark -/

#guard refusesWith (rawBytes [0xEF, 0xBB, 0xBF, 0x31]) fun
  | .byteOrderMark => true
  | _ => false
#guard parses (ascii "1") (.number [0x31])

/-! #### Policy refusals name their reason -/

def isUnpairedSurrogate : Reject → Bool
  | .unpairedSurrogate _ => true
  | _ => false

def isNoncharacter : Reject → Bool
  | .noncharacter _ => true
  | _ => false

#guard refusesWith (ascii "\"\\uDEAD\"") isUnpairedSurrogate
#guard refusesWith (ascii "\"\\uFDD0\"") isNoncharacter
#guard refusesWith (ascii "\"\\uDBFF\\uDFFF\"") isNoncharacter
#guard refusesWith (rawBytes [0x22, 0xF4, 0x8F, 0xBF, 0xBF, 0x22]) isNoncharacter

/-! #### Empty input -/

#guard refuses (rawBytes [])
#guard refuses (rawBytes [0x20, 0x09, 0x0A])
#guard parses (ascii "1") (.number [0x31])

/-! #### Depth -/

#guard parsesWith { Limits.default with maxDepth := 3 } (ascii "[[[1]]]")
  (.array [.array [.array [.number [0x31]]]])
#guard errorWith { Limits.default with maxDepth := 2 } (ascii "[[[1]]]") =
  .depthExceeded
#guard parsesWith { Limits.default with maxDepth := 0 } (ascii "1") (.number [0x31])

/-! #### Capacity -/

#guard parsesWith { Limits.default with maxTokens := 5 } (ascii "[1,2]")
  (.array [.number [0x31], .number [0x32]])
#guard errorWith { Limits.default with maxTokens := 4 } (ascii "[1,2]") =
  .outOfCapacity
#guard isInvalid (errorWith { Limits.default with maxTokens := 1 } (ascii "01"))

/-! #### Length -/

#guard parsesWith { Limits.default with maxInput := 3 } (ascii "[1]")
  (.array [.number [0x31]])
#guard errorWith { Limits.default with maxInput := 2 } (ascii "[1]") = .inputTooLong
#guard errorWith { Limits.default with maxInput := 2 } (ascii "[x]") = .inputTooLong
#guard isInvalid (errorWith Limits.default (ascii "[x]"))

/-! #### Boundary offsets

`bq n` is a string of `n` `a`s with its real closing quote; `br k m` carries
`k` escaped backslashes, written in the doubled form JSON requires, so an
even/odd escaping bug shows up in the value. -/

def bq (n : Nat) : Bytes :=
  ascii ("\"" ++ String.ofList (List.replicate n 'a') ++ "\"")

def br (k m : Nat) : Bytes :=
  ascii ("\"" ++ String.ofList (List.replicate m 'a') ++
    String.ofList (List.replicate (2 * k) '\\') ++ "\"")

#guard parses (bq 30) (.string (List.replicate 30 97))
#guard parses (bq 31) (.string (List.replicate 31 97))
#guard parses (bq 32) (.string (List.replicate 32 97))
#guard parses (bq 62) (.string (List.replicate 62 97))
#guard parses (bq 63) (.string (List.replicate 63 97))
#guard parses (bq 64) (.string (List.replicate 64 97))

#guard parses (br 1 29) (.string (List.replicate 29 97 ++ List.replicate 1 92))
#guard parses (br 2 27) (.string (List.replicate 27 97 ++ List.replicate 2 92))
#guard parses (br 3 25) (.string (List.replicate 25 97 ++ List.replicate 3 92))
#guard parses (br 1 61) (.string (List.replicate 61 97 ++ List.replicate 1 92))
#guard parses (br 2 59) (.string (List.replicate 59 97 ++ List.replicate 2 92))
#guard parses (br 3 57) (.string (List.replicate 57 97 ++ List.replicate 3 92))

/-! #### A lexeme longer than a machine word is kept exactly -/

def bigLexeme : String := String.ofList (List.replicate 4096 '7')

#guard parses (ascii bigLexeme) (.number (ascii bigLexeme))

/-! ### The renderer's own fixtures

The corpus's accept rows compare renderings, so a rendering bug must not be able
to make a row vacuous: these pin the renderer on values whose rendering is not
in question. -/

#guard renderValue .null = "null"
#guard renderValue (.bool true) = "true"
#guard renderValue (.bool false) = "false"
#guard renderValue (.number [0x31]) = "#31"
#guard renderValue (.number [0x2D, 0x30]) = "#2d30"
#guard renderValue (.string []) = "\"\""
#guard renderValue (.string [0x61, 0x62]) = "\"97 98\""
#guard renderValue (.array []) = "[]"
#guard renderValue (.array [.number [0x31], .null]) = "[#31,null]"
#guard renderValue (.object []) = "{}"
#guard renderValue (.object [([0x61], .number [0x31])]) = "{\"97\":#31}"

end LeanLLVMTest.Json

/-! ### Axiom pins

The footprint of every soundness-claiming theorem and of the reflection lemmas.
No printed axiom list contains a `LeanLLVM.JSON` constant: every claim above
rests on a proof. -/

/-- info: 'LeanLLVM.JSON.parseRef_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.parseRef_sound

/-- info: 'LeanLLVM.JSON.parseRef_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.parseRef_complete

/-- info: 'LeanLLVM.JSON.tape_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.tape_valid

/-- info: 'LeanLLVM.JSON.decodeTape_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.decodeTape_correct

/-- info: 'LeanLLVM.JSON.accepted_is_rfc_text' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.accepted_is_rfc_text

/-- info: 'LeanLLVM.JSON.rfc_text_accepted_on_policy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.rfc_text_accepted_on_policy

/-- info: 'LeanLLVM.JSON.parseRef_inputTooLong' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.parseRef_inputTooLong

/-- info: 'LeanLLVM.JSON.parseRef_not_invalid_on_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.parseRef_not_invalid_on_valid

/-- info: 'LeanLLVM.JSON.decoded_number_is_span_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.decoded_number_is_span_bytes

/-- info: 'LeanLLVM.JSON.numLexB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.numLexB_iff

/-- info: 'LeanLLVM.JSON.numLexB_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.numLexB_nonempty

/-- info: 'LeanLLVM.JSON.scanChars_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.scanChars_iff

/-- info: 'LeanLLVM.JSON.valid_iff_strict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.valid_iff_strict

/-- info: 'LeanLLVM.JSON.utf8_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.utf8_scalar

/-- info: 'LeanLLVM.JSON.decoded_string_is_span_literal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.decoded_string_is_span_literal

/-! ### Statement pins

An axiom pin fixes the footprint, not the claim: a conclusion narrowed to
something weaker keeps the same footprint.  Each pin below restates the
theorem's type, so weakening a statement fails to elaborate here even when the
axioms listed above are unchanged. -/

open LeanLLVM.JSON in
example : ∀ (t : Tape) (v : Value), decodeTape t = some v →
    spansWellFormed t = true ∧ ValidDocument t.input v :=
  LeanLLVM.JSON.tape_valid

open LeanLLVM.JSON in
example : ∀ (b : Bytes) (cs : List Nat) (rest : Bytes),
    scanChars b = .ok (cs, rest) ↔ StrChars .strict b cs rest :=
  LeanLLVM.JSON.scanChars_iff

open LeanLLVM.JSON in
example : ∀ (bs : Bytes) (v : Value),
    (RfcText bs v ∧ Policy v) ↔ StrictText bs v :=
  LeanLLVM.JSON.valid_iff_strict

/-! ### The block layer

`LeanLLVM/JSON/ScanBlock.lean`'s theorems: the mask's lane reading, the
`List.ofFn` bridge, the take discipline, the 32-byte indexing bridge, the range
identity the body's unsigned comparison computes, and the block operation's
contract.  The last two are the ones the emitted classifier is checked against,
so their statements are restated below as well as their footprints. -/

/-- info: 'LeanLLVM.JSON.maskOfList_getLsbD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.maskOfList_getLsbD

/-- info: 'LeanLLVM.JSON.maskOf_eq_maskOfList' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.maskOf_eq_maskOfList

/-- info: 'LeanLLVM.JSON.maskOfList_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.maskOfList_take

/-- info: 'LeanLLVM.JSON.ofFn_of_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.ofFn_of_length

/-- info: 'LeanLLVM.JSON.tab_newline_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.tab_newline_range

/-- info: 'LeanLLVM.JSON.scanBlock_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.scanBlock_correct

open LeanLLVM.JSON in
example : ∀ {bs : List UInt8} {k : Nat} {b : UInt8}, k < 32 → bs[k]? = some b →
    (maskOfList bs).getLsbD k = IsStructOrSpaceB b :=
  @LeanLLVM.JSON.maskOfList_getLsbD

open LeanLLVM.JSON in
example : ∀ (st : ScanState) (block : Block32) (valid : Nat), valid ≤ 32 →
    (valid = 32 →
        scanBlock st block valid = ({ pos := st.pos + 32 }, maskOf block, .ok) ∧
        ∀ k : Fin 32, (maskOf block).getLsbD k.val = IsStructOrSpaceB (block k)) ∧
    (valid < 32 →
        scanBlock st block valid = (st, (0 : BlockInfo), .short)) :=
  LeanLLVM.JSON.scanBlock_correct
