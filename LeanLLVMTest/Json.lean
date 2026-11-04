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
def ascii (s : String) : Bytes := ByteString.literal s.toUTF8.toList

/-- A byte string from literal byte values. -/
def rawBytes (bs : List Nat) : Bytes := ByteString.literal (bs.map UInt8.ofNat)

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

#guard scanChars (rawBytes [0x5C, 0x22, 0x22]) = .ok ([0x22], ByteString.empty)
#guard scanChars (rawBytes [0x5C, 0x5C, 0x22]) = .ok ([0x5C], ByteString.empty)
#guard scanChars (rawBytes [0x5C, 0x2F, 0x22]) = .ok ([0x2F], ByteString.empty)
#guard scanChars (rawBytes [0x5C, 0x62, 0x5C, 0x66, 0x5C, 0x6E, 0x5C, 0x72,
    0x5C, 0x74, 0x22]) = .ok ([8, 12, 10, 13, 9], ByteString.empty)
#guard scanChars (rawBytes [0x5C, 0x75, 0x30, 0x30, 0x30, 0x30, 0x22]) =
  .ok ([0], ByteString.empty)
#guard scanChars (rawBytes [0x5C, 0x75, 0x30, 0x30, 0x65, 0x39, 0x22]) =
  .ok ([0xE9], ByteString.empty)

#guard scanChars (rawBytes [0x5C, 0x71, 0x22]) = .error (.badEscape 0)
#guard scanChars (rawBytes [0x5C, 0x75, 0x31, 0x32, 0x22]) = .error .ended
#guard scanChars (rawBytes [0x5C, 0x75, 0x5A, 0x5A, 0x5A, 0x5A, 0x22]) =
  .error (.badEscape 2)
#guard scanChars (rawBytes [0x61, 0x62, 0x63, 0x5C]) = .error .ended

/-! ### Strict UTF-8 (RFC 3629 §4) -/

#guard scanChars (rawBytes [0xC3, 0xA9, 0x22]) = .ok ([0xE9], ByteString.empty)
#guard scanChars (rawBytes [0xE2, 0x82, 0xAC, 0x22]) = .ok ([0x20AC], ByteString.empty)
#guard scanChars (rawBytes [0xF0, 0x90, 0x8D, 0x88, 0x22]) = .ok ([0x10348], ByteString.empty)
#guard scanChars (rawBytes [0xF0, 0x90, 0x80, 0x80, 0x22]) = .ok ([0x10000], ByteString.empty)
#guard scanChars (rawBytes [0xF4, 0x8F, 0xBF, 0xBD, 0x22]) = .ok ([0x10FFFD], ByteString.empty)

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

#guard scanChars (rawBytes [0x7F, 0x22]) = .ok ([0x7F], ByteString.empty)
#guard scanChars (rawBytes [0x00, 0x22]) = .error (.controlCharacter 0)
#guard scanChars (rawBytes [0x1F, 0x22]) = .error (.controlCharacter 0)
#guard scanChars (rawBytes [0x09, 0x22]) = .error (.controlCharacter 0)
#guard scanChars (rawBytes [0x0A, 0x22]) = .error (.controlCharacter 0)

/-! ### Surrogate pairs and unpaired escapes (RFC 8259 §7, §8.2; RFC 7493 §2.1) -/

#guard scanChars (rawBytes [0x5C, 0x75, 0x44, 0x38, 0x33, 0x34,
    0x5C, 0x75, 0x44, 0x44, 0x31, 0x45, 0x22]) = .ok ([0x1D11E], ByteString.empty)
#guard scanChars (rawBytes [0xF0, 0x9D, 0x84, 0x9E, 0x22]) = .ok ([0x1D11E], ByteString.empty)
#guard scanChars (rawBytes [0x5C, 0x75, 0x44, 0x38, 0x30, 0x30,
    0x5C, 0x75, 0x44, 0x45, 0x41, 0x44, 0x22]) = .ok ([0x102AD], ByteString.empty)

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
  .ok ([0xFFFD], ByteString.empty)
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
    refine ⟨by decide, ByteString.empty, ?_, by decide⟩
    refine StrChars.cons ?_ StrChars.nil
    exact StrChar.escLone (h0 := 0x44) (h1 := 0x45) (h2 := 0x41) (h3 := 0x44)
      (c := 0xDEAD) (rest := 0x22 +: ByteString.empty) rfl (by decide) (by decide)
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
  refine ⟨by decide, ByteString.empty, ?_, by decide⟩
  refine StrChars.cons ?_ StrChars.nil
  exact StrChar.escPair (h0 := 0x44) (h1 := 0x38) (h2 := 0x30) (h3 := 0x30)
    (l0 := 0x44) (l1 := 0x45) (l2 := 0x41) (l3 := 0x44)
    (hi := 0xD800) (lo := 0xDEAD) (c := 0x102AD) (rest := 0x22 +: ByteString.empty)
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

#guard parses (ascii "0") (.number (ByteString.literal [0x30]))
#guard parses (ascii "\"a\"") (.string [0x61])
#guard parses (ascii "[]") (.array [])
#guard parses (ascii "{}") (.object [])
#guard parses (ascii "[1,2]") (.array [.number (ByteString.literal [0x31]), .number (ByteString.literal [0x32])])
#guard parses (ascii "{\"a\":1,\"a\":2}")
  (.object [([0x61], .number (ByteString.literal [0x31])), ([0x61], .number (ByteString.literal [0x32]))])
#guard parses (ascii "{\"a\":1,\"b\":2,\"a\":3}")
  (.object [([0x61], .number (ByteString.literal [0x31])), ([0x62], .number (ByteString.literal [0x32])),
    ([0x61], .number (ByteString.literal [0x33]))])
#guard parses (ascii "{\"\":0}") (.object [([], .number (ByteString.literal [0x30]))])
#guard parses (ascii "{\"a\":{\"b\":[true,null]}}")
  (.object [([0x61], .object [([0x62], .array [.bool true, .null])])])
#guard parses (ascii "[ 1 , 2 ]") (.array [.number (ByteString.literal [0x31]), .number (ByteString.literal [0x32])])
#guard parses (ascii "{\"a\" : 1}") (.object [([0x61], .number (ByteString.literal [0x31]))])
#guard parses (ascii " 1 ") (.number (ByteString.literal [0x31]))
#guard parses (rawBytes [0x09, 0x0D, 0x0A, 0x20, 0x31, 0x20, 0x0A])
  (.number (ByteString.literal [0x31]))

/-! #### Trailing data -/

#guard refuses (ascii "1 2")
#guard refuses (ascii "1,")
#guard refuses (rawBytes [0x6E, 0x75, 0x6C, 0x6C, 0x00])
#guard refuses (ascii "[1]]")
#guard refuses (ascii "}:")
#guard parses (ascii " 1 ") (.number (ByteString.literal [0x31]))

/-! #### Separators and closers, each with its control -/

#guard refuses (ascii "[1,]")
#guard parses (ascii "[1]") (.array [.number (ByteString.literal [0x31])])
#guard refuses (ascii "{\"a\":1,}")
#guard parses (ascii "{\"a\":1}") (.object [([0x61], .number (ByteString.literal [0x31]))])
#guard refuses (ascii "[1 2]")
#guard parses (ascii "[1,2]") (.array [.number (ByteString.literal [0x31]), .number (ByteString.literal [0x32])])
#guard refuses (ascii "{\"a\" 1}")
#guard refuses (ascii "{\"a\":1 \"b\":2}")
#guard refuses (ascii "[1,,2]")

/-! #### Byte-order mark -/

#guard refusesWith (rawBytes [0xEF, 0xBB, 0xBF, 0x31]) fun
  | .byteOrderMark => true
  | _ => false
#guard parses (ascii "1") (.number (ByteString.literal [0x31]))

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
#guard parses (ascii "1") (.number (ByteString.literal [0x31]))

/-! #### Depth -/

#guard parsesWith { Limits.default with maxDepth := 3 } (ascii "[[[1]]]")
  (.array [.array [.array [.number (ByteString.literal [0x31])]]])
#guard errorWith { Limits.default with maxDepth := 2 } (ascii "[[[1]]]") =
  .depthExceeded
#guard parsesWith { Limits.default with maxDepth := 0 } (ascii "1") (.number (ByteString.literal [0x31]))

/-! #### Capacity -/

#guard parsesWith { Limits.default with maxTokens := 5 } (ascii "[1,2]")
  (.array [.number (ByteString.literal [0x31]), .number (ByteString.literal [0x32])])
#guard errorWith { Limits.default with maxTokens := 4 } (ascii "[1,2]") =
  .outOfCapacity
#guard isInvalid (errorWith { Limits.default with maxTokens := 1 } (ascii "01"))

/-! #### Length -/

#guard parsesWith { Limits.default with maxInput := 3 } (ascii "[1]")
  (.array [.number (ByteString.literal [0x31])])
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
#guard renderValue (.number (ByteString.literal [0x31])) = "#31"
#guard renderValue (.number (ByteString.literal [0x2D, 0x30])) = "#2d30"
#guard renderValue (.string []) = "\"\""
#guard renderValue (.string [0x61, 0x62]) = "\"97 98\""
#guard renderValue (.array []) = "[]"
#guard renderValue (.array [.number (ByteString.literal [0x31]), .null]) = "[#31,null]"
#guard renderValue (.object []) = "{}"
#guard renderValue (.object [([0x61], .number (ByteString.literal [0x31]))]) = "{\"97\":#31}"

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

/-- info: 'LeanLLVM.JSON.numRunFrom_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.numRunFrom_eq

/-- info: 'LeanLLVM.JSON.scanCharsEnd_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.scanCharsEnd_sound

/-- info: 'LeanLLVM.JSON.scanCharsEnd_ok_of_scanCharsFrom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.scanCharsEnd_ok_of_scanCharsFrom

/-- info: 'LeanLLVM.JSON.hasPrefixB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.hasPrefixB_iff

/-
No pin covered this lemma, so a proof change would have shown only through the
theorems that use it (`scanChars_eq` → `scanChars_iff` → the headline pins).  Its
`[propext]` comes from the proof route, not the statement: the four `by omega`
steps over negated conjunctions, each carrying `Classical.choice`, are now
`Nat.not_lt.mpr` (for `hlt`) and a transitive range split against `hbad`; the
`by decide` steps on the literal bytes are unchanged and were never the source.
-/
/-- info: 'LeanLLVM.JSON.scanCharsFrom_utf8_lead' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.scanCharsFrom_utf8_lead

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

/-- info: 'LeanLLVM.JSON.maskOfList_eq_maskOfListWith' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.maskOfList_eq_maskOfListWith

/-- info: 'LeanLLVM.JSON.maskOfListWith_getLsbD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.maskOfListWith_getLsbD

/-- info: 'LeanLLVM.JSON.blockAt_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.blockAt_apply

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
example : ∀ (bs : List UInt8), maskOfList bs = maskOfListWith IsStructOrSpaceB bs :=
  LeanLLVM.JSON.maskOfList_eq_maskOfListWith

open LeanLLVM.JSON in
example : ∀ {f : UInt8 → Bool} {bs : List UInt8} {k : Nat} {b : UInt8},
    k < 32 → bs[k]? = some b → (maskOfListWith f bs).getLsbD k = f b :=
  @LeanLLVM.JSON.maskOfListWith_getLsbD

open LeanLLVM.JSON in
example : ∀ (bs : Bytes) (i : Nat) (h : i + 32 ≤ bs.size) (k : Fin 32),
    blockAt bs i h k = bs[i + k.val] :=
  LeanLLVM.JSON.blockAt_apply

open LeanLLVM.JSON in
example : ∀ (st : ScanState) (block : Block32) (valid : Nat), valid ≤ 32 →
    (valid = 32 →
        scanBlock st block valid = ({ pos := st.pos + 32 }, maskOf block, .ok) ∧
        ∀ k : Fin 32, (maskOf block).getLsbD k.val = IsStructOrSpaceB (block k)) ∧
    (valid < 32 →
        scanBlock st block valid = (st, (0 : BlockInfo), .short)) :=
  LeanLLVM.JSON.scanBlock_correct

/-! ### The body state and the byte rule

`LeanLLVM/JSON/ScanBody.lean`'s theorems: the two initial states are well formed,
the byte rule preserves well-formedness, the UTF-8 requirement accepts exactly
`Utf8Char`'s byte counts, and it rejects both an out-of-range continuation byte
and a byte no character starts with.  The `BodyState.body` arity `example` sits
beside the definition in that module, where a re-added state field fails to
elaborate.  The two `step` rejections print no axiom at all: they are `decide` on
the definition, which is the instrument a `step` whose fallbacks read as the
`none` constructor cannot satisfy, because that `step` accepts both bytes. -/

/-- info: 'LeanLLVM.JSON.BodyState.init_wellFormed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.BodyState.init_wellFormed

/-- info: 'LeanLLVM.JSON.BodyState.body_wellFormed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.BodyState.body_wellFormed

/-- info: 'LeanLLVM.JSON.bodyStep_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.bodyStep_wellFormed

/-- info: 'LeanLLVM.JSON.utf8Len_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.utf8Len_iff

/-- info: 'LeanLLVM.JSON.utf8Char_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.utf8Char_length

/-- info: 'LeanLLVM.JSON.step_rejects_cont' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.step_rejects_cont

/-- info: 'LeanLLVM.JSON.step_rejects_lead' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.step_rejects_lead

open LeanLLVM.JSON in
example : BodyState.init.WellFormed :=
  LeanLLVM.JSON.BodyState.init_wellFormed

open LeanLLVM.JSON in
example : BodyState.body.WellFormed :=
  LeanLLVM.JSON.BodyState.body_wellFormed

open LeanLLVM.JSON in
example : ∀ {st : BodyState}, st.WellFormed → ∀ {b : UInt8} {st' : BodyState},
    bodyStep st b = .cont st' → st'.WellFormed :=
  @LeanLLVM.JSON.bodyStep_wellFormed

open LeanLLVM.JSON in
example : ∀ (b : Bytes) (n : Nat),
    utf8Len .none b = some n ↔
      ∃ (c : Nat) (rest : Bytes), Utf8Char b c rest ∧ b.length = rest.length + n :=
  LeanLLVM.JSON.utf8Len_iff

open LeanLLVM.JSON in
example : ∀ {b : Bytes} {c : Nat} {rest : Bytes}, Utf8Char b c rest →
    b.length = rest.length +
      (if c < 0x80 then 1 else if c < 0x800 then 2 else
        if c < 0x10000 then 3 else 4) :=
  @LeanLLVM.JSON.utf8Char_length

open LeanLLVM.JSON in
example : Utf8Need.step (.more 1 0x80 0xBF) 0x22 = Option.none :=
  LeanLLVM.JSON.step_rejects_cont

open LeanLLVM.JSON in
example : Utf8Need.step .none 0x80 = Option.none :=
  LeanLLVM.JSON.step_rejects_lead

/-! ### The window fold

`LeanLLVM/JSON/ScanWindow.lean`'s theorems, one per claim the fold makes: each mask
read back lane by lane on the carry the byte rule held at that lane, the
classification mask equal to the block layer's, the carry equal to the window's own
byte run, well-formedness preserved across a window, and the carry's composition over
two lists.  The alternative escape rule — parity over every backslash since the body's
opening quote — is refused by a theorem on a fixed body rather than by a `#guard`: a
comparison of two `Bool`s would assert nothing about the rule, while the theorem says
the alternative is not a description of the fold. -/

/-- info: 'LeanLLVM.JSON.windowOf_content_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.windowOf_content_agrees

/-- info: 'LeanLLVM.JSON.windowOf_delim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.windowOf_delim

/-- info: 'LeanLLVM.JSON.windowOf_stop_close' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.windowOf_stop_close

/-- info: 'LeanLLVM.JSON.windowOf_quote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.windowOf_quote

/-- info: 'LeanLLVM.JSON.windowOf_backslash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.windowOf_backslash

/-- info: 'LeanLLVM.JSON.windowOf_structural' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.windowOf_structural

/-- info: 'LeanLLVM.JSON.windowAt_structural' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.windowAt_structural

/-- info: 'LeanLLVM.JSON.windowOf_carry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.windowOf_carry

/-- info: 'LeanLLVM.JSON.windowOf_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.windowOf_wellFormed

/-- info: 'LeanLLVM.JSON.carryAt_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.carryAt_append

/-- info: 'LeanLLVM.JSON.backslashParityEscapes_not_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.backslashParityEscapes_not_refines

open LeanLLVM.JSON in
example : ∀ {bs : List UInt8} {st : BodyState} {k : Nat} {b : UInt8},
    k < 32 → bs[k]? = some b →
      (windowOf bs st).content.getLsbD k = IsContentLane (carryAt bs st k) b :=
  @LeanLLVM.JSON.windowOf_content_agrees

open LeanLLVM.JSON in
example : ∀ {bs : List UInt8} {st : BodyState} {k : Nat} {b : UInt8},
    k < 32 → bs[k]? = some b →
      (windowOf bs st).delim.getLsbD k =
        (match bodyStep (carryAt bs st k) b with | .closed => true | _ => false) :=
  @LeanLLVM.JSON.windowOf_delim

open LeanLLVM.JSON in
example : ∀ {bs : List UInt8} {st : BodyState} {k : Nat},
    (windowOf bs st).stop = some (.close k) → (windowOf bs st).delim.getLsbD k = true :=
  @LeanLLVM.JSON.windowOf_stop_close

open LeanLLVM.JSON in
example : ∀ {bs : List UInt8} {st : BodyState} {k : Nat} {b : UInt8},
    k < 32 → bs[k]? = some b → (∀ s, bodyStep (carryAt bs st k) b ≠ .refused s) →
      (windowOf bs st).quote.getLsbD k = IsQuoteB b :=
  @LeanLLVM.JSON.windowOf_quote

open LeanLLVM.JSON in
example : ∀ {bs : List UInt8} {st : BodyState} {k : Nat} {b : UInt8},
    k < 32 → bs[k]? = some b → (∀ s, bodyStep (carryAt bs st k) b ≠ .refused s) →
      (windowOf bs st).backslash.getLsbD k = IsBackslashB b :=
  @LeanLLVM.JSON.windowOf_backslash

open LeanLLVM.JSON in
example : ∀ (bs : List UInt8) (st : BodyState),
    (windowOf bs st).structural = maskOfList bs :=
  LeanLLVM.JSON.windowOf_structural

open LeanLLVM.JSON in
example : ∀ (bs : Bytes) (i : Nat) (h : i + 32 ≤ bs.size) (st : BodyState),
    (windowAt bs i h st).structural = (scanBlock ⟨i⟩ (blockAt bs i h) 32).2.1 :=
  LeanLLVM.JSON.windowAt_structural

open LeanLLVM.JSON in
example : ∀ (bs : List UInt8) (st : BodyState),
    (windowOf bs st).carry = carryAt bs st 32 :=
  LeanLLVM.JSON.windowOf_carry

open LeanLLVM.JSON in
example : ∀ {bs : List UInt8} {st : BodyState}, st.WellFormed →
    (windowOf bs st).carry.WellFormed :=
  @LeanLLVM.JSON.windowOf_wellFormed

open LeanLLVM.JSON in
example : ∀ (a b : List UInt8) (st : BodyState) (k : Nat),
    carryAt (a ++ b) st (a.length + k) = carryAt b (carryAt a st a.length) k :=
  LeanLLVM.JSON.carryAt_append

open LeanLLVM.JSON in
example :
    ¬ (∀ (bs : List UInt8) (k : Nat), k < 32 → bs[k]? = some 0x22 →
        ((windowOf bs BodyState.body).delim.getLsbD k = true ↔
          backslashParityEscapes bs k = false)) :=
  LeanLLVM.JSON.backslashParityEscapes_not_refines

/-! ### The run, the scan and the tail

`LeanLLVM/JSON/ScanString.lean`'s theorems, and the stop readback of
`LeanLLVM/JSON/ScanWindow.lean` that the window step consumes: the fold's stop is the
first lane the byte rule does not continue past, the run reaches that lane with the
fold's carry, the four bounds a `bodyRun` end satisfies, the tail's own bound, the
scan's window branch as an equation, and the block operation's cursor.  `scanStringAt_succ`
is the centre of these pins: a `scanStringAt` that matched the run, or that computed its
own `i + 32`, would keep every other pin here and every `#guard` while no longer
consuming the window.  The bounds are restated as well as pinned because a restatement is
what fixes their hypotheses, which a build alone does not check: a closing run's bound
stands without one, the two open-run bounds carry the start inside the input — the
early-stop one with the position short of the fuel — the window bound carries
`i + 32 ≤ bs.size`, and `tailRun_open_at` carries the start inside the input as well. -/

section

set_option maxRecDepth 10000

/-- info: 'LeanLLVM.JSON.ContinuesBefore' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.ContinuesBefore

/-- info: 'LeanLLVM.JSON.windowOf_stop_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.windowOf_stop_spec

/-- info: 'LeanLLVM.JSON.scanWindow_stop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.scanWindow_stop

/-- info: 'LeanLLVM.JSON.scanStringAt_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.scanStringAt_succ

/-- info: 'LeanLLVM.JSON.scanStringAt_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.scanStringAt_pos

/-- info: 'LeanLLVM.JSON.bodyRun_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.bodyRun_bound

/-- info: 'LeanLLVM.JSON.bodyRun_open_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.bodyRun_open_bound

/-- info: 'LeanLLVM.JSON.bodyRun_open_at_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.bodyRun_open_at_end

/-- info: 'LeanLLVM.JSON.bodyRun_open_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.bodyRun_open_window

/-- info: 'LeanLLVM.JSON.tailRun_open_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.tailRun_open_at

open LeanLLVM.JSON in
example : ∀ (bs : List UInt8) (st : BodyState) (k : Nat),
    ContinuesBefore bs st k =
      (∀ j, j < k → ∀ {b : UInt8}, bs[j]? = some b →
        ∃ st', bodyStep (carryAt bs st j) b = .cont st') :=
  fun _ _ _ => rfl

open LeanLLVM.JSON in
example : ∀ (bs : List UInt8) (st : BodyState),
    (match (windowOf bs st).stop with
     | none => ContinuesBefore bs st 32
     | some (.close k) =>
         k < 32 ∧ (∃ b : UInt8, bs[k]? = some b) ∧ ContinuesBefore bs st k ∧
           ∀ {b : UInt8}, bs[k]? = some b → bodyStep (carryAt bs st k) b = .closed
     | some (.refuse k s) =>
         k < 32 ∧ (∃ b : UInt8, bs[k]? = some b) ∧ ContinuesBefore bs st k ∧
           ∀ {b : UInt8}, bs[k]? = some b → bodyStep (carryAt bs st k) b = .refused s) :=
  fun _ _ => LeanLLVM.JSON.windowOf_stop_spec

open LeanLLVM.JSON in
example : ∀ (bs : Bytes) (i : Nat) (h : i + 32 ≤ bs.size) (st : BodyState),
    bodyRun bs 32 i st =
      match (windowAt bs i h st).stop with
      | some (.close k) => .closed (i + k + 1)
      | some (.refuse k s) => .refused s (i + k)
      | none => .open (windowAt bs i h st).carry (i + 32) :=
  LeanLLVM.JSON.scanWindow_stop

open LeanLLVM.JSON in
example : ∀ (bs : Bytes) (fuel i : Nat) (st : BodyState),
    scanStringAt bs (fuel + 1) i st =
      (if h : i + 32 ≤ bs.size then
        match (windowAt bs i h st).stop with
        | some (.close k) => .ok (i + k + 1)
        | some (.refuse k s) => .error (s, i + k)
        | none =>
            scanStringAt bs fuel (scanBlock ⟨i⟩ (blockAt bs i h) 32).1.pos
              (windowAt bs i h st).carry
      else tailRun bs i st) :=
  LeanLLVM.JSON.scanStringAt_succ

open LeanLLVM.JSON in
example : ∀ (bs : Bytes) (i : Nat) (h : i + 32 ≤ bs.size),
    (scanBlock ⟨i⟩ (blockAt bs i h) 32).1.pos = i + 32 :=
  LeanLLVM.JSON.scanStringAt_pos

open LeanLLVM.JSON in
example : ∀ {bs : Bytes} {fuel i : Nat} {st : BodyState} {k : Nat},
    bodyRun bs fuel i st = .closed k → i < k ∧ k ≤ i + fuel ∧ k ≤ bs.size :=
  @LeanLLVM.JSON.bodyRun_bound

open LeanLLVM.JSON in
example : ∀ {bs : Bytes} {fuel i pos : Nat} {st st' : BodyState},
    i ≤ bs.size → bodyRun bs fuel i st = .open st' pos →
      i ≤ pos ∧ pos ≤ min (i + fuel) bs.size :=
  @LeanLLVM.JSON.bodyRun_open_bound

open LeanLLVM.JSON in
example : ∀ {bs : Bytes} {fuel i pos : Nat} {st st' : BodyState},
    i ≤ bs.size → bodyRun bs fuel i st = .open st' pos → pos < i + fuel →
      pos = bs.size :=
  @LeanLLVM.JSON.bodyRun_open_at_end

open LeanLLVM.JSON in
example : ∀ {bs : Bytes} {i pos : Nat} {st st' : BodyState},
    i + 32 ≤ bs.size → bodyRun bs 32 i st = .open st' pos → pos = i + 32 :=
  @LeanLLVM.JSON.bodyRun_open_window

open LeanLLVM.JSON in
example : ∀ {bs : Bytes} {i pos : Nat} {st st' : BodyState},
    i ≤ bs.size → bodyRun bs (bs.size - i) i st = .open st' pos → pos = bs.size :=
  @LeanLLVM.JSON.tailRun_open_at

end

/-! ### The refinement

`LeanLLVM/JSON/ScanBlocks.lean`: the whole-scan statement `docs/contract.md:89` names, and
the three cases the block model was opened with.  Those cases come first because they are
the composition in miniature: a surrogate pair whose twelve bytes the run consumes before
the quote closes it, and a control byte the fold refuses at the lane the run refuses at.
The character that straddles a window boundary is scanned below, with the one wholly
inside a window, so the two splits are read together.  Each `#guard` writes its expectation
out by hand; none reads a value back out of the definition it tests.  Then the footprints,
and a restatement of each statement beside its pin, because a build passes for a theorem
that grew a hypothesis and a footprint does not name a conclusion. -/

namespace LeanLLVMTest.Json

open LeanLLVM.JSON

/-- `\uD83D\uDE00` and the quote that follows it: twelve bytes of escape, and the fold's
only delimiter lane is the thirteenth. -/
def pairWindow : List UInt8 :=
  [0x5C, 0x75, 0x44, 0x38, 0x33, 0x44, 0x5C, 0x75, 0x44, 0x45, 0x30, 0x30, 0x22]

#guard (windowOf pairWindow BodyState.body).stop = some (.close 12)
#guard (windowOf pairWindow BodyState.body).delim = ((1 : BitVec 32) <<< 12)
#guard bodyRun (ByteString.literal pairWindow) 13 0 BodyState.body = .closed 13

/-- A content lane, then a control byte, then the quote: the fold refuses where the run
refuses, and the refusal is the string stage's to read. -/
def controlWindow : List UInt8 := [0x61, 0x01, 0x22]

#guard (windowOf controlWindow BodyState.body).stop = some (.refuse 1 .control)
#guard bodyRun (ByteString.literal controlWindow) 2 0 BodyState.body =
  .refused .control 1

/-- The same window with the control byte replaced by a content byte: the detector that
refused lane one finds the closing lane instead, so the refusal above is the control
byte's and not a detector that refuses every lane. -/
def contentWindow : List UInt8 := [0x61, 0x62, 0x22]

#guard (windowOf contentWindow BodyState.body).stop = some (.close 2)
#guard bodyRun (ByteString.literal contentWindow) 3 0 BodyState.body = .closed 3

/- The one-character body, `"a"`: the body state starts inside the body, so the second
quote closes rather than opens.  The scan and the reference scan are asserted separately,
so neither reading is taken from the other. -/
#guard scanStringBlocks (rawBytes [0x22, 0x61, 0x22]) 0 = .ok 3
#guard ((scanCharsEnd (rawBytes [0x22, 0x61, 0x22]) 1 0).map (fun p => (p.1, p.2.val))) =
  .ok ([0x61], 3)

/-- info: 'LeanLLVM.JSON.scan_simd_refines_scalar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.scan_simd_refines_scalar

/-- info: 'LeanLLVM.JSON.scanStringBlocks_ok_of_scanCharsEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.scanStringBlocks_ok_of_scanCharsEnd

/-- info: 'LeanLLVM.JSON.scanStringBlocks_refusal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.scanStringBlocks_refusal

/-- info: 'LeanLLVM.JSON.tailRun_ended' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.JSON.tailRun_ended

example : ∀ (bs : Bytes),
    (∀ (q : Nat) (cs : List Nat) (stop : { n : Nat // n ≤ bs.size }),
        bs[q]? = some 0x22 → scanCharsEnd bs (q + 1) 0 = .ok (cs, stop) →
          scanStringBlocks bs q = .ok stop.val) ∧
    (∀ (q : Nat) {k : Nat},
        bs[q]? = some 0x22 → scanStringBlocks bs q = .ok k →
          q < k ∧ k ≤ bs.size ∧ bs[k - 1]? = some 0x22) :=
  LeanLLVM.JSON.scan_simd_refines_scalar

example : ∀ {bs : Bytes} {q : Nat} {cs : List Nat} {stop : { n : Nat // n ≤ bs.size }},
    bs[q]? = some 0x22 → scanCharsEnd bs (q + 1) 0 = .ok (cs, stop) →
      scanStringBlocks bs q = .ok stop.val :=
  @LeanLLVM.JSON.scanStringBlocks_ok_of_scanCharsEnd

example : ∀ {bs : Bytes} {q : Nat} {s : Refusal}, bs[q]? = some 0x22 →
    scanStringBlocks bs q = .error s →
      ∀ (cs : List Nat) (stop : { n : Nat // n ≤ bs.size }),
        scanCharsEnd bs (q + 1) 0 ≠ .ok (cs, stop) :=
  @LeanLLVM.JSON.scanStringBlocks_refusal

example : ∀ (bs : Bytes) (i : Nat), bs.size ≤ i → ∀ (st : BodyState),
    tailRun bs i st = .error (.ended, i) :=
  LeanLLVM.JSON.tailRun_ended

end LeanLLVMTest.Json

/-! ### Fixed windows and tails

The calls the theorem statements quantify over, as closed decisions: one full block read
field by field in two body states, both escape parities on the byte rule's own decision,
the refused lane, a two-byte character split across a window boundary and the same
character carried wholly inside one, a close inside the second window, and the tail of the
last ten bytes.  Every equality and every refusal below has an affirmative control in
this run — the same bytes in a neighbouring state, or the same reading on a window that
clears, closes or accepts — so a fold or a run that answered one way for every input
would fail one of the pair.

No expectation is read back out of the definition it tests: the masks, stops and indices
are hand-written constants, and the two-against-three-backslash pair is the control that
makes the parity reading a reading rather than a constant.  The footprints and statement
restatements for these theorems are in the sections above, beside the module each pins. -/

namespace LeanLLVMTest.Json

open LeanLLVM.JSON

/-- The block: a quote, a backslash and the byte it escapes, a tab, content lanes, and a
two-byte character across the last two lanes. -/
def specBlock : Block32 :=
  fun k =>
    match k.val with
    | 0 => 0x22
    | 1 => 0x5C
    | 2 => 0x6E
    | 3 => 0x09
    | 30 => 0xC3
    | 31 => 0xA9
    | _ => 0x61

/-- The same block as the lane list the fold reads. -/
def specWindow : List UInt8 := List.ofFn specBlock

/- Outside a body the quote at lane zero opens one, the tab at lane three is the body's
own refusal, lanes four to twenty-nine are content, and the two-byte character completes
inside the window: no delimiter, and a carry that is the body state.  `structural` is the
block's decision and is the same in both states, which is what makes its equality with
`maskOf` a claim about the block rather than about the state. -/
#guard (windowOf specWindow BodyState.init).structural = (0x0000000B : BitVec 32)
#guard (windowOf specWindow BodyState.init).quote = (0x00000001 : BitVec 32)
#guard (windowOf specWindow BodyState.init).backslash = (0x00000002 : BitVec 32)
#guard (windowOf specWindow BodyState.init).content = (0x3FFFFFF0 : BitVec 32)
#guard (windowOf specWindow BodyState.init).delim = (0 : BitVec 32)
#guard (windowOf specWindow BodyState.init).stop = some (.refuse 3 .control)
#guard (windowOf specWindow BodyState.init).carry = BodyState.body
#guard (windowOf specWindow BodyState.init).structural = maskOf specBlock

/- The control: the same bytes read as a body already open, where the first quote closes
it and the tab is refused behind that earlier stop.  `delim` and `stop` move; the three
masks that carry the block's own decisions do not. -/
#guard (windowOf specWindow BodyState.body).delim = (0x00000001 : BitVec 32)
#guard (windowOf specWindow BodyState.body).stop = some (.close 0)
#guard (windowOf specWindow BodyState.body).structural = maskOf specBlock
#guard (windowOf specWindow BodyState.body).content = (0x3FFFFFF0 : BitVec 32)
#guard (windowOf specWindow BodyState.body).quote = (0x00000001 : BitVec 32)
#guard (windowOf specWindow BodyState.body).backslash = (0x00000002 : BitVec 32)

/- Two backslashes and the quote: the run's parity is even at the second quote, so it
closes the body, and the opening quote at lane zero is the only other quote lane. -/
def evenRunWindow : List UInt8 := [0x22, 0x5C, 0x5C, 0x22]

#guard (windowOf evenRunWindow BodyState.init).stop = some (.close 3)
#guard (windowOf evenRunWindow BodyState.init).delim = (0x00000008 : BitVec 32)
#guard (windowOf evenRunWindow BodyState.init).content = (0 : BitVec 32)

/- One backslash, then the quote: the parity is odd, the quote is escaped, and the body
does not close — the same reading, the opposite side. -/
def oddRunWindow : List UInt8 := [0x5C, 0x22]

#guard (windowOf oddRunWindow BodyState.body).stop = none
#guard (windowOf oddRunWindow BodyState.body).delim = (0 : BitVec 32)
#guard (windowOf oddRunWindow BodyState.body).quote = (0x00000002 : BitVec 32)

/- Three backslashes and the quote: odd again, so still no close.  The backslash lane is
three bits wide and the quote lane is marked while the delimiter is not, which is what
keeps the quote lane and the delimiter lane apart. -/
def oddRunThree : List UInt8 := [0x5C, 0x5C, 0x5C, 0x22]

#guard (windowOf oddRunThree BodyState.body).stop = none
#guard (windowOf oddRunThree BodyState.body).delim = (0 : BitVec 32)
#guard (windowOf oddRunThree BodyState.body).backslash = (0x00000007 : BitVec 32)
#guard (windowOf oddRunThree BodyState.body).quote = (0x00000008 : BitVec 32)

/- The control for both parities: two backslashes and the quote close at lane two. -/
#guard (windowOf [0x5C, 0x5C, 0x22] BodyState.body).stop = some (.close 2)

/-- A content lane, a backslash and the quote it escapes, then a content lane: the
escaped quote is neither a delimiter nor content, and the fold's `content` lane is the
predicate's decision on every lane of the window. -/
def escapeLaneWindow : List UInt8 := [0x61, 0x5C, 0x22, 0x62]

#guard (windowOf escapeLaneWindow BodyState.body).content = (0x00000009 : BitVec 32)
#guard (windowOf escapeLaneWindow BodyState.body).delim = (0 : BitVec 32)
#guard (windowOf escapeLaneWindow BodyState.body).stop = none
#guard (windowOf escapeLaneWindow BodyState.body).content.getLsbD 2 = false
#guard IsContentLane (carryAt escapeLaneWindow BodyState.body 2) 0x22 = false
#guard (windowOf escapeLaneWindow BodyState.body).content.getLsbD 0 = true
#guard IsContentLane (carryAt escapeLaneWindow BodyState.body 0) 0x61 = true
#guard (escapeLaneWindow.zipIdx.take 32).all (fun p =>
  (windowOf escapeLaneWindow BodyState.body).content.getLsbD p.2 =
    IsContentLane (carryAt escapeLaneWindow BodyState.body p.2) p.1)

/- The closing quote's own lane, for the same reading: content one at lane zero and the
delimiter set at lane one. -/
#guard (windowOf [0x61, 0x22] BodyState.body).content = (0x00000001 : BitVec 32)
#guard (windowOf [0x61, 0x22] BodyState.body).delim = (0x00000002 : BitVec 32)
#guard IsContentLane (carryAt [0x61, 0x22] BodyState.body 1) 0x22 = false

/- A lead byte and the quote that follows it: the sequence is still owed at lane one, so
the rule refuses the quote as `badUtf8` and the quote lane is not set. -/
#guard (windowOf [0xC3, 0x22] BodyState.body).stop = some (.refuse 1 .badUtf8)
#guard (windowOf [0xC3, 0x22] BodyState.body).quote = (0 : BitVec 32)

/- The control: a content byte in place of the lead, where the quote lane is set and the
stop is the close. -/
#guard (windowOf [0x61, 0x22] BodyState.body).stop = some (.close 1)
#guard (windowOf [0x61, 0x22] BodyState.body).quote = (0x00000002 : BitVec 32)

/-- Thirty-one content lanes and the lead byte of a two-byte character in the last lane:
the window cannot clear the sequence, so its carry owes the continuation at lane
thirty-two.  The character wholly inside a window sits immediately below as its control. -/
def splitBoundary : List UInt8 := List.replicate 31 0x61 ++ [0xC3]

#guard (windowOf splitBoundary BodyState.body).stop = none
#guard (windowOf splitBoundary BodyState.body).content = (0x7FFFFFFF : BitVec 32)
#guard (windowOf splitBoundary BodyState.body).carry =
  (⟨true, false, Utf8Need.more 1 0x80 0xBF⟩ : BodyState)
#guard bodyRun (ByteString.literal (splitBoundary ++ [0xA9])) 32 0 BodyState.body =
  .open (⟨true, false, Utf8Need.more 1 0x80 0xBF⟩ : BodyState) 32

/-- The control: thirty content lanes, then the same two-byte character, both bytes inside
the one window — the fold's carry after thirty-one lanes still owes the continuation and
the thirty-second lane clears it.  The boundary case above and this one are the same
reading at the two sides of a window's edge. -/
def splitWindow : List UInt8 := List.replicate 30 0x61 ++ [0xC3, 0xA9]

#guard (carryAt splitWindow BodyState.body 31) =
  (⟨true, false, Utf8Need.more 1 0x80 0xBF⟩ : BodyState)
#guard (carryAt splitWindow BodyState.body 32) = BodyState.body
#guard (windowOf splitWindow BodyState.body).carry = BodyState.body
#guard (windowOf splitWindow BodyState.body).stop = none
#guard bodyRun (ByteString.literal splitWindow) 32 0 BodyState.body =
  .open BodyState.body 32

/-- The lead byte at carrier index thirty-two, its continuation at thirty-three: carried
into a body, the next step clears the sequence and the quote after it closes the body at
index thirty-four. -/
def splitBody : Bytes := ByteString.literal ((0x22 :: splitBoundary) ++ [0xA9, 0x22])

#guard scanStringBlocks splitBody 0 = .ok 35

/-- The control: the same carrier without the lead byte.  The continuation byte is then
read with nothing outstanding and the rule refuses it, so the acceptance above is the
carry's rather than a reading that ignores the requirement. -/
def noLeadBody : Bytes :=
  ByteString.literal ((0x22 :: List.replicate 32 0x61) ++ [0xA9, 0x22])

#guard scanStringBlocks noLeadBody 0 = .error (.badUtf8, 33)

/-- A body whose closing quote sits in the second window: the first window is all
content, and the second window's stop is its own lane seventeen, so the scan reports the
carrier index fifty-one without reading the bytes after the close. -/
def secondWindowBody : Bytes :=
  ByteString.literal ((0x22 :: List.replicate 49 0x61) ++ (0x22 :: List.replicate 20 0x61))

#guard scanStringBlocks secondWindowBody 0 = .ok 51

/-- The control: the same carrier with that quote replaced by a content byte, where no
window stops and the tail of six bytes runs out at the input's end. -/
def secondWindowOpen : Bytes :=
  ByteString.literal ((0x22 :: List.replicate 50 0x61) ++ List.replicate 20 0x61)

#guard scanStringBlocks secondWindowOpen 0 = .error (.ended, 65)

/-- A body with a control byte at index five, and the same body with a content byte
there. -/
def controlList : List UInt8 :=
  0x22 :: (List.replicate 4 0x61 ++ [0x01] ++ List.replicate 27 0x61 ++ [0x22])

def controlFreeList : List UInt8 :=
  0x22 :: (List.replicate 4 0x61 ++ [0x62] ++ List.replicate 27 0x61 ++ [0x22])

#guard (windowOf (controlList.drop 1) BodyState.body).stop = some (.refuse 4 .control)
#guard scanStringBlocks (ByteString.literal controlList) 0 = .error (.control, 5)

/- The control: the same lanes with a content byte, where the window has no stop and the
scan closes at the carrier's length. -/
#guard (windowOf (controlFreeList.drop 1) BodyState.body).stop = none
#guard scanStringBlocks (ByteString.literal controlFreeList) 0 = .ok 34

/- A two-byte character cut off after its lead byte is `ended` at the tail's start, and
the same input with the continuation and the quote is accepted. -/
#guard tailRun (rawBytes [0x22, 0x61, 0xC3]) 1 BodyState.body = .error (.ended, 1)
#guard scanStringBlocks (rawBytes [0x22, 0x61, 0xC3]) 0 = .error (.ended, 1)
#guard scanStringBlocks (rawBytes [0x22, 0x61, 0xC3, 0xA9, 0x22]) 0 = .ok 5

/- A stray continuation byte in a body: the requirement rejects it, so the scan reports
`badUtf8` at the byte's own index, and the same body with the lead byte in front of it is
accepted. -/
#guard scanStringBlocks (rawBytes [0x22, 0xC3, 0x22]) 0 = .error (.badUtf8, 2)
#guard scanStringBlocks (rawBytes [0x22, 0xC3, 0xA9, 0x22]) 0 = .ok 4

/- A body with no closing quote is `ended` at the body's first byte, and the control
appends the quote and closes. -/
#guard scanStringBlocks (rawBytes [0x22, 0x61, 0x62]) 0 = .error (.ended, 1)
#guard scanStringBlocks (rawBytes [0x22, 0x61, 0x62, 0x22]) 0 = .ok 4

/-- A closing quote in the last ten bytes: the window at index one covers the first
thirty-two body bytes, and the ten bytes after it are the tail, stepped one at a time.
The scan's stop and the reference scan's are asserted separately, so neither is taken
from the other. -/
def tailBody : Bytes := ByteString.literal (0x22 :: (List.replicate 41 0x61 ++ [0x22]))

#guard tailBody.size = 43
#guard tailBody.size - 33 = 10
#guard scanStringBlocks tailBody 0 = .ok 43
#guard ((scanCharsEnd tailBody 1 0).map (fun p => p.2.val)) = .ok 43

end LeanLLVMTest.Json

/-! ### The emitted classifier body

`LeanLLVM/Vellum/JsonClassifyIR.lean` pins the fixture, builds its AST
register by register, and proves the body's contract against the block layer:
the packed lanes are the block mask, the outcome does not depend on the
allocator state the run is seeded with, and an unreadable block is `ub`.  The
pack fact it consumes is `lanesToNat_testBit`; the `BitVec` side of the mask
proof reaches it through core's `BitVec.getLsbD_ofNat`.  Each statement is
restated below beside its footprint. -/

/-- info: 'LeanLLVM.lanesToNat_testBit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.lanesToNat_testBit

-- `Classical.choice` in the two footprints below is inherited, not entailed:
-- `zip_replicate_right` → `classify32_block` → `classify32_step` carries it
-- from core's `Nat.right_eq_add` (itself `by omega`), which applies
-- `Classical.propDecidable` to `b = a + b` and `a = 0` — both
-- `Nat.decEq`-decidable.  It is a core tactic artefact, not an arbitrary-`Prop`
-- frame, and not `bv_decide`.
/--
info: 'LeanLLVM.Vellum.JsonClassifyIR.classify32_next_independent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.Vellum.JsonClassifyIR.classify32_next_independent

/--
info: 'LeanLLVM.Vellum.JsonClassifyIR.scannerLLVM_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.Vellum.JsonClassifyIR.scannerLLVM_refines

/--
info: 'LeanLLVM.Vellum.JsonClassifyIR.classify32_undefined_of_no_read' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanLLVM.Vellum.JsonClassifyIR.classify32_undefined_of_no_read

open LeanLLVM.JSON LeanLLVM.Vellum.JsonClassifyIR in
example : ∀ (l : List (BitVec 1)) (k : Nat),
    (LeanLLVM.lanesToNat l).testBit k = (l[k]? = some (1 : BitVec 1)) :=
  @LeanLLVM.lanesToNat_testBit

open LeanLLVM.JSON LeanLLVM.Vellum.JsonClassifyIR in
example : ∀ (block : Block32) (mem : LeanLLVM.Mem) (p n m : Nat),
    LeanLLVM.readBytes mem p 32 = some (List.ofFn block) →
    LeanLLVM.runFuel LeanLLVM.noCalls 10000 classify32Function
        { (LeanLLVM.initState classify32Function [LeanLLVM.Value.ptr p]) with
          mem := mem, next := n } =
      LeanLLVM.runFuel LeanLLVM.noCalls 10000 classify32Function
        { (LeanLLVM.initState classify32Function [LeanLLVM.Value.ptr p]) with
          mem := mem, next := m } :=
  @classify32_next_independent

open LeanLLVM.JSON LeanLLVM.Vellum.JsonClassifyIR in
example : ∀ (block : Block32) (mem : LeanLLVM.Mem) (p : Nat),
    LeanLLVM.readBytes mem p 32 = some (List.ofFn block) →
    LeanLLVM.runFuel LeanLLVM.noCalls 10000 classify32Function
        { (LeanLLVM.initState classify32Function [LeanLLVM.Value.ptr p]) with
          mem := mem } =
      some (LeanLLVM.Outcome.ret
        (some (LeanLLVM.Value.int 32 (maskOf block))) mem) :=
  @scannerLLVM_refines

open LeanLLVM.JSON LeanLLVM.Vellum.JsonClassifyIR in
example : ∀ (mem : LeanLLVM.Mem) (p : Nat),
    LeanLLVM.readBytes mem p 32 = none →
    LeanLLVM.runFuel LeanLLVM.noCalls 10000 classify32Function
        { (LeanLLVM.initState classify32Function [LeanLLVM.Value.ptr p]) with
          mem := mem } = some LeanLLVM.Outcome.ub :=
  @classify32_undefined_of_no_read
