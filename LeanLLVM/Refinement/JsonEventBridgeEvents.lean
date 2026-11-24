/-
The event decoder against the token decoder, after canonicalisation.

`JsonEventValue` states the transfer `EventsParseValue`: a related record trace's
consumer events decode to the token decoder's value once the token decoder's
number lexemes are canonicalised.  This module is the first half of that proof,
the canonicalising token decoder itself:

* `parseValueKB` / `parseElemsKB` / `parseMembersKB` are `parseValueTB`'s
  structural cases with each number's lexeme rendered by `canonLexeme`, so the
  two decoders consume the same tokens and differ only in a number's value;
* `parseValueK t = (parseValueT t).bind canonValue` is the tape-level form the
  transfer's right-hand side uses;
* `parseValueKB_map` states the correspondence exactly: the canonicalising
  decoder's result is the token decoder's result with `canonValue`, `canonValues`
  or `canonMembers` applied to the value and the remainder untouched.

The event-side bisimulation is **not** proved here.  Proving `EventsParseValue`
also needs the record relation's token layout: `Stage2Records` alone admits
events `[kind 3, kind 4]` with tokens `[openBracket, comma, closeBracket]`, where
`valueOfEvents` returns `some (.array [])` and `parseValueTB` returns `none`, so
the relation alone does not satisfy the bisimulation.  The missing half is
therefore `decodeValue` success implying the token decoder's value and remainder
— the tape decoder's span-and-cursor discipline turned into the token list's
layout — which this module does not claim.
-/
import LeanLLVM.Refinement.JsonEventBridge
import LeanLLVM.Refinement.JsonCanon

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The canonicalising token decoder

`parseValueTB` with each number's lexeme replaced by `canonLexeme`'s rendering.
The structural cases are `parseValueTB`'s, so the two decoders consume the same
tokens and differ only in a number's value. -/

mutual

/-- One value at the head of a token list, with the tokens after it, numbers
canonically rendered. -/
def parseValueKB (bs : Bytes) : Nat → List Token →
    Option (JSON.Value × List Token)
  | 0, _ => none
  | _, [] => none
  | f + 1, tok :: rest =>
      match tok with
      | .null _ => some (.null, rest)
      | .bool b _ => some (.bool b, rest)
      | .number s =>
          match canonLexeme ((bs.drop s.start).take (s.stop - s.start)) with
          | some lex => some (.number lex, rest)
          | none => none
      | .string s =>
          match scanCharsEnd bs (s.start + 1) 0 with
          | .ok (cs, _) => some (.string cs, rest)
          | .error _ => none
      | .punct .openBracket _ =>
          match parseElemsKB bs f rest with
          | some (vs, rest') => some (.array vs, rest')
          | none => none
      | .punct .openBrace _ =>
          match parseMembersKB bs f rest with
          | some (ms, rest') => some (.object ms, rest')
          | none => none
      | _ => none

/-- Array elements, closed by `]`, numbers canonically rendered. -/
def parseElemsKB (bs : Bytes) : Nat → List Token →
    Option (List JSON.Value × List Token)
  | 0, _ => none
  | _, [] => none
  | _ + 1, .punct .closeBracket _ :: rest => some ([], rest)
  | f + 1, tok :: rest =>
      match parseValueKB bs f (tok :: rest) with
      | some (v, rest') =>
          match rest' with
          | .punct .comma _ :: rest'' =>
              match parseElemsKB bs f rest'' with
              | some (vs, r) => some (v :: vs, r)
              | none => none
          | .punct .closeBracket _ :: rest'' => some ([v], rest'')
          | _ => none
      | none => none

/-- Object members, closed by `}`, numbers canonically rendered. -/
def parseMembersKB (bs : Bytes) : Nat → List Token →
    Option (List (List Nat × JSON.Value) × List Token)
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
                  match parseValueKB bs f (v :: vs) with
                  | some (val, rest') =>
                      match rest' with
                      | .punct .comma _ :: rest'' =>
                          match parseMembersKB bs f rest'' with
                          | some (ms, r) => some ((cs, val) :: ms, r)
                          | none => none
                      | .punct .closeBrace _ :: rest'' => some ([(cs, val)], rest'')
                      | _ => none
                  | none => none
          | _ => none
  | _ + 1, _ :: _ => none

end

/-- **The tape's value, canonically rendered.**  `parseValueT`'s descent with the
number rendering applied, so it is the object the event decoder is compared with
in `JsonEventValue`'s `EventsParseValue`. -/
def parseValueK (t : JSON.Tape) : Option JSON.Value :=
  match parseValueTB t.input (t.tokens.length + 1) t.tokens with
  | some (v, []) => canonValue v
  | _ => none

/-- `parseValueK` is the canonicalisation of `parseValueT`: the bind on the
option is `parseValueT`'s own match, with `canonValue` read at the value it
returns. -/
theorem parseValueK_eq_bind (t : JSON.Tape) :
    parseValueK t = (parseValueT t).bind canonValue := by
  unfold parseValueK parseValueT
  cases h : parseValueTB t.input (t.tokens.length + 1) t.tokens with
  | none => rfl
  | some p =>
      obtain ⟨v, rest⟩ := p
      cases rest with
      | nil => rfl
      | cons tok rest => rfl

/-! ### The canonicalising decoder against the token decoder

The three functions are `parseValueTB`'s with the number arm mapped through
`canonLexeme`; containers recurse, so the correspondence is that the
canonicalising decoder is the token decoder's result with `canonValue` /
`canonValues` / `canonMembers` applied. -/

/-! The canonicalisation's constructors, so the correspondence's leaves reduce
without unfolding the whole mutual block. -/

@[simp] theorem canonLexeme_eq (l : Bytes) :
    canonLexeme l =
      (StrtodReader.reader l).map
        (fun d => ByteString.literal (bitsLexeme (strtodSpec d).toBits)) := rfl
@[simp] theorem canonValue_null : canonValue (JSON.Value.null) = some JSON.Value.null := rfl
@[simp] theorem canonValue_bool (b : Bool) :
    canonValue (JSON.Value.bool b) = some (JSON.Value.bool b) := rfl
@[simp] theorem canonValue_string (cs : List Nat) :
    canonValue (JSON.Value.string cs) = some (JSON.Value.string cs) := rfl
@[simp] theorem canonValue_number (l : Bytes) :
    canonValue (JSON.Value.number l) = (canonLexeme l).map JSON.Value.number := rfl
@[simp] theorem canonValue_array (vs : List JSON.Value) :
    canonValue (JSON.Value.array vs) = (canonValues vs).map JSON.Value.array := rfl
@[simp] theorem canonValue_object (ms : List (List Nat × JSON.Value)) :
    canonValue (JSON.Value.object ms) = (canonMembers ms).map JSON.Value.object := rfl
@[simp] theorem canonValues_nil : canonValues ([] : List JSON.Value) = some [] := rfl
@[simp] theorem canonValues_cons (v : JSON.Value) (vs : List JSON.Value) :
    canonValues (v :: vs) =
      (canonValue v).bind
        (fun v' => (canonValues vs).map (fun vs' => v' :: vs')) := rfl
@[simp] theorem canonMembers_nil :
    canonMembers ([] : List (List Nat × JSON.Value)) = some [] := rfl
@[simp] theorem canonMembers_cons (k : List Nat) (v : JSON.Value)
    (ms : List (List Nat × JSON.Value)) :
    canonMembers ((k, v) :: ms) =
      (canonValue v).bind
        (fun v' => (canonMembers ms).map (fun ms' => (k, v') :: ms')) := rfl

/-- The element list's successor step: for any head token that is not the
closing bracket, the canonicalising list is the token list's canonicalisation.
The head token's kind is irrelevant beyond the parser's own branch, so the step
is stated once and the main correspondence applies it to every value head. -/
private theorem elems_succ_eq (bs : Bytes) (f : Nat) (tok : Token)
    (rest : List Token)
    (hV : ∀ toks, parseValueKB bs f toks =
      (parseValueTB bs f toks).bind
        (fun p => (canonValue p.1).map (fun v => (v, p.2))))
    (hE : ∀ toks, parseElemsKB bs f toks =
      (parseElemsTB bs f toks).bind
        (fun p => (canonValues p.1).map (fun vs => (vs, p.2))))
    (hnot : ∀ s : Span, tok ≠ JSON.Token.punct .closeBracket s) :
    parseElemsKB bs (f + 1) (tok :: rest) =
      (parseElemsTB bs (f + 1) (tok :: rest)).bind
        (fun p => (canonValues p.1).map (fun vs => (vs, p.2))) := by
  cases tok with
  | punct k s =>
      cases k with
      | closeBracket => exact absurd rfl (hnot s)
      | openBracket =>
          simp only [parseElemsKB, parseElemsTB, hV, Option.bind_some,
            Option.map_some]
          cases hv : parseValueTB bs f
              (JSON.Token.punct .openBracket s :: rest) with
          | none => simp [hv]
          | some p =>
              obtain ⟨v, rest'⟩ := p
              cases rest' with
              | nil => cases hc : canonValue v <;> simp [hv, hc]
              | cons tok2 rest'' =>
                  cases tok2 with
                  | punct k2 s2 =>
                      cases k2 with
                      | closeBracket =>
                          cases hc : canonValue v <;> simp [hv, hc]
                      | comma =>
                          cases he : parseElemsTB bs f rest'' with
                          | none =>
                              cases hc : canonValue v <;> simp [hv, hc, he, hE]
                          | some q =>
                              obtain ⟨vs, r⟩ := q
                              cases h2 : canonValues vs with
                              | none =>
                                  cases hc : canonValue v <;>
                                    simp [hv, hc, he, h2, hE]
                              | some vs' =>
                                  cases hc : canonValue v <;>
                                    simp [hv, hc, he, h2, hE]
                      | _ =>
                          cases hc : canonValue v <;> simp [hv, hc]
                  | _ => cases hc : canonValue v <;> simp [hv, hc]
      | openBrace =>
          simp only [parseElemsKB, parseElemsTB, hV, Option.bind_some,
            Option.map_some]
          cases hv : parseValueTB bs f
              (JSON.Token.punct .openBrace s :: rest) with
          | none => simp [hv]
          | some p =>
              obtain ⟨v, rest'⟩ := p
              cases rest' with
              | nil => cases hc : canonValue v <;> simp [hv, hc]
              | cons tok2 rest'' =>
                  cases tok2 with
                  | punct k2 s2 =>
                      cases k2 with
                      | closeBracket =>
                          cases hc : canonValue v <;> simp [hv, hc]
                      | comma =>
                          cases he : parseElemsTB bs f rest'' with
                          | none =>
                              cases hc : canonValue v <;> simp [hv, hc, he, hE]
                          | some q =>
                              obtain ⟨vs, r⟩ := q
                              cases h2 : canonValues vs with
                              | none =>
                                  cases hc : canonValue v <;>
                                    simp [hv, hc, he, h2, hE]
                              | some vs' =>
                                  cases hc : canonValue v <;>
                                    simp [hv, hc, he, h2, hE]
                      | _ =>
                          cases hc : canonValue v <;> simp [hv, hc]
                  | _ => cases hc : canonValue v <;> simp [hv, hc]
      | closeBrace =>
          simp only [parseElemsKB, parseElemsTB, hV, Option.bind_some,
            Option.map_some]
          cases hv : parseValueTB bs f
              (JSON.Token.punct .closeBrace s :: rest) with
          | none => simp [hv]
          | some p =>
              obtain ⟨v, rest'⟩ := p
              cases rest' with
              | nil => cases hc : canonValue v <;> simp [hv, hc]
              | cons tok2 rest'' =>
                  cases tok2 with
                  | punct k2 s2 =>
                      cases k2 with
                      | closeBracket =>
                          cases hc : canonValue v <;> simp [hv, hc]
                      | comma =>
                          cases he : parseElemsTB bs f rest'' with
                          | none =>
                              cases hc : canonValue v <;> simp [hv, hc, he, hE]
                          | some q =>
                              obtain ⟨vs, r⟩ := q
                              cases h2 : canonValues vs with
                              | none =>
                                  cases hc : canonValue v <;>
                                    simp [hv, hc, he, h2, hE]
                              | some vs' =>
                                  cases hc : canonValue v <;>
                                    simp [hv, hc, he, h2, hE]
                      | _ =>
                          cases hc : canonValue v <;> simp [hv, hc]
                  | _ => cases hc : canonValue v <;> simp [hv, hc]
      | comma =>
          simp only [parseElemsKB, parseElemsTB, hV, Option.bind_some,
            Option.map_some]
          cases hv : parseValueTB bs f
              (JSON.Token.punct .comma s :: rest) with
          | none => simp [hv]
          | some p =>
              obtain ⟨v, rest'⟩ := p
              cases rest' with
              | nil => cases hc : canonValue v <;> simp [hv, hc]
              | cons tok2 rest'' =>
                  cases tok2 with
                  | punct k2 s2 =>
                      cases k2 with
                      | closeBracket =>
                          cases hc : canonValue v <;> simp [hv, hc]
                      | comma =>
                          cases he : parseElemsTB bs f rest'' with
                          | none =>
                              cases hc : canonValue v <;> simp [hv, hc, he, hE]
                          | some q =>
                              obtain ⟨vs, r⟩ := q
                              cases h2 : canonValues vs with
                              | none =>
                                  cases hc : canonValue v <;>
                                    simp [hv, hc, he, h2, hE]
                              | some vs' =>
                                  cases hc : canonValue v <;>
                                    simp [hv, hc, he, h2, hE]
                      | _ =>
                          cases hc : canonValue v <;> simp [hv, hc]
                  | _ => cases hc : canonValue v <;> simp [hv, hc]
      | colon =>
          simp only [parseElemsKB, parseElemsTB, hV, Option.bind_some,
            Option.map_some]
          cases hv : parseValueTB bs f
              (JSON.Token.punct .colon s :: rest) with
          | none => simp [hv]
          | some p =>
              obtain ⟨v, rest'⟩ := p
              cases rest' with
              | nil => cases hc : canonValue v <;> simp [hv, hc]
              | cons tok2 rest'' =>
                  cases tok2 with
                  | punct k2 s2 =>
                      cases k2 with
                      | closeBracket =>
                          cases hc : canonValue v <;> simp [hv, hc]
                      | comma =>
                          cases he : parseElemsTB bs f rest'' with
                          | none =>
                              cases hc : canonValue v <;> simp [hv, hc, he, hE]
                          | some q =>
                              obtain ⟨vs, r⟩ := q
                              cases h2 : canonValues vs with
                              | none =>
                                  cases hc : canonValue v <;>
                                    simp [hv, hc, he, h2, hE]
                              | some vs' =>
                                  cases hc : canonValue v <;>
                                    simp [hv, hc, he, h2, hE]
                      | _ =>
                          cases hc : canonValue v <;> simp [hv, hc]
                  | _ => cases hc : canonValue v <;> simp [hv, hc]
  | null s =>
      simp only [parseElemsKB, parseElemsTB, hV, Option.bind_some,
        Option.map_some]
      cases hv : parseValueTB bs f (JSON.Token.null s :: rest) with
      | none => simp [hv]
      | some p =>
          obtain ⟨v, rest'⟩ := p
          cases rest' with
          | nil => cases hc : canonValue v <;> simp [hv, hc]
          | cons tok2 rest'' =>
              cases tok2 with
              | punct k2 s2 =>
                  cases k2 with
                  | closeBracket => cases hc : canonValue v <;> simp [hv, hc]
                  | comma =>
                      cases he : parseElemsTB bs f rest'' with
                      | none => cases hc : canonValue v <;> simp [hv, hc, he, hE]
                      | some q =>
                          obtain ⟨vs, r⟩ := q
                          cases h2 : canonValues vs with
                          | none =>
                              cases hc : canonValue v <;> simp [hv, hc, he, h2, hE]
                          | some vs' =>
                              cases hc : canonValue v <;> simp [hv, hc, he, h2, hE]
                  | _ => cases hc : canonValue v <;> simp [hv, hc]
              | _ => cases hc : canonValue v <;> simp [hv, hc]
  | bool b s =>
      simp only [parseElemsKB, parseElemsTB, hV, Option.bind_some,
        Option.map_some]
      cases hv : parseValueTB bs f (JSON.Token.bool b s :: rest) with
      | none => simp [hv]
      | some p =>
          obtain ⟨v, rest'⟩ := p
          cases rest' with
          | nil => cases hc : canonValue v <;> simp [hv, hc]
          | cons tok2 rest'' =>
              cases tok2 with
              | punct k2 s2 =>
                  cases k2 with
                  | closeBracket => cases hc : canonValue v <;> simp [hv, hc]
                  | comma =>
                      cases he : parseElemsTB bs f rest'' with
                      | none => cases hc : canonValue v <;> simp [hv, hc, he, hE]
                      | some q =>
                          obtain ⟨vs, r⟩ := q
                          cases h2 : canonValues vs with
                          | none =>
                              cases hc : canonValue v <;> simp [hv, hc, he, h2, hE]
                          | some vs' =>
                              cases hc : canonValue v <;> simp [hv, hc, he, h2, hE]
                  | _ => cases hc : canonValue v <;> simp [hv, hc]
              | _ => cases hc : canonValue v <;> simp [hv, hc]
  | number s =>
      simp only [parseElemsKB, parseElemsTB, hV, Option.bind_some,
        Option.map_some]
      cases hv : parseValueTB bs f (JSON.Token.number s :: rest) with
      | none => simp [hv]
      | some p =>
          obtain ⟨v, rest'⟩ := p
          cases rest' with
          | nil => cases hc : canonValue v <;> simp [hv, hc]
          | cons tok2 rest'' =>
              cases tok2 with
              | punct k2 s2 =>
                  cases k2 with
                  | closeBracket => cases hc : canonValue v <;> simp [hv, hc]
                  | comma =>
                      cases he : parseElemsTB bs f rest'' with
                      | none => cases hc : canonValue v <;> simp [hv, hc, he, hE]
                      | some q =>
                          obtain ⟨vs, r⟩ := q
                          cases h2 : canonValues vs with
                          | none =>
                              cases hc : canonValue v <;> simp [hv, hc, he, h2, hE]
                          | some vs' =>
                              cases hc : canonValue v <;> simp [hv, hc, he, h2, hE]
                  | _ => cases hc : canonValue v <;> simp [hv, hc]
              | _ => cases hc : canonValue v <;> simp [hv, hc]
  | string s =>
      simp only [parseElemsKB, parseElemsTB, hV, Option.bind_some,
        Option.map_some]
      cases hv : parseValueTB bs f (JSON.Token.string s :: rest) with
      | none => simp [hv]
      | some p =>
          obtain ⟨v, rest'⟩ := p
          cases rest' with
          | nil => cases hc : canonValue v <;> simp [hv, hc]
          | cons tok2 rest'' =>
              cases tok2 with
              | punct k2 s2 =>
                  cases k2 with
                  | closeBracket => cases hc : canonValue v <;> simp [hv, hc]
                  | comma =>
                      cases he : parseElemsTB bs f rest'' with
                      | none => cases hc : canonValue v <;> simp [hv, hc, he, hE]
                      | some q =>
                          obtain ⟨vs, r⟩ := q
                          cases h2 : canonValues vs with
                          | none =>
                              cases hc : canonValue v <;> simp [hv, hc, he, h2, hE]
                          | some vs' =>
                              cases hc : canonValue v <;> simp [hv, hc, he, h2, hE]
                  | _ => cases hc : canonValue v <;> simp [hv, hc]
              | _ => cases hc : canonValue v <;> simp [hv, hc]

/-- The member list's successor step after a key and colon. -/
private theorem members_succ_eq (bs : Bytes) (f : Nat) (s : Span)
    (rest : List Token)
    (hV : ∀ toks, parseValueKB bs f toks =
      (parseValueTB bs f toks).bind
        (fun p => (canonValue p.1).map (fun v => (v, p.2))))
    (hM : ∀ toks, parseMembersKB bs f toks =
      (parseMembersTB bs f toks).bind
        (fun p => (canonMembers p.1).map (fun ms => (ms, p.2)))) :
    parseMembersKB bs (f + 1) (JSON.Token.string s :: rest) =
      (parseMembersTB bs (f + 1) (JSON.Token.string s :: rest)).bind
        (fun p => (canonMembers p.1).map (fun ms => (ms, p.2))) := by
  simp only [parseMembersKB, parseMembersTB]
  cases hs : scanCharsEnd bs (s.start + 1) 0 with
  | error e => simp [hs]
  | ok p =>
      obtain ⟨cs, stop⟩ := p
      cases rest with
      | nil => simp [hs]
      | cons tok1 rest1 =>
          cases tok1 with
          | punct k1 s1 =>
              cases k1 with
              | colon =>
                  cases rest1 with
                  | nil => simp [hs]
                  | cons v vs =>
                      simp only [hV]
                      cases hv : parseValueTB bs f (v :: vs) with
                      | none => simp [hs, hv]
                      | some p2 =>
                          obtain ⟨val, rest2⟩ := p2
                          cases rest2 with
                          | nil => cases hc : canonValue val <;> simp [hs, hv, hc]
                          | cons tok3 rest3 =>
                              cases tok3 with
                              | punct k3 s3 =>
                                  cases k3 with
                                  | comma =>
                                      cases hm : parseMembersTB bs f rest3 with
                                      | none =>
                                          cases hc : canonValue val <;>
                                            simp [hs, hv, hc, hm, hM]
                                      | some q =>
                                          obtain ⟨ms, r⟩ := q
                                          cases h2 : canonMembers ms with
                                          | none =>
                                              cases hc : canonValue val <;>
                                                simp [hs, hv, hc, hm, h2, hM]
                                          | some ms' =>
                                              cases hc : canonValue val <;>
                                                simp [hs, hv, hc, hm, h2, hM]
                                  | closeBrace =>
                                      cases hc : canonValue val <;>
                                        simp [hs, hv, hc]
                                  | _ => cases hc : canonValue val <;>
                                        simp [hs, hv, hc]
                              | _ => cases hc : canonValue val <;> simp [hs, hv, hc]
              | _ => simp [hs]
          | _ => simp [hs]

theorem parseValueKB_map (bs : Bytes) : ∀ f,
    (∀ toks, parseValueKB bs f toks =
      (parseValueTB bs f toks).bind
        (fun p => (canonValue p.1).map (fun v => (v, p.2)))) ∧
    (∀ toks, parseElemsKB bs f toks =
      (parseElemsTB bs f toks).bind
        (fun p => (canonValues p.1).map (fun vs => (vs, p.2)))) ∧
    (∀ toks, parseMembersKB bs f toks =
      (parseMembersTB bs f toks).bind
        (fun p => (canonMembers p.1).map (fun ms => (ms, p.2)))) := by
  intro f
  induction f with
  | zero =>
      refine ⟨?_, ?_, ?_⟩ <;> intro toks <;>
        simp only [parseValueKB, parseElemsKB, parseMembersKB, parseValueTB,
          parseElemsTB, parseMembersTB, Option.bind_none]
  | succ f ih =>
      obtain ⟨ihV, ihE, ihM⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · intro toks
        cases toks with
        | nil => simp only [parseValueKB, parseValueTB, Option.bind_none]
        | cons tok rest =>
          cases tok with
          | null s =>
              simp only [parseValueKB, parseValueTB, canonValue_null,
                Option.bind_some, Option.map_some]
          | bool b s =>
              simp only [parseValueKB, parseValueTB, canonValue_bool,
                Option.bind_some, Option.map_some]
          | number s =>
              simp only [parseValueKB, parseValueTB, canonValue_number,
                canonLexeme.eq_def]
              cases h : StrtodReader.reader
                  ((bs.drop s.start).take (s.stop - s.start)) with
              | none => simp [h]
              | some d => simp [h]
          | string s =>
              simp only [parseValueKB, parseValueTB, canonValue_string,
                Option.bind_some, Option.map_some]
              cases h : scanCharsEnd bs (s.start + 1) 0 with
              | error e => simp [h]
              | ok p => obtain ⟨cs, stop⟩ := p; simp [h]
          | punct k s =>
              cases k with
              | openBracket =>
                  simp only [parseValueKB, parseValueTB, ihE, canonValue_array,
                    Option.bind_some, Option.map_some, Option.map_map]
                  cases h : parseElemsTB bs f rest with
                  | none => simp [h]
                  | some p =>
                      obtain ⟨vs, r⟩ := p
                      cases hc : canonValues vs with
                      | none => simp [h, hc]
                      | some vs' => simp [h, hc]
              | openBrace =>
                  simp only [parseValueKB, parseValueTB, ihM, canonValue_object,
                    Option.bind_some, Option.map_some, Option.map_map]
                  cases h : parseMembersTB bs f rest with
                  | none => simp [h]
                  | some p =>
                      obtain ⟨ms, r⟩ := p
                      cases hc : canonMembers ms with
                      | none => simp [h, hc]
                      | some ms' => simp [h, hc]
              | closeBracket =>
                  simp only [parseValueKB, parseValueTB, Option.bind_none]
              | closeBrace =>
                  simp only [parseValueKB, parseValueTB, Option.bind_none]
              | comma =>
                  simp only [parseValueKB, parseValueTB, Option.bind_none]
              | colon =>
                  simp only [parseValueKB, parseValueTB, Option.bind_none]
      · intro toks
        cases toks with
        | nil => simp only [parseElemsKB, parseElemsTB, Option.bind_none]
        | cons tok rest =>
          cases tok with
          | punct k s =>
              cases k with
              | closeBracket =>
                  simp only [parseElemsKB, parseElemsTB, canonValues_nil,
                    Option.bind_some, Option.map_some]
              | openBracket =>
                  exact elems_succ_eq bs f _ rest ihV ihE
                    (by intro s' h; cases h)
              | openBrace =>
                  exact elems_succ_eq bs f _ rest ihV ihE
                    (by intro s' h; cases h)
              | closeBrace =>
                  exact elems_succ_eq bs f _ rest ihV ihE
                    (by intro s' h; cases h)
              | comma =>
                  exact elems_succ_eq bs f _ rest ihV ihE
                    (by intro s' h; cases h)
              | colon =>
                  exact elems_succ_eq bs f _ rest ihV ihE
                    (by intro s' h; cases h)
          | null s =>
              exact elems_succ_eq bs f _ rest ihV ihE (by intro s' h; cases h)
          | bool b s =>
              exact elems_succ_eq bs f _ rest ihV ihE (by intro s' h; cases h)
          | number s =>
              exact elems_succ_eq bs f _ rest ihV ihE (by intro s' h; cases h)
          | string s =>
              exact elems_succ_eq bs f _ rest ihV ihE (by intro s' h; cases h)
      · intro toks
        cases toks with
        | nil => simp only [parseMembersKB, parseMembersTB, Option.bind_none]
        | cons tok rest =>
          cases tok with
          | punct k s =>
              cases k with
              | closeBrace =>
                  simp only [parseMembersKB, parseMembersTB, canonMembers_nil,
                    Option.bind_some, Option.map_some]
              | _ =>
                  simp only [parseMembersKB, parseMembersTB, Option.bind_none]
          | string s => exact members_succ_eq bs f s rest ihV ihM
          | _ =>
              simp only [parseMembersKB, parseMembersTB, Option.bind_none]



/-! The pins: the canonicalising decoder and its correspondence carry only the
standard footprint, so a `noncomputable` edit that widened it would fail this
module's build. -/

/--
info: 'LeanLLVM.Refinement.parseValueK_eq_bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Refinement.parseValueK_eq_bind

/--
info: 'LeanLLVM.Refinement.parseValueKB_map' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Refinement.parseValueKB_map

end LeanLLVM.Refinement
