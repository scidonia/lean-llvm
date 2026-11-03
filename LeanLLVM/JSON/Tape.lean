/-
The tape: tokens with source spans, and a decoder that reads the meaning back
out of the input through those spans.

A tape is source-backed — the input is part of the value — so a token that names
a span has no meaning beside the bytes it indexes, and the decoder can refuse a
tape whose spans do not point at the bytes its token kinds denote.

The tape is the index-based artefact over the caller's bytes: every token's
meaning is read out of `Tape.input` through its `Span`, never out of a payload
carried beside it.  `Value` and `decodeTape` are the specification-side decoding,
so materialising a number's lexeme or a string's code points is the reference
layer's cost, not the shipped path's; a consumer that wants the bytes takes the
span instead.  `decoded_number_is_span_bytes` and
`decoded_string_is_span_literal` are the theorems that make that substitution
safe.
-/
import LeanLLVM.JSON.Spec
import LeanLLVM.JSON.Scan

namespace LeanLLVM.JSON

open ByteString

/-- A half-open byte range into the tape's input. -/
structure Span where
  start : Nat
  stop : Nat
deriving DecidableEq, Repr

inductive Punct where
  | openBracket | closeBracket | openBrace | closeBrace | comma | colon
deriving DecidableEq, Repr

/-- A tape token: its kind and its span, with no decoded payload.  A string token
is a pair of indexes, so a consumer that wants the text must read the input
through the span, and `decodeTape` cannot be fooled by a payload the input does
not support. -/
inductive Token where
  | punct (k : Punct) (s : Span)
  | null (s : Span)
  | bool (b : Bool) (s : Span)
  | number (s : Span)
  | string (s : Span)
deriving DecidableEq, Repr

/-- A tape is its input and the tokens read from it.  The input is part of the
value: a tape is source-backed, and a span is meaningful only against the bytes
it indexes. -/
structure Tape where
  input : Bytes
  tokens : List Token
deriving DecidableEq, Repr

def Token.span : Token → Span
  | .punct _ s => s
  | .null s => s
  | .bool _ s => s
  | .number s => s
  | .string s => s

/-- Span discipline, decided: every span lies inside the input, is non-empty,
spans are in order without overlap, and a punctuation span is one byte.  Nesting
containment is not checked here — the tape carries no depth field — and is a
consequence of `tape_valid` instead. -/
def checkSpans (bs : Bytes) : List Token → Nat → Bool
  | [], _ => true
  | tok :: rest, prev =>
      let s := tok.span
      decide (prev ≤ s.start) && decide (s.start < s.stop) &&
        decide (s.stop ≤ bs.length) &&
        (match tok with | .punct _ _ => decide (s.stop = s.start + 1) | _ => true) &&
        checkSpans bs rest s.stop

def spansWellFormed (t : Tape) : Bool := checkSpans t.input t.tokens 0

/-! ### The decoder

A second implementation, over tokens *and* bytes.  It reads the bytes through the
spans, so a span that does not point at the bytes its kind denotes makes the tape
undecodable.  Containers are decoded inside `decodeValue`, so a first element or
key is decoded at `rest` — a strict subterm of the token list — and the tails
continue at the remainder a `Decoded`/`ElemsTail`/`MembersTail` carries.  The
progress fields are the decrease the tail's continuation cannot see through
`decodeValue`'s result. -/

/-- A decoded value: the value, the tokens that follow it, the byte cursor, and the
proof that at least one token was consumed. -/
structure Decoded (src : List Token) where
  value : Value
  rest : List Token
  cursor : Nat
  shrunk : rest.length < src.length

/-- A decoded element tail, which may consume no token at all. -/
structure ElemsTail (src : List Token) where
  values : List Value
  rest : List Token
  cursor : Nat
  moved : rest.length ≤ src.length

/-- A decoded member tail. -/
structure MembersTail (src : List Token) where
  members : List (List Nat × Value)
  rest : List Token
  cursor : Nat
  moved : rest.length ≤ src.length

mutual

/-- Decode one value at byte cursor `i`.  Containers are handled here rather than
in a body function, so every recursive call is on a strict subterm of the token
list: the first element or key is decoded at `rest`, and a tail continues at the
`shrunk` remainder.  The colon and comma tokens are matched where the grammar puts
them and their spans are checked, so `{"a" : 1}` and `{"a" :1}` are different
claims and neither is a tape over `{"a"1}`. -/
def decodeValue (bs : Bytes) (i : Nat) : (toks : List Token) → Option (Decoded toks)
  | [] => none
  | .null s :: rest =>
      if s == ⟨i, i + 4⟩ && HasPrefixB bs i (literal [0x6E, 0x75, 0x6C, 0x6C]) then
        some { value := .null, rest := rest, cursor := i + 4, shrunk := by simp }
      else none
  | .bool b s :: rest =>
      let lit := if b then literal [0x74, 0x72, 0x75, 0x65]
        else literal [0x66, 0x61, 0x6C, 0x73, 0x65]
      if s == ⟨i, i + lit.length⟩ && HasPrefixB bs i lit then
        some { value := .bool b, rest := rest, cursor := i + lit.length,
               shrunk := by simp }
      else none
  | .number s :: rest =>
      let lex := numRun (bs.drop i)
      if s == ⟨i, i + lex.length⟩ && numLexB lex then
        some { value := .number lex, rest := rest, cursor := i + lex.length,
               shrunk := by simp }
      else none
  | .string s :: rest =>
      match scanChars (bs.drop (i + 1)) with
      | .error _ => none
      | .ok (cs, after) =>
          -- `after` begins past the closing quote, so `stop` is one past it and
          -- the span covers both quotes; a span ending at the quote is short.
          -- The opening quote at `i` is checked too: the span claims to cover a
          -- string literal, and a span that starts anywhere else does not.
          let stop := bs.length - after.length
          if decide (bs[i]? = some 0x22) && decide (s = ⟨i, stop⟩) then
            some { value := .string cs, rest := rest, cursor := stop,
                   shrunk := by simp }
          else none
  | .punct .openBracket s :: .punct .closeBracket c :: rest' =>
      let body := skipFrom bs (i + 1)
      if s == ⟨i, i + 1⟩ && decide (bs[i]? = some 0x5B) &&
          c == ⟨body, body + 1⟩ && decide (bs[body]? = some 0x5D) then
        some { value := .array [], rest := rest', cursor := body + 1,
               shrunk := by simp only [List.length_cons] at ⊢; omega }
      else none
  | .punct .openBracket s :: rest =>
      if s == ⟨i, i + 1⟩ && decide (bs[i]? = some 0x5B) then
        let body := skipFrom bs (i + 1)
        match decodeValue bs body rest with
        | none => none
        | some d =>
          have hd : d.rest.length < rest.length := d.shrunk
          match decodeElemsTail bs d.cursor d.rest with
          | none => none
          | some t =>
            match hC : t.rest with
            | .punct .closeBracket c :: rest' =>
                if c == ⟨t.cursor, t.cursor + 1⟩ && decide (bs[t.cursor]? = some 0x5D) then
                  some { value := .array (d.value :: t.values), rest := rest',
                         cursor := t.cursor + 1,
                         shrunk := (by
                           simp only [List.length_cons] at ⊢
                           have hC' : t.rest.length = rest'.length + 1 := by
                             rw [hC]; simp
                           have h1 := d.shrunk
                           have h2 := t.moved
                           omega) }
                else none
            | _ => none
      else none
  | .punct .openBrace s :: .punct .closeBrace c :: rest' =>
      let body := skipFrom bs (i + 1)
      if s == ⟨i, i + 1⟩ && decide (bs[i]? = some 0x7B) &&
          c == ⟨body, body + 1⟩ && decide (bs[body]? = some 0x7D) then
        some { value := .object [], rest := rest', cursor := body + 1,
               shrunk := by simp only [List.length_cons] at ⊢; omega }
      else none
  | .punct .openBrace s :: rest =>
      if s == ⟨i, i + 1⟩ && decide (bs[i]? = some 0x7B) then
        let body := skipFrom bs (i + 1)
        match decodeValue bs body rest with
        | none => none
        | some k =>
          have hk : k.rest.length < rest.length := k.shrunk
          match k.value with
          | .string cs =>
            let colon := skipFrom bs k.cursor   -- `name-separator = ws %x3A ws`
            match hColon : k.rest with
            | .punct .colon sc :: rest1 =>
                have hColonLen : k.rest.length = rest1.length + 1 := by
                  rw [hColon]; simp
                if sc == ⟨colon, colon + 1⟩ && decide (bs[colon]? = some 0x3A) then
                  match decodeValue bs (skipFrom bs (colon + 1)) rest1 with
                  | none => none
                  | some d =>
                    have hd : d.rest.length < rest1.length := d.shrunk
                    match decodeMembersTail bs d.cursor d.rest with
                    | none => none
                    | some t =>
                      match hC : t.rest with
                      | .punct .closeBrace c :: rest' =>
                          if c == ⟨t.cursor, t.cursor + 1⟩ &&
                             decide (bs[t.cursor]? = some 0x7D) then
                            some { value := .object ((cs, d.value) :: t.members),
                                   rest := rest', cursor := t.cursor + 1,
                                   shrunk := (by
                                     simp only [List.length_cons] at ⊢
                                     have hC' : t.rest.length = rest'.length + 1 := by
                                       rw [hC]; simp
                                     have hColon' : k.rest.length = rest1.length + 1 := by
                                       rw [hColon]; simp
                                     have h1 := k.shrunk
                                     have h2 := d.shrunk
                                     have h3 := t.moved
                                     omega) }
                          else none
                      | _ => none
                else none
            | _ => none
          | _ => none
      else none
  | _ :: _ => none
termination_by toks => toks.length
decreasing_by
  all_goals (simp only [List.length_cons]; omega)

/-- The element tail, entered at the raw cursor after a value.  It skips whitespace
before deciding: RFC 8259 §2 allows it on both sides of every structural
character, so the comma token is checked at `skipFrom bs j` and the cursor it
returns is the skipped one.  A comma token is matched, not a byte: the tape is a
token list, and matching only the byte would let a tape with no comma token decode
an array it does not describe. -/
def decodeElemsTail (bs : Bytes) (j : Nat) : (toks : List Token) →
    Option (ElemsTail toks)
  | .punct .comma s :: rest =>
      let c := skipFrom bs j
      if s == ⟨c, c + 1⟩ && decide (bs[c]? = some 0x2C) then
        match decodeValue bs (skipFrom bs (c + 1)) rest with
        | none => none
        | some d =>
          have hd : d.rest.length < rest.length := d.shrunk
          match decodeElemsTail bs d.cursor d.rest with
          | none => none
          | some t => some { values := d.value :: t.values, rest := t.rest,
                             cursor := t.cursor,
                             moved := (by
                               simp only [List.length_cons]
                               have h1 := d.shrunk
                               have h2 := t.moved
                               omega) }
      else none
  | rest => some { values := [], rest := rest, cursor := skipFrom bs j,
                   moved := Nat.le_refl _ }
termination_by toks => toks.length
decreasing_by
  all_goals (simp only [List.length_cons]; omega)

/-- The member tail. -/
def decodeMembersTail (bs : Bytes) (j : Nat) : (toks : List Token) →
    Option (MembersTail toks)
  | .punct .comma s :: rest =>
      let c := skipFrom bs j          -- `value-separator = ws %x2C ws`
      if s == ⟨c, c + 1⟩ && decide (bs[c]? = some 0x2C) then
        match decodeValue bs (skipFrom bs (c + 1)) rest with
        | none => none
        | some k =>
          have hk : k.rest.length < rest.length := k.shrunk
          match k.value with
          | .string cs =>
            let colon := skipFrom bs k.cursor
            match hColon : k.rest with
            | .punct .colon sc :: rest1 =>
                have hColonLen : k.rest.length = rest1.length + 1 := by
                  rw [hColon]; simp
                if sc == ⟨colon, colon + 1⟩ && decide (bs[colon]? = some 0x3A) then
                  match decodeValue bs (skipFrom bs (colon + 1)) rest1 with
                  | none => none
                  | some d =>
                    have hd : d.rest.length < rest1.length := d.shrunk
                    match decodeMembersTail bs d.cursor d.rest with
                    | none => none
                    | some t =>
                      some { members := (cs, d.value) :: t.members, rest := t.rest,
                             cursor := t.cursor,
                             moved := (by
                               simp only [List.length_cons]
                               have hColon' : k.rest.length = rest1.length + 1 := by
                                 rw [hColon]; simp
                               have h1 := d.shrunk
                               have h2 := t.moved
                               omega) }
                else none
            | _ => none
          | _ => none
      else none
  | rest => some { members := [], rest := rest, cursor := skipFrom bs j,
                   moved := Nat.le_refl _ }
termination_by toks => toks.length
decreasing_by
  all_goals (simp only [List.length_cons]; omega)

end

/-- Read the tape against its input: `some v` only when every token's span points
at the bytes its kind denotes, the token list is consumed exactly, and the input
is consumed exactly apart from whitespace at both ends. -/
def decodeTape (t : Tape) : Option Value :=
  match decodeValue t.input (skipFrom t.input 0) t.tokens with
  | some d =>
      if d.rest = [] && skipFrom t.input d.cursor = t.input.length then some d.value
      else none
  | none => none

end LeanLLVM.JSON
