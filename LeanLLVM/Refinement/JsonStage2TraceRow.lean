/-
The per-record row: the parser's tape against the emitted records.

`JsonStage2TokenCorrespondence` states what a record says about a token
(`TokenRecord`, `tokenRecord_number`, `tokenRecord_string`) and
`JsonStage2WalkAlignment` states the row the walk still owes (`WalkTraceRow`) with
its composition (`emittedStream_of_row`).  What neither had is the parser's side of
that row: the facts a token carries — a literal's span and bytes, a number's
lexeme, a key or string's body — were reachable only through the parser's private
per-branch lemmas.

They are public now.  `LeanLLVM.JSON.TapeCorrect`'s `TokenBytes` states them per
class against the tape, and `tape_tokenBytes` proves them of every token of a tape
the decoder accepts.  This module reads them at the byte list the records are
stated over, hands them to `TokenRecord`'s constructors one class at a time, and
names the payload each record then carries:

* **per class, from the tape** — `tokenRecord_null_of_tape`, `_true_`, `_false_`,
  `tokenRecord_number_of_tape`, `tokenRecord_string_plain_of_tape` and
  `tokenRecord_string_arena_of_tape`: the parser's token facts plus the record's own
  choice of form give the relation's constructor;
* **the payload, named** — `row_number_payload_of_tape` and
  `row_string_payload_of_tape`: `tokenRecord_number` and `tokenRecord_string`
  instantiated at those records, so a walked number's bits are `strtodSpec`'s of the
  span's lexeme and a walked string's body is the span's code points;
* **the row itself** — `walkTraceRow_of_position`: length agreement plus
  `TokenRecord` at every index is `WalkTraceRow`, the hypothesis
  `emittedStream_of_row` consumes.

The plain string form's `escapeCodePoints` slice of the *raw* body is the walk's own
read of a body it chose as unescaped: the parser's fact is `bodyCodePoints`, which
`bodyCodePoints_of_stringAt` supplies from the tape's `StringAt`.  So the plain
form's premise stays the arm's, and both forms' code points are the parser's.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonStage2WalkAlignment
import LeanLLVM.JSON.Correct

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The tape's token facts, at the records' byte list

`TokenRecord` is stated over `List UInt8`; a tape's input is a `Bytes`
(`ByteString.literal bs` at the run's own read).  The transported predicate and the
per-class readings are the two steps a record's constructor takes from the tape. -/

/-- **`TokenBytes` at the record's byte list.**  The tape's input is the record
vocabulary's `ByteString.literal bs`, so a token's facts transport to that list. -/
theorem TokenBytes.of_input {t : Tape} {bs : List UInt8}
    (hin : t.input = ByteString.literal bs) {tok : Token}
    (h : TokenBytes t.input tok) : TokenBytes (ByteString.literal bs) tok := by
  rw [← hin]
  exact h

/-- **A literal token's span and bytes, from the tape.** -/
theorem tape_tokenBytes_null {t : Tape} {v : JSON.Value} {bs : List UInt8}
    (h : decodeTape t = some v) (hin : t.input = ByteString.literal bs)
    {s : Span} (htok : Token.null s ∈ t.tokens) :
    (bs.drop s.start).take 4 = [0x6E, 0x75, 0x6C, 0x6C] ∧ s.stop = s.start + 4 := by
  have hb := TokenBytes.of_input hin (tape_tokenBytes t v h (.null s) htok)
  refine ⟨?_, hb.2⟩
  have h1 := congrArg (fun b : Bytes => b.data.toList) hb.1
  rw [ByteString.data_toList_take, ByteString.data_toList_drop,
    ByteString.data_toList_literal] at h1
  exact h1

/-- **A `true` token's span and bytes, from the tape.** -/
theorem tape_tokenBytes_true {t : Tape} {v : JSON.Value} {bs : List UInt8}
    (h : decodeTape t = some v) (hin : t.input = ByteString.literal bs)
    {s : Span} (htok : Token.bool true s ∈ t.tokens) :
    (bs.drop s.start).take 4 = [0x74, 0x72, 0x75, 0x65] ∧ s.stop = s.start + 4 := by
  have hb := TokenBytes.of_input hin (tape_tokenBytes t v h (.bool true s) htok)
  refine ⟨?_, hb.2⟩
  have h1 := congrArg (fun b : Bytes => b.data.toList) hb.1
  rw [ByteString.data_toList_take, ByteString.data_toList_drop,
    ByteString.data_toList_literal] at h1
  exact h1

/-- **A `false` token's span and bytes, from the tape.** -/
theorem tape_tokenBytes_false {t : Tape} {v : JSON.Value} {bs : List UInt8}
    (h : decodeTape t = some v) (hin : t.input = ByteString.literal bs)
    {s : Span} (htok : Token.bool false s ∈ t.tokens) :
    (bs.drop s.start).take 5 = [0x66, 0x61, 0x6C, 0x73, 0x65] ∧ s.stop = s.start + 5 := by
  have hb := TokenBytes.of_input hin (tape_tokenBytes t v h (.bool false s) htok)
  refine ⟨?_, hb.2⟩
  have h1 := congrArg (fun b : Bytes => b.data.toList) hb.1
  rw [ByteString.data_toList_take, ByteString.data_toList_drop,
    ByteString.data_toList_literal] at h1
  exact h1

/-- **A number token's span and lexeme, from the tape.**  The span holds a maximal
run of number bytes, and that run is an RFC 8259 number. -/
theorem tape_tokenBytes_number {t : Tape} {v : JSON.Value} {bs : List UInt8}
    (h : decodeTape t = some v) (hin : t.input = ByteString.literal bs)
    {s : Span} (htok : Token.number s ∈ t.tokens) :
    ∃ lex : List UInt8, (bs.drop s.start).take (s.stop - s.start) = lex ∧
      lex.length = s.stop - s.start ∧ RfcNumber (ByteString.literal lex) := by
  have hb := TokenBytes.of_input hin (tape_tokenBytes t v h (.number s) htok)
  obtain ⟨lex, htake, hlen, hnum⟩ := hb
  refine ⟨lex.data.toList, ?_, ?_, ?_⟩
  · have h1 := congrArg (fun b : Bytes => b.data.toList) htake
    rw [ByteString.data_toList_take, ByteString.data_toList_drop,
      ByteString.data_toList_literal] at h1
    exact h1
  · rw [← hlen, ByteString.length_eq_size, ByteString.size_eq_data,
      Array.length_toList]
  · rwa [ByteString.literal_data_toList]

/-- **A key or string token's quote and body, from the tape.**  The span opens with
the quotation mark and reads as a JSON string literal. -/
theorem tape_tokenBytes_string {t : Tape} {v : JSON.Value} {bs : List UInt8}
    (h : decodeTape t = some v) (hin : t.input = ByteString.literal bs)
    {s : Span} (htok : Token.string s ∈ t.tokens) :
    bs[s.start]? = some 0x22 ∧
      ∃ cs : List Nat, StringAt .strict (ByteString.literal bs) s.start s.stop cs := by
  have hb := TokenBytes.of_input hin (tape_tokenBytes t v h (.string s) htok)
  refine ⟨?_, hb.2⟩
  have h1 := hb.1
  rwa [ByteString.getElem?_literal] at h1

/-! ### The span's body is the parser's

`bodyCodePoints` is the specification's reading of a token's body; `StringAt` is the
grammar's literal at the same span and the decoder's scan produced it, so the two
are the same code point list.  This is the string payload's parser-side half, and
both record forms consume it. -/

/-- **The span's body code points are the grammar's.** -/
theorem bodyCodePoints_of_stringAt {bs : List UInt8} {i j : Nat} {cs : List Nat}
    (h : StringAt .strict (ByteString.literal bs) i j cs) :
    bodyCodePoints bs ⟨i, j⟩ = some cs := by
  obtain ⟨-, rest, hstr, -⟩ := h
  have hscan : scanChars ((ByteString.literal bs).drop (i + 1)) = .ok (cs, rest) :=
    (scanChars_iff _ cs rest).mpr hstr
  rw [scanChars_eq] at hscan
  obtain ⟨stop, hstop, -⟩ :=
    scanCharsEnd_ok_of_scanCharsFrom (bs := ByteString.literal bs) (i := i + 1)
      (off := 0) hscan
  unfold bodyCodePoints
  rw [hstop]

/-- **A tape's string token has the grammar's body code points.**  The two steps —
the tape's `StringAt` and the scan's agreement — composed for a token of an accepted
tape. -/
theorem tape_bodyCodePoints {t : Tape} {v : JSON.Value} {bs : List UInt8}
    (h : decodeTape t = some v) (hin : t.input = ByteString.literal bs)
    {s : Span} (htok : Token.string s ∈ t.tokens) :
    ∃ cs : List Nat, bodyCodePoints bs s = some cs := by
  obtain ⟨-, cs, hsa⟩ := tape_tokenBytes_string h hin htok
  exact ⟨cs, bodyCodePoints_of_stringAt hsa⟩

/-! ### One record per token, from the tape

The relation's constructors, with their document-side and parser-side hypotheses
discharged from the tape's own token facts.  What stays a hypothesis is the record
the walk emitted: its class and, for a string, its form and slice. -/

/-- **A `null` record at a tape's token.** -/
theorem tokenRecord_null_of_tape {t : Tape} {v : JSON.Value} {bs arena : List UInt8}
    (h : decodeTape t = some v) (hin : t.input = ByteString.literal bs)
    {s : Span} (htok : Token.null s ∈ t.tokens) :
    TokenRecord bs arena (.tag 10) (.null s) := by
  obtain ⟨hbytes, hspan⟩ := tape_tokenBytes_null h hin htok
  exact TokenRecord.nullTag hbytes hspan

/-- **A `true` record at a tape's token.** -/
theorem tokenRecord_true_of_tape {t : Tape} {v : JSON.Value} {bs arena : List UInt8}
    (h : decodeTape t = some v) (hin : t.input = ByteString.literal bs)
    {s : Span} (htok : Token.bool true s ∈ t.tokens) :
    TokenRecord bs arena (.tag 8) (.bool true s) := by
  obtain ⟨hbytes, hspan⟩ := tape_tokenBytes_true h hin htok
  exact TokenRecord.trueTag hbytes hspan

/-- **A `false` record at a tape's token.** -/
theorem tokenRecord_false_of_tape {t : Tape} {v : JSON.Value} {bs arena : List UInt8}
    (h : decodeTape t = some v) (hin : t.input = ByteString.literal bs)
    {s : Span} (htok : Token.bool false s ∈ t.tokens) :
    TokenRecord bs arena (.tag 9) (.bool false s) := by
  obtain ⟨hbytes, hspan⟩ := tape_tokenBytes_false h hin htok
  exact TokenRecord.falseTag hbytes hspan

/-- **A number record at a tape's token.**  The parser supplies the span and the
lexeme; the walk supplies the decomposition — a `Decimal` whose lexeme is the
bytes the span holds — and the record is `strtodSpec`'s bits of it. -/
theorem tokenRecord_number_of_tape {t : Tape} {v : JSON.Value} {bs arena : List UInt8}
    (h : decodeTape t = some v) (hin : t.input = ByteString.literal bs)
    {s : Span} (htok : Token.number s ∈ t.tokens)
    {d : Decimal} (hwf : d.wellFormed)
    (hlex : d.lexeme.data.toList = (bs.drop s.start).take (s.stop - s.start)) :
    TokenRecord bs arena (.number (strtodSpec d).toBits) (.number s) := by
  obtain ⟨lex, htake, hlen, hnum⟩ := tape_tokenBytes_number h hin htok
  have hlexpos : 0 < lex.length := by
    have h1 : 0 < (ByteString.literal lex).length := rfcNumber_nonempty hnum
    simpa using h1
  have hle : s.start ≤ s.stop := by omega
  have hlen' : d.lexeme.length = s.stop - s.start := by
    have hl : d.lexeme.data.toList.length = lex.length := by rw [hlex, htake]
    have hsize : d.lexeme.length = d.lexeme.data.toList.length := by
      rw [ByteString.length_eq_size, ByteString.size_eq_data, ← Array.length_toList]
    omega
  refine TokenRecord.number hwf ?_ ?_
  · omega
  · rw [hlex]

/-- **A plain string record at a tape's token.**  The span opens with the quote and
its body's code points are the grammar's (`bodyCodePoints`); the record's field
addresses the document's body and its length is the body's, and the raw slice's
code points — the walk's reading of a body it emitted unescaped — are the same. -/
theorem tokenRecord_string_plain_of_tape {t : Tape} {v : JSON.Value} {bs arena : List UInt8}
    (h : decodeTape t = some v) (hin : t.input = ByteString.literal bs)
    {s : Span} (htok : Token.string s ∈ t.tokens) {key : Bool} {len : Nat} {cs : List Nat}
    (hspan : s.stop = s.start + 2 + len)
    (hcode : bodyCodePoints bs s = some cs)
    (hbody : escapeCodePoints ((bs.drop (s.start + 1)).take len) = some cs) :
    TokenRecord bs arena (.str key len (plainSpan (s.start + 1))) (.string s) := by
  obtain ⟨hq, -⟩ := tape_tokenBytes_string h hin htok
  exact TokenRecord.strPlain hq hspan hbody hcode

/-- **An arena string record at a tape's token.**  The span opens with the quote; the
record's field is an arena offset below `2 ^ 63` whose slice reads the span's code
points; and the span holds at least its two quotes. -/
theorem tokenRecord_string_arena_of_tape {t : Tape} {v : JSON.Value} {bs arena : List UInt8}
    (h : decodeTape t = some v) (hin : t.input = ByteString.literal bs)
    {s : Span} (htok : Token.string s ∈ t.tokens) {key : Bool} {len off : Nat}
    {cs : List Nat}
    (hlen : s.start + 2 ≤ s.stop) (hoff : off < 2 ^ 63)
    (hcode : bodyCodePoints bs s = some cs)
    (harena : escapeCodePoints ((arena.drop off).take len) = some cs) :
    TokenRecord bs arena (.str key len off) (.string s) := by
  obtain ⟨hq, -⟩ := tape_tokenBytes_string h hin htok
  exact TokenRecord.strArena hq hlen hcode hoff harena

/-! ### The payload each record carries

The construction above produces the record; the correspondence's own theorems name
its payload.  These are those two instantiations at the tape's record, stated so a
consumer reads the payload relation rather than re-deriving it. -/

/-- **A walked number's payload is the span's lexeme under `strtodSpec`.**  The
record built at a number token carries, by `tokenRecord_number`, bits that are
`strtodSpec`'s of a well-formed decomposition of exactly the bytes the token's span
holds. -/
theorem row_number_payload_of_tape {t : Tape} {v : JSON.Value} {bs arena : List UInt8}
    (h : decodeTape t = some v) (hin : t.input = ByteString.literal bs)
    {s : Span} (htok : Token.number s ∈ t.tokens)
    {d : Decimal} (hwf : d.wellFormed)
    (hlex : d.lexeme.data.toList = (bs.drop s.start).take (s.stop - s.start)) :
    ∃ d' : Decimal, d'.wellFormed ∧
      (bs.drop s.start).take (s.stop - s.start) = d'.lexeme.data.toList ∧
      (strtodSpec d).toBits = (strtodSpec d').toBits := by
  have hrec : TokenRecord bs arena (.number (strtodSpec d).toBits) (.number s) :=
    tokenRecord_number_of_tape h hin htok hwf hlex
  obtain ⟨bits, d', hbits, hwf', -, hlex', hbits'⟩ := tokenRecord_number hrec
  refine ⟨d', hwf', hlex', ?_⟩
  have hb : (strtodSpec d).toBits = bits := (EventRecord.number.injEq _ _).mp hbits
  rw [hb]
  exact hbits'

/-- **A walked string's payload is the parser's body.**  Either form names its body
by a length and a field, and the code points the record's slice decodes to are the
token's own — `bodyCodePoints`, which the tape's `StringAt` supplies. -/
theorem row_string_payload_of_tape {t : Tape} {v : JSON.Value} {bs arena : List UInt8}
    (h : decodeTape t = some v) (hin : t.input = ByteString.literal bs)
    {s : Span} (htok : Token.string s ∈ t.tokens) {key : Bool} {len field : Nat}
    (hrec : TokenRecord bs arena (.str key len field) (.string s)) :
    ∃ cs : List Nat, bodyCodePoints bs s = some cs ∧
      ((field = plainSpan (s.start + 1) ∧ s.stop = s.start + 2 + len ∧
          escapeCodePoints ((bs.drop (s.start + 1)).take len) = some cs) ∨
        (field < 2 ^ 63 ∧ s.start + 2 ≤ s.stop ∧
          escapeCodePoints ((arena.drop field).take len) = some cs)) := by
  obtain ⟨cs, hcode⟩ := tape_bodyCodePoints h hin htok
  obtain ⟨-, key', len', field', cs', hr, hcode', hfield⟩ := tokenRecord_string hrec
  cases hr
  have hcs : cs' = cs := by
    rw [hcode] at hcode'
    exact (Option.some.inj hcode').symm
  refine ⟨cs, hcode, ?_⟩
  rcases hfield with ⟨hfield, hstop, hbody⟩ | ⟨hbelow, hspan, harena⟩
  · exact Or.inl ⟨hfield, hstop, by rw [hcs] at hbody; exact hbody⟩
  · exact Or.inr ⟨hbelow, hspan, by rw [hcs] at harena; exact harena⟩

/-! ### The row

`WalkTraceRow` is `List.Forall₂` of `TokenRecord` over the record trace and the
parser's record-carrying tokens.  A per-arm proof produces one element per step, so
the row's assembly is the index form: length agreement plus the relation at every
index. -/

/-- **The row, from its elements.**  A per-index `TokenRecord` over two lists of the
same length is `List.Forall₂`: the step form a per-arm proof produces, assembled. -/
theorem forall₂_of_position {bs arena : List UInt8} :
    ∀ (n : Nat) {rs : List EventRecord} {toks : List Token},
      rs.length = n → toks.length = n →
      (∀ (k : Nat) (r : EventRecord), rs[k]? = some r →
        ∀ (tok : Token), toks[k]? = some tok → TokenRecord bs arena r tok) →
      List.Forall₂ (TokenRecord bs arena) rs toks
  | 0, rs, toks, hrs, hts, _ => by
      have hrs' : rs = [] := List.eq_nil_of_length_eq_zero hrs
      have hts' : toks = [] := List.eq_nil_of_length_eq_zero hts
      subst hrs'
      subst hts'
      exact List.Forall₂.nil
  | n + 1, rs, toks, hrs, hts, hpos => by
      cases rs with
      | nil => exact absurd hrs (by simp only [List.length_nil]; omega)
      | cons r rs' =>
          cases toks with
          | nil => exact absurd hts (by simp only [List.length_nil]; omega)
          | cons tok toks' =>
              refine List.Forall₂.cons (hpos 0 r ?_ tok ?_) ?_
              · rw [List.getElem?_cons_zero]
              · rw [List.getElem?_cons_zero]
              · refine forall₂_of_position n ?_ ?_ ?_
                · simp only [List.length_cons] at hrs ⊢
                  omega
                · simp only [List.length_cons] at hts ⊢
                  omega
                · intro k r' hr' tok' htok'
                  refine hpos (k + 1) r' ?_ tok' ?_
                  · rw [List.getElem?_cons_succ]
                    exact hr'
                  · rw [List.getElem?_cons_succ]
                    exact htok'

/-- **The trace row at a tape.**  Length agreement with the parser's
record-carrying tokens, and `TokenRecord` at every index — the elements the per-class
theorems above produce — is `WalkTraceRow`, which `emittedStream_of_row` turns into
the encoding, the byte-level relation and the decoded skeleton. -/
theorem walkTraceRow_of_position {bs arena : List UInt8} {t : Tape}
    {rs : List EventRecord}
    (hlen : rs.length = (Token.nonSeparators t.tokens).length)
    (hpos : ∀ (k : Nat) (r : EventRecord), rs[k]? = some r →
      ∀ (tok : Token), (Token.nonSeparators t.tokens)[k]? = some tok →
        TokenRecord bs arena r tok) :
    WalkTraceRow bs arena t rs :=
  forall₂_of_position rs.length rfl hlen.symm hpos

/-! ### A worked row

The `null` document's tape: one token, one record.  The record is built through the
exposed facts (`tokenRecord_null_of_tape`) rather than by a constructor chain, so the
row's assembly is exercised at a real tape. -/

/-- The `null` document's tape, as a tape value. -/
def nullTape : Tape := ⟨ByteString.literal nullDoc, [.null ⟨0, 4⟩]⟩

/-- **The row at the `null` document's tape.**  The tape's acceptance is the one
hypothesis — `decodeTape`'s decision at this document, which the tape's own
construction supplies — and the row's content is the derivation: the record comes
from the exposed token facts (`tokenRecord_null_of_tape`) rather than from a
constructor chain, and the index form assembles it. -/
theorem null_row_of_tape (hdec : decodeTape nullTape = some .null) :
    WalkTraceRow nullDoc [] nullTape ([EventRecord.tag 10] : List EventRecord) := by
  have hsep : Token.nonSeparators nullTape.tokens = [.null ⟨0, 4⟩] := rfl
  refine walkTraceRow_of_position ?_ ?_
  · rw [hsep]
    rfl
  · intro k r hr tok htok
    rw [hsep] at htok
    cases k with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hr htok
        subst hr
        subst htok
        exact tokenRecord_null_of_tape hdec rfl (by
          show Token.null ⟨0, 4⟩ ∈ nullTape.tokens
          rw [nullTape]
          simp)
    | succ j =>
        rw [List.getElem?_cons_succ] at htok
        cases htok

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.TokenBytes.of_input' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TokenBytes.of_input

/-- info: 'LeanLLVM.Refinement.tape_tokenBytes_null' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tape_tokenBytes_null

/-- info: 'LeanLLVM.Refinement.tape_tokenBytes_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tape_tokenBytes_true

/-- info: 'LeanLLVM.Refinement.tape_tokenBytes_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tape_tokenBytes_false

/-- info: 'LeanLLVM.Refinement.tape_tokenBytes_number' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tape_tokenBytes_number

/-- info: 'LeanLLVM.Refinement.tape_tokenBytes_string' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tape_tokenBytes_string

/-- info: 'LeanLLVM.Refinement.bodyCodePoints_of_stringAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bodyCodePoints_of_stringAt

/-- info: 'LeanLLVM.Refinement.tape_bodyCodePoints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tape_bodyCodePoints

/-- info: 'LeanLLVM.Refinement.tokenRecord_null_of_tape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tokenRecord_null_of_tape

/-- info: 'LeanLLVM.Refinement.tokenRecord_true_of_tape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tokenRecord_true_of_tape

/-- info: 'LeanLLVM.Refinement.tokenRecord_false_of_tape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tokenRecord_false_of_tape

/-- info: 'LeanLLVM.Refinement.tokenRecord_number_of_tape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tokenRecord_number_of_tape

/-- info: 'LeanLLVM.Refinement.tokenRecord_string_plain_of_tape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tokenRecord_string_plain_of_tape

/-- info: 'LeanLLVM.Refinement.tokenRecord_string_arena_of_tape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tokenRecord_string_arena_of_tape

/-- info: 'LeanLLVM.Refinement.row_number_payload_of_tape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms row_number_payload_of_tape

/-- info: 'LeanLLVM.Refinement.row_string_payload_of_tape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms row_string_payload_of_tape

/-- info: 'LeanLLVM.Refinement.forall₂_of_position' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms forall₂_of_position

/-- info: 'LeanLLVM.Refinement.walkTraceRow_of_position' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms walkTraceRow_of_position

/-- info: 'LeanLLVM.Refinement.null_row_of_tape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms null_row_of_tape

end LeanLLVM.Refinement
