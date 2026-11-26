/-
The record trace at the reference parser's tokens, record for record.

`JsonStage2Hsem` states the event stream's relation `Stage2Records` and uses it
as the accept clause's evidence: the walk's trace `rs` relates to the tape's
`tokens`.  What that module does not have is the relation's *content*: a
consumer reading `Stage2Records bs arena rs toks` has to `cases` on its
thirteen constructors to learn what one record says about one token, and
the tree's two instantiations (`null_records`, `pair_records`) exhibit the
relation at two documents rather than stating what it says in general.

This module supplies that content, in the three forms a consumer needs:

* **the relation is one record per record-carrying token, in order**
  (`stage2Records_iff_forall₂`).  The pointwise relation `TokenRecord` holds
  between a record and a token exactly when the record is that token's, and
  `Stage2Records` is `List.Forall₂` of it over the token list with the two
  separators removed.  `Token.nonSeparators` is the removal, and it is a
  function, so "commas and colons are consumed by their own constructors" is the
  statement that they do not appear in the right-hand list at all rather than a
  side condition on each constructor;
* **what one record says about its token** (`tokenRecord_tag`,
  `tokenRecord_number`, `tokenRecord_string`): the record's tag byte names the
  token's kind, the token's span is the one the record's class admits (its
  one-byte or literal length, its lexeme, or its span field), and the payload is
  the class's — the document's bytes at the span for the containers and
  literals, the span's lexeme and `strtodSpec`'s bits for a number, the body's
  code points through `escapeCodePoints` for a string in either of its two
  forms.  Each is universal in the token and the span: an elimination, not a case
  in a list;
* **the emitted stream's record skeleton is decodable** (`parseSkeleton_trace`):
  the encoding's first byte announces each record's width, so the tag sequence
  of a trace's bytes is a total function of those bytes.  A trace of related
  records therefore decodes: the stream is not only related to the tokens but is
  a sequence of records the reader recovers, with each record's payload read out
  of the document, the arena or `strtodSpec`.

The correspondence is stated at the run's own reads in
`stage2Records_at_accept`: the same bytes for the parser and the walk
(`t.input = ByteString.literal bs`), the arena at the **used** prefix
(`readBytes m dst ndstU = some (arena.take ndstU)`, derived from the reported
extent rather than assumed at it), the event stream at the reported cursor, the
record-for-record agreement and the decoded skeleton.  Its hypotheses are the
accept path's own, which is the shape `parserHalf_accept` consumes from
`Stage2OutcomeEvidence`'s accept branch.

# What this does not prove, and why it is named here

The relation is *between* the walk's trace and the parser's tokens; it does not
say the walk emitted this trace.  That row — the walk's `C.events` equal to the
tokens' encoding — is not a consequence of the boundary post (`stage2Post`'s
verdict is two-valued and says nothing about the stream's meaning) and needs an
alignment this tree does not state: the entry stream's positions
(`WalkGeom.ent`, ordered and inside the document, with nothing tying them to the
parser's token starts) against `parseValue`'s cursors.  Every per-arm fact the
walk proof carries is about *its own* positions (`entryPos G C.k`, the scan's
extents), so a per-arm record can be related to *a* token at its span but not to
*the parser's token at that position*.  `stage2Records_at_accept` is therefore
stated at the trace the run's own read names; closing the row needs the
entry-stream/token-start alignment as a walk invariant, which is where a
per-arm proof would start.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonStage2Hsem

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonUtf8IR

/-! ### The separators, removed

`Stage2Records`'s two separator constructors consume no record, so the relation
is a correspondence between the records and the *other* tokens.  The removal is
a function of the token list, written by construction rather than through
`List.filter`, so each equation is the constructor's. -/

/-- The tokens that carry a record, in order: comma and colon removed.  A
separator's own span is not re-checked by the relation — it is removed here — so
the correspondence constrains the record-carrying tokens' kinds, spans and
payloads and leaves a comma's or colon's position to the tape. -/
def Token.nonSeparators : List Token → List Token
  | [] => []
  | .punct .comma _ :: rest => Token.nonSeparators rest
  | .punct .colon _ :: rest => Token.nonSeparators rest
  | tok :: rest => tok :: Token.nonSeparators rest

/-! ### One record, one token

The whole-trace relation's record-carrying constructors, at one record and one
token.  Each fixes the record's shape and payload and binds the token's span, so
an elimination gives the class's agreement rather than the trace's. -/

/-- **One record agrees with one token.**  The record's shape is the token's
class: a container's or literal's tag byte at its one-byte or literal span, a
number's `strtodSpec` payload at the span's lexeme, or a key/string record in
either of its two forms — `plainSpan` addressing the document's body, or an
arena offset addressing the decoded code points. -/
inductive TokenRecord (bs arena : List UInt8) : EventRecord → Token → Prop where
  /-- `{` (`T_OBJ = 1`). -/
  | openBrace {s : Span} (hbyte : bs[s.start]? = some 0x7B) (hspan : s.stop = s.start + 1) :
      TokenRecord bs arena (EventRecord.tag 1) (.punct .openBrace s)
  /-- `}` (`T_OBJ_END = 2`). -/
  | closeBrace {s : Span} (hbyte : bs[s.start]? = some 0x7D) (hspan : s.stop = s.start + 1) :
      TokenRecord bs arena (EventRecord.tag 2) (.punct .closeBrace s)
  /-- `[` (`T_ARR = 3`). -/
  | openBracket {s : Span} (hbyte : bs[s.start]? = some 0x5B) (hspan : s.stop = s.start + 1) :
      TokenRecord bs arena (EventRecord.tag 3) (.punct .openBracket s)
  /-- `]` (`T_ARR_END = 4`). -/
  | closeBracket {s : Span} (hbyte : bs[s.start]? = some 0x5D) (hspan : s.stop = s.start + 1) :
      TokenRecord bs arena (EventRecord.tag 4) (.punct .closeBracket s)
  /-- `true` (`T_TRUE = 8`) at the four-byte literal. -/
  | trueTag {s : Span}
      (hbytes : (bs.drop s.start).take 4 = [0x74, 0x72, 0x75, 0x65])
      (hspan : s.stop = s.start + 4) :
      TokenRecord bs arena (EventRecord.tag 8) (.bool true s)
  /-- `false` (`T_FALSE = 9`) at the five-byte literal. -/
  | falseTag {s : Span}
      (hbytes : (bs.drop s.start).take 5 = [0x66, 0x61, 0x6C, 0x73, 0x65])
      (hspan : s.stop = s.start + 5) :
      TokenRecord bs arena (EventRecord.tag 9) (.bool false s)
  /-- `null` (`T_NULL = 10`) at the four-byte literal. -/
  | nullTag {s : Span}
      (hbytes : (bs.drop s.start).take 4 = [0x6E, 0x75, 0x6C, 0x6C])
      (hspan : s.stop = s.start + 4) :
      TokenRecord bs arena (EventRecord.tag 10) (.null s)
  /-- A number (`T_NUM = 7`): `strtodSpec`'s bits of the reader's normalised
  decimal of the span's own bytes. -/
  | number {s : Span} {d : Decimal} {lex : Bytes}
      (hread : StrtodReader.reader lex = some d)
      (hspan : s.stop = s.start + lex.length)
      (hlexeme : (bs.drop s.start).take (s.stop - s.start) = lex.data.toList) :
      TokenRecord bs arena (EventRecord.number (strtodSpec d).toBits) (.number s)
  /-- A key or string whose body the document holds, at the token's own
  escape-aware scan. -/
  | strPlain {key : Bool} {s : Span} {len : Nat} {cs : List Nat}
      (hquote : bs[s.start]? = some 0x22)
      (hspan : s.stop = s.start + 2 + len)
      (hcode : bodyCodePoints bs s = some cs) :
      TokenRecord bs arena (EventRecord.str key len (plainSpan (s.start + 1))) (.string s)
  /-- A key or string whose body the arena holds. -/
  | strArena {key : Bool} {s : Span} {len off : Nat} {cs : List Nat}
      (hquote : bs[s.start]? = some 0x22)
      (hspan : s.start + 2 ≤ s.stop)
      (hcode : bodyCodePoints bs s = some cs)
      (hbelow : off < 2 ^ 63)
      (harena : escapeCodePoints ((arena.drop off).take len) = some cs) :
      TokenRecord bs arena (EventRecord.str key len off) (.string s)

/-! ### The trace is the pointwise relation

`Stage2Records` peels one record per constructor, and the separators ride along
between them, so induction on it gives the pointwise relation over the token list
with the separators removed; the converse builds the separators back, one
constructor each. -/

namespace Stage2Records

/-- **Record for record.**  A related trace is the pointwise relation over the
tokens that carry records, with the separators removed. -/
theorem forall₂ {bs arena : List UInt8} {rs : List EventRecord} {toks : List Token}
    (h : Stage2Records bs arena rs toks) :
    List.Forall₂ (TokenRecord bs arena) rs (Token.nonSeparators toks) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | comma _ ih => exact ih
  | colon _ ih => exact ih
  | openBrace hb hs _ ih => exact List.Forall₂.cons (.openBrace hb hs) ih
  | closeBrace hb hs _ ih => exact List.Forall₂.cons (.closeBrace hb hs) ih
  | openBracket hb hs _ ih => exact List.Forall₂.cons (.openBracket hb hs) ih
  | closeBracket hb hs _ ih => exact List.Forall₂.cons (.closeBracket hb hs) ih
  | trueTag hb hs _ ih => exact List.Forall₂.cons (.trueTag hb hs) ih
  | falseTag hb hs _ ih => exact List.Forall₂.cons (.falseTag hb hs) ih
  | nullTag hb hs _ ih => exact List.Forall₂.cons (.nullTag hb hs) ih
  | number hr hs hlex _ ih => exact List.Forall₂.cons (.number hr hs hlex) ih
  | strPlain hq hs hcode _ ih =>
      exact List.Forall₂.cons (.strPlain hq hs hcode) ih
  | strArena hq hs hcode hbelow harena _ ih =>
      exact List.Forall₂.cons (.strArena hq hs hcode hbelow harena) ih

/-- **The converse**: the pointwise relation over the token list, separators
removed, is the trace's relation.  A separator contributes its own constructor
and no record. -/
theorem of_forall₂ {bs arena : List UInt8} :
    ∀ {rs : List EventRecord} {toks : List Token},
      List.Forall₂ (TokenRecord bs arena) rs (Token.nonSeparators toks) →
      Stage2Records bs arena rs toks
  | rs, [], h => by
      change List.Forall₂ (TokenRecord bs arena) rs ([] : List Token) at h
      cases h with
      | nil => exact Stage2Records.nil
  | rs, .punct .comma s :: rest, h =>
      Stage2Records.comma (of_forall₂ h)
  | rs, .punct .colon s :: rest, h =>
      Stage2Records.colon (of_forall₂ h)
  | rs, .punct .openBracket s :: rest, h => by
      change List.Forall₂ (TokenRecord bs arena) rs
        (.punct .openBracket s :: Token.nonSeparators rest) at h
      cases h with
      | cons hrec htail =>
          cases hrec with
          | openBracket hb hs =>
              exact Stage2Records.openBracket hb hs (of_forall₂ htail)
  | rs, .punct .closeBracket s :: rest, h => by
      change List.Forall₂ (TokenRecord bs arena) rs
        (.punct .closeBracket s :: Token.nonSeparators rest) at h
      cases h with
      | cons hrec htail =>
          cases hrec with
          | closeBracket hb hs =>
              exact Stage2Records.closeBracket hb hs (of_forall₂ htail)
  | rs, .punct .openBrace s :: rest, h => by
      change List.Forall₂ (TokenRecord bs arena) rs
        (.punct .openBrace s :: Token.nonSeparators rest) at h
      cases h with
      | cons hrec htail =>
          cases hrec with
          | openBrace hb hs =>
              exact Stage2Records.openBrace hb hs (of_forall₂ htail)
  | rs, .punct .closeBrace s :: rest, h => by
      change List.Forall₂ (TokenRecord bs arena) rs
        (.punct .closeBrace s :: Token.nonSeparators rest) at h
      cases h with
      | cons hrec htail =>
          cases hrec with
          | closeBrace hb hs =>
              exact Stage2Records.closeBrace hb hs (of_forall₂ htail)
  | rs, .null s :: rest, h => by
      change List.Forall₂ (TokenRecord bs arena) rs
        (.null s :: Token.nonSeparators rest) at h
      cases h with
      | cons hrec htail =>
          cases hrec with
          | nullTag hb hs =>
              exact Stage2Records.nullTag hb hs (of_forall₂ htail)
  | rs, .bool true s :: rest, h => by
      change List.Forall₂ (TokenRecord bs arena) rs
        (.bool true s :: Token.nonSeparators rest) at h
      cases h with
      | cons hrec htail =>
          cases hrec with
          | trueTag hb hs =>
              exact Stage2Records.trueTag hb hs (of_forall₂ htail)
  | rs, .bool false s :: rest, h => by
      change List.Forall₂ (TokenRecord bs arena) rs
        (.bool false s :: Token.nonSeparators rest) at h
      cases h with
      | cons hrec htail =>
          cases hrec with
          | falseTag hb hs =>
              exact Stage2Records.falseTag hb hs (of_forall₂ htail)
  | rs, .number s :: rest, h => by
      change List.Forall₂ (TokenRecord bs arena) rs
        (.number s :: Token.nonSeparators rest) at h
      cases h with
      | cons hrec htail =>
          cases hrec with
          | number hr hs hlex =>
              exact Stage2Records.number hr hs hlex (of_forall₂ htail)
  | rs, .string s :: rest, h => by
      change List.Forall₂ (TokenRecord bs arena) rs
        (.string s :: Token.nonSeparators rest) at h
      cases h with
      | cons hrec htail =>
          cases hrec with
          | strPlain hq hs hcode =>
              exact Stage2Records.strPlain hq hs hcode (of_forall₂ htail)
          | strArena hq hs hcode hbelow harena =>
              exact Stage2Records.strArena hq hs hcode hbelow harena (of_forall₂ htail)

end Stage2Records

/-- **The correspondence, record for record.**  The whole-trace relation holds
exactly when the trace is the pointwise relation over the token list with its two
separators removed: one record per record-carrying token, in order, and the
separators consumed by their own constructors. -/
theorem stage2Records_iff_forall₂ {bs arena : List UInt8} {rs : List EventRecord}
    {toks : List Token} :
    Stage2Records bs arena rs toks ↔
      List.Forall₂ (TokenRecord bs arena) rs (Token.nonSeparators toks) :=
  ⟨Stage2Records.forall₂, Stage2Records.of_forall₂⟩

/-! ### What one record says about its token

The two directions a consumer needs, per class: the record's first byte is the
token's class tag, the token's span is the record's span discipline, and the
payload is the class's — the document's bytes at the span for a container or a
literal, the span's lexeme and `strtodSpec`'s bits for a number, and the body's
code points through `escapeCodePoints` for a key or string in either form. -/

/-- The tag byte a record's emitter writes first. -/
def EventRecord.tagVal : EventRecord → Nat
  | .tag t => t
  | .number _ => stage2TagNum
  | .str key _ _ => if key then EventRecord.tagKey else EventRecord.tagStr

/-- The tag byte a token's class writes: `none` for the two separators, which
write no record, and for a key or string, whose 5/6 tag is the grammar position's
choice rather than the token's. -/
def tokenClassTag? : Token → Option Nat
  | .punct .openBrace _ => some 1
  | .punct .closeBrace _ => some 2
  | .punct .openBracket _ => some 3
  | .punct .closeBracket _ => some 4
  | .punct .comma _ => none
  | .punct .colon _ => none
  | .null _ => some 10
  | .bool true _ => some 8
  | .bool false _ => some 9
  | .number _ => some stage2TagNum
  | .string _ => none

/-- **The record's first byte is the token's class tag.**  On a related pair the
tag byte names the token's class — the four containers, the three literals, or
the number — and a key/string record's tag is `T_KEY`/`T_STR`, which is the
grammar position's choice rather than the token's, so no class tag is claimed for
it. -/
theorem tokenRecord_tagVal {bs arena : List UInt8} {r : EventRecord} {tok : Token}
    (h : TokenRecord bs arena r tok) :
    (∃ n : Nat, tokenClassTag? tok = some n ∧ r.tagVal = n) ∨
      (∃ (key : Bool) (len field : Nat), r = .str key len field) := by
  cases h with
  | openBrace _ _ => exact Or.inl ⟨1, rfl, rfl⟩
  | closeBrace _ _ => exact Or.inl ⟨2, rfl, rfl⟩
  | openBracket _ _ => exact Or.inl ⟨3, rfl, rfl⟩
  | closeBracket _ _ => exact Or.inl ⟨4, rfl, rfl⟩
  | trueTag _ _ => exact Or.inl ⟨8, rfl, rfl⟩
  | falseTag _ _ => exact Or.inl ⟨9, rfl, rfl⟩
  | nullTag _ _ => exact Or.inl ⟨10, rfl, rfl⟩
  | number _ _ _ => exact Or.inl ⟨stage2TagNum, rfl, rfl⟩
  | strPlain hq hs hcode =>
      exact Or.inr ⟨_, _, _,
        rfl⟩
  | strArena hq hs hcode hbelow harena =>
      exact Or.inr ⟨_, _, _, rfl⟩

/-- **Scalars and containers**: a tag record's token is the class's, at the class's
span, and the document holds the class's bytes there.  This is the seven-class
elimination — one disjunct per tag the encoding writes. -/
theorem tokenRecord_tag {bs arena : List UInt8} {n : Nat} {tok : Token}
    (h : TokenRecord bs arena (.tag n) tok) :
    (n = 1 ∧ ∃ s : Span, tok = .punct .openBrace s ∧
        bs[s.start]? = some 0x7B ∧ s.stop = s.start + 1) ∨
    (n = 2 ∧ ∃ s : Span, tok = .punct .closeBrace s ∧
        bs[s.start]? = some 0x7D ∧ s.stop = s.start + 1) ∨
    (n = 3 ∧ ∃ s : Span, tok = .punct .openBracket s ∧
        bs[s.start]? = some 0x5B ∧ s.stop = s.start + 1) ∨
    (n = 4 ∧ ∃ s : Span, tok = .punct .closeBracket s ∧
        bs[s.start]? = some 0x5D ∧ s.stop = s.start + 1) ∨
    (n = 8 ∧ ∃ s : Span, tok = .bool true s ∧
        (bs.drop s.start).take 4 = [0x74, 0x72, 0x75, 0x65] ∧ s.stop = s.start + 4) ∨
    (n = 9 ∧ ∃ s : Span, tok = .bool false s ∧
        (bs.drop s.start).take 5 = [0x66, 0x61, 0x6C, 0x73, 0x65] ∧
        s.stop = s.start + 5) ∨
    (n = 10 ∧ ∃ s : Span, tok = .null s ∧
        (bs.drop s.start).take 4 = [0x6E, 0x75, 0x6C, 0x6C] ∧ s.stop = s.start + 4) := by
  cases h with
  | openBrace hb hs => exact Or.inl ⟨rfl, _, rfl, hb, hs⟩
  | closeBrace hb hs => exact Or.inr (Or.inl ⟨rfl, _, rfl, hb, hs⟩)
  | openBracket hb hs => exact Or.inr (Or.inr (Or.inl ⟨rfl, _, rfl, hb, hs⟩))
  | closeBracket hb hs =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, _, rfl, hb, hs⟩)))
  | trueTag hb hs =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, _, rfl, hb, hs⟩))))
  | falseTag hb hs =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, _, rfl, hb, hs⟩)))))
  | nullTag hb hs =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, _, rfl, hb, hs⟩)))))

/-- **A number record's payload is `strtodSpec`'s bits of the reader's decimal.**
The token's span is the lexeme's — `s.stop = s.start + lex.length` with the
document holding exactly `lex` — the reader reads `lex` as `d`, and the record's
eight payload bytes are the bits of `strtodSpec d`.  The conversion's own
arithmetic is the model's (`stage2NumFast_writes_strtodSpec`); the *body's*
conversion is `ub` at the walk's call selection
(`stage2Calls_noCalls_numFast`), which is the number class's boundary and not this
relation's. -/
theorem tokenRecord_number {bs arena : List UInt8} {r : EventRecord} {s : Span}
    (h : TokenRecord bs arena r (.number s)) :
    ∃ (bits : Nat) (d : Decimal) (lex : Bytes), r = .number bits ∧
      StrtodReader.reader lex = some d ∧
      s.stop = s.start + lex.length ∧
      (bs.drop s.start).take (s.stop - s.start) = lex.data.toList ∧
      bits = (strtodSpec d).toBits := by
  cases h with
  | number hread hspan hlex => exact ⟨_, _, _, rfl, hread, hspan, hlex, rfl⟩

/-- **A key or string record's fields are the span's body.**  The token's span
opens with a quote, its body's code points are `bodyCodePoints`'s, and the record
is one of the two forms: `plainSpan` over the document's body at the token's own
escape-aware reading, or an arena offset below `2 ^ 63` whose slice reads back as
those code points. -/
theorem tokenRecord_string {bs arena : List UInt8} {r : EventRecord} {s : Span}
    (h : TokenRecord bs arena r (.string s)) :
    bs[s.start]? = some 0x22 ∧
      ∃ (key : Bool) (len field : Nat) (cs : List Nat),
        r = .str key len field ∧ bodyCodePoints bs s = some cs ∧
        ((field = plainSpan (s.start + 1) ∧ s.stop = s.start + 2 + len) ∨
          (field < 2 ^ 63 ∧ s.start + 2 ≤ s.stop ∧
            escapeCodePoints ((arena.drop field).take len) = some cs)) := by
  cases h with
  | strPlain hq hs hcode =>
      exact ⟨hq, _, _, _, _, rfl, hcode, Or.inl ⟨rfl, hs⟩⟩
  | strArena hq hs hcode hbelow harena =>
      exact ⟨hq, _, _, _, _, rfl, hcode, Or.inr ⟨hbelow, hs, harena⟩⟩

/-! ### A binary64 value's bits are a word

The encoding's exponent field and significand fit the pattern, so a value's bits
are below `2 ^ 64` and a record's eight payload bytes hold them exactly.  At
`strtodSpec d` the bound is `toBits_lt_two_pow_64 _ (strtodSpec_isCode d)`, and the
composition is not written here: elaborating an application of
`strtodSpec_isCode` reduces `(strtodSpec d).IsCode`, whose `strtodSpec` unfolding
reaches a `10 ^ 2098`-scale exponent and exceeds the elaborator's recursion
depth.  So the number payload's word-ness is cited from the model's `IsCode`
statement rather than restated; the payload's *content* is
`tokenRecord_number`'s. -/

/-- **The bits of a binary64 value are a 64-bit word.** -/
theorem toBits_lt_two_pow_64 (f : Binary64) (h : f.IsCode) : f.toBits < 2 ^ 64 := by
  cases f with
  | inf neg =>
      cases neg <;> simp only [Binary64.toBits] <;> decide
  | fin neg E m =>
      simp only [Binary64.IsCode] at h
      rcases h with ⟨hE, hm⟩ | ⟨hE1, hE2, hm1, hm2⟩
      · subst hE
        have h52 : (2 : Nat) ^ 52 = 4503599627370496 := by decide
        have h63 : (2 : Nat) ^ 63 = 9223372036854775808 := by decide
        have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
        rw [h52] at hm
        cases neg with
        | false =>
            simp only [Binary64.toBits, Bool.false_eq_true, ite_false, ite_true]
            rw [h64]
            omega
        | true =>
            simp only [Binary64.toBits, ite_true]
            rw [h63, h64]
            omega
      · have h52 : (2 : Nat) ^ 52 = 4503599627370496 := by decide
        have h53 : (2 : Nat) ^ 53 = 9007199254740992 := by decide
        have h63 : (2 : Nat) ^ 63 = 9223372036854775808 := by decide
        have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
        rw [h53] at hm2
        rw [h52] at hm1
        have hne : E ≠ 0 := by omega
        cases neg with
        | false =>
            simp only [Binary64.toBits, Bool.false_eq_true, ite_false, hne]
            rw [h52, h64]
            omega
        | true =>
            simp only [Binary64.toBits, ite_true, hne, ite_false]
            rw [h52, h63, h64]
            omega

/-! ### The stream's record skeleton

`encodedBytes` writes the record's tag byte first and then a fixed-width payload —
one byte for a container or literal tag, nine for a number, thirteen for a key or
string (`EventRecord.encodedSize_tag`, `_number`, `_str`).  The tag byte therefore
announces its own record's width, so the *sequence of tags* is a function of the
stream: a reader recovers the record boundaries without knowing anything the walk
knew.  `parseSkeleton` is that function and `parseSkeleton_trace` states that a
related trace's bytes read back as its tags. -/

/-- The width a record's first byte announces: thirteen for a key or string, nine
for a number, one otherwise — the three widths the emitters write. -/
def recordWidth (b : UInt8) : Nat :=
  if b.toNat = EventRecord.tagKey ∨ b.toNat = EventRecord.tagStr then 13
  else if b.toNat = stage2TagNum then 9
  else 1

/-- The stream's record skeleton: each record's tag byte, stepping over the width
that byte announces.  Total, so it reads every stream; on a trace's encoding it is
the trace's tags (`parseSkeleton_trace`). -/
def parseSkeleton : List UInt8 → List Nat
  | [] => []
  | b :: rest => b.toNat :: parseSkeleton (rest.drop (recordWidth b - 1))
termination_by evs => evs.length
decreasing_by
  simp only [List.length_cons, List.length_drop]
  omega

/-- The skeleton of the empty stream. -/
theorem parseSkeleton_nil : parseSkeleton [] = [] := by rw [parseSkeleton]

/-- The skeleton of a stream with a head: the head's tag, then the skeleton past
the width the head announces. -/
theorem parseSkeleton_cons (b : UInt8) (rest : List UInt8) :
    parseSkeleton (b :: rest) =
      b.toNat :: parseSkeleton (rest.drop (recordWidth b - 1)) := by
  rw [parseSkeleton]

/-- Dropping a blob's length from the blob and a continuation is the
continuation. -/
theorem drop_append_length : ∀ (a b : List UInt8), List.drop a.length (a ++ b) = b
  | [], _ => rfl
  | _ :: a, b => drop_append_length a b

/-- The tags the encoding writes as one byte: the four containers and the three
literals.  5, 6 and 7 are the wider records' tags. -/
def EventRecord.Tagged : EventRecord → Prop
  | .tag t => t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 8 ∨ t = 9 ∨ t = 10
  | _ => True

/-- A byte's value is its `UInt8.ofNat` value below 256. -/
theorem ofNat_toNat_of_lt {t : Nat} (h : t < 256) : (UInt8.ofNat t).toNat = t := by
  rw [show UInt8.ofNat t = OfNat.ofNat t from rfl, UInt8.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

/-- **A one-byte tag's width.** -/
theorem recordWidth_of_tag {t : Nat} (h5 : t ≠ 5) (h6 : t ≠ 6) (h7 : t ≠ 7)
    (hlt : t < 256) : recordWidth (UInt8.ofNat t) = 1 := by
  rw [recordWidth, ofNat_toNat_of_lt hlt]
  split_ifs with h1 h2
  · exfalso
    rcases h1 with h | h
    · simp only [EventRecord.tagKey] at h; omega
    · simp only [EventRecord.tagStr] at h; omega
  · exfalso
    simp only [stage2TagNum] at h2
    omega
  · rfl

/-- **A key or string tag's width.** -/
theorem recordWidth_of_str (key : Bool) :
    recordWidth (UInt8.ofNat (if key then EventRecord.tagKey else EventRecord.tagStr)) = 13 := by
  cases key <;> decide

/-- **A number tag's width.** -/
theorem recordWidth_of_num : recordWidth (UInt8.ofNat stage2TagNum) = 9 := by decide

/-- **One record's first byte announces its own width.**  For a trace record the
skeleton of its encoding followed by any stream is the record's tag and the
stream's skeleton: the payload is stepped over exactly. -/
theorem parseSkeleton_encodedBytes {r : EventRecord} {rest : List UInt8}
    (h : r.Tagged) :
    parseSkeleton (r.encodedBytes ++ rest) = r.tagVal :: parseSkeleton rest := by
  cases r with
  | tag t =>
      have htag : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 8 ∨ t = 9 ∨ t = 10 := h
      have h5 : t ≠ 5 := by omega
      have h6 : t ≠ 6 := by omega
      have h7 : t ≠ 7 := by omega
      have hbyte : (UInt8.ofNat t).toNat = t := ofNat_toNat_of_lt (by omega)
      have hw : recordWidth (UInt8.ofNat t) = 1 := recordWidth_of_tag h5 h6 h7 (by omega)
      simp only [EventRecord.encodedBytes, EventRecord.tagVal, List.cons_append,
        List.nil_append]
      rw [parseSkeleton_cons, hw, hbyte]
      rfl
  | number bits =>
      have hbyte : (UInt8.ofNat stage2TagNum).toNat = stage2TagNum := by decide
      have hlen : (wordBytes 8 bits).length = 8 := natToBytes_length bits 8
      simp only [EventRecord.encodedBytes, EventRecord.tagVal, numberRecord,
        List.flatten_cons, List.flatten_nil, List.nil_append, List.cons_append,
        List.append_nil]
      rw [parseSkeleton_cons, recordWidth_of_num, hbyte]
      have hd : List.drop 8 (wordBytes 8 bits ++ rest) = rest := by
        rw [← hlen]
        exact drop_append_length _ _
      rw [hd]
  | str key len field =>
      have hbyte : (UInt8.ofNat (if key then EventRecord.tagKey else EventRecord.tagStr)).toNat =
          (if key then EventRecord.tagKey else EventRecord.tagStr) := by
        cases key <;> decide
      have hlen : (wordBytes 4 len ++ wordBytes 8 field).length = 12 := by
        simp only [List.length_append, wordBytes, natToBytes_length]
      simp only [EventRecord.encodedBytes, EventRecord.tagVal, List.cons_append,
        List.nil_append, List.append_assoc]
      rw [parseSkeleton_cons, recordWidth_of_str, hbyte]
      have h1213 : 13 - 1 = 12 := by decide
      rw [h1213]
      have hd : List.drop 12 (wordBytes 4 len ++ (wordBytes 8 field ++ rest)) = rest := by
        rw [← List.append_assoc, ← hlen]
        exact drop_append_length _ _
      rw [hd]

/-- **A related trace is a `Tagged` trace.**  Every record the relation admits
carries one of the seven one-byte tags, a number's tag, or a key/string's. -/
theorem Stage2Records.tagged {bs arena : List UInt8} {rs : List EventRecord}
    {toks : List Token} (h : Stage2Records bs arena rs toks) :
    ∀ r ∈ rs, r.Tagged := by
  induction h with
  | nil => intro r hr; cases hr
  | comma _ ih => exact ih
  | colon _ ih => exact ih
  | openBrace _ _ _ ih =>
      intro r hr; rcases List.mem_cons.mp hr with rfl | hr
      · exact Or.inl rfl
      · exact ih r hr
  | closeBrace _ _ _ ih =>
      intro r hr; rcases List.mem_cons.mp hr with rfl | hr
      · exact Or.inr (Or.inl rfl)
      · exact ih r hr
  | openBracket _ _ _ ih =>
      intro r hr; rcases List.mem_cons.mp hr with rfl | hr
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact ih r hr
  | closeBracket _ _ _ ih =>
      intro r hr; rcases List.mem_cons.mp hr with rfl | hr
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact ih r hr
  | trueTag _ _ _ ih =>
      intro r hr; rcases List.mem_cons.mp hr with rfl | hr
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact ih r hr
  | falseTag _ _ _ ih =>
      intro r hr; rcases List.mem_cons.mp hr with rfl | hr
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · exact ih r hr
  | nullTag _ _ _ ih =>
      intro r hr; rcases List.mem_cons.mp hr with rfl | hr
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      · exact ih r hr
  | number _ _ _ _ ih =>
      intro r hr; rcases List.mem_cons.mp hr with rfl | hr
      · trivial
      · exact ih r hr
  | strPlain _ _ _ _ ih =>
      intro r hr; rcases List.mem_cons.mp hr with rfl | hr
      · trivial
      · exact ih r hr
  | strArena _ _ _ _ _ _ ih =>
      intro r hr; rcases List.mem_cons.mp hr with rfl | hr
      · trivial
      · exact ih r hr

/-- **The emitted stream's skeleton is the trace's tags.**  At a related trace the
stream's bytes read back, record by record, as the trace's tag bytes — the record
boundaries and the classes, recovered from the stream itself. -/
theorem parseSkeleton_trace (rs : List EventRecord) (h : ∀ r ∈ rs, r.Tagged) :
    parseSkeleton (rs.map EventRecord.encodedBytes).flatten = rs.map EventRecord.tagVal := by
  induction rs with
  | nil => simp only [List.map_nil, List.flatten_nil, parseSkeleton_nil]
  | cons r rs ih =>
      have hr : r.Tagged := h r (by simp)
      have htail : ∀ x ∈ rs, x.Tagged := fun x hx => h x (by simp [hx])
      simp only [List.map_cons, List.flatten_cons]
      rw [parseSkeleton_encodedBytes hr, ih htail]

/-! ### The correspondence at the run's own reads

The two vocabularies meet at the run's reported extents: the arena at the **used**
prefix (derived from the reserved read, `usedPrefix_of_reserved`), the event
stream at the reported cursor, and the parser's tape for the *same* bytes. -/

/-- **The correspondence at an accepted run's reads.**  The tape is the reference
parser's for the document the arguments name; the arena reads at the used prefix
`ndstU`; the event stream reads at its reported cursor; the trace agrees with the
tape's tokens record for record (`TokenRecord`, separators excepted); and the
stream's skeleton is the trace's tag sequence.  So the emitted stream is not left
as a bare relation: its record structure is decoded from the bytes, each record's
kind and payload are the class's own, and the token list it names is the parser's
at the same document. -/
theorem stage2Records_at_accept {bs arena evs : List UInt8} {t : Tape}
    {rs : List EventRecord} {m : Mem} {dst ev ndst' nev' ndstU : Nat}
    (hparse : parseBytes Limits.default (ByteString.literal bs) = .ok t)
    (hdst : readBytes m dst ndst' = some arena)
    (hU : ndstU ≤ ndst')
    (hev : readBytes m ev nev' = some evs)
    (hrecs : evs = (rs.map EventRecord.encodedBytes).flatten)
    (hrel : Stage2Records bs (arena.take ndstU) rs t.tokens) :
    t.input = ByteString.literal bs ∧
      readBytes m dst ndstU = some (arena.take ndstU) ∧
      List.Forall₂ (TokenRecord bs (arena.take ndstU)) rs
        (Token.nonSeparators t.tokens) ∧
      readBytes m ev nev' = some evs ∧
      parseSkeleton evs = rs.map EventRecord.tagVal := by
  obtain ⟨-, -, hin, -⟩ := decodeTape_correct Limits.default (ByteString.literal bs) t hparse
  refine ⟨hin, usedPrefix_of_reserved hdst hU, Stage2Records.forall₂ hrel, hev, ?_⟩
  rw [hrecs]
  exact parseSkeleton_trace rs (Stage2Records.tagged hrel)

/-! ### Controls

The exactness theorem has to reproduce the trace examples and to *separate* the
classes: a trace whose record is the wrong class for its token is not related, so
the relation is not a vacuous wrapper around the examples. -/

/-- The `null` document's trace, from the pointwise form rather than by a
constructor chain: the general form specializes to the example. -/
theorem null_records_of_forall₂ :
    Stage2Records nullDoc [] ([EventRecord.tag 10] : List EventRecord) [.null ⟨0, 4⟩] :=
  Stage2Records.of_forall₂
    (List.Forall₂.cons (.nullTag (by decide) (by decide)) List.Forall₂.nil)

/-- **The relation separates classes.**  A `true` tag on the `null` document's
token is not related: the pointwise form leaves no constructor for it. -/
theorem null_trueTag_not_records :
    ¬ Stage2Records nullDoc [] ([EventRecord.tag 8] : List EventRecord) [.null ⟨0, 4⟩] := by
  intro h
  have h' := Stage2Records.forall₂ h
  cases h' with
  | cons hrec _ => cases hrec

/-- **The relation separates spans.**  The `null` tag at a span holding `true`'s
bytes is not related: the literal's own bytes are the constructor's premise. -/
theorem trueTag_null_span_not_records :
    ¬ Stage2Records ([0x74, 0x72, 0x75, 0x65] : List UInt8) []
        ([EventRecord.tag 8] : List EventRecord) [.null ⟨0, 4⟩] := by
  intro h
  have h' := Stage2Records.forall₂ h
  cases h' with
  | cons hrec _ => cases hrec

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.TokenRecord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TokenRecord

/-- info: 'LeanLLVM.Refinement.tokenRecord_tagVal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tokenRecord_tagVal

/-- info: 'LeanLLVM.Refinement.tokenRecord_tag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tokenRecord_tag

/-- info: 'LeanLLVM.Refinement.tokenRecord_number' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tokenRecord_number

/-- info: 'LeanLLVM.Refinement.tokenRecord_string' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tokenRecord_string

/-- info: 'LeanLLVM.Refinement.Stage2Records.forall₂' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Stage2Records.forall₂

/-- info: 'LeanLLVM.Refinement.Stage2Records.of_forall₂' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Stage2Records.of_forall₂

/-- info: 'LeanLLVM.Refinement.stage2Records_iff_forall₂' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Records_iff_forall₂

/-- info: 'LeanLLVM.Refinement.toBits_lt_two_pow_64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms toBits_lt_two_pow_64

/-- info: 'LeanLLVM.Refinement.parseSkeleton' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parseSkeleton

/-- info: 'LeanLLVM.Refinement.parseSkeleton_encodedBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parseSkeleton_encodedBytes

/-- info: 'LeanLLVM.Refinement.Stage2Records.tagged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Stage2Records.tagged

/-- info: 'LeanLLVM.Refinement.parseSkeleton_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parseSkeleton_trace

/-- info: 'LeanLLVM.Refinement.stage2Records_at_accept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Records_at_accept

/-- info: 'LeanLLVM.Refinement.null_records_of_forall₂' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms null_records_of_forall₂

/-- info: 'LeanLLVM.Refinement.null_trueTag_not_records' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms null_trueTag_not_records

/-- info: 'LeanLLVM.Refinement.trueTag_null_span_not_records' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms trueTag_null_span_not_records
