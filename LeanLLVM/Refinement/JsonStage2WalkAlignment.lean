/-
The walk's entry stream at the reference parser's token boundaries.

`JsonStage2TokenCorrespondence` states what the record trace says about the
reference parser's tokens and proves it at the run's own reads
(`stage2Records_at_accept`), but the relation's left side is a trace supplied
beside the run: that module names the row — the trace is the walk's `C.events` —
rather than deriving it, because the walk's proof has no clause tying
`WalkGeom.ent` to `parseValue`'s cursors.  `WalkGeom.ent` is ordered and inside
the document (`WalkGeom.order`, `WalkGeom.inside`) and nothing else: a position
is not yet a token start, so an arm's record can be related to *some* token at
its span but not to *the parser's token at that entry*.

This module states that tie and proves what it does and does not give.

**The clause.**  `WalkAlign G t` says the tape is the reference parser's for the
geometry's document (`t.input = ByteString.literal G.bs`), the entry count is the
token count, and at every entry index `k` the parser's token `t.tokens[k]` starts
at `entryPos G k`, the document byte there is one its class accepts, and — where
the next token exists — the next entry is the next token's start.  The class
relation is `classOfByte`, the parser's own first-byte dispatch written as a
function, with the number class read as `-` or a digit: the assertion is that the
byte announces the class of the token's own kind, so an arm's byte test and the
parser's constructor are the same claim.

**The loop head's reading.**  `WalkAlign.head` reads the clause at a head state:
the parser's token at the carried index starts at `entryPos G C.k`, and the
walk's `%8`, `%idxprom.i` and `%arrayidx10.i` are that token's class byte and
start.  The eleven `WalkAlign.head_*` corollaries turn the walk's byte test into
the parser's constructor — the form a per-arm proof consumes, because the arm's
branch on `%8` is then a statement about the parser's token and not about a byte
it alone knows.

**Preservation.**  The clause is a claim about the staging (`G.ent`, `G.bs`, the
tape) and no step of the walk writes it: `WalkChain.inv_align` carries it beside
`WalkInv` from a trace's head to its tail.  What might make that vacuous is that
the memory changes under the reads the clause rests on; `WalkInv.doc_read` and
`WalkInv.entries_read` say it does not — the document and the entry stream lie
outside the walk's frame (`WalkInv.doc_outside`, `WalkInv.entry_outside`), so
every state still reads the staged bytes and hence the staged positions.  The
walk's index advance is covered by the clause's own next-entry conjunct, read at
`k + 1` (`WalkAlign.next`).

**What the clause closes.**  The four container classes' rows are theorems, not
an arm's obligation: the alignment fixes the start and the byte, the tape's span
discipline (`checkSpans`, through `spansWellFormed`) fixes the one-byte stop, and
`TokenRecord`'s own constructor follows (`tokenRecord_punct`).  The two
separators carry no record, so they owe no row at all.

**What it does not close.**  The trace.  The alignment says which token an entry
is; it says nothing about the record an arm appended.  Hence it does not imply
the encoding, and `align_not_enough` proves that rather than asserting it: a
geometry at the `null` document whose single entry is the parser's token start,
with an empty trace, satisfies the alignment and emits nothing — `Stage2Records`
is false of the pair.  The row still owed is `WalkTraceRow`, and
`emittedStream_of_row` is the composition that turns it into the relation, the
stream's byte-level form and its decoded skeleton.  The three remaining classes
are why it is not a theorem here: a literal's exact span, a string's body and a
number's lexeme are the parser's token-construction facts, and
`LeanLLVM/JSON/Correct.lean` keeps them private — `DecodesValue` and the mutual
induction's per-branch facts are `private`, and what the tape exposes is the span
discipline (`tape_valid`) and the span-level decode; punctuation's one-byte shape
is the only class whose `TokenRecord` constructor the span discipline alone
supplies.  Naming the row is the honest statement: the alignment is necessary for
it, and insufficient without it.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonStage2TokenCorrespondence
import LeanLLVM.Refinement.JsonStage2WalkScope
import LeanLLVM.Refinement.JsonEntrySteps

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### The parser's classes

The reference parser dispatches a value on the first byte at its cursor
(`parseValue`): four container bytes, the opening quote, the three literal
keywords, and `-` or a digit for a number.  The two separators are classes of the
grammar position rather than of a value.  `TokClass` is that dispatch, and
`classOfByte` its byte reading; the number class is the one whose byte is not a
single value, so it is read as `-` or a digit rather than as one byte. -/

/-- The reference parser's first-byte classes. -/
inductive TokClass where
  /-- `[`. -/
  | openBracket
  /-- `]`. -/
  | closeBracket
  /-- `{`. -/
  | openBrace
  /-- `}`. -/
  | closeBrace
  /-- `,`. -/
  | comma
  /-- `:`. -/
  | colon
  /-- `null`. -/
  | null
  /-- `true`. -/
  | true
  /-- `false`. -/
  | false
  /-- `"`. -/
  | string
  /-- `-` or a digit. -/
  | number
deriving DecidableEq, Repr

/-- The class of a token's kind: the constructor's branch.  A separator is its
own class, and a string's class is the opening quote's. -/
def tokenClass : Token → TokClass
  | .punct .openBracket _ => .openBracket
  | .punct .closeBracket _ => .closeBracket
  | .punct .openBrace _ => .openBrace
  | .punct .closeBrace _ => .closeBrace
  | .punct .comma _ => .comma
  | .punct .colon _ => .colon
  | .null _ => .null
  | .bool true _ => .true
  | .bool false _ => .false
  | .string _ => .string
  | .number _ => .number

/-- The class a document byte announces: the parser's own first-byte test.  The
number test is first because the number class is the only one that is not a
single byte; the classes are disjoint, so the order does not change which class a
byte names (the ten literal bytes are decidably outside the number test).

The comparisons are `decide` rather than `BEq`: `UInt8`'s `==` carries
`Classical.choice` in its instance, and the clause's footprint stays at
`propext` and `Quot.sound`. -/
def classOfByte (b : UInt8) : Option TokClass :=
  if decide (b = 0x2D) || IsDigitB b then some .number
  else if decide (b = 0x5B) then some .openBracket
  else if decide (b = 0x5D) then some .closeBracket
  else if decide (b = 0x7B) then some .openBrace
  else if decide (b = 0x7D) then some .closeBrace
  else if decide (b = 0x2C) then some .comma
  else if decide (b = 0x3A) then some .colon
  else if decide (b = 0x6E) then some .null
  else if decide (b = 0x74) then some .true
  else if decide (b = 0x66) then some .false
  else if decide (b = 0x22) then some .string
  else none

/-- The number class is the class of `-` and of the digits. -/
theorem classOfByte_number {b : UInt8} (h : b = 0x2D ∨ IsDigitB b = true) :
    classOfByte b = some .number := by
  have h' : (decide (b = 0x2D) || IsDigitB b) = true := by
    rcases h with rfl | h
    · simp
    · rw [h]; exact Bool.or_true _
  simp only [classOfByte]
  rw [ite_eq_left h']

/-- `[` names the bracket class. -/
theorem classOfByte_openBracket : classOfByte 0x5B = some .openBracket := by decide

/-- `]` names the bracket class. -/
theorem classOfByte_closeBracket : classOfByte 0x5D = some .closeBracket := by decide

/-- `{` names the brace class. -/
theorem classOfByte_openBrace : classOfByte 0x7B = some .openBrace := by decide

/-- `}` names the brace class. -/
theorem classOfByte_closeBrace : classOfByte 0x7D = some .closeBrace := by decide

/-- `,` names the comma class. -/
theorem classOfByte_comma : classOfByte 0x2C = some .comma := by decide

/-- `:` names the colon class. -/
theorem classOfByte_colon : classOfByte 0x3A = some .colon := by decide

/-- `n` names the `null` class. -/
theorem classOfByte_null : classOfByte 0x6E = some .null := by decide

/-- `t` names the `true` class. -/
theorem classOfByte_true : classOfByte 0x74 = some .true := by decide

/-- `f` names the `false` class. -/
theorem classOfByte_false : classOfByte 0x66 = some .false := by decide

/-- `"` names the string class. -/
theorem classOfByte_string : classOfByte 0x22 = some .string := by decide

/-! The class determines the constructor: the inversions the loop-head corollaries
read.  Each is a case analysis on the token, with the other classes refuted by
their own class equation. -/

/-- An `openBracket`-class token is the bracket. -/
theorem tokenClass_openBracket {tok : Token} (h : tokenClass tok = .openBracket) :
    ∃ s : Span, tok = .punct .openBracket s := by
  cases tok with
  | punct k s => cases k <;> simp [tokenClass] at h; exact ⟨s, rfl⟩
  | null _ => simp [tokenClass] at h
  | bool b _ => cases b <;> simp [tokenClass] at h
  | number _ => simp [tokenClass] at h
  | string _ => simp [tokenClass] at h

/-- A `closeBracket`-class token is the bracket. -/
theorem tokenClass_closeBracket {tok : Token} (h : tokenClass tok = .closeBracket) :
    ∃ s : Span, tok = .punct .closeBracket s := by
  cases tok with
  | punct k s => cases k <;> simp [tokenClass] at h; exact ⟨s, rfl⟩
  | null _ => simp [tokenClass] at h
  | bool b _ => cases b <;> simp [tokenClass] at h
  | number _ => simp [tokenClass] at h
  | string _ => simp [tokenClass] at h

/-- An `openBrace`-class token is the brace. -/
theorem tokenClass_openBrace {tok : Token} (h : tokenClass tok = .openBrace) :
    ∃ s : Span, tok = .punct .openBrace s := by
  cases tok with
  | punct k s => cases k <;> simp [tokenClass] at h; exact ⟨s, rfl⟩
  | null _ => simp [tokenClass] at h
  | bool b _ => cases b <;> simp [tokenClass] at h
  | number _ => simp [tokenClass] at h
  | string _ => simp [tokenClass] at h

/-- A `closeBrace`-class token is the brace. -/
theorem tokenClass_closeBrace {tok : Token} (h : tokenClass tok = .closeBrace) :
    ∃ s : Span, tok = .punct .closeBrace s := by
  cases tok with
  | punct k s => cases k <;> simp [tokenClass] at h; exact ⟨s, rfl⟩
  | null _ => simp [tokenClass] at h
  | bool b _ => cases b <;> simp [tokenClass] at h
  | number _ => simp [tokenClass] at h
  | string _ => simp [tokenClass] at h

/-- A `comma`-class token is the comma. -/
theorem tokenClass_comma {tok : Token} (h : tokenClass tok = .comma) :
    ∃ s : Span, tok = .punct .comma s := by
  cases tok with
  | punct k s => cases k <;> simp [tokenClass] at h; exact ⟨s, rfl⟩
  | null _ => simp [tokenClass] at h
  | bool b _ => cases b <;> simp [tokenClass] at h
  | number _ => simp [tokenClass] at h
  | string _ => simp [tokenClass] at h

/-- A `colon`-class token is the colon. -/
theorem tokenClass_colon {tok : Token} (h : tokenClass tok = .colon) :
    ∃ s : Span, tok = .punct .colon s := by
  cases tok with
  | punct k s => cases k <;> simp [tokenClass] at h; exact ⟨s, rfl⟩
  | null _ => simp [tokenClass] at h
  | bool b _ => cases b <;> simp [tokenClass] at h
  | number _ => simp [tokenClass] at h
  | string _ => simp [tokenClass] at h

/-- A `null`-class token is the literal. -/
theorem tokenClass_null {tok : Token} (h : tokenClass tok = .null) :
    ∃ s : Span, tok = .null s := by
  cases tok with
  | punct k s => cases k <;> simp [tokenClass] at h
  | null s => exact ⟨s, rfl⟩
  | bool b _ => cases b <;> simp [tokenClass] at h
  | number _ => simp [tokenClass] at h
  | string _ => simp [tokenClass] at h

/-- A `true`-class token is the literal. -/
theorem tokenClass_true {tok : Token} (h : tokenClass tok = .true) :
    ∃ s : Span, tok = .bool true s := by
  cases tok with
  | punct k s => cases k <;> simp [tokenClass] at h
  | null _ => simp [tokenClass] at h
  | bool b s => cases b <;> simp [tokenClass] at h; exact ⟨s, rfl⟩
  | number _ => simp [tokenClass] at h
  | string _ => simp [tokenClass] at h

/-- A `false`-class token is the literal. -/
theorem tokenClass_false {tok : Token} (h : tokenClass tok = .false) :
    ∃ s : Span, tok = .bool false s := by
  cases tok with
  | punct k s => cases k <;> simp [tokenClass] at h
  | null _ => simp [tokenClass] at h
  | bool b s => cases b <;> simp [tokenClass] at h; exact ⟨s, rfl⟩
  | number _ => simp [tokenClass] at h
  | string _ => simp [tokenClass] at h

/-- A `string`-class token is the quoted token. -/
theorem tokenClass_string {tok : Token} (h : tokenClass tok = .string) :
    ∃ s : Span, tok = .string s := by
  cases tok with
  | punct k s => cases k <;> simp [tokenClass] at h
  | null _ => simp [tokenClass] at h
  | bool b _ => cases b <;> simp [tokenClass] at h
  | number _ => simp [tokenClass] at h
  | string s => exact ⟨s, rfl⟩

/-- A `number`-class token is the number. -/
theorem tokenClass_number {tok : Token} (h : tokenClass tok = .number) :
    ∃ s : Span, tok = .number s := by
  cases tok with
  | punct k s => cases k <;> simp [tokenClass] at h
  | null _ => simp [tokenClass] at h
  | bool b _ => cases b <;> simp [tokenClass] at h
  | number s => exact ⟨s, rfl⟩
  | string _ => simp [tokenClass] at h

/-- **The alignment clause.**  The tape is the parser's for the geometry's
document; the entry count is the token count; each entry index names a token
starting at `entryPos G k`; the byte there is one the token's class announces; and
where there is a next token, the next entry is its start.  The class clause is an
implication rather than a component of the token existential, so the two parts can
be read separately: the byte is the class's, whatever the token's shape. -/
def WalkAlign {m0 : Mem} (G : WalkGeom m0) (t : Tape) : Prop :=
  t.input = ByteString.literal G.bs ∧
    G.nep = t.tokens.length ∧
    (∀ k, k < G.nep → ∃ tok : Token, ∃ b : UInt8,
      t.tokens[k]? = some tok ∧ tok.span.start = entryPos G k ∧
        G.bs[entryPos G k]? = some b) ∧
    (∀ k, k < G.nep → ∀ (tok : Token) (b : UInt8),
      t.tokens[k]? = some tok → G.bs[entryPos G k]? = some b →
        classOfByte b = some (tokenClass tok)) ∧
    (∀ k, k + 1 < G.nep → ∃ tok : Token,
      t.tokens[k + 1]? = some tok ∧ tok.span.start = entryPos G (k + 1))

/-- The clause's first conjunct: the tape is the parser's for this document. -/
theorem WalkAlign.input {m0 : Mem} {G : WalkGeom m0} {t : Tape} (h : WalkAlign G t) :
    t.input = ByteString.literal G.bs := h.1

/-- The clause's second conjunct: one entry per token. -/
theorem WalkAlign.tokens_length {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    (h : WalkAlign G t) : G.nep = t.tokens.length := h.2.1

/-- The entry stream's own length, from the staging rather than from the clause:
`WalkGeom.entries` reads `G.nep` lanes.  Together with `WalkAlign.tokens_length`
this is the statement that the two streams have the same index range. -/
theorem WalkAlign.ent_length {m0 : Mem} (G : WalkGeom m0) : G.ent.length = G.nep :=
  readLanes32_length m0 G.ep G.nep G.ent G.entries

/-- **The clause at one index.**  The parser's token there, its start, and the
document byte the walk reads. -/
theorem WalkAlign.at {m0 : Mem} {G : WalkGeom m0} {t : Tape} (h : WalkAlign G t)
    {k : Nat} (hk : k < G.nep) :
    ∃ tok : Token, ∃ b : UInt8,
      t.tokens[k]? = some tok ∧ tok.span.start = entryPos G k ∧
        G.bs[entryPos G k]? = some b :=
  h.2.2.1 k hk

/-- **The class clause at one index**: the byte the walk reads is the one the
parser's token announces. -/
theorem WalkAlign.class {m0 : Mem} {G : WalkGeom m0} {t : Tape} (h : WalkAlign G t)
    {k : Nat} (hk : k < G.nep) {tok : Token} {b : UInt8}
    (htok : t.tokens[k]? = some tok) (hbs : G.bs[entryPos G k]? = some b) :
    classOfByte b = some (tokenClass tok) :=
  h.2.2.2.1 k hk tok b htok hbs

/-- **The next entry is the next token's start.**  The clause's third reading, at
`k + 1`: this is what makes the walk's index advance preserve the clause rather
than re-establish it. -/
theorem WalkAlign.next {m0 : Mem} {G : WalkGeom m0} {t : Tape} (h : WalkAlign G t)
    {k : Nat} (hk : k + 1 < G.nep) :
    ∃ tok : Token, t.tokens[k + 1]? = some tok ∧ tok.span.start = entryPos G (k + 1) :=
  h.2.2.2.2 k hk

/-- **The loop head's alignment, at the walk's registers.**  At a head state the
parser's token at the carried index starts at `entryPos G C.k`, the walk's `%8`
is that token's class byte, `%idxprom.i` is the start, and `%arrayidx10.i` is its
address.  This is the clause read at the index the dispatch is about to use. -/
theorem WalkAlign.head {m0 : Mem} {G : WalkGeom m0} {t : Tape} {C : WalkCarry G}
    {s : State} (h : WalkAlign G t) (hInv : WalkInv G C s) (hk : C.k < G.nep) :
    ∃ tok : Token, ∃ b : UInt8,
      t.tokens[C.k]? = some tok ∧ tok.span.start = entryPos G C.k ∧
        entryByte G C.k = b ∧ classOfByte b = some (tokenClass tok) ∧
        lookupName s.env "%8" = some (.int 8 (BitVec.ofNat 8 b.toNat)) ∧
        lookupName s.env "%idxprom.i" =
          some (.int 64 (BitVec.ofNat 64 (entryPos G C.k))) ∧
        lookupName s.env "%arrayidx10.i" = some (.ptr (G.b + entryPos G C.k)) := by
  obtain ⟨tok, b, htok, hstart, hbs⟩ := h.at hk
  have hbyte : entryByte G C.k = b := by
    show G.bs.getD (entryPos G C.k) 0 = b
    rw [List.getD_eq_getElem?_getD, hbs]
    rfl
  have hcls : classOfByte b = some (tokenClass tok) := h.class hk htok hbs
  refine ⟨tok, b, htok, hstart, hbyte, hcls, ?_, hInv.idx_reg, hInv.iter.regarr⟩
  rw [← hbyte]
  exact hInv.iter.reg8

/-- **The class at the loop head, from the byte.**  When the walk's byte is a
class's byte, the parser's token at the carried index is of that class: the
alignment names the class through the byte, so this is an equality rather than a
case over the token. -/
theorem WalkAlign.head_class {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (h : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) {cls : TokClass} {b0 : UInt8}
    (hbyte : entryByte G C.k = b0) (hcls : classOfByte b0 = some cls) :
    ∃ tok : Token, t.tokens[C.k]? = some tok ∧ tokenClass tok = cls ∧
      tok.span.start = entryPos G C.k := by
  obtain ⟨tok, b, htok, hstart, hbyteb, hclsTok, -⟩ := h.head hInv hk
  have hb : b = b0 := by rw [← hbyteb]; exact hbyte
  rw [hb] at hclsTok
  rw [hcls] at hclsTok
  exact ⟨tok, htok, (Option.some.inj hclsTok).symm, hstart⟩

/-- **The opener at the loop head.** -/
theorem WalkAlign.head_openBrace {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (h : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hbyte : entryByte G C.k = 0x7B) :
    ∃ sp : Span, t.tokens[C.k]? = some (.punct .openBrace sp) ∧
      sp.start = entryPos G C.k := by
  obtain ⟨tok, htok, hcls, hstart⟩ :=
    h.head_class hInv hk hbyte classOfByte_openBrace
  obtain ⟨sp, rfl⟩ := tokenClass_openBrace hcls
  exact ⟨sp, htok, hstart⟩

/-- **The closer at the loop head.** -/
theorem WalkAlign.head_closeBrace {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (h : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hbyte : entryByte G C.k = 0x7D) :
    ∃ sp : Span, t.tokens[C.k]? = some (.punct .closeBrace sp) ∧
      sp.start = entryPos G C.k := by
  obtain ⟨tok, htok, hcls, hstart⟩ :=
    h.head_class hInv hk hbyte classOfByte_closeBrace
  obtain ⟨sp, rfl⟩ := tokenClass_closeBrace hcls
  exact ⟨sp, htok, hstart⟩

/-- **The array opener at the loop head.** -/
theorem WalkAlign.head_openBracket {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (h : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hbyte : entryByte G C.k = 0x5B) :
    ∃ sp : Span, t.tokens[C.k]? = some (.punct .openBracket sp) ∧
      sp.start = entryPos G C.k := by
  obtain ⟨tok, htok, hcls, hstart⟩ :=
    h.head_class hInv hk hbyte classOfByte_openBracket
  obtain ⟨sp, rfl⟩ := tokenClass_openBracket hcls
  exact ⟨sp, htok, hstart⟩

/-- **The array closer at the loop head.** -/
theorem WalkAlign.head_closeBracket {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (h : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hbyte : entryByte G C.k = 0x5D) :
    ∃ sp : Span, t.tokens[C.k]? = some (.punct .closeBracket sp) ∧
      sp.start = entryPos G C.k := by
  obtain ⟨tok, htok, hcls, hstart⟩ :=
    h.head_class hInv hk hbyte classOfByte_closeBracket
  obtain ⟨sp, rfl⟩ := tokenClass_closeBracket hcls
  exact ⟨sp, htok, hstart⟩

/-- **The comma at the loop head.** -/
theorem WalkAlign.head_comma {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (h : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hbyte : entryByte G C.k = 0x2C) :
    ∃ sp : Span, t.tokens[C.k]? = some (.punct .comma sp) ∧
      sp.start = entryPos G C.k := by
  obtain ⟨tok, htok, hcls, hstart⟩ :=
    h.head_class hInv hk hbyte classOfByte_comma
  obtain ⟨sp, rfl⟩ := tokenClass_comma hcls
  exact ⟨sp, htok, hstart⟩

/-- **The colon at the loop head.** -/
theorem WalkAlign.head_colon {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (h : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hbyte : entryByte G C.k = 0x3A) :
    ∃ sp : Span, t.tokens[C.k]? = some (.punct .colon sp) ∧
      sp.start = entryPos G C.k := by
  obtain ⟨tok, htok, hcls, hstart⟩ :=
    h.head_class hInv hk hbyte classOfByte_colon
  obtain ⟨sp, rfl⟩ := tokenClass_colon hcls
  exact ⟨sp, htok, hstart⟩

/-- **`null` at the loop head.** -/
theorem WalkAlign.head_null {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (h : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hbyte : entryByte G C.k = 0x6E) :
    ∃ sp : Span, t.tokens[C.k]? = some (.null sp) ∧ sp.start = entryPos G C.k := by
  obtain ⟨tok, htok, hcls, hstart⟩ :=
    h.head_class hInv hk hbyte classOfByte_null
  obtain ⟨sp, rfl⟩ := tokenClass_null hcls
  exact ⟨sp, htok, hstart⟩

/-- **`true` at the loop head.** -/
theorem WalkAlign.head_true {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (h : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hbyte : entryByte G C.k = 0x74) :
    ∃ sp : Span, t.tokens[C.k]? = some (.bool true sp) ∧ sp.start = entryPos G C.k := by
  obtain ⟨tok, htok, hcls, hstart⟩ :=
    h.head_class hInv hk hbyte classOfByte_true
  obtain ⟨sp, rfl⟩ := tokenClass_true hcls
  exact ⟨sp, htok, hstart⟩

/-- **`false` at the loop head.** -/
theorem WalkAlign.head_false {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (h : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hbyte : entryByte G C.k = 0x66) :
    ∃ sp : Span, t.tokens[C.k]? = some (.bool false sp) ∧ sp.start = entryPos G C.k := by
  obtain ⟨tok, htok, hcls, hstart⟩ :=
    h.head_class hInv hk hbyte classOfByte_false
  obtain ⟨sp, rfl⟩ := tokenClass_false hcls
  exact ⟨sp, htok, hstart⟩

/-- **A string at the loop head.** -/
theorem WalkAlign.head_string {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (h : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hbyte : entryByte G C.k = 0x22) :
    ∃ sp : Span, t.tokens[C.k]? = some (.string sp) ∧ sp.start = entryPos G C.k := by
  obtain ⟨tok, htok, hcls, hstart⟩ :=
    h.head_class hInv hk hbyte classOfByte_string
  obtain ⟨sp, rfl⟩ := tokenClass_string hcls
  exact ⟨sp, htok, hstart⟩

/-- **A number at the loop head.**  The class's byte is not one value: the
hypothesis is the parser's own test, `-` or a digit. -/
theorem WalkAlign.head_number {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (h : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) {b0 : UInt8} (hbyte : entryByte G C.k = b0)
    (hb : b0 = 0x2D ∨ IsDigitB b0 = true) :
    ∃ sp : Span, t.tokens[C.k]? = some (.number sp) ∧ sp.start = entryPos G C.k := by
  obtain ⟨tok, htok, hcls, hstart⟩ :=
    h.head_class hInv hk hbyte (classOfByte_number hb)
  obtain ⟨sp, rfl⟩ := tokenClass_number hcls
  exact ⟨sp, htok, hstart⟩

/-! ### The clause's data survives the walk

The clause rests on two reads of the staged memory: the document and the entry
stream.  `WalkInv.frame` is silence outside the run's write extents, and both
objects end at or below the call's cursor, so no step disturbs either — the
positions the clause names are the positions every state reads. -/

/-- **The document still reads as the staging's.**  Every state of the walk reads
`G.bs` at `G.b`, because the document lies outside the frame. -/
theorem WalkInv.doc_read {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) : readBytes s.mem G.b G.n = some G.bs := by
  rw [readBytes_eq_of_UnchangedOn (mem := m0) (m := s.mem)
    (unchangedOutside_iff_inRegions.mp h.frame)
    (a := G.b) (n := G.n)
    (fun i hi => h.doc_outside (by omega) (by omega))]
  exact G.doc

/-- **The entry stream still reads as the staging's.**  The table's lanes are
outside the frame, so the walk's own positions are the ones it started with: the
clause's left side is not re-derived from memory that a step could have written.
The lane congruence is `readLanes32_congr` (`JsonEntrySteps`), read at the frame's
silence rather than restated. -/
theorem WalkInv.entries_read {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) : readLanes32 s.mem G.ep G.nep = some G.ent := by
  rw [JsonEntrySteps.readLanes32_congr m0 s.mem G.ep G.nep (fun j _ => by
    rw [readBytes_eq_of_UnchangedOn (mem := m0) (m := s.mem)
      (unchangedOutside_iff_inRegions.mp h.frame)
      (a := G.ep + 4 * j) (n := 4)
      (fun i hi => h.entry_outside (by omega) (by omega))])]
  exact G.entries

/-! ### The clause is preserved by every step

`WalkLink` is the dispatch's step relation and `WalkChain` a trace of links; the
alignment is not a field of `WalkInv` because it mentions the parser's tape, a
run-fixed parameter, and nothing a step writes — so it rides the trace beside the
invariant rather than being re-established at each link. -/

namespace WalkScope

theorem WalkLink.align {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' : State} {t : Tape}
    (_hl : WalkLink calls G C s C' s') (hal : WalkAlign G t) : WalkAlign G t := hal

/-- **Every trace carries the alignment beside the invariant.**  A chain's tail
has both clauses a loop-head consumer reads: `WalkInv` at the tail and the
alignment, unchanged. -/
theorem WalkChain.inv_align {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' : State} {t : Tape}
    (h : WalkChain calls G C s C' s') (hal : WalkAlign G t) :
    WalkInv G C' s' ∧ WalkAlign G t := by
  induction h with
  | nil hinv => exact ⟨hinv, hal⟩
  | tail _ _ ih => exact ih

/-- **The alignment at the tail of a trace**, stated alone for the consumers that
need only it. -/
theorem WalkChain.align {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' : State} {t : Tape}
    (h : WalkChain calls G C s C' s') (hal : WalkAlign G t) : WalkAlign G t :=
  (h.inv_align hal).2

end WalkScope

/-! ### What the clause closes: the containers' rows

`checkSpans` is the tape's span discipline, and `spansWellFormed` is it at the
tape.  A punctuation token's discipline is the one-byte stop, which is the last
fact `TokenRecord`'s container constructors need beyond the byte; the alignment
supplies the start and the byte.  So a container entry's row is a theorem — the
arm supplies its own tag and byte test, nothing about the token. -/

/-- **The span discipline `checkSpans` gives each token of the list**: the span is
non-empty, inside the input, and a punctuation span is one byte. -/
theorem checkSpans_mem {bs : Bytes} {toks : List Token} {prev : Nat}
    (h : checkSpans bs toks prev = true) {tok : Token} (hm : tok ∈ toks) :
    tok.span.start < tok.span.stop ∧ tok.span.stop ≤ bs.length ∧
      ∀ (p : Punct) (s : Span), tok = .punct p s → s.stop = s.start + 1 := by
  induction toks generalizing prev with
  | nil => simp at hm
  | cons head rest ih =>
      simp only [checkSpans] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨-, hlt⟩, hle⟩, hpun⟩, hrest⟩ := h
      rcases List.mem_cons.mp hm with rfl | hm'
      · refine ⟨hlt, hle, ?_⟩
        intro p s heq
        subst heq
        exact of_decide_eq_true hpun
      · exact ih hrest hm'

/-- The byte a punctuation token's class announces. -/
def punctByte : Punct → UInt8
  | .openBracket => 0x5B
  | .closeBracket => 0x5D
  | .openBrace => 0x7B
  | .closeBrace => 0x7D
  | .comma => 0x2C
  | .colon => 0x3A

/-- The tag the emitter writes for a container's marker.  The two separators
carry no record, so their entry is the placeholder `0` and the callers below
exclude them. -/
def punctTag : Punct → Nat
  | .openBracket => 3
  | .closeBracket => 4
  | .openBrace => 1
  | .closeBrace => 2
  | .comma => 0
  | .colon => 0

/-- **A container entry's row.**  The alignment's start, the tape's one-byte
discipline, and `TokenRecord`'s own constructor: the class's record at the class's
span. -/
theorem tokenRecord_punct {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {arena : List UInt8} {k : Nat} (h : WalkAlign G t)
    (hspans : spansWellFormed t = true) (hk : k < G.nep)
    {p : Punct} {s : Span}
    (hp : p = .openBrace ∨ p = .closeBrace ∨ p = .openBracket ∨ p = .closeBracket)
    (htok : t.tokens[k]? = some (.punct p s))
    (hbyte : G.bs[entryPos G k]? = some (punctByte p)) :
    s.start = entryPos G k ∧ s.stop = s.start + 1 ∧
      TokenRecord G.bs arena (.tag (punctTag p)) (.punct p s) := by
  obtain ⟨tok, b, htok', hstart, hbs⟩ := h.at hk
  have htok_eq : tok = .punct p s := by
    rw [htok] at htok'
    exact (Option.some.inj htok').symm
  subst htok_eq
  have hstart' : s.start = entryPos G k := hstart
  obtain ⟨-, -, hdisc⟩ := checkSpans_mem (prev := 0) hspans (List.mem_of_getElem? htok)
  have hstop : s.stop = s.start + 1 := hdisc p s rfl
  rw [← hstart'] at hbyte
  refine ⟨hstart', hstop, ?_⟩
  rcases hp with rfl | rfl | rfl | rfl
  · exact TokenRecord.openBrace hbyte hstop
  · exact TokenRecord.closeBrace hbyte hstop
  · exact TokenRecord.openBracket hbyte hstop
  · exact TokenRecord.closeBracket hbyte hstop

/-! ### The staged entry stream: the quote lanes

`WalkAlign` is the walk's alignment for a *token-start* stream — one entry per
token, at its `span.start`.  The ABI hands the walk a different stream whenever the
document has a string: `kernel/json/stage2.h:60` defines `ep` as "quote characters,
the structural bytes and the first byte of every scalar", so a string contributes
two lanes, its first byte and its closing quote.  `["ab","cd"]` is the smallest
witness — `[0, 1, 4, 5, 6, 9, 10]`, seven entries for five tokens — and the string
arm reads the lane *after* its own as the closing quote (`JsonStage2IR:639-641`,
`%sub260.i = close - %idxprom.i - 1`) and leaves the index two entries further on
(`%inc208.i = %k.0.i249 + 2`).

**Why this is a second relation and not a generalization of `WalkAlign`.**
`WalkTracePrefix` is indexed by *tokens*: the trace so far is
`Token.recordTokens t.tokens C.k` and the exit condition is
`C.k = t.tokens.length`.  On a quote-inclusive stream the carry's index counts
*entries*, and the two indices part company at the first string — the arm advances
the entry index by two and the token index by one — so no substitution makes the old
clause true of the new stream, and the token-start clause is false of every document
that has a string.  Stating `WalkAlignQuoted` beside it keeps each relation honest
about the index it counts: `WalkAlign` remains the string-free case, which the
container, number and separator rows consume, and `Token.entryLanes_stringFree` is
the theorem that the two streams coincide there.  That is one staging with a case
rather than two accounts of the ABI, and it is why the string rows state their
carries' token indices beside their entry indices instead of equating them.

**What the string rows take from here.**  `WalkAlignQuoted.input` is the tape's
document — the payload arms' body read-back reads it — `WalkAlignQuoted.ent` and
`WalkAlignQuoted.lane_pos` fix the entry positions, and
`WalkAlignQuoted.stringExtent` is the arm's arithmetic: the lane after a string's
start lane is its closing quote, so `close = lane k + 1` is `span.stop - 1` and the
body extent `close - start - 1` is `span.stop - span.start - 2`.  What stays the
arm's is the record it appended and the body's read-back.
-/

/-- **One lane of the staged entry stream.**  A token contributes its first byte; a
string token contributes its closing quote as the next lane. -/
inductive EntryLane where
  /-- A token's first byte. -/
  | start (tok : Token)
  /-- A string token's closing quote. -/
  | close (tok : Token)
deriving DecidableEq, Repr

/-- The document position a lane reads.  A start lane reads `span.start`; a string's
close lane reads the quote just before `span.stop`, which is where the token's span
ends. -/
def EntryLane.pos : EntryLane → Nat
  | .start tok => tok.span.start
  | .close tok => tok.span.stop - 1

/-- The lanes a token contributes: a string's closing quote, nothing otherwise. -/
def Token.closeLane : Token → List EntryLane
  | .string s => [.close (.string s)]
  | _ => []

/-- **The staged entry stream, token by token**: each token's first byte, followed by
a string's closing quote. -/
def Token.entryLanes : List Token → List EntryLane
  | [] => []
  | tok :: rest => .start tok :: (Token.closeLane tok ++ Token.entryLanes rest)

/-- The lane list at the empty token list. -/
theorem Token.entryLanes_nil : Token.entryLanes [] = [] := rfl

/-- The lane list at a token list's head: its first byte, then its close lane or
nothing, then the remaining tokens' lanes. -/
theorem Token.entryLanes_cons (tok : Token) (rest : List Token) :
    Token.entryLanes (tok :: rest) =
      .start tok :: (Token.closeLane tok ++ Token.entryLanes rest) := rfl

/-- A string token's two lanes. -/
theorem Token.entryLanes_string (sp : Span) (rest : List Token) :
    Token.entryLanes (Token.string sp :: rest) =
      .start (.string sp) :: .close (.string sp) :: Token.entryLanes rest := rfl

/-- **A token that is not a string contributes one lane.** -/
theorem Token.entryLanes_start {tok : Token} {rest : List Token}
    (h : ∀ sp : Span, tok ≠ .string sp) :
    Token.entryLanes (tok :: rest) = .start tok :: Token.entryLanes rest := by
  rw [Token.entryLanes_cons]
  cases tok with
  | string s => exact absurd rfl (h s)
  | punct p s => rfl
  | null s => rfl
  | bool b s => rfl
  | number s => rfl

/-- **The alignment at the quote-inclusive stream.**  The tape is the parser's for the
geometry's document, the geometry's entry positions are the lanes' positions, and at
every start lane the document's byte is the one the token's class announces.  The
close lanes carry no class: the token they close is the one whose start lane is
before them, and `Token.entryLanes_succ_string` is that adjacency. -/
def WalkAlignQuoted {m0 : Mem} (G : WalkGeom m0) (t : Tape) : Prop :=
  t.input = ByteString.literal G.bs ∧
    G.ent = (Token.entryLanes t.tokens).map EntryLane.pos ∧
    (∀ k, k < G.nep → ∀ (tok : Token),
      (Token.entryLanes t.tokens)[k]? = some (.start tok) →
        ∃ b : UInt8, G.bs[tok.span.start]? = some b ∧
          classOfByte b = some (tokenClass tok))

/-- The clause's first conjunct: the tape is the parser's for this document. -/
theorem WalkAlignQuoted.input {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    (h : WalkAlignQuoted G t) : t.input = ByteString.literal G.bs := h.1

/-- The clause's second conjunct: the entry positions are the lanes' positions. -/
theorem WalkAlignQuoted.ent {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    (h : WalkAlignQuoted G t) :
    G.ent = (Token.entryLanes t.tokens).map EntryLane.pos := h.2.1

/-- The entry count, at the lanes: `WalkGeom.entries` reads `G.nep` lanes, so the
count is the lane list's length. -/
theorem WalkAlignQuoted.nep {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    (h : WalkAlignQuoted G t) : G.nep = (Token.entryLanes t.tokens).length := by
  rw [← WalkAlign.ent_length G, h.ent, List.length_map]

/-- The lane at an entry, and its position: the clause read at one index. -/
theorem WalkAlignQuoted.at {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    (h : WalkAlignQuoted G t) {k : Nat} (hk : k < G.nep) :
    ∃ lane : EntryLane, (Token.entryLanes t.tokens)[k]? = some lane := by
  have hlen : k < (Token.entryLanes t.tokens).length := by
    rw [← h.nep]; exact hk
  exact ⟨_, List.getElem?_eq_getElem hlen⟩

/-- **The entry's position is its lane's.**  `entryPos` reads `G.ent`, and the clause
says that list is the lanes' positions. -/
theorem WalkAlignQuoted.lane_pos {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    (h : WalkAlignQuoted G t) {k : Nat} (lane : EntryLane)
    (hlane : (Token.entryLanes t.tokens)[k]? = some lane) :
    entryPos G k = lane.pos := by
  unfold entryPos
  rw [h.ent, List.getD_eq_getElem?_getD, List.getElem?_map, hlane]
  rfl

/-- The clause's third conjunct, at one index: a start lane's byte announces its
token's class. -/
theorem WalkAlignQuoted.class {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    (h : WalkAlignQuoted G t) {k : Nat} (hk : k < G.nep) {tok : Token}
    (hlane : (Token.entryLanes t.tokens)[k]? = some (.start tok)) :
    ∃ b : UInt8, G.bs[tok.span.start]? = some b ∧
      classOfByte b = some (tokenClass tok) :=
  h.2.2 k hk tok hlane

/-- **The two streams are one where no token is a string.**  With no string token the
lane list is the token starts, so the quote-inclusive staging's entry positions are
`WalkAlign`'s token-start positions.  This is the case in which the two relations say
the same thing, and it is the whole difference between them: a string token's closing
quote is a lane of its own, and no token starts there. -/
theorem Token.entryLanes_stringFree {toks : List Token}
    (h : ∀ tok ∈ toks, ∀ sp : Span, tok ≠ .string sp) :
    (Token.entryLanes toks).map EntryLane.pos =
      toks.map (fun tok => tok.span.start) := by
  induction toks with
  | nil => rw [Token.entryLanes_nil]; rfl
  | cons tok rest ih =>
      have htok : ∀ sp : Span, tok ≠ .string sp := fun sp hs => h tok (by simp) sp hs
      have hrest : ∀ t ∈ rest, ∀ sp : Span, t ≠ .string sp :=
        fun t ht sp hs => h t (by simp [ht]) sp hs
      rw [Token.entryLanes_start htok, List.map_cons, List.map_cons, ih hrest]
      rfl

/-- **The lane after a string's start lane is its closing quote.**  The two lanes are
the arm's two entries: `close = lane k + 1` reads the string's own span. -/
theorem Token.entryLanes_succ_string {toks : List Token} {k : Nat} {sp : Span}
    (h : (Token.entryLanes toks)[k]? = some (.start (.string sp))) :
    (Token.entryLanes toks)[k + 1]? = some (.close (.string sp)) := by
  induction toks generalizing k with
  | nil => rw [Token.entryLanes_nil] at h; simp at h
  | cons tok rest ih =>
      cases tok with
      | string s =>
          rw [Token.entryLanes_string] at h ⊢
          cases k with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq, EntryLane.start.injEq,
                Token.string.injEq] at h
              subst h
              simp
          | succ k =>
              simp only [List.getElem?_cons_succ] at h ⊢
              cases k with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at h
                  cases h
              | succ k =>
                  simp only [List.getElem?_cons_succ] at h ⊢
                  exact ih h
      | punct p s =>
          rw [Token.entryLanes_start (tok := Token.punct p s) (by intro sp hh; cases hh)] at h ⊢
          cases k with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq, EntryLane.start.injEq] at h
              cases h
          | succ k =>
              simp only [List.getElem?_cons_succ] at h ⊢
              exact ih h
      | null s =>
          rw [Token.entryLanes_start (tok := Token.null s) (by intro sp hh; cases hh)] at h ⊢
          cases k with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq, EntryLane.start.injEq] at h
              cases h
          | succ k =>
              simp only [List.getElem?_cons_succ] at h ⊢
              exact ih h
      | bool b s =>
          rw [Token.entryLanes_start (tok := Token.bool b s) (by intro sp hh; cases hh)] at h ⊢
          cases k with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq, EntryLane.start.injEq] at h
              cases h
          | succ k =>
              simp only [List.getElem?_cons_succ] at h ⊢
              exact ih h
      | number s =>
          rw [Token.entryLanes_start (tok := Token.number s) (by intro sp hh; cases hh)] at h ⊢
          cases k with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq, EntryLane.start.injEq] at h
              cases h
          | succ k =>
              simp only [List.getElem?_cons_succ] at h ⊢
              exact ih h

/-- **The string arm's read at the staged stream.**  The next lane is the closing
quote, so the arm's `close = lane k + 1` is `span.stop - 1`, its body opens at
`span.start + 1`, and the extent `close - start - 1` it forms (`%sub260.i`) is the
span's body.  `hquote` is the tape's two-quote span: the closing quote is inside the
token, which is `tape_tokenBytes_string`'s content for a string token. -/
theorem WalkAlignQuoted.stringExtent {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    (h : WalkAlignQuoted G t) {k : Nat} {sp : Span}
    (hquote : sp.start + 2 ≤ sp.stop)
    (hstart : (Token.entryLanes t.tokens)[k]? = some (.start (.string sp))) :
    entryPos G k = sp.start ∧ entryPos G (k + 1) = sp.stop - 1 ∧
      entryPos G (k + 1) - entryPos G k - 1 = sp.stop - sp.start - 2 := by
  have h1 : entryPos G k = sp.start :=
    h.lane_pos (EntryLane.start (.string sp)) hstart
  have hclose := Token.entryLanes_succ_string hstart
  have hlen : (Token.entryLanes t.tokens).length = G.nep := h.nep.symm
  have hk1 : k + 1 < G.nep := by
    have := (List.getElem?_eq_some_iff.mp hclose).1
    omega
  have h2 : entryPos G (k + 1) = sp.stop - 1 :=
    h.lane_pos (EntryLane.close (.string sp)) hclose
  refine ⟨h1, h2, ?_⟩
  rw [h2, h1]
  omega

/-! ### What is still owed: the trace row, and its composition

The row is at the parser's own token indices — which is what the alignment makes
available — and it is the only hypothesis `emittedStream_of_row` consumes beyond
the stream's own read.  `align_not_enough` shows it is not a consequence of the
alignment: the two clauses are independent. -/

/-- **The trace row.**  The walk's emitted records are the parser's
record-carrying tokens' records, in order: the pointwise relation over the token
list with the two separators removed, which is exactly
`stage2Records_iff_forall₂`'s right side. -/
def WalkTraceRow (bs arena : List UInt8) (t : Tape) (rs : List EventRecord) : Prop :=
  List.Forall₂ (TokenRecord bs arena) rs (Token.nonSeparators t.tokens)

/-- **The row gives the encoding.**  With the row and the stream's flattening, the
trace is the relation, the stream is its byte-level form, and the stream's
skeleton reads back as the trace's tags — the three clauses
`stage2Records_at_accept` carries, at the walk's own trace. -/
theorem emittedStream_of_row {bs arena : List UInt8} {t : Tape}
    {rs : List EventRecord} {evs : List UInt8}
    (hrow : WalkTraceRow bs arena t rs)
    (hrecs : evs = (rs.map EventRecord.encodedBytes).flatten) :
    Stage2Records bs arena rs t.tokens ∧
      Stage2EventRel bs arena evs t.tokens ∧
      parseSkeleton evs = rs.map EventRecord.tagVal := by
  have hrel : Stage2Records bs arena rs t.tokens := Stage2Records.of_forall₂ hrow
  refine ⟨hrel, stage2EventRel_of_records hrecs hrel, ?_⟩
  rw [hrecs]
  exact parseSkeleton_trace rs (Stage2Records.tagged hrel)

/-- **The emitted stream at a walk state, from the row.**  The trace's flattening
is what `WalkInv.evBytes` reads at the log's cursor, so with the row those bytes —
the stream the walk has written — are the parser's tokens' encoding: the relation,
the byte-level form and the decoded skeleton.  The alignment is not a hypothesis
here because it is not what proves the row: it is what makes the row *statable* at
the parser's token indices (`WalkAlign.at`/`.class`/`.next`), and the row is the
one thing an arm-level proof still owes. -/
theorem emittedStream_at_walk {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {t : Tape} {arena : List UInt8}
    (hInv : WalkInv G C s) (hrow : WalkTraceRow G.bs arena t C.events) :
    readBytes s.mem (G.ev + G.nev0)
        ((C.events.map EventRecord.encodedBytes).flatten).length =
      some ((C.events.map EventRecord.encodedBytes).flatten) ∧
      Stage2Records G.bs arena C.events t.tokens ∧
      parseSkeleton ((C.events.map EventRecord.encodedBytes).flatten) =
        C.events.map EventRecord.tagVal := by
  have hrel : Stage2Records G.bs arena C.events t.tokens :=
    Stage2Records.of_forall₂ hrow
  exact ⟨hInv.evBytes, hrel,
    parseSkeleton_trace C.events (Stage2Records.tagged hrel)⟩

/-- **The alignment does not give the encoding.**  At the `null` document the
parser's token starts at entry `0` and its class is `n`, so an entry stream of
`[0]` satisfies the alignment; an empty trace at that geometry still satisfies
it, and `Stage2Records` is false of the pair — the emitted stream is not the
token's encoding.  This is the row's independence, and it is why
`emittedStream_of_row` takes the row rather than deriving it. -/
theorem align_not_enough {m0 : Mem} (G : WalkGeom m0) (hent : G.ent = [0])
    (hnep : G.nep = 1) (hbs : G.bs = nullDoc) :
    WalkAlign G ⟨ByteString.literal nullDoc, [.null ⟨0, 4⟩]⟩ ∧
      ¬ Stage2Records nullDoc [] ([] : List EventRecord) [.null ⟨0, 4⟩] := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hbs]
    · rw [hnep]; rfl
    · intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      exact ⟨.null ⟨0, 4⟩, 0x6E, rfl, by rw [entryPos, hent]; rfl,
        by rw [entryPos, hent, hbs]; rfl⟩
    · intro k hk tok b htok hbs'
      have hk0 : k = 0 := by omega
      subst hk0
      have htok1 : tok = .null ⟨0, 4⟩ := by
        have h : (some (.null ⟨0, 4⟩) : Option Token) = some tok := htok
        exact (Option.some.inj h).symm
      have hb1 : b = 0x6E := by
        have h0 : (some 0x6E : Option UInt8) = some b := by
          rw [← hbs']
          rw [entryPos, hent, hbs]
          rfl
        exact (Option.some.inj h0).symm
      subst htok1
      subst hb1
      exact classOfByte_null
    · intro k hk
      omega
  · intro h
    have h' := Stage2Records.forall₂ h
    cases h'

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.TokClass' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.TokClass

/-- info: 'LeanLLVM.Refinement.tokenClass' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.tokenClass

/-- info: 'LeanLLVM.Refinement.classOfByte' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.classOfByte

/-- info: 'LeanLLVM.Refinement.punctByte' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.punctByte

/-- info: 'LeanLLVM.Refinement.punctTag' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.punctTag

/-- info: 'LeanLLVM.Refinement.WalkAlign' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign

/-- info: 'LeanLLVM.Refinement.WalkTraceRow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkTraceRow

/-- info: 'LeanLLVM.Refinement.classOfByte_number' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.classOfByte_number

/-- info: 'LeanLLVM.Refinement.classOfByte_openBracket' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.classOfByte_openBracket

/-- info: 'LeanLLVM.Refinement.classOfByte_closeBracket' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.classOfByte_closeBracket

/-- info: 'LeanLLVM.Refinement.classOfByte_openBrace' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.classOfByte_openBrace

/-- info: 'LeanLLVM.Refinement.classOfByte_closeBrace' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.classOfByte_closeBrace

/-- info: 'LeanLLVM.Refinement.classOfByte_comma' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.classOfByte_comma

/-- info: 'LeanLLVM.Refinement.classOfByte_colon' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.classOfByte_colon

/-- info: 'LeanLLVM.Refinement.classOfByte_null' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.classOfByte_null

/-- info: 'LeanLLVM.Refinement.classOfByte_true' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.classOfByte_true

/-- info: 'LeanLLVM.Refinement.classOfByte_false' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.classOfByte_false

/-- info: 'LeanLLVM.Refinement.classOfByte_string' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.classOfByte_string

/-- info: 'LeanLLVM.Refinement.tokenClass_openBracket' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.tokenClass_openBracket

/-- info: 'LeanLLVM.Refinement.tokenClass_closeBracket' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.tokenClass_closeBracket

/-- info: 'LeanLLVM.Refinement.tokenClass_openBrace' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.tokenClass_openBrace

/-- info: 'LeanLLVM.Refinement.tokenClass_closeBrace' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.tokenClass_closeBrace

/-- info: 'LeanLLVM.Refinement.tokenClass_comma' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.tokenClass_comma

/-- info: 'LeanLLVM.Refinement.tokenClass_colon' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.tokenClass_colon

/-- info: 'LeanLLVM.Refinement.tokenClass_null' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.tokenClass_null

/-- info: 'LeanLLVM.Refinement.tokenClass_true' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.tokenClass_true

/-- info: 'LeanLLVM.Refinement.tokenClass_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.tokenClass_false

/-- info: 'LeanLLVM.Refinement.tokenClass_string' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.tokenClass_string

/-- info: 'LeanLLVM.Refinement.tokenClass_number' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.tokenClass_number

/-- info: 'LeanLLVM.Refinement.WalkAlign.input' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.input

/-- info: 'LeanLLVM.Refinement.WalkAlign.tokens_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.tokens_length

/-- info: 'LeanLLVM.Refinement.WalkAlign.ent_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.ent_length

/-- info: 'LeanLLVM.Refinement.WalkAlign.at' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.at

/-- info: 'LeanLLVM.Refinement.WalkAlign.class' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.class

/-- info: 'LeanLLVM.Refinement.WalkAlign.next' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.next

/-- info: 'LeanLLVM.Refinement.WalkAlign.head' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.head

/-- info: 'LeanLLVM.Refinement.WalkAlign.head_class' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.head_class

/-- info: 'LeanLLVM.Refinement.WalkAlign.head_openBrace' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.head_openBrace

/-- info: 'LeanLLVM.Refinement.WalkAlign.head_closeBrace' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.head_closeBrace

/-- info: 'LeanLLVM.Refinement.WalkAlign.head_openBracket' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.head_openBracket

/-- info: 'LeanLLVM.Refinement.WalkAlign.head_closeBracket' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.head_closeBracket

/-- info: 'LeanLLVM.Refinement.WalkAlign.head_comma' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.head_comma

/-- info: 'LeanLLVM.Refinement.WalkAlign.head_colon' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.head_colon

/-- info: 'LeanLLVM.Refinement.WalkAlign.head_null' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.head_null

/-- info: 'LeanLLVM.Refinement.WalkAlign.head_true' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.head_true

/-- info: 'LeanLLVM.Refinement.WalkAlign.head_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.head_false

/-- info: 'LeanLLVM.Refinement.WalkAlign.head_string' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.head_string

/-- info: 'LeanLLVM.Refinement.WalkAlign.head_number' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlign.head_number

/-- info: 'LeanLLVM.Refinement.WalkInv.doc_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.doc_read

/-- info: 'LeanLLVM.Refinement.WalkInv.entries_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.entries_read

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.align' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.align

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkChain.inv_align' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkChain.inv_align

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkChain.align' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkChain.align

/-- info: 'LeanLLVM.Refinement.checkSpans_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.checkSpans_mem

/-- info: 'LeanLLVM.Refinement.tokenRecord_punct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.tokenRecord_punct

/-- info: 'LeanLLVM.Refinement.emittedStream_of_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.emittedStream_of_row

/-- info: 'LeanLLVM.Refinement.emittedStream_at_walk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.emittedStream_at_walk

/-- info: 'LeanLLVM.Refinement.align_not_enough' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.align_not_enough

/-- info: 'LeanLLVM.Refinement.Token.entryLanes_start' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.Token.entryLanes_start

/-- info: 'LeanLLVM.Refinement.Token.entryLanes_stringFree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.Token.entryLanes_stringFree

/-- info: 'LeanLLVM.Refinement.Token.entryLanes_succ_string' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.Token.entryLanes_succ_string

/-- info: 'LeanLLVM.Refinement.WalkAlignQuoted.nep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlignQuoted.nep

/-- info: 'LeanLLVM.Refinement.WalkAlignQuoted.lane_pos' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlignQuoted.lane_pos

/-- info: 'LeanLLVM.Refinement.WalkAlignQuoted.stringExtent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkAlignQuoted.stringExtent

end LeanLLVM.Refinement
