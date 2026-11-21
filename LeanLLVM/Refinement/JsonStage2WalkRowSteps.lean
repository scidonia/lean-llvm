/-
The trace row's step engine: the prefix correspondence, and the record at the head.

`JsonStage2TraceRow` proves the per-class half of `WalkTraceRow`: a tape's token
facts (`tape_tokenBytes_*`, `tape_bodyCodePoints`) produce `TokenRecord`'s
constructors (`tokenRecord_*_of_tape`), and `walkTraceRow_of_position` assembles
the row from a per-index relation.  What stands between those theorems and the
walk's own trace is where a record sits and when the index moves:

* `WalkTraceRow` is a statement about the *whole* token list with the two
  separators removed, while the walk's carry holds the records emitted so far and
  the index of the entry it is on — so the row is false of every intermediate
  state, and no single arm can produce it;
* an arm appends its record one at a time (`events := C.events ++ [r]`:
  `WalkScope.openC₉`, `WalkLink.if_then328_i`, `WalkLink.outReserveStore`, the
  last-entry tail's `events := C.events ++ [ev]`), and the loop's merge advances
  the index separately, so what a step preserves is a *prefix* correspondence.

This module states that correspondence and proves the step lemmas that preserve
it, so a per-arm proof supplies one record's relation and nothing else:

* `Token.recordTokens` is the record-carrying tokens before an index, and
  `Token.recordTokens_succ_of_separator` / `_of_record` are its two step equations:
  a separator contributes nothing and every other class contributes itself;
* `WalkTracePrefix` is the correspondence at a carry — the trace so far is the
  records of `Token.recordTokens t.tokens C.k` — and `WalkTracePrefix.emit` /
  `WalkTracePrefixEmit.advance` are the append and the index advance, with
  `WalkTracePrefix.emit_advance` the pair as one step for the links that do both;
* `WalkAlign.traceRow_of_prefix` is the composition: at `C.k = G.nep` the prefix
  *is* `WalkTraceRow`, so the whole row follows from per-entry evidence; and
  `nullTraceRow_of_steps` runs the engine at the `null` document's tape, producing
  the row `JsonStage2TraceRow`'s `null_row_of_tape` states directly;
* `WalkTracePrefix.length` is the correspondence's cost — one record per
  record-carrying entry before the index — and `WalkTracePrefix.events_le` reads it
  as `C.events.length ≤ C.k`, which is `WalkInv.events_le_of_tight`'s clause, so
  the correspondence does not fight the invariant the walk already carries;
* `prefix_not_enough` shows the correspondence is independent of the alignment
  (`align_not_enough`'s counterpart one level up): the alignment names the token an
  entry is, it does not name the record an arm appended.

The per-class layer at the loop head is here too, at the token the alignment
names: `headTokenRecord_*` for the four containers and the three literals (the
tape's own facts plus `WalkAlign.head_*`), and `headTokenRecord_number` /
`headTokenRecord_string_plain` / `headTokenRecord_string_arena` with the payload
premise the number and escape arms supply.  `headRow_openBrace` and
`headRow_openBracket` are those arms' rows end to end: the opener's tag select
(`WalkScope.ifEnd24St`) at the byte the head carries is the parser's tag, so the
two opening containers need no record premise at all.

Two layers sit on top of that.  The **step** a revolution makes is `WalkTraceStep`
(the index past exactly one entry and the correspondence regained), produced by the
arms' two forms (`WalkTraceStep.emit`, `WalkTraceStep.separator`) and read as a count
by `gain_of_separator`/`gain_of_record`; `WalkRevolution` is the same step at `WalkInv`
and the loop head, which `containerOpenRevolution_*_step` inhabit for the openers.  The
**induction** is `WalkTraceChain` with `WalkTraceChain.of_steps` — a step at every head
index composes for any number of entries — and `walkTraceRow_of_revolutions` reads it
as the row at `G.nep`.  `row_separatedPayload` is the first document that needs it: the
row of a five-entry document whose two payload revolutions are its only premises
(`row_commaBracket`, `row_colonBrace`).

## What remains

The three residuals `ParserRows` names, at their own vocabulary:

* **the trace row** — the per-entry premise, with the first link family's glue:
  `WalkTracePrefix.of_seed` at the seed, `emit_merge`/`keep_merge` at each arm's
  merge, `row_of_last` at the last entry, and `WalkAlign.traceRow_of_prefix` at the
  exit.  The four containers' and the two separators' carries are read off
  `WalkScope`'s own definitions, and `containerOpenRevolution_*` runs the opener's
  nine links, the merge and the header's pass as one step from the seed — so `[`,
  `{`, `[]` and `{}` have their rows (`row_open*`, `row_openClose*`).  The step those
  rows are instances of is `WalkTraceStep` (its two producers are the arms' own forms,
  and `gain_of_separator`/`gain_of_record` read it as a count), and the induction over
  revolutions for longer documents is here too: `WalkTraceChain` composes the steps,
  `WalkTraceChain.of_steps` is the induction for any number of entries, and
  `walkTraceRow_of_revolutions` is the row at `G.nep` from a step at every head index.
  Its first use at a document is `row_separatedPayload`, the row of a document that
  reaches a separator (`row_commaBracket`, `row_colonBrace`): the arms' net effects at
  each link and the two payload revolutions are its premises, and the containers'
  records, the separator's silence and the last entry's reading are derived there.
  The payload arms' revolutions are here as well: `payloadStep_of_segment` is the step
  at a merge carry whose index and record are the arm's, `payloadStep_number` and
  `payloadStep_string_plain`/`_arena` add the entry's record from the tape, and
  `payloadRevolution_*` carry each arm's `WalkSegment` beside it.  `row_numberDocument`
  (`[1,2]`) instantiates the number revolutions, proving the numerals' decomposition
  from the document's own bytes; `row_stringPlainDocument`/`row_stringArenaDocument`
  (`["ab","cd"]`) are at the staged entry stream instead — `WalkAlignQuoted`'s quote
  lanes — because a string's closing quote is an entry of its own.  They carry the
  entry index and the token count separately (`WalkTracePrefixAt`), take the arm's
  two readings of the stream (`close = lane k + 1`, the extent
  `close - idxprom - 1`) as the record's fields, and step the entry index by two at
  each string.  The plain row derives the raw-body read-back from the document's
  bytes at the token's span; the arena row takes the decoded length and arena base as
  parameters and the arena-slice read-back at the token's span (its literal instance
  proves both from `stringDocumentArena`).  A read-back quantified over every span is
  not a premise that can hold: `bodyCodePoints` returns `some` at spans that are not
  tokens, so the earlier all-spans form was false.  What remains is outside the row: the
  payload arms' `WalkSegment`s (the dispatch layer composes them) and the closers' and
  the separators' walk-level routes (`WalkRevolution` is stated and the openers
  inhabit it);
* **the refusal bit** — `VerdictWord`'s two directions at the run's word.  The
  carry has `refusal` and the boundary has `verdict = 0 ∨ verdict = 1`, so the row
  is the two route families: at `1`, `verdictWord_one_of_valid`'s `ValidDocument`
  witness (the accepting route names the value, the depth and the token count); at
  `0`, `verdictWord_zero_of_noValid`'s absence, i.e. the refusing routes cover
  every document the parser accepts.  Neither is a fact about the list
  correspondence above — both are about the *document*, and the second is the
  converse of the entry stage's completeness;
* **the refusal offset** — each refusing route stores a position
  (`stage2.h:60-61`), and `RefusalOffset bs e` asks it to be the parser's
  `rejectPos`, or `n` where the UTF-8 stage failed.  The routes are produced
  (`JsonStage2WalkDispatchRefusalsOfStaging`'s arms, `JsonStage2WalkFlushPost`'s
  flush word); what is missing is the parser-side statement that its own refusal at
  such a document carries that position.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonStage2TraceRow
import LeanLLVM.Refinement.JsonStage2WalkDispatchOpeners
import LeanLLVM.Refinement.JsonStage2WalkDispatchClosers
import LeanLLVM.Refinement.JsonStage2WalkDispatchAboveZeroDomain

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The record-carrying tokens before an index

`Token.nonSeparators` removes the two separators from a whole token list.  The
walk consumes its entries one at a time, so the list it has records for is a
prefix of that, and the two step equations below are what an entry's class does to
it. -/

/-- **The record-carrying tokens among the first `k`.**  This is the list a
prefix of the trace must be the records of; at `k = tokens.length` it is
`Token.nonSeparators`. -/
def Token.recordTokens (toks : List Token) (k : Nat) : List Token :=
  Token.nonSeparators (toks.take k)

/-- The prefix at no entries is empty. -/
theorem Token.recordTokens_zero (toks : List Token) :
    Token.recordTokens toks 0 = [] := rfl

/-- The prefix at every entry is the whole list, separators removed. -/
theorem Token.recordTokens_full (toks : List Token) :
    Token.recordTokens toks toks.length = Token.nonSeparators toks := by
  unfold Token.recordTokens
  rw [List.take_length]

/-- **The removal never lengthens a list**: a separator is dropped and every other
token is kept. -/
theorem Token.nonSeparators_length_le (l : List Token) :
    (Token.nonSeparators l).length ≤ l.length := by
  induction l with
  | nil => decide
  | cons tok rest ih =>
      cases tok with
      | punct p s =>
          cases p with
          | comma =>
              show (Token.nonSeparators rest).length ≤ rest.length + 1
              omega
          | colon =>
              show (Token.nonSeparators rest).length ≤ rest.length + 1
              omega
          | openBracket =>
              show (Token.nonSeparators rest).length + 1 ≤ rest.length + 1
              omega
          | closeBracket =>
              show (Token.nonSeparators rest).length + 1 ≤ rest.length + 1
              omega
          | openBrace =>
              show (Token.nonSeparators rest).length + 1 ≤ rest.length + 1
              omega
          | closeBrace =>
              show (Token.nonSeparators rest).length + 1 ≤ rest.length + 1
              omega
      | null s =>
          show (Token.nonSeparators rest).length + 1 ≤ rest.length + 1
          omega
      | bool b s =>
          show (Token.nonSeparators rest).length + 1 ≤ rest.length + 1
          omega
      | number s =>
          show (Token.nonSeparators rest).length + 1 ≤ rest.length + 1
          omega
      | string s =>
          show (Token.nonSeparators rest).length + 1 ≤ rest.length + 1
          omega

/-- **The prefix is at most the index**: at most one record per entry consumed. -/
theorem Token.recordTokens_length_le (toks : List Token) (k : Nat) :
    (Token.recordTokens toks k).length ≤ k := by
  unfold Token.recordTokens
  exact le_trans (Token.nonSeparators_length_le _) (List.length_take_le k toks)

/-! ### The separators, and the other classes

`Token.nonSeparators` is written by construction, so a separator at the head
removes itself and any other class keeps its head.  The two facts are the step
equations' content. -/

/-- A token that is neither a comma nor a colon is kept by
`Token.nonSeparators`. -/
theorem Token.nonSeparators_cons_other {tok : Token} {rest : List Token}
    (hc : ∀ s : Span, tok ≠ .punct .comma s)
    (hd : ∀ s : Span, tok ≠ .punct .colon s) :
    Token.nonSeparators (tok :: rest) = tok :: Token.nonSeparators rest := by
  cases tok with
  | punct p s =>
      cases p with
      | comma => exact absurd rfl (hc s)
      | colon => exact absurd rfl (hd s)
      | openBracket => rfl
      | closeBracket => rfl
      | openBrace => rfl
      | closeBrace => rfl
  | null s => rfl
  | bool b s => rfl
  | number s => rfl
  | string s => rfl

/-- **The separators, removed from a concatenation.**  The removal distributes
over an append, which is what turns "the tokens before `k`, then the one at `k`"
into a prefix with one more element. -/
theorem Token.nonSeparators_append (l₁ l₂ : List Token) :
    Token.nonSeparators (l₁ ++ l₂) =
      Token.nonSeparators l₁ ++ Token.nonSeparators l₂ := by
  induction l₁ with
  | nil => rfl
  | cons tok rest ih =>
      cases tok with
      | punct p sp =>
          cases p with
          | comma =>
              show Token.nonSeparators (rest ++ l₂) =
                Token.nonSeparators rest ++ Token.nonSeparators l₂
              exact ih
          | colon =>
              show Token.nonSeparators (rest ++ l₂) =
                Token.nonSeparators rest ++ Token.nonSeparators l₂
              exact ih
          | openBracket =>
              show (.punct .openBracket sp) :: Token.nonSeparators (rest ++ l₂) =
                ((.punct .openBracket sp) :: Token.nonSeparators rest) ++
                  Token.nonSeparators l₂
              rw [List.cons_append, ih]
          | closeBracket =>
              show (.punct .closeBracket sp) :: Token.nonSeparators (rest ++ l₂) =
                ((.punct .closeBracket sp) :: Token.nonSeparators rest) ++
                  Token.nonSeparators l₂
              rw [List.cons_append, ih]
          | openBrace =>
              show (.punct .openBrace sp) :: Token.nonSeparators (rest ++ l₂) =
                ((.punct .openBrace sp) :: Token.nonSeparators rest) ++
                  Token.nonSeparators l₂
              rw [List.cons_append, ih]
          | closeBrace =>
              show (.punct .closeBrace sp) :: Token.nonSeparators (rest ++ l₂) =
                ((.punct .closeBrace sp) :: Token.nonSeparators rest) ++
                  Token.nonSeparators l₂
              rw [List.cons_append, ih]
      | null sp =>
          show (.null sp) :: Token.nonSeparators (rest ++ l₂) =
            ((.null sp) :: Token.nonSeparators rest) ++ Token.nonSeparators l₂
          rw [List.cons_append, ih]
      | bool b sp =>
          show (.bool b sp) :: Token.nonSeparators (rest ++ l₂) =
            ((.bool b sp) :: Token.nonSeparators rest) ++ Token.nonSeparators l₂
          rw [List.cons_append, ih]
      | number sp =>
          show (.number sp) :: Token.nonSeparators (rest ++ l₂) =
            ((.number sp) :: Token.nonSeparators rest) ++ Token.nonSeparators l₂
          rw [List.cons_append, ih]
      | string sp =>
          show (.string sp) :: Token.nonSeparators (rest ++ l₂) =
            ((.string sp) :: Token.nonSeparators rest) ++ Token.nonSeparators l₂
          rw [List.cons_append, ih]

/-- The token at an index, as the prefix's last element: `take (k + 1)` is
`take k` followed by that token. -/
private theorem list_take_succ_of_getElem? {α : Type} :
    ∀ (l : List α) (k : Nat) (a : α), l[k]? = some a →
      l.take (k + 1) = l.take k ++ [a]
  | [], k, a, h => by simp at h
  | b :: l, 0, a, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rfl
  | b :: l, k + 1, a, h => by
      rw [List.getElem?_cons_succ] at h
      show b :: l.take (k + 1) = b :: (l.take k ++ [a])
      rw [list_take_succ_of_getElem? l k a h]

/-- The comma is a separator: on its own it carries no record. -/
theorem Token.nonSeparators_comma (s : Span) :
    Token.nonSeparators [.punct .comma s] = [] := rfl

/-- The colon is a separator: on its own it carries no record. -/
theorem Token.nonSeparators_colon (s : Span) :
    Token.nonSeparators [.punct .colon s] = [] := rfl

/-- **A separator at the index adds nothing to the prefix.** -/
theorem Token.recordTokens_succ_of_separator {toks : List Token} {k : Nat}
    {p : Punct} {s : Span} (h : toks[k]? = some (.punct p s))
    (hp : p = .comma ∨ p = .colon) :
    Token.recordTokens toks (k + 1) = Token.recordTokens toks k := by
  unfold Token.recordTokens
  rw [list_take_succ_of_getElem? toks k _ h, Token.nonSeparators_append]
  rcases hp with rfl | rfl
  · rw [Token.nonSeparators_comma, List.append_nil]
  · rw [Token.nonSeparators_colon, List.append_nil]

/-- **Any other class at the index adds itself to the prefix.** -/
theorem Token.recordTokens_succ_of_record {toks : List Token} {k : Nat} {tok : Token}
    (h : toks[k]? = some tok)
    (hc : ∀ s : Span, tok ≠ .punct .comma s)
    (hd : ∀ s : Span, tok ≠ .punct .colon s) :
    Token.recordTokens toks (k + 1) = Token.recordTokens toks k ++ [tok] := by
  unfold Token.recordTokens
  rw [list_take_succ_of_getElem? toks k tok h, Token.nonSeparators_append,
    Token.nonSeparators_cons_other hc hd]
  rfl

/-- **An append of relations is the relation of the appended lists.** -/
theorem forall₂_append {α β : Type} {R : α → β → Prop} {l₁ : List α}
    {l₂ : List β} {l₁' : List α} {l₂' : List β} (h : List.Forall₂ R l₁ l₂)
    (h' : List.Forall₂ R l₁' l₂') :
    List.Forall₂ R (l₁ ++ l₁') (l₂ ++ l₂') := by
  induction h with
  | nil => exact h'
  | cons hhead _ ih => exact List.Forall₂.cons hhead ih

/-- **A related pair of lists has one length.** -/
theorem forall₂_length {α β : Type} {R : α → β → Prop} {l₁ : List α}
    {l₂ : List β} (h : List.Forall₂ R l₁ l₂) : l₁.length = l₂.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => rw [List.length_cons, List.length_cons, ih]

/-- **A record's token is not a separator.**  `TokenRecord`'s constructors all
name a container, a literal, a number or a string, so the token a record agrees
with is one `Token.nonSeparators` keeps. -/
theorem TokenRecord.not_separator {bs arena : List UInt8} {r : EventRecord} {tok : Token}
    (h : TokenRecord bs arena r tok) :
    (∀ s : Span, tok ≠ .punct .comma s) ∧ (∀ s : Span, tok ≠ .punct .colon s) := by
  cases h with
  | openBrace _ _ => refine ⟨?_, ?_⟩ <;> (intro s h; cases h)
  | closeBrace _ _ => refine ⟨?_, ?_⟩ <;> (intro s h; cases h)
  | openBracket _ _ => refine ⟨?_, ?_⟩ <;> (intro s h; cases h)
  | closeBracket _ _ => refine ⟨?_, ?_⟩ <;> (intro s h; cases h)
  | trueTag _ _ => refine ⟨?_, ?_⟩ <;> (intro s h; cases h)
  | falseTag _ _ => refine ⟨?_, ?_⟩ <;> (intro s h; cases h)
  | nullTag _ _ => refine ⟨?_, ?_⟩ <;> (intro s h; cases h)
  | number _ _ _ => refine ⟨?_, ?_⟩ <;> (intro s h; cases h)
  | strPlain _ _ _ _ => refine ⟨?_, ?_⟩ <;> (intro s h; cases h)
  | strArena _ _ _ _ _ => refine ⟨?_, ?_⟩ <;> (intro s h; cases h)

/-! ### The prefix correspondence

The walk's trace at a carry is the records of the entries it has passed.  Two
states are needed, because the append and the index advance are different links:
`WalkTracePrefix` is "the entries before `k`, recorded", and `WalkTracePrefixEmit`
is the same with the current entry's record already appended and the index not yet
moved.  The emitted form carries the token's class too, so the advance needs no
second reading of it. -/

/-- **The correspondence at a carry.**  The records emitted so far are the records
of the record-carrying tokens before the carried index. -/
def WalkTracePrefix {m0 : Mem} (G : WalkGeom m0) (arena : List UInt8) (t : Tape)
    (C : WalkCarry G) : Prop :=
  List.Forall₂ (TokenRecord G.bs arena) C.events (Token.recordTokens t.tokens C.k)

/-- **The correspondence with the current entry's record appended**: the state
between an arm's append and the merge's index advance.  The token is named beside
the row, and its class with it, because the advance has to know that
`Token.recordTokens` grows by it. -/
def WalkTracePrefixEmit {m0 : Mem} (G : WalkGeom m0) (arena : List UInt8) (t : Tape)
    (C : WalkCarry G) (tok : Token) : Prop :=
  List.Forall₂ (TokenRecord G.bs arena) C.events
      (Token.recordTokens t.tokens C.k ++ [tok]) ∧
    (∀ s : Span, tok ≠ .punct .comma s) ∧
    (∀ s : Span, tok ≠ .punct .colon s)

namespace WalkTracePrefix

/-- The seed is no entries and no records. -/
theorem of_seed {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C : WalkCarry G} (hk : C.k = 0) (hev : C.events = []) :
    WalkTracePrefix G arena t C := by
  unfold WalkTracePrefix
  rw [hk, hev]
  exact List.Forall₂.nil

/-- The correspondence is read at any carry with the same two fields. -/
theorem congr {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C C' : WalkCarry G} (h : WalkTracePrefix G arena t C)
    (hk : C'.k = C.k) (hev : C'.events = C.events) :
    WalkTracePrefix G arena t C' := by
  unfold WalkTracePrefix at *
  rw [hk, hev]
  exact h

/-- **The record count.**  The trace's length is the record-carrying entries before
the index, not merely bounded by it. -/
theorem length {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C : WalkCarry G} (h : WalkTracePrefix G arena t C) :
    C.events.length = (Token.recordTokens t.tokens C.k).length := by
  unfold WalkTracePrefix at h
  exact forall₂_length h

/-- **The correspondence implies the walk's own count bound.**  At most one record
per entry consumed, so `C.events.length ≤ C.k` — `WalkInv.events_le_of_tight`'s
clause before the append, which is why the two invariants do not fight. -/
theorem events_le {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8}
    {t : Tape} {C : WalkCarry G} (h : WalkTracePrefix G arena t C) :
    C.events.length ≤ C.k := by
  rw [length h]
  exact Token.recordTokens_length_le t.tokens C.k

/-- **The append.**  One arm's record, related to the token at the carried index,
extends the correspondence by that token. -/
theorem emit {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C C' : WalkCarry G} {tok : Token} {r : EventRecord}
    (h : WalkTracePrefix G arena t C) (hrec : TokenRecord G.bs arena r tok)
    (hk : C'.k = C.k) (hev : C'.events = C.events ++ [r]) :
    WalkTracePrefixEmit G arena t C' tok := by
  obtain ⟨hc, hd⟩ := hrec.not_separator
  refine ⟨?_, hc, hd⟩
  unfold WalkTracePrefix at h
  rw [hk, hev]
  exact forall₂_append h (List.Forall₂.cons hrec List.Forall₂.nil)

/-- **The index advance**, from the emitted form: the entry's record is the one the
prefix was missing, so moving the index past it restores the correspondence. -/
theorem advance {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C C' : WalkCarry G} {tok : Token}
    (h : WalkTracePrefixEmit G arena t C tok)
    (htok : t.tokens[C.k]? = some tok)
    (hk : C'.k = C.k + 1) (hev : C'.events = C.events) :
    WalkTracePrefix G arena t C' := by
  obtain ⟨hrow, hc, hd⟩ := h
  unfold WalkTracePrefix
  rw [hk, hev, Token.recordTokens_succ_of_record htok hc hd]
  exact hrow

/-- **The append and the advance as one step.**  An arm that appends its record and
whose merge moves the index at the same link needs only this. -/
theorem emit_advance {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C C' : WalkCarry G} {tok : Token} {r : EventRecord}
    (h : WalkTracePrefix G arena t C) (htok : t.tokens[C.k]? = some tok)
    (hrec : TokenRecord G.bs arena r tok)
    (hk : C'.k = C.k + 1) (hev : C'.events = C.events ++ [r]) :
    WalkTracePrefix G arena t C' := by
  obtain ⟨hc, hd⟩ := hrec.not_separator
  unfold WalkTracePrefix at h ⊢
  rw [hk, hev, Token.recordTokens_succ_of_record htok hc hd]
  exact forall₂_append h (List.Forall₂.cons hrec List.Forall₂.nil)

/-- **A separator's advance.**  A comma or a colon carries no record, so the index
moves and the correspondence does not change. -/
theorem advance_separator {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C C' : WalkCarry G} {p : Punct} {s : Span}
    (h : WalkTracePrefix G arena t C)
    (htok : t.tokens[C.k]? = some (.punct p s)) (hp : p = .comma ∨ p = .colon)
    (hk : C'.k = C.k + 1) (hev : C'.events = C.events) :
    WalkTracePrefix G arena t C' := by
  unfold WalkTracePrefix at h ⊢
  rw [hk, hev, Token.recordTokens_succ_of_separator htok hp]
  exact h

/-- **The row, at the end of the index.**  With the index at the whole token list
the prefix *is* `WalkTraceRow`: the separators are gone from both sides and every
record-carrying token has its record. -/
theorem toTraceRow {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C : WalkCarry G} (h : WalkTracePrefix G arena t C) (hk : C.k = t.tokens.length) :
    WalkTraceRow G.bs arena t C.events := by
  unfold WalkTracePrefix at h
  unfold WalkTraceRow
  rw [hk, Token.recordTokens_full] at h
  exact h

end WalkTracePrefix

namespace WalkTracePrefixEmit

/-- The emitted form is read at any carry with the same two fields. -/
theorem congr {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C C' : WalkCarry G} {tok : Token} (h : WalkTracePrefixEmit G arena t C tok)
    (hk : C'.k = C.k) (hev : C'.events = C.events) :
    WalkTracePrefixEmit G arena t C' tok := by
  obtain ⟨hrow, hc, hd⟩ := h
  refine ⟨?_, hc, hd⟩
  rw [hk, hev]
  exact hrow

end WalkTracePrefixEmit

/-- **The row from the prefix, at the walk's own alignment.**  `WalkAlign` says the
entry count is the token count, so the exit state's index is the whole list. -/
theorem WalkAlign.traceRow_of_prefix {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8}
    {t : Tape} {C : WalkCarry G} (hal : WalkAlign G t)
    (h : WalkTracePrefix G arena t C) (hk : C.k = G.nep) :
    WalkTraceRow G.bs arena t C.events :=
  h.toTraceRow (by rw [hk, hal.tokens_length])

/-- **The alignment does not give the correspondence.**  At the `null` document's
tape — the one `align_not_enough` satisfies — a carry at the exit index with no
records violates the prefix correspondence: the entry is a record-carrying token
and no record was appended.  This is why `WalkTracePrefix` is a clause of the arm
layer rather than a consequence of the alignment. -/
theorem prefix_not_enough {m0 : Mem} (G : WalkGeom m0) {C : WalkCarry G}
    (hk : C.k = 1) (hev : C.events = []) :
    ¬ WalkTracePrefix G ([] : List UInt8) ⟨ByteString.literal nullDoc, [.null ⟨0, 4⟩]⟩ C := by
  intro h
  have hlen := forall₂_length h
  rw [hev, hk] at hlen
  exact absurd hlen (by decide)

/-- **A worked instance of the engine.**  At the `null` document's tape, the seed at
index zero with no records and one emitting step at the single entry give
`WalkTraceRow` — the row `JsonStage2TraceRow`'s `null_row_of_tape` states directly.
The step is `WalkTracePrefix.emit_advance`'s, so the composition through the
prefix machinery is exercised at a real tape and not only stated. -/
theorem nullTraceRow_of_steps {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (hbs : G.bs = nullDoc)
    (hdec : decodeTape ⟨ByteString.literal nullDoc, [.null ⟨0, 4⟩]⟩ = some .null) :
    WalkTraceRow G.bs ([] : List UInt8) ⟨ByteString.literal nullDoc, [.null ⟨0, 4⟩]⟩
      ([EventRecord.tag 10] : List EventRecord) := by
  let t : Tape := ⟨ByteString.literal nullDoc, [.null ⟨0, 4⟩]⟩
  let C0 : WalkCarry G := { C with k := 0, events := [] }
  let C1 : WalkCarry G := { C with k := 1, events := [EventRecord.tag 10] }
  have h0 : WalkTracePrefix G ([] : List UInt8) t C0 := WalkTracePrefix.of_seed rfl rfl
  have htok : t.tokens[0]? = some (.null ⟨0, 4⟩) := rfl
  have hmem : Token.null ⟨0, 4⟩ ∈ t.tokens := by
    show Token.null ⟨0, 4⟩ ∈ [Token.null ⟨0, 4⟩]
    exact List.mem_cons_self ..
  have hrec : TokenRecord G.bs ([] : List UInt8) (EventRecord.tag 10) (.null ⟨0, 4⟩) := by
    rw [hbs]
    exact tokenRecord_null_of_tape (t := t) (bs := nullDoc) hdec rfl hmem
  have h1 : WalkTracePrefix G ([] : List UInt8) t C1 :=
    WalkTracePrefix.emit_advance h0 htok hrec rfl rfl
  exact h1.toTraceRow rfl

/-! ### The record at the loop head, by class

`WalkAlign.head_*` names the parser's token at the carried index from the walk's
own byte test; these read the tape's facts at that token.  Each is the record half
of an arm's row: the arm supplies the record it appended, and the parser's side is
closed here.

The container case is `tokenRecord_punct` at the head's byte; the three literals
and the two payload classes read `JsonStage2TraceRow`'s per-class constructors. -/

/-- **The document byte at the entry's position.**  The alignment reads the byte
the walk's `%8` holds at `entryPos`, which is `entryByte` by definition. -/
theorem WalkAlign.bs_getElem {m0 : Mem} {G : WalkGeom m0} {t : Tape} (hal : WalkAlign G t)
    {k : Nat} (hk : k < G.nep) {b : UInt8} (hbyte : entryByte G k = b) :
    G.bs[entryPos G k]? = some b := by
  obtain ⟨tok, b', -, -, hbs⟩ := hal.at hk
  have hb' : b' = entryByte G k := by
    show b' = G.bs.getD (entryPos G k) 0
    rw [List.getD_eq_getElem?_getD, hbs]
    rfl
  rw [← hbyte, ← hb']
  exact hbs

/-- **A container's record at the loop head.**  The token is the one the head's
byte test names (`WalkAlign.head_*`, or the arm's own reading), the span
discipline makes it one byte, and the head's byte is the class's `punctByte`. -/
theorem headTokenRecord_punct {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} (hal : WalkAlign G t)
    (hk : C.k < G.nep) (hspans : spansWellFormed t = true) (arena : List UInt8)
    {p : Punct} {sp : Span}
    (hp : p = .openBrace ∨ p = .closeBrace ∨ p = .openBracket ∨ p = .closeBracket)
    (htok : t.tokens[C.k]? = some (.punct p sp))
    (hbyte : entryByte G C.k = punctByte p) :
    TokenRecord G.bs arena (.tag (punctTag p)) (.punct p sp) := by
  have hbs : G.bs[entryPos G C.k]? = some (punctByte p) :=
    hal.bs_getElem hk hbyte
  exact (tokenRecord_punct hal hspans hk hp htok hbs).2.2

/-- **`null`'s record at the loop head.** -/
theorem headTokenRecord_null {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) {v : JSON.Value} (hdec : decodeTape t = some v)
    (arena : List UInt8) (hbyte : entryByte G C.k = 0x6E) :
    ∃ sp : Span, t.tokens[C.k]? = some (.null sp) ∧
      TokenRecord G.bs arena (.tag 10) (.null sp) := by
  obtain ⟨sp, htok, -⟩ := hal.head_null hInv hk hbyte
  exact ⟨sp, htok, tokenRecord_null_of_tape hdec hal.input (List.mem_of_getElem? htok)⟩

/-- **`true`'s record at the loop head.** -/
theorem headTokenRecord_true {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) {v : JSON.Value} (hdec : decodeTape t = some v)
    (arena : List UInt8) (hbyte : entryByte G C.k = 0x74) :
    ∃ sp : Span, t.tokens[C.k]? = some (.bool true sp) ∧
      TokenRecord G.bs arena (.tag 8) (.bool true sp) := by
  obtain ⟨sp, htok, -⟩ := hal.head_true hInv hk hbyte
  exact ⟨sp, htok, tokenRecord_true_of_tape hdec hal.input (List.mem_of_getElem? htok)⟩

/-- **`false`'s record at the loop head.** -/
theorem headTokenRecord_false {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) {v : JSON.Value} (hdec : decodeTape t = some v)
    (arena : List UInt8) (hbyte : entryByte G C.k = 0x66) :
    ∃ sp : Span, t.tokens[C.k]? = some (.bool false sp) ∧
      TokenRecord G.bs arena (.tag 9) (.bool false sp) := by
  obtain ⟨sp, htok, -⟩ := hal.head_false hInv hk hbyte
  exact ⟨sp, htok, tokenRecord_false_of_tape hdec hal.input (List.mem_of_getElem? htok)⟩

/-- **A number's record at the loop head.**  The parser supplies the span and the
lexeme (`tape_tokenBytes_number` through `tokenRecord_number_of_tape`); the arm
supplies the decomposition whose lexeme is those bytes. -/
theorem headTokenRecord_number {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) {v : JSON.Value} (hdec : decodeTape t = some v)
    (arena : List UInt8) {b0 : UInt8} (hbyte : entryByte G C.k = b0)
    (hb : b0 = 0x2D ∨ IsDigitB b0 = true)
    {d : Decimal} (hwf : d.wellFormed)
    (hlex : ∀ sp : Span, t.tokens[C.k]? = some (.number sp) →
      d.lexeme.data.toList = (G.bs.drop sp.start).take (sp.stop - sp.start)) :
    ∃ sp : Span, t.tokens[C.k]? = some (.number sp) ∧
      TokenRecord G.bs arena (.number (strtodSpec d).toBits) (.number sp) := by
  obtain ⟨sp, htok, -⟩ := hal.head_number hInv hk hbyte hb
  exact ⟨sp, htok,
    tokenRecord_number_of_tape hdec hal.input (List.mem_of_getElem? htok) hwf (hlex sp htok)⟩

/-- **A string's record at the loop head, the body in the document.**  The span's
code points are the parser's (`tape_bodyCodePoints`); the arm supplies that the raw
body it emitted unescaped reads back to them, which is its own choice of form. -/
theorem headTokenRecord_string_plain {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) {v : JSON.Value} (hdec : decodeTape t = some v)
    (arena : List UInt8) (hbyte : entryByte G C.k = 0x22)
    {key : Bool} {len : Nat}
    (hspan : ∀ sp : Span, t.tokens[C.k]? = some (.string sp) →
      sp.stop = sp.start + 2 + len)
    (hbody : ∀ sp : Span, t.tokens[C.k]? = some (.string sp) → ∀ cs : List Nat,
      bodyCodePoints G.bs sp = some cs →
      escapeCodePoints ((G.bs.drop (sp.start + 1)).take len) = some cs) :
    ∃ (sp : Span) (cs : List Nat), t.tokens[C.k]? = some (.string sp) ∧
      bodyCodePoints G.bs sp = some cs ∧
      TokenRecord G.bs arena (.str key len (plainSpan (sp.start + 1))) (.string sp) := by
  obtain ⟨sp, htok, -⟩ := hal.head_string hInv hk hbyte
  obtain ⟨cs, hcode⟩ := tape_bodyCodePoints hdec hal.input (List.mem_of_getElem? htok)
  refine ⟨sp, cs, htok, hcode, ?_⟩
  exact tokenRecord_string_plain_of_tape hdec hal.input (List.mem_of_getElem? htok)
    (hspan sp htok) hcode (hbody sp htok cs hcode)

/-- **A string's record at the loop head, the body in the arena.**  The span's code
points are the parser's; the arm supplies that the arena's slice at its offset reads
back to them, which is what the escape unit's answer means. -/
theorem headTokenRecord_string_arena {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) {v : JSON.Value} (hdec : decodeTape t = some v)
    (arena : List UInt8) (hbyte : entryByte G C.k = 0x22)
    {key : Bool} {len off : Nat}
    (hlen : ∀ sp : Span, t.tokens[C.k]? = some (.string sp) → sp.start + 2 ≤ sp.stop)
    (hoff : off < 2 ^ 63)
    (harena : ∀ sp : Span, t.tokens[C.k]? = some (.string sp) → ∀ cs : List Nat,
      bodyCodePoints G.bs sp = some cs →
      escapeCodePoints ((arena.drop off).take len) = some cs) :
    ∃ (sp : Span) (cs : List Nat), t.tokens[C.k]? = some (.string sp) ∧
      bodyCodePoints G.bs sp = some cs ∧
      TokenRecord G.bs arena (.str key len off) (.string sp) := by
  obtain ⟨sp, htok, -⟩ := hal.head_string hInv hk hbyte
  obtain ⟨cs, hcode⟩ := tape_bodyCodePoints hdec hal.input (List.mem_of_getElem? htok)
  refine ⟨sp, cs, htok, hcode, ?_⟩
  exact tokenRecord_string_arena_of_tape hdec hal.input (List.mem_of_getElem? htok)
    (hlen sp htok) hoff hcode (harena sp htok cs hcode)

/-! ### The openers' rows, end to end

The opener's record is `EventRecord.tag (ifEnd24St b)`: the block's own select on
the byte it dispatched.  At the two opening bytes that select is the parser's tag,
so the arm's record needs no premise about its contents — the alignment's byte and
`tokenRecord_punct` close it. -/

/-- The opener's tag select at `{`: the parser's `T_OBJ`. -/
theorem ifEnd24St_openBrace : (WalkScope.ifEnd24St 0x7B).toNat = 1 := by decide

/-- The opener's tag select at `[`: the parser's `T_ARR`. -/
theorem ifEnd24St_openBracket : (WalkScope.ifEnd24St 0x5B).toNat = 3 := by decide

/-- **The brace opener's row.**  The record `WalkScope.openC₉` appends at this
head, related to the parser's token there. -/
theorem headRow_openBrace {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hspans : spansWellFormed t = true) (arena : List UInt8)
    (hbyte : entryByte G C.k = 0x7B) :
    ∃ sp : Span, t.tokens[C.k]? = some (.punct .openBrace sp) ∧
      TokenRecord G.bs arena (.tag (WalkScope.ifEnd24St 0x7B).toNat) (.punct .openBrace sp) := by
  obtain ⟨sp, htok, -⟩ := hal.head_openBrace hInv hk hbyte
  refine ⟨sp, htok, ?_⟩
  rw [ifEnd24St_openBrace]
  exact headTokenRecord_punct hal hk hspans arena (Or.inl rfl) htok (by rw [hbyte]; rfl)

/-- **The bracket opener's row.** -/
theorem headRow_openBracket {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hspans : spansWellFormed t = true) (arena : List UInt8)
    (hbyte : entryByte G C.k = 0x5B) :
    ∃ sp : Span, t.tokens[C.k]? = some (.punct .openBracket sp) ∧
      TokenRecord G.bs arena (.tag (WalkScope.ifEnd24St 0x5B).toNat) (.punct .openBracket sp) := by
  obtain ⟨sp, htok, -⟩ := hal.head_openBracket hInv hk hbyte
  refine ⟨sp, htok, ?_⟩
  rw [ifEnd24St_openBracket]
  exact headTokenRecord_punct hal hk hspans arena (Or.inr (Or.inr (Or.inl rfl))) htok
    (by rw [hbyte]; rfl)

/-! ### The merge's carry, and the trace across it

An arm's route ends at `cleanup478.i` with its record already appended — the opener's
`WalkScope.openC₉` and the closer's `WalkScope.closeCEnd` — and the back edge at
`while.body.i` then moves the index past the entry.  The append and the advance are
different links, so a step's correspondence is the pair: the append read at the merge
carry, the advance read at the head.  `emit_merge` and `keep_merge` are that pair; the
four containers and the two separators then supply the carries' own equations from
`WalkScope`'s definitions and the record from the parser's side
(`headRow_openBrace`/`headRow_openBracket`, `headTokenRecord_punct` at the closing
byte).

The last entry is the arm with no head after it: its merge carry's index moves to the
stream's end and the loop leaves, so `row_of_last` reads the emitted form as the whole
row.  The four `*LastRow` theorems are that reading at each container's byte, and the
opener's revolution ties them to the walk's own links so a `[]` or a `{}` reaches its
closer's row from the seed. -/

open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR
open WalkScope

/-- The opener's merge carry keeps the index. -/
theorem WalkScope.openC₉_k {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (b : BitVec 8) :
    (WalkScope.openC₉ C b).k = C.k := rfl

/-- The opener's merge carry appends the tag its byte selects. -/
theorem WalkScope.openC₉_events {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (b : BitVec 8) :
    (WalkScope.openC₉ C b).events =
      C.events ++ [EventRecord.tag (WalkScope.ifEnd24St b).toNat] := rfl

/-- The closer's merge carry keeps the index. -/
theorem WalkScope.closeCEnd_k {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (spz : BitVec 32) (c8 : BitVec 8) : (WalkScope.closeCEnd C spz c8).k = C.k := rfl

/-- The closer's merge carry appends its tag byte. -/
theorem WalkScope.closeCEnd_events {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (spz : BitVec 32) (c8 : BitVec 8) :
    (WalkScope.closeCEnd C spz c8).events = C.events ++ [EventRecord.tag c8.toNat] := rfl

namespace WalkTracePrefix

/-- **One record across the merge, and the index beside it.**  A route whose merge
carry appends the entry's record at the entry's own index, and whose back edge then
moves the index past that entry, preserves the correspondence in one step. -/
theorem emit_merge {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C Cd C' : WalkCarry G} {tok : Token} {r : EventRecord}
    (h : WalkTracePrefix G arena t C) (htok : t.tokens[C.k]? = some tok)
    (hrec : TokenRecord G.bs arena r tok)
    (hkC : Cd.k = C.k) (hevC : Cd.events = C.events ++ [r])
    (hk' : C'.k = Cd.k + 1) (hev' : C'.events = Cd.events) :
    WalkTracePrefix G arena t C' := by
  have htok' : t.tokens[Cd.k]? = some tok := by rw [hkC]; exact htok
  exact advance (h.emit hrec hkC hevC) htok' hk' hev'

/-- **A separator across the merge.**  The merge carry adds no record, so the
correspondence is read at it unchanged, and the back edge's advance is
`advance_separator`'s. -/
theorem keep_merge {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C Cd C' : WalkCarry G} {p : Punct} {s : Span}
    (h : WalkTracePrefix G arena t C)
    (htok : t.tokens[C.k]? = some (.punct p s)) (hp : p = .comma ∨ p = .colon)
    (hkC : Cd.k = C.k) (hevC : Cd.events = C.events)
    (hk' : C'.k = Cd.k + 1) (hev' : C'.events = Cd.events) :
    WalkTracePrefix G arena t C' := by
  have htok' : t.tokens[Cd.k]? = some (.punct p s) := by rw [hkC]; exact htok
  exact (h.congr hkC hevC).advance_separator htok' hp hk' hev'

/-- **The row at the last entry.**  An arm that reaches the merge at the entry before
the stream's end leaves the record trace complete once its index moves past that
entry: the emitted form's row is already the whole `WalkTraceRow`. -/
theorem row_of_last {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C : WalkCarry G} {tok : Token} (h : WalkTracePrefixEmit G arena t C tok)
    (htok : t.tokens[C.k]? = some tok) (hk : C.k + 1 = t.tokens.length) :
    WalkTraceRow G.bs arena t C.events := by
  obtain ⟨hrow, hc, hd⟩ := h
  unfold WalkTraceRow
  rw [← Token.recordTokens_full t.tokens, ← hk,
    Token.recordTokens_succ_of_record htok hc hd]
  exact hrow

end WalkTracePrefix

/-! ### The four containers, at their own carries

The opener's record is `WalkScope.ifEnd24St b` — the tag the push's select writes —
and the closer's is the tag byte its `phi` holds.  At the document's bytes those are
the parser's tags (`3`/`1` for `[`/`{`, `4`/`2` for `]`/`}`), so the arms' records are
`TokenRecord`'s container constructor at the parser's token. -/

/-- The bracket opener's byte, as the header's select reads it: the register holds
`BitVec.ofNat 8 (entryByte G C.k).toNat`, and at the document's byte that is the
literal the select's arms test. -/
theorem bitVec_ofNat_entryByte_5B : BitVec.ofNat 8 ((0x5B : UInt8)).toNat = (0x5B : BitVec 8) :=
  by decide

/-- The brace opener's byte, at the header's select. -/
theorem bitVec_ofNat_entryByte_7B : BitVec.ofNat 8 ((0x7B : UInt8)).toNat = (0x7B : BitVec 8) :=
  by decide

/-- The entry's byte read as the header's select does, from the document's byte. -/
theorem bitVec_ofNat_entryByte {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) {u : UInt8}
    (h : entryByte G C.k = u) :
    BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 u.toNat := by rw [h]

/-- **The bracket opener's tag at the document's byte**: the header's select on `[`
is the parser's `T_ARR`. -/
theorem ifEnd24St_entryByte_5B {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (h : entryByte G C.k = 0x5B) :
    (WalkScope.ifEnd24St (BitVec.ofNat 8 (entryByte G C.k).toNat)).toNat = 3 := by
  rw [bitVec_ofNat_entryByte C h, bitVec_ofNat_entryByte_5B, ifEnd24St_openBracket]

/-- **The brace opener's tag at the document's byte**: the header's select on `{`
is the parser's `T_OBJ`. -/
theorem ifEnd24St_entryByte_7B {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (h : entryByte G C.k = 0x7B) :
    (WalkScope.ifEnd24St (BitVec.ofNat 8 (entryByte G C.k).toNat)).toNat = 1 := by
  rw [bitVec_ofNat_entryByte C h, bitVec_ofNat_entryByte_7B, ifEnd24St_openBrace]

/-- **The bracket opener's record across its merge.** -/
theorem containerOpenEmit_bracket {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} {arena : List UInt8}
    (h : WalkTracePrefix G arena t C) (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hspans : spansWellFormed t = true)
    (hbyte : entryByte G C.k = 0x5B) :
    ∃ tok : Token, t.tokens[C.k]? = some tok ∧
      WalkTracePrefixEmit G arena t
        (WalkScope.openC₉ C (BitVec.ofNat 8 (entryByte G C.k).toNat)) tok := by
  obtain ⟨sp, htok, hrec⟩ := headRow_openBracket hal hInv hk hspans arena hbyte
  refine ⟨.punct .openBracket sp, htok, ?_⟩
  have hb : BitVec.ofNat 8 (entryByte G C.k).toNat = (0x5B : BitVec 8) := by
    rw [bitVec_ofNat_entryByte C hbyte]
    exact bitVec_ofNat_entryByte_5B
  rw [hb]
  exact WalkTracePrefix.emit h hrec rfl rfl

/-- **The brace opener's record across its merge.** -/
theorem containerOpenEmit_brace {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} {arena : List UInt8}
    (h : WalkTracePrefix G arena t C) (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hspans : spansWellFormed t = true)
    (hbyte : entryByte G C.k = 0x7B) :
    ∃ tok : Token, t.tokens[C.k]? = some tok ∧
      WalkTracePrefixEmit G arena t
        (WalkScope.openC₉ C (BitVec.ofNat 8 (entryByte G C.k).toNat)) tok := by
  obtain ⟨sp, htok, hrec⟩ := headRow_openBrace hal hInv hk hspans arena hbyte
  refine ⟨.punct .openBrace sp, htok, ?_⟩
  have hb : BitVec.ofNat 8 (entryByte G C.k).toNat = (0x7B : BitVec 8) := by
    rw [bitVec_ofNat_entryByte C hbyte]
    exact bitVec_ofNat_entryByte_7B
  rw [hb]
  exact WalkTracePrefix.emit h hrec rfl rfl

/-- The next head's carry, from the opener's merge.  The two field equations are the
merge and the back edge's, which `WalkScope.containerOpenSeg`'s endpoint and
`WalkLink.whileBody` supply. -/
theorem containerOpenHead_bracket {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C C' : WalkCarry G} {s : State} {arena : List UInt8}
    (h : WalkTracePrefix G arena t C) (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hspans : spansWellFormed t = true)
    (hbyte : entryByte G C.k = 0x5B)
    (hk' : C'.k = C.k + 1)
    (hev' : C'.events =
      (WalkScope.openC₉ C (BitVec.ofNat 8 (entryByte G C.k).toNat)).events) :
    WalkTracePrefix G arena t C' := by
  obtain ⟨tok, htok, hem⟩ := containerOpenEmit_bracket h hal hInv hk hspans hbyte
  refine WalkTracePrefix.advance hem htok ?_ hev'
  show C'.k = C.k + 1
  exact hk'

/-- **The brace opener's revolution, on the trace.** -/
theorem containerOpenHead_brace {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C C' : WalkCarry G} {s : State} {arena : List UInt8}
    (h : WalkTracePrefix G arena t C) (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hspans : spansWellFormed t = true)
    (hbyte : entryByte G C.k = 0x7B)
    (hk' : C'.k = C.k + 1)
    (hev' : C'.events =
      (WalkScope.openC₉ C (BitVec.ofNat 8 (entryByte G C.k).toNat)).events) :
    WalkTracePrefix G arena t C' := by
  obtain ⟨tok, htok, hem⟩ := containerOpenEmit_brace h hal hInv hk hspans hbyte
  refine WalkTracePrefix.advance hem htok ?_ hev'
  show C'.k = C.k + 1
  exact hk'

/-- **The closing bracket's record across its merge.**  The route's tag byte is the
`phi`'s `4`, the parser's `T_ARR_END`, so the merge's record is the row's. -/
theorem containerCloseEmit_bracket {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} {arena : List UInt8} {spz : BitVec 32} {c8 : BitVec 8}
    (h : WalkTracePrefix G arena t C) (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hspans : spansWellFormed t = true)
    (hbyte : entryByte G C.k = 0x5D) (hc8 : c8 = BitVec.ofNat 8 4) :
    ∃ tok : Token, t.tokens[C.k]? = some tok ∧
      WalkTracePrefixEmit G arena t (WalkScope.closeCEnd C spz c8) tok := by
  obtain ⟨sp, htok, -⟩ := hal.head_closeBracket hInv hk hbyte
  have hrec : TokenRecord G.bs arena (.tag (punctTag .closeBracket))
      (.punct .closeBracket sp) :=
    headTokenRecord_punct hal hk hspans arena (Or.inr (Or.inr (Or.inr rfl))) htok
      (by rw [hbyte]; rfl)
  refine ⟨.punct .closeBracket sp, htok, ?_⟩
  have hev : (WalkScope.closeCEnd C spz c8).events =
      C.events ++ [EventRecord.tag (punctTag .closeBracket)] := by
    rw [WalkScope.closeCEnd_events, hc8]
    rfl
  exact WalkTracePrefix.emit h hrec rfl hev

/-- **The closing brace's record across its merge.**  The route's tag byte is `2`,
the parser's `T_OBJ_END`. -/
theorem containerCloseEmit_brace {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} {arena : List UInt8} {spz : BitVec 32} {c8 : BitVec 8}
    (h : WalkTracePrefix G arena t C) (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hspans : spansWellFormed t = true)
    (hbyte : entryByte G C.k = 0x7D) (hc8 : c8 = BitVec.ofNat 8 2) :
    ∃ tok : Token, t.tokens[C.k]? = some tok ∧
      WalkTracePrefixEmit G arena t (WalkScope.closeCEnd C spz c8) tok := by
  obtain ⟨sp, htok, -⟩ := hal.head_closeBrace hInv hk hbyte
  have hrec : TokenRecord G.bs arena (.tag (punctTag .closeBrace))
      (.punct .closeBrace sp) :=
    headTokenRecord_punct hal hk hspans arena (Or.inr (Or.inl rfl)) htok
      (by rw [hbyte]; rfl)
  refine ⟨.punct .closeBrace sp, htok, ?_⟩
  have hev : (WalkScope.closeCEnd C spz c8).events =
      C.events ++ [EventRecord.tag (punctTag .closeBrace)] := by
    rw [WalkScope.closeCEnd_events, hc8]
    rfl
  exact WalkTracePrefix.emit h hrec rfl hev

/-- **The separators' merge keeps the correspondence.**  A comma or a colon carries
no record, so the merge carry's trace is the entry's predecessor's and the back
edge's advance is the empty one. -/
theorem separatorHead {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C Cd C' : WalkCarry G} {s : State} {arena : List UInt8}
    (h : WalkTracePrefix G arena t C) (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep)
    (hbyte : entryByte G C.k = 0x2C ∨ entryByte G C.k = 0x3A)
    (hkC : Cd.k = C.k) (hevC : Cd.events = C.events)
    (hk' : C'.k = Cd.k + 1) (hev' : C'.events = Cd.events) :
    WalkTracePrefix G arena t C' := by
  rcases hbyte with hb | hb
  · obtain ⟨sp, htok, -⟩ := hal.head_comma hInv hk hb
    exact WalkTracePrefix.keep_merge h htok (Or.inl rfl) hkC hevC hk' hev'
  · obtain ⟨sp, htok, -⟩ := hal.head_colon hInv hk hb
    exact WalkTracePrefix.keep_merge h htok (Or.inr rfl) hkC hevC hk' hev'

/-! ### The container-only rows

Each is the arm at the last entry: the record the merge appended and the entries
before it.  `[` and `{` are one-entry documents and reach these from the seed
directly; a `[]` or `{}` reaches the closer's row from the head the opener's
revolution leaves, which is `containerOpenHead_*`'s. -/

/-- **The row at a bracket opener's last entry.** -/
theorem containerOpenLastRow_bracket {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} {arena : List UInt8}
    (h : WalkTracePrefix G arena t C) (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hspans : spansWellFormed t = true)
    (hbyte : entryByte G C.k = 0x5B) (hlast : C.k + 1 = t.tokens.length) :
    WalkTraceRow G.bs arena t (C.events ++ [EventRecord.tag 3]) := by
  obtain ⟨tok, htok, hem⟩ := containerOpenEmit_bracket h hal hInv hk hspans hbyte
  have hrow := WalkTracePrefix.row_of_last hem htok (by
    show (WalkScope.openC₉ C (BitVec.ofNat 8 (entryByte G C.k).toNat)).k + 1 =
      t.tokens.length
    rw [WalkScope.openC₉_k]
    exact hlast)
  rw [WalkScope.openC₉_events, ifEnd24St_entryByte_5B C hbyte] at hrow
  exact hrow

/-- **The row at a brace opener's last entry.** -/
theorem containerOpenLastRow_brace {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} {arena : List UInt8}
    (h : WalkTracePrefix G arena t C) (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hspans : spansWellFormed t = true)
    (hbyte : entryByte G C.k = 0x7B) (hlast : C.k + 1 = t.tokens.length) :
    WalkTraceRow G.bs arena t (C.events ++ [EventRecord.tag 1]) := by
  obtain ⟨tok, htok, hem⟩ := containerOpenEmit_brace h hal hInv hk hspans hbyte
  have hrow := WalkTracePrefix.row_of_last hem htok (by
    show (WalkScope.openC₉ C (BitVec.ofNat 8 (entryByte G C.k).toNat)).k + 1 =
      t.tokens.length
    rw [WalkScope.openC₉_k]
    exact hlast)
  rw [WalkScope.openC₉_events, ifEnd24St_entryByte_7B C hbyte] at hrow
  exact hrow

/-- **The row at a closing bracket's last entry.** -/
theorem containerCloseLastRow_bracket {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} {arena : List UInt8} {spz : BitVec 32} {c8 : BitVec 8}
    (h : WalkTracePrefix G arena t C) (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hspans : spansWellFormed t = true)
    (hbyte : entryByte G C.k = 0x5D) (hc8 : c8 = BitVec.ofNat 8 4)
    (hlast : C.k + 1 = t.tokens.length) :
    WalkTraceRow G.bs arena t (C.events ++ [EventRecord.tag 4]) := by
  obtain ⟨tok, htok, hem⟩ := containerCloseEmit_bracket h hal hInv hk hspans hbyte hc8
  have hrow := WalkTracePrefix.row_of_last hem htok (by
    show (WalkScope.closeCEnd C spz c8).k + 1 = t.tokens.length
    rw [WalkScope.closeCEnd_k]
    exact hlast)
  rw [WalkScope.closeCEnd_events, hc8] at hrow
  simpa using hrow

/-- **The row at a closing brace's last entry.** -/
theorem containerCloseLastRow_brace {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} {arena : List UInt8} {spz : BitVec 32} {c8 : BitVec 8}
    (h : WalkTracePrefix G arena t C) (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hk : C.k < G.nep) (hspans : spansWellFormed t = true)
    (hbyte : entryByte G C.k = 0x7D) (hc8 : c8 = BitVec.ofNat 8 2)
    (hlast : C.k + 1 = t.tokens.length) :
    WalkTraceRow G.bs arena t (C.events ++ [EventRecord.tag 2]) := by
  obtain ⟨tok, htok, hem⟩ := containerCloseEmit_brace h hal hInv hk hspans hbyte hc8
  have hrow := WalkTracePrefix.row_of_last hem htok (by
    show (WalkScope.closeCEnd C spz c8).k + 1 = t.tokens.length
    rw [WalkScope.closeCEnd_k]
    exact hlast)
  rw [WalkScope.closeCEnd_events, hc8] at hrow
  simpa using hrow

/-- **At no entries the trace is empty.**  At `k = 0` the correspondence relates the
carry's records to the empty list, and only the empty list stands in that relation —
so the seed's emptiness is read off the correspondence rather than assumed beside it. -/
theorem WalkTracePrefix.events_eq_nil {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8}
    {t : Tape} {C : WalkCarry G} (h : WalkTracePrefix G arena t C) (hk : C.k = 0) :
    C.events = [] := by
  have hlen := forall₂_length h
  rw [hk, Token.recordTokens_zero, List.length_nil] at hlen
  exact List.eq_nil_of_length_eq_zero hlen

/-- **The one-entry bracket document's row.**  The document's only token is the open
bracket, the header's select on its byte is the parser's `T_ARR`, and the merge's
index reaches the stream's end: the trace is the one record. -/
theorem row_openBracketOnly {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} {arena : List UInt8}
    (h : WalkTracePrefix G arena t C) (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hspans : spansWellFormed t = true) (hk0 : C.k = 0)
    (hbyte : entryByte G 0 = 0x5B) (hnep : G.nep = 1)
    (htokens : t.tokens = [.punct .openBracket ⟨0, 1⟩]) :
    WalkTraceRow G.bs arena t ([EventRecord.tag 3] : List EventRecord) := by
  have hk : C.k < G.nep := by rw [hk0, hnep]; decide
  have hbyte' : entryByte G C.k = 0x5B := by rw [hk0]; exact hbyte
  have hlast : C.k + 1 = t.tokens.length := by rw [hk0, htokens]; rfl
  have hrow := containerOpenLastRow_bracket h hal hInv hk hspans hbyte' hlast
  rw [WalkTracePrefix.events_eq_nil h hk0, List.nil_append] at hrow
  exact hrow

/-- **The one-entry brace document's row.**  The same at `{`, whose select is the
parser's `T_OBJ`. -/
theorem row_openBraceOnly {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} {arena : List UInt8}
    (h : WalkTracePrefix G arena t C) (hal : WalkAlign G t) (hInv : WalkInv G C s)
    (hspans : spansWellFormed t = true) (hk0 : C.k = 0)
    (hbyte : entryByte G 0 = 0x7B) (hnep : G.nep = 1)
    (htokens : t.tokens = [.punct .openBrace ⟨0, 1⟩]) :
    WalkTraceRow G.bs arena t ([EventRecord.tag 1] : List EventRecord) := by
  have hk : C.k < G.nep := by rw [hk0, hnep]; decide
  have hbyte' : entryByte G C.k = 0x7B := by rw [hk0]; exact hbyte
  have hlast : C.k + 1 = t.tokens.length := by rw [hk0, htokens]; rfl
  have hrow := containerOpenLastRow_brace h hal hInv hk hspans hbyte' hlast
  rw [WalkTracePrefix.events_eq_nil h hk0, List.nil_append] at hrow
  exact hrow

/-! ### The opener's revolution, end to end

The head's four links and the tail's five reach the merge carry `WalkScope.openC₉`,
whose record is the parser's at the entry; the merge's step and the header's pass then
move the index and the depth.  The two carries are the route's own, so the step is the
walk's and not a carry chosen for the trace — which is what a `[]` or a `{}` needs to
reach its closer's row from the seed. -/

/-- **The bracket opener's revolution, with its record.** -/
theorem containerOpenRevolution_bracket {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {arena : List UInt8} {t : Tape} (h : WalkTracePrefix G arena t C)
    (hal : WalkAlign G t) (hspans : spansWellFormed t = true)
    (hbyte : entryByte G C.k = 0x5B) (hsp519 : C.sp ≤ 519)
    {rd : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) (hcont : C.k + 1 < G.nep) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = C.sp + 1 ∧
      C'.k = C.k + 1 ∧ C'.events = C.events ++ [EventRecord.tag 3] ∧
      WalkTracePrefix G arena t C' := by
  have hklt : C.k < G.nep :=
    WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)
  have hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 91 := by
    rw [hbyte]; decide
  have h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 91)) := by
    rw [LeanLLVM.evalOperand_reg_of hInv.iter.reg8, hbe]
  -- the head's four links, then the tail's five, to the merge carry
  have hh := openBracketHead G C s hInv hblock h8 hbe
  have hread' : readBytes (openBrS₄ s).mem (G.next0 + 8) 4 =
      some (natToBytes rd.toNat 4) := by
    rw [openBrS₄_mem]; exact hread
  have hpreV' : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (openHeadC C).sp), .int 32 rd,
       .ptr (openHeadC C).stage.ctype, .ptr (openHeadC C).stage.cst]
      (openBrS₄ s).mem (openBrS₄ s).next := by
    rw [openBrS₄_mem, openBrS₄_next]; exact hpreV
  have ht := openTailSeg G (openHeadC C) (openBrS₄ s) hh.inv' rfl
    (b := BitVec.ofNat 8 (entryByte G C.k).toNat) rfl hsp519 hread' hpreV' r hcall hret
    hklt
  have hseg := hh.trans ht
  -- the merge's closing step, at its own two phis
  have hguard : C.k + 1 < (BitVec.ofNat 64 G.nep).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (openNep_lt G)]
    exact hcont
  have hpre₉ : (openS₉ (openHeadC C) (openBrS₄ s) r rd
      (BitVec.ofNat 8 (entryByte G C.k).toNat)).pre = some "out_reserve.exit.i.i" := rfl
  obtain ⟨-, hinvB, -⟩ :=
    walkBack_step_at (calls := stage2Calls stage2SubCalls) (G := G)
      (C := openC₉ (openHeadC C) (BitVec.ofNat 8 (entryByte G C.k).toNat))
      (s := openS₉ (openHeadC C) (openBrS₄ s) r rd
        (BitVec.ofNat 8 (entryByte G C.k).toNat))
      (spv := C.sp + 1) (k2 := C.k + 1)
      hseg.inv' rfl hpre₉
      (by show phiIncoming "out_reserve.exit.i.i" cleanupSpIncoming =
          some (.reg "%inc33.i"); decide)
      (by simp only [evalOperand]
          exact openS₉_inc33 (openHeadC C) (openBrS₄ s) r rd
            (BitVec.ofNat 8 (entryByte G C.k).toNat))
      (by show phiIncoming "out_reserve.exit.i.i" cleanupKIncoming =
          some (.reg "%inc.i"); decide)
      (by simp only [evalOperand]
          rw [openS₉_inc (openHeadC C) (openBrS₄ s) r rd
            (BitVec.ofNat 8 (entryByte G C.k).toNat)]
          exact LeanLLVM.evalOperand_reg_of hh.inv'.inc_reg)
      (by
        rw [openS₉_nep (openHeadC C) (openBrS₄ s) r rd
          (BitVec.ofNat 8 (entryByte G C.k).toNat)]
        exact hh.inv'.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep))
          (by simp [walkStaticRegs]))
      hguard
  -- the header's pass, at the two phi values
  obtain ⟨s'', hl''⟩ :=
    WalkLink.whileBody (calls := stage2Calls stage2SubCalls) G
      { openC₉ (openHeadC C) (BitVec.ofNat 8 (entryByte G C.k).toNat) with
        block := "while.body.i", inner := walkInnerCap G }
      (cleanup478Out (openS₉ (openHeadC C) (openBrS₄ s) r rd
        (BitVec.ofNat 8 (entryByte G C.k).toNat)) (C.sp + 1) (C.k + 1)) hinvB rfl rfl
      (cleanup478Out_k (s := openS₉ (openHeadC C) (openBrS₄ s) r rd
        (BitVec.ofNat 8 (entryByte G C.k).toNat)) (spv := C.sp + 1) (k2 := C.k + 1))
      (cleanup478Out_sp (s := openS₉ (openHeadC C) (openBrS₄ s) r rd
        (BitVec.ofNat 8 (entryByte G C.k).toNat)) (spv := C.sp + 1) (k2 := C.k + 1))
      (by show C.k < C.k + 1; omega)
      (by show C.k + 1 < G.nep; exact hcont)
      (by
        show C.sp + 1 ≤ stage2StackExtent
        have h520 : stage2StackExtent = 520 := rfl
        omega)
      (by
        show C.sp + 1 ≤ (openC₉ (openHeadC C) (BitVec.ofNat 8 (entryByte G C.k).toNat)).wlen
        show C.sp + 1 ≤ max C.wlen (C.sp + 1)
        exact le_max_right _ _)
  refine ⟨_, s'', hl''.inv', rfl, rfl, rfl, ?_, ?_⟩
  · show (openC₉ (openHeadC C) (BitVec.ofNat 8 (entryByte G C.k).toNat)).events
      = C.events ++ [EventRecord.tag 3]
    rw [WalkScope.openC₉_events, ifEnd24St_entryByte_5B C hbyte]
  · show WalkTracePrefix G arena t
      { openC₉ (openHeadC C) (BitVec.ofNat 8 (entryByte G C.k).toNat) with
        block := walkLoopHead, inner := walkInnerCap G, k := C.k + 1, sp := C.sp + 1 }
    exact containerOpenHead_bracket h hal hInv hklt hspans hbyte rfl rfl

/-- **The brace opener's revolution, with its record.** -/
theorem containerOpenRevolution_brace {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {arena : List UInt8} {t : Tape} (h : WalkTracePrefix G arena t C)
    (hal : WalkAlign G t) (hspans : spansWellFormed t = true)
    (hbyte : entryByte G C.k = 0x7B) (hsp519 : C.sp ≤ 519)
    {rd : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) (hcont : C.k + 1 < G.nep) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkInv G C' s' ∧ C'.block = walkLoopHead ∧ C'.sp = C.sp + 1 ∧
      C'.k = C.k + 1 ∧ C'.events = C.events ++ [EventRecord.tag 1] ∧
      WalkTracePrefix G arena t C' := by
  have hklt : C.k < G.nep :=
    WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)
  have hbe : BitVec.ofNat 8 (entryByte G C.k).toNat = BitVec.ofNat 8 123 := by
    rw [hbyte]; decide
  have h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 123)) := by
    rw [LeanLLVM.evalOperand_reg_of hInv.iter.reg8, hbe]
  have hh := openBraceHead G C s hInv hblock h8 hbe
  have hread' : readBytes (openBcS₄ s).mem (G.next0 + 8) 4 =
      some (natToBytes rd.toNat 4) := by
    rw [openBcS₄_mem]; exact hread
  have hpreV' : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 (openHeadC C).sp), .int 32 rd,
       .ptr (openHeadC C).stage.ctype, .ptr (openHeadC C).stage.cst]
      (openBcS₄ s).mem (openBcS₄ s).next := by
    rw [openBcS₄_mem, openBcS₄_next]; exact hpreV
  have ht := openTailSeg G (openHeadC C) (openBcS₄ s) hh.inv' rfl
    (b := BitVec.ofNat 8 (entryByte G C.k).toNat) rfl hsp519 hread' hpreV' r hcall hret
    hklt
  have hseg := hh.trans ht
  have hguard : C.k + 1 < (BitVec.ofNat 64 G.nep).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (openNep_lt G)]
    exact hcont
  have hpre₉ : (openS₉ (openHeadC C) (openBcS₄ s) r rd
      (BitVec.ofNat 8 (entryByte G C.k).toNat)).pre = some "out_reserve.exit.i.i" := rfl
  obtain ⟨-, hinvB, -⟩ :=
    walkBack_step_at (calls := stage2Calls stage2SubCalls) (G := G)
      (C := openC₉ (openHeadC C) (BitVec.ofNat 8 (entryByte G C.k).toNat))
      (s := openS₉ (openHeadC C) (openBcS₄ s) r rd
        (BitVec.ofNat 8 (entryByte G C.k).toNat))
      (spv := C.sp + 1) (k2 := C.k + 1)
      hseg.inv' rfl hpre₉
      (by show phiIncoming "out_reserve.exit.i.i" cleanupSpIncoming =
          some (.reg "%inc33.i"); decide)
      (by simp only [evalOperand]
          exact openS₉_inc33 (openHeadC C) (openBcS₄ s) r rd
            (BitVec.ofNat 8 (entryByte G C.k).toNat))
      (by show phiIncoming "out_reserve.exit.i.i" cleanupKIncoming =
          some (.reg "%inc.i"); decide)
      (by simp only [evalOperand]
          rw [openS₉_inc (openHeadC C) (openBcS₄ s) r rd
            (BitVec.ofNat 8 (entryByte G C.k).toNat)]
          exact LeanLLVM.evalOperand_reg_of hh.inv'.inc_reg)
      (by
        rw [openS₉_nep (openHeadC C) (openBcS₄ s) r rd
          (BitVec.ofNat 8 (entryByte G C.k).toNat)]
        exact hh.inv'.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep))
          (by simp [walkStaticRegs]))
      hguard
  obtain ⟨s'', hl''⟩ :=
    WalkLink.whileBody (calls := stage2Calls stage2SubCalls) G
      { openC₉ (openHeadC C) (BitVec.ofNat 8 (entryByte G C.k).toNat) with
        block := "while.body.i", inner := walkInnerCap G }
      (cleanup478Out (openS₉ (openHeadC C) (openBcS₄ s) r rd
        (BitVec.ofNat 8 (entryByte G C.k).toNat)) (C.sp + 1) (C.k + 1)) hinvB rfl rfl
      (cleanup478Out_k (s := openS₉ (openHeadC C) (openBcS₄ s) r rd
        (BitVec.ofNat 8 (entryByte G C.k).toNat)) (spv := C.sp + 1) (k2 := C.k + 1))
      (cleanup478Out_sp (s := openS₉ (openHeadC C) (openBcS₄ s) r rd
        (BitVec.ofNat 8 (entryByte G C.k).toNat)) (spv := C.sp + 1) (k2 := C.k + 1))
      (by show C.k < C.k + 1; omega)
      (by show C.k + 1 < G.nep; exact hcont)
      (by
        show C.sp + 1 ≤ stage2StackExtent
        have h520 : stage2StackExtent = 520 := rfl
        omega)
      (by
        show C.sp + 1 ≤ (openC₉ (openHeadC C) (BitVec.ofNat 8 (entryByte G C.k).toNat)).wlen
        show C.sp + 1 ≤ max C.wlen (C.sp + 1)
        exact le_max_right _ _)
  refine ⟨_, s'', hl''.inv', rfl, rfl, rfl, ?_, ?_⟩
  · show (openC₉ (openHeadC C) (BitVec.ofNat 8 (entryByte G C.k).toNat)).events
      = C.events ++ [EventRecord.tag 1]
    rw [WalkScope.openC₉_events, ifEnd24St_entryByte_7B C hbyte]
  · show WalkTracePrefix G arena t
      { openC₉ (openHeadC C) (BitVec.ofNat 8 (entryByte G C.k).toNat) with
        block := walkLoopHead, inner := walkInnerCap G, k := C.k + 1, sp := C.sp + 1 }
    exact containerOpenHead_brace h hal hInv hklt hspans hbyte rfl rfl

/-! ### The two-entry container documents' rows

`[]` and `{}` are the documents whose entry stream is one opener and its delimiter.
The opener's revolution is a proved step from the seed (`containerOpenRevolution_*`),
so the closer's row is read at the head it leaves: the trace is the two records, and
nothing between them is a carry supplied by hand. -/

/-- **The document `[]`'s row.**  Two entries, one record each: the bracket opener's
`T_ARR` and the closing bracket's `T_ARR_END`. -/
theorem row_openCloseBracket {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {arena : List UInt8} {C₀ : WalkCarry G} {s : State}
    (h : DelimiterLastDocument G (0x5B : UInt8) 0x5D)
    (hal : WalkAlign G t) (hspans : spansWellFormed t = true)
    (htokens : t.tokens = [.punct .openBracket ⟨0, 1⟩, .punct .closeBracket ⟨1, 2⟩])
    (hpre₀ : WalkTracePrefix G arena t C₀) (hk₀ : C₀.k = 0) (hsp₀ : C₀.sp = 0)
    (hblock₀ : C₀.block = walkLoopHead) (hInv : WalkInv G C₀ s)
    {rd : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C₀.sp), .int 32 rd,
       .ptr C₀.stage.ctype, .ptr C₀.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C₀.sp), .int 32 rd,
       .ptr C₀.stage.ctype, .ptr C₀.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkTraceRow G.bs arena t ([EventRecord.tag 3, EventRecord.tag 4] : List EventRecord) := by
  have hcont : C₀.k + 1 < G.nep := by rw [hk₀, h.count]; decide
  have hbyte₀ : entryByte G C₀.k = 0x5B := by rw [hk₀]; exact h.entryByte_zero
  obtain ⟨C₁, s₁, hInv₁, -, -, hk₁, hev₁, hpre₁⟩ :=
    containerOpenRevolution_bracket G C₀ s hInv hblock₀ hpre₀ hal hspans hbyte₀
      (by rw [hsp₀]; decide) (rd := rd) hread hpreV r hcall hret hcont
  have hbyte₁ : entryByte G C₁.k = 0x5D := by
    rw [hk₁, hk₀]
    simpa using h.entryByte_one
  have hklt₁ : C₁.k < G.nep := by rw [hk₁, hk₀, h.count]; decide
  have hlast : C₁.k + 1 = t.tokens.length := by rw [hk₁, hk₀, htokens]; rfl
  have hrow := containerCloseLastRow_bracket hpre₁ hal hInv₁ hklt₁ hspans hbyte₁
    (spz := BitVec.ofNat 32 0) (c8 := BitVec.ofNat 8 4) rfl hlast
  simpa [hev₁, WalkTracePrefix.events_eq_nil hpre₀ hk₀] using hrow

/-- **The document `{}`'s row.**  The same two entries at the brace's bytes: `T_OBJ`
and `T_OBJ_END`. -/
theorem row_openCloseBrace {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {arena : List UInt8} {C₀ : WalkCarry G} {s : State}
    (h : DelimiterLastDocument G (0x7B : UInt8) 0x7D)
    (hal : WalkAlign G t) (hspans : spansWellFormed t = true)
    (htokens : t.tokens = [.punct .openBrace ⟨0, 1⟩, .punct .closeBrace ⟨1, 2⟩])
    (hpre₀ : WalkTracePrefix G arena t C₀) (hk₀ : C₀.k = 0) (hsp₀ : C₀.sp = 0)
    (hblock₀ : C₀.block = walkLoopHead) (hInv : WalkInv G C₀ s)
    {rd : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C₀.sp), .int 32 rd,
       .ptr C₀.stage.ctype, .ptr C₀.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C₀.sp), .int 32 rd,
       .ptr C₀.stage.ctype, .ptr C₀.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkTraceRow G.bs arena t ([EventRecord.tag 1, EventRecord.tag 2] : List EventRecord) := by
  have hcont : C₀.k + 1 < G.nep := by rw [hk₀, h.count]; decide
  have hbyte₀ : entryByte G C₀.k = 0x7B := by rw [hk₀]; exact h.entryByte_zero
  obtain ⟨C₁, s₁, hInv₁, -, -, hk₁, hev₁, hpre₁⟩ :=
    containerOpenRevolution_brace G C₀ s hInv hblock₀ hpre₀ hal hspans hbyte₀
      (by rw [hsp₀]; decide) (rd := rd) hread hpreV r hcall hret hcont
  have hbyte₁ : entryByte G C₁.k = 0x7D := by
    rw [hk₁, hk₀]
    simpa using h.entryByte_one
  have hklt₁ : C₁.k < G.nep := by rw [hk₁, hk₀, h.count]; decide
  have hlast : C₁.k + 1 = t.tokens.length := by rw [hk₁, hk₀, htokens]; rfl
  have hrow := containerCloseLastRow_brace hpre₁ hal hInv₁ hklt₁ hspans hbyte₁
    (spz := BitVec.ofNat 32 0) (c8 := BitVec.ofNat 8 2) rfl hlast
  simpa [hev₁, WalkTracePrefix.events_eq_nil hpre₀ hk₀] using hrow

/-! ### The per-revolution step

Each row above is one arm at one index.  A document longer than two entries needs the
step the loop takes *between* arms and the induction that composes those steps, and
both are stated here at the level a row is read from.

`WalkTraceStep` is one revolution's effect on the trace: the index past exactly one
entry, and the correspondence regained.  Its two producers are the arms' own forms —
`WalkTraceStep.emit` for a class that appends one record, `WalkTraceStep.separator` for
the two that append none — and `gain_of_separator`/`gain_of_record` read the step as a
count, so "appends exactly its entry's record" is a statement rather than a reading of
the definition: the trace grows by one at a record-carrying entry and not at all at a
separator.

`WalkRevolution` is the same step at the walk's own state: `WalkInv` and the loop head
at both ends, so the step is the loop's and not a carry chosen for the trace.
`containerOpenRevolution_bracket_step`/`_brace_step` are its two inhabited instances
today, and each carries the record it appended beside the relation; the other arms owe
their own, with the payload premises the header's residual list names.

`WalkTraceChain` composes steps, `WalkTraceChain.of_steps` is the induction for any
number of entries — the step family supplies one revolution per head index — and
`walkTraceRow_of_revolutions` is the row at `G.nep`. -/

/-- **One revolution at the trace.**  The index moves past exactly the entry the
revolution consumed, and the trace is still the records of the entries passed. -/
structure WalkTraceStep {m0 : Mem} (G : WalkGeom m0) (arena : List UInt8) (t : Tape)
    (C C' : WalkCarry G) : Prop where
  /-- The index advances by exactly one entry. -/
  k' : C'.k = C.k + 1
  /-- The trace is the entries passed. -/
  trace : WalkTracePrefix G arena t C'

namespace WalkTraceStep

/-- **An emitting arm's step.**  One record, related to the entry's token, and the
index past that entry: `WalkTracePrefix.emit_advance` read as a resolution step. -/
theorem emit {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C C' : WalkCarry G} {tok : Token} {r : EventRecord}
    (h : WalkTracePrefix G arena t C) (htok : t.tokens[C.k]? = some tok)
    (hrec : TokenRecord G.bs arena r tok) (hk : C'.k = C.k + 1)
    (hev : C'.events = C.events ++ [r]) : WalkTraceStep G arena t C C' where
  k' := hk
  trace := h.emit_advance htok hrec hk hev

/-- **A separator's step.**  A comma or a colon carries no record, so the trace is the
predecessor's and only the index moves. -/
theorem separator {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C C' : WalkCarry G} {p : Punct} {s : Span}
    (h : WalkTracePrefix G arena t C) (htok : t.tokens[C.k]? = some (.punct p s))
    (hp : p = .comma ∨ p = .colon) (hk : C'.k = C.k + 1)
    (hev : C'.events = C.events) : WalkTraceStep G arena t C C' where
  k' := hk
  trace := h.advance_separator htok hp hk hev

/-- **A separator moves the count by nothing.**  The step's trace has exactly the
records the predecessor's had. -/
theorem gain_of_separator {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C C' : WalkCarry G} {p : Punct} {s : Span} (h : WalkTraceStep G arena t C C')
    (hpre : WalkTracePrefix G arena t C) (htok : t.tokens[C.k]? = some (.punct p s))
    (hp : p = .comma ∨ p = .colon) : C'.events.length = C.events.length := by
  have h1 : C'.events.length = (Token.recordTokens t.tokens C'.k).length :=
    WalkTracePrefix.length h.trace
  have h2 : C.events.length = (Token.recordTokens t.tokens C.k).length :=
    WalkTracePrefix.length hpre
  rw [h1, h2, h.k', Token.recordTokens_succ_of_separator htok hp]

/-- **A record-carrying entry moves the count by one.**  The step's trace is exactly
the predecessor's plus that one record. -/
theorem gain_of_record {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C C' : WalkCarry G} {tok : Token} (h : WalkTraceStep G arena t C C')
    (hpre : WalkTracePrefix G arena t C) (htok : t.tokens[C.k]? = some tok)
    (hc : ∀ s : Span, tok ≠ .punct .comma s) (hd : ∀ s : Span, tok ≠ .punct .colon s) :
    C'.events.length = C.events.length + 1 := by
  have h1 : C'.events.length = (Token.recordTokens t.tokens C'.k).length :=
    WalkTracePrefix.length h.trace
  have h2 : C.events.length = (Token.recordTokens t.tokens C.k).length :=
    WalkTracePrefix.length hpre
  rw [h1, h2, h.k', Token.recordTokens_succ_of_record htok hc hd, List.length_append,
    List.length_singleton]

end WalkTraceStep

/-- **One revolution at the walk's head.**  `WalkInv` at the loop head with the trace
prefix, one revolution, and the loop head again with the prefix and the index past that
entry: the step's premises are the arm's and its conclusion is the carry the loop
reaches. -/
structure WalkRevolution {m0 : Mem} (G : WalkGeom m0) (arena : List UInt8) (t : Tape)
    (s : State) (C C' : WalkCarry G) : Prop where
  /-- The invariant at the head the revolution starts from. -/
  inv : WalkInv G C s
  /-- That head is the loop's. -/
  block : C.block = walkLoopHead
  /-- The invariant at the head it leaves. -/
  inv' : ∃ s' : State, WalkInv G C' s'
  /-- That head is the loop's too. -/
  block' : C'.block = walkLoopHead
  /-- The index advances by exactly one entry. -/
  k' : C'.k = C.k + 1
  /-- The trace is the entries passed. -/
  trace : WalkTracePrefix G arena t C'

namespace WalkRevolution

/-- The trace's own half of a revolution: the part the induction composes. -/
theorem toTraceStep {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {s : State} {C C' : WalkCarry G} (h : WalkRevolution G arena t s C C') :
    WalkTraceStep G arena t C C' where
  k' := h.k'
  trace := h.trace

end WalkRevolution

/-- **The bracket opener's revolution is the loop's step.**  `containerOpenRevolution_
bracket`'s conclusion is `WalkRevolution`'s fields; the two facts the trace reads from
it are stated beside the relation — the entry is the parser's open bracket, and the
record the arm appended is `T_ARR`. -/
theorem containerOpenRevolution_bracket_step {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {arena : List UInt8} {t : Tape} (h : WalkTracePrefix G arena t C)
    (hal : WalkAlign G t) (hspans : spansWellFormed t = true)
    (hbyte : entryByte G C.k = 0x5B) (hsp519 : C.sp ≤ 519)
    {rd : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) (hcont : C.k + 1 < G.nep) :
    ∃ (C' : WalkCarry G) (sp : Span),
      WalkRevolution G arena t s C C' ∧
        t.tokens[C.k]? = some (.punct .openBracket sp) ∧
        C'.events = C.events ++ [EventRecord.tag 3] := by
  obtain ⟨C', s', hInv', hblock', -, hk', hev', hpre'⟩ :=
    containerOpenRevolution_bracket G C s hInv hblock h hal hspans hbyte hsp519
      hread hpreV r hcall hret hcont
  have hklt : C.k < G.nep :=
    WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)
  obtain ⟨sp, htok, -⟩ := hal.head_openBracket hInv hklt hbyte
  refine ⟨C', sp, ?_, htok, hev'⟩
  exact { inv := hInv, block := hblock, inv' := ⟨s', hInv'⟩, block' := hblock', k' := hk', trace := hpre' }

/-- **The brace opener's revolution is the loop's step.**  The same at `{`, whose
record is `T_OBJ`. -/
theorem containerOpenRevolution_brace_step {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    {arena : List UInt8} {t : Tape} (h : WalkTracePrefix G arena t C)
    (hal : WalkAlign G t) (hspans : spansWellFormed t = true)
    (hbyte : entryByte G C.k = 0x7B) (hsp519 : C.sp ≤ 519)
    {rd : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rd,
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) (hcont : C.k + 1 < G.nep) :
    ∃ (C' : WalkCarry G) (sp : Span),
      WalkRevolution G arena t s C C' ∧
        t.tokens[C.k]? = some (.punct .openBrace sp) ∧
        C'.events = C.events ++ [EventRecord.tag 1] := by
  obtain ⟨C', s', hInv', hblock', -, hk', hev', hpre'⟩ :=
    containerOpenRevolution_brace G C s hInv hblock h hal hspans hbyte hsp519
      hread hpreV r hcall hret hcont
  have hklt : C.k < G.nep :=
    WalkInv.head_lt hInv (by simpa only [walkLoopHead] using hblock)
  obtain ⟨sp, htok, -⟩ := hal.head_openBrace hInv hklt hbyte
  refine ⟨C', sp, ?_, htok, hev'⟩
  exact { inv := hInv, block := hblock, inv' := ⟨s', hInv'⟩, block' := hblock', k' := hk', trace := hpre' }

/-- **A payload entry's revolution.**  The entry's arm appends its one record and the
index moves past the entry.  This is the shape the number's and the string's arms owe:
`TokenRecord`'s `number`/`strPlain`/`strArena` constructor at the entry's token, whose
premises are the payload premises the header's residual list names. -/
def WalkPayloadStep {m0 : Mem} (G : WalkGeom m0) (arena : List UInt8) (t : Tape)
    (C C' : WalkCarry G) (r : EventRecord) : Prop :=
  WalkTraceStep G arena t C C' ∧ C'.events = C.events ++ [r]

/-! ### The induction over revolutions

`WalkTraceChain` is a list of steps — the run of the loop's revolutions, recorded one
at a time — and `of_steps` is the induction for any number of entries.  The index is
the chain's length (`k_eq`), the correspondence is carried by `carries`, and
`traceRow` reads the chain's end as the row when its index reaches the whole token
list. -/

/-- **A run of revolutions.**  `WalkTraceChain G arena t n C C'` is `n` trace steps
from `C` to `C'`. -/
inductive WalkTraceChain {m0 : Mem} (G : WalkGeom m0) (arena : List UInt8) (t : Tape) :
    Nat → WalkCarry G → WalkCarry G → Prop
  /-- No revolutions: the carry stands. -/
  | zero (C : WalkCarry G) : WalkTraceChain G arena t 0 C C
  /-- One revolution, then the rest. -/
  | succ {n : Nat} {C C' C'' : WalkCarry G} (h : WalkTraceStep G arena t C C')
      (hs : WalkTraceChain G arena t n C' C'') :
      WalkTraceChain G arena t (n + 1) C C''

namespace WalkTraceChain

/-- **The chain's index.**  `n` revolutions move the index by `n`. -/
theorem k_eq {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {n : Nat} {C C' : WalkCarry G} (h : WalkTraceChain G arena t n C C') :
    C'.k = C.k + n := by
  induction h with
  | zero => simp
  | succ hstep _ ih => rw [ih, hstep.k']; omega

/-- **The chain carries the correspondence.** -/
theorem carries {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {n : Nat} {C C' : WalkCarry G} (h : WalkTraceChain G arena t n C C') :
    WalkTracePrefix G arena t C → WalkTracePrefix G arena t C' := by
  induction h with
  | zero => exact id
  | succ hstep _ ih => exact fun hpre => ih hstep.trace

/-- **The row at the chain's end.**  A chain whose end index is the whole token list
has the row as its trace. -/
theorem traceRow {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {n : Nat} {C C' : WalkCarry G} (h : WalkTraceChain G arena t n C C')
    (hpre : WalkTracePrefix G arena t C) (hkend : C'.k = t.tokens.length) :
    WalkTraceRow G.bs arena t C'.events :=
  (carries h hpre).toTraceRow hkend

/-- **The induction over revolutions.**  A step at every head index composes for any
number of entries: from a carry at `C.k`, `m` revolutions reach a carry `m` further on,
as long as the index stays inside the entry stream. -/
theorem of_steps {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    (hstep : ∀ (C : WalkCarry G), C.k < G.nep → WalkTracePrefix G arena t C →
      ∃ C', WalkTraceStep G arena t C C') :
    ∀ (m : Nat) (C : WalkCarry G), C.k + m ≤ G.nep → WalkTracePrefix G arena t C →
      ∃ C', WalkTraceChain G arena t m C C' := by
  intro m
  induction m with
  | zero =>
      intro C _ hpre
      exact ⟨C, WalkTraceChain.zero C⟩
  | succ m ih =>
      intro C hle hpre
      have hk : C.k < G.nep := by omega
      obtain ⟨C', hstep'⟩ := hstep C hk hpre
      have hle' : C'.k + m ≤ G.nep := by
        have := hstep'.k'
        omega
      obtain ⟨C'', hchain⟩ := ih C' hle' hstep'.trace
      exact ⟨C'', WalkTraceChain.succ hstep' hchain⟩

end WalkTraceChain

/-- **The row, for any number of entries.**  From the seed — index zero, the trace
correspondence — a step at every head index gives a carry at the entry count and the
whole document's row: `WalkAlign.traceRow_of_prefix` at the chain's end. -/
theorem walkTraceRow_of_revolutions {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8}
    {t : Tape}
    (hstep : ∀ (C : WalkCarry G), C.k < G.nep → WalkTracePrefix G arena t C →
      ∃ C', WalkTraceStep G arena t C C')
    (hal : WalkAlign G t) {C₀ : WalkCarry G} (hk₀ : C₀.k = 0)
    (hpre₀ : WalkTracePrefix G arena t C₀) :
    ∃ C : WalkCarry G, C.k = G.nep ∧ WalkTraceRow G.bs arena t C.events := by
  have hle : C₀.k + G.nep ≤ G.nep := by omega
  obtain ⟨C, hchain⟩ := WalkTraceChain.of_steps hstep G.nep C₀ hle hpre₀
  have hk : C.k = G.nep := by
    have := WalkTraceChain.k_eq hchain
    omega
  exact ⟨C, hk, WalkAlign.traceRow_of_prefix hal (WalkTraceChain.carries hchain hpre₀) hk⟩

/-! ### The separator reached: a two-payload document's row

The rows above are the separator's neighbours: `[]` and `{}` hold no separator between
their entries.  A separator's arm is reached by a document with two value entries
inside one container, and its row is the induction's first use at a document: the
opener's revolution, a payload entry, the separator, a payload entry and the close.
The two payload revolutions are the premises this layer cannot derive
(`WalkPayloadStep`), because their records are their own arms' and those arms are the
header's residual; everything else — the two containers' records, the separator's
silence and the last entry's reading — is derived here, from the alignment, the tape's
own token list and the arms' net effects.  The
separator is named by its token rather than by a byte premise: this layer reads the
tape, and only the containers' records need the byte (`headTokenRecord_punct`'s
`hbyte`), which is why the two payload entries carry no byte either.

The five entries' arms are stated once at `Punct`s and bytes, so the comma and the
colon, and the bracket and the brace, are one theorem: `row_commaBracketPayload` and
`row_colonBracePayload` are the two documents, and `row_commaBracket`/`row_colonBrace`
are their rows at the seed. -/

/-- **The row of a payload-separated document.**  Five entries: an opening container,
a payload, the separator, a payload, and the closing container.  `C₀` is the seed,
`C₁` the head the opener's revolution leaves, `C₂` the head after the first payload,
`C₃` the head after the separator, `C₄` the head after the second payload, and `Cm` the
closer's merge carry. -/
theorem row_separatedPayload {m0 : Mem} {G : WalkGeom m0} {t : Tape} {arena : List UInt8}
    {C₀ C₁ C₂ C₃ C₄ Cm : WalkCarry G} {so sm sc : Span} {tok₁ tok₂ : Token}
    {r₁ r₂ : EventRecord} {po ps pc : Punct}
    (hpo : po = .openBracket ∨ po = .openBrace)
    (hps : ps = .comma ∨ ps = .colon)
    (hpc : pc = .closeBracket ∨ pc = .closeBrace)
    (hal : WalkAlign G t) (hspans : spansWellFormed t = true)
    (htokens : t.tokens = [.punct po so, tok₁, .punct ps sm, tok₂, .punct pc sc])
    (hpre₀ : WalkTracePrefix G arena t C₀) (hk₀ : C₀.k = 0)
    (hbyteo : entryByte G C₀.k = punctByte po)
    (hk₁ : C₁.k = C₀.k + 1)
    (hev₁ : C₁.events = C₀.events ++ [EventRecord.tag (punctTag po)])
    (hpay₁ : WalkPayloadStep G arena t C₁ C₂ r₁)
    (hk₃ : C₃.k = C₂.k + 1) (hev₃ : C₃.events = C₂.events)
    (hpay₂ : WalkPayloadStep G arena t C₃ C₄ r₂)
    (hbytec : entryByte G C₄.k = punctByte pc)
    (hkM : Cm.k = C₄.k)
    (hevM : Cm.events = C₄.events ++ [EventRecord.tag (punctTag pc)]) :
    WalkTraceRow G.bs arena t
      (C₀.events ++ [EventRecord.tag (punctTag po), r₁, r₂,
        EventRecord.tag (punctTag pc)]) := by
  obtain ⟨hstep₁, hev₁'⟩ := hpay₁
  obtain ⟨hstep₂, hev₂'⟩ := hpay₂
  have hne : G.nep = 5 := by simp [hal.tokens_length, htokens]
  have hk₂ : C₂.k = 2 := by
    have := hstep₁.k'
    omega
  have hk₃' : C₃.k = 3 := by omega
  have hk₄ : C₄.k = 4 := by
    have := hstep₂.k'
    omega
  -- the opener's record, and its record-bearing step
  have htok₀ : t.tokens[C₀.k]? = some (.punct po so) := by simp [hk₀, htokens]
  have hlt₀ : C₀.k < G.nep := by omega
  have hp₀ : po = .openBrace ∨ po = .closeBrace ∨ po = .openBracket ∨ po = .closeBracket := by
    rcases hpo with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl h
  have hstepO : WalkTraceStep G arena t C₀ C₁ :=
    WalkTraceStep.emit hpre₀ htok₀
      (headTokenRecord_punct hal hlt₀ hspans arena hp₀ htok₀ hbyteo) hk₁ hev₁
  -- the separator's own step
  have htok₂ : t.tokens[C₂.k]? = some (.punct ps sm) := by simp [hk₂, htokens]
  have hstepS : WalkTraceStep G arena t C₂ C₃ :=
    WalkTraceStep.separator hstep₁.trace htok₂ hps hk₃ hev₃
  -- the run up to the last payload
  have hchain : WalkTraceChain G arena t 4 C₀ C₄ :=
    WalkTraceChain.succ hstepO (WalkTraceChain.succ hstep₁
      (WalkTraceChain.succ hstepS (WalkTraceChain.succ hstep₂
        (WalkTraceChain.zero C₄))))
  have hpre₄ : WalkTracePrefix G arena t C₄ := WalkTraceChain.carries hchain hpre₀
  -- the closer's record at the merge, and the last entry's row
  have htok₄ : t.tokens[C₄.k]? = some (.punct pc sc) := by simp [hk₄, htokens]
  have hlt₄ : C₄.k < G.nep := by omega
  have hpC : pc = .openBrace ∨ pc = .closeBrace ∨ pc = .openBracket ∨ pc = .closeBracket := by
    rcases hpc with h | h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inl h)
  have hem : WalkTracePrefixEmit G arena t Cm (.punct pc sc) :=
    WalkTracePrefix.emit hpre₄ (headTokenRecord_punct hal hlt₄ hspans arena hpC htok₄ hbytec)
      hkM hevM
  have htokM : t.tokens[Cm.k]? = some (.punct pc sc) := by simp [hkM, hk₄, htokens]
  have hlast : Cm.k + 1 = t.tokens.length := by simp [hkM, hk₄, htokens]
  have hrow := WalkTracePrefix.row_of_last hem htokM hlast
  rw [hevM, hev₂', hev₃, hev₁', hev₁] at hrow
  simpa using hrow

/-- **The document `[p₁,p₂]`'s row.**  The separator between the two payloads is the
comma and the container is the bracket. -/
theorem row_commaBracketPayload {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {arena : List UInt8} {C₀ C₁ C₂ C₃ C₄ Cm : WalkCarry G} {so sm sc : Span}
    {tok₁ tok₂ : Token} {r₁ r₂ : EventRecord}
    (hal : WalkAlign G t) (hspans : spansWellFormed t = true)
    (htokens : t.tokens = [.punct .openBracket so, tok₁, .punct .comma sm, tok₂,
      .punct .closeBracket sc])
    (hpre₀ : WalkTracePrefix G arena t C₀) (hk₀ : C₀.k = 0)
    (hbyteo : entryByte G C₀.k = 0x5B)
    (hk₁ : C₁.k = C₀.k + 1) (hev₁ : C₁.events = C₀.events ++ [EventRecord.tag 3])
    (hpay₁ : WalkPayloadStep G arena t C₁ C₂ r₁)
    (hk₃ : C₃.k = C₂.k + 1) (hev₃ : C₃.events = C₂.events)
    (hpay₂ : WalkPayloadStep G arena t C₃ C₄ r₂)
    (hbytec : entryByte G C₄.k = 0x5D)
    (hkM : Cm.k = C₄.k) (hevM : Cm.events = C₄.events ++ [EventRecord.tag 4]) :
    WalkTraceRow G.bs arena t
      (C₀.events ++ [EventRecord.tag 3, r₁, r₂, EventRecord.tag 4]) :=
  row_separatedPayload (po := .openBracket) (ps := .comma) (pc := .closeBracket)
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hal hspans htokens hpre₀ hk₀ hbyteo hk₁ hev₁
    hpay₁ hk₃ hev₃ hpay₂ hbytec hkM hevM

/-- **The document `[p₁,p₂]`'s row at the seed.**  The trace before the opener is empty
(`WalkTracePrefix.events_eq_nil`), so the row is the four records alone. -/
theorem row_commaBracket {m0 : Mem} {G : WalkGeom m0} {t : Tape} {arena : List UInt8}
    {C₀ C₁ C₂ C₃ C₄ Cm : WalkCarry G} {so sm sc : Span} {tok₁ tok₂ : Token}
    {r₁ r₂ : EventRecord}
    (hal : WalkAlign G t) (hspans : spansWellFormed t = true)
    (htokens : t.tokens = [.punct .openBracket so, tok₁, .punct .comma sm, tok₂,
      .punct .closeBracket sc])
    (hpre₀ : WalkTracePrefix G arena t C₀) (hk₀ : C₀.k = 0)
    (hbyteo : entryByte G C₀.k = 0x5B)
    (hk₁ : C₁.k = C₀.k + 1) (hev₁ : C₁.events = C₀.events ++ [EventRecord.tag 3])
    (hpay₁ : WalkPayloadStep G arena t C₁ C₂ r₁)
    (hk₃ : C₃.k = C₂.k + 1) (hev₃ : C₃.events = C₂.events)
    (hpay₂ : WalkPayloadStep G arena t C₃ C₄ r₂)
    (hbytec : entryByte G C₄.k = 0x5D)
    (hkM : Cm.k = C₄.k) (hevM : Cm.events = C₄.events ++ [EventRecord.tag 4]) :
    WalkTraceRow G.bs arena t
      ([EventRecord.tag 3, r₁, r₂, EventRecord.tag 4] : List EventRecord) := by
  have hrow := row_commaBracketPayload hal hspans htokens hpre₀ hk₀ hbyteo hk₁ hev₁
    hpay₁ hk₃ hev₃ hpay₂ hbytec hkM hevM
  simpa [WalkTracePrefix.events_eq_nil hpre₀ hk₀] using hrow

/-- **The document `{p₁:p₂}`'s row.**  The same five entries at the colon and the
brace: the separator's arm is reached by an object's second member. -/
theorem row_colonBracePayload {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {arena : List UInt8} {C₀ C₁ C₂ C₃ C₄ Cm : WalkCarry G} {so sm sc : Span}
    {tok₁ tok₂ : Token} {r₁ r₂ : EventRecord}
    (hal : WalkAlign G t) (hspans : spansWellFormed t = true)
    (htokens : t.tokens = [.punct .openBrace so, tok₁, .punct .colon sm, tok₂,
      .punct .closeBrace sc])
    (hpre₀ : WalkTracePrefix G arena t C₀) (hk₀ : C₀.k = 0)
    (hbyteo : entryByte G C₀.k = 0x7B)
    (hk₁ : C₁.k = C₀.k + 1) (hev₁ : C₁.events = C₀.events ++ [EventRecord.tag 1])
    (hpay₁ : WalkPayloadStep G arena t C₁ C₂ r₁)
    (hk₃ : C₃.k = C₂.k + 1) (hev₃ : C₃.events = C₂.events)
    (hpay₂ : WalkPayloadStep G arena t C₃ C₄ r₂)
    (hbytec : entryByte G C₄.k = 0x7D)
    (hkM : Cm.k = C₄.k) (hevM : Cm.events = C₄.events ++ [EventRecord.tag 2]) :
    WalkTraceRow G.bs arena t
      (C₀.events ++ [EventRecord.tag 1, r₁, r₂, EventRecord.tag 2]) :=
  row_separatedPayload (po := .openBrace) (ps := .colon) (pc := .closeBrace)
    (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) hal hspans htokens hpre₀ hk₀ hbyteo hk₁ hev₁
    hpay₁ hk₃ hev₃ hpay₂ hbytec hkM hevM

/-- **The document `{p₁:p₂}`'s row at the seed.** -/
theorem row_colonBrace {m0 : Mem} {G : WalkGeom m0} {t : Tape} {arena : List UInt8}
    {C₀ C₁ C₂ C₃ C₄ Cm : WalkCarry G} {so sm sc : Span} {tok₁ tok₂ : Token}
    {r₁ r₂ : EventRecord}
    (hal : WalkAlign G t) (hspans : spansWellFormed t = true)
    (htokens : t.tokens = [.punct .openBrace so, tok₁, .punct .colon sm, tok₂,
      .punct .closeBrace sc])
    (hpre₀ : WalkTracePrefix G arena t C₀) (hk₀ : C₀.k = 0)
    (hbyteo : entryByte G C₀.k = 0x7B)
    (hk₁ : C₁.k = C₀.k + 1) (hev₁ : C₁.events = C₀.events ++ [EventRecord.tag 1])
    (hpay₁ : WalkPayloadStep G arena t C₁ C₂ r₁)
    (hk₃ : C₃.k = C₂.k + 1) (hev₃ : C₃.events = C₂.events)
    (hpay₂ : WalkPayloadStep G arena t C₃ C₄ r₂)
    (hbytec : entryByte G C₄.k = 0x7D)
    (hkM : Cm.k = C₄.k) (hevM : Cm.events = C₄.events ++ [EventRecord.tag 2]) :
    WalkTraceRow G.bs arena t
      ([EventRecord.tag 1, r₁, r₂, EventRecord.tag 2] : List EventRecord) := by
  have hrow := row_colonBracePayload hal hspans htokens hpre₀ hk₀ hbyteo hk₁ hev₁
    hpay₁ hk₃ hev₃ hpay₂ hbytec hkM hevM
  simpa [WalkTracePrefix.events_eq_nil hpre₀ hk₀] using hrow

/-! ### The payload arms' steps

`row_separatedPayload` leaves two payload revolutions as premises.  An arm's run from
the loop head ends at the merge carry `cleanup478.i`, which the dispatch layer states as
a `WalkSegment`, and the merge's own reading of that carry is the arm's: the index it
kept and the one record it appended.  The merge's `%k.2.i` is the header's `%inc.i`, so
the carry the loop leaves carries the index one entry on, and the trace at it is
`WalkTraceStep.emit`'s.

The three payload classes are the number's and the string's two forms.  Beside its
segment each takes the payload premise the header's residual list names — the numeral's
decomposition and the string's read-back — because those are the arm's reading of the
document rather than the row's: the numeral is the arm's `num_fast_el1` decomposition of
the span's bytes, and the string's body is the escape unit's answer at the bytes it wrote.
The span, the token and the record's relation are the row's, and they are derived here.
-/

/-- **A payload arm's step.**  The arm's segment reaches the merge carry with the index
unmoved and the record appended; the entry's token is the one the head's byte names and
the record is related to it.  The carry the header leaves is that merge carry one index
on, which is `WalkTraceStep.emit`'s `hk` and `hev`. -/
theorem payloadStep_of_segment {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8}
    {t : Tape} {C Cd : WalkCarry G} {r : EventRecord} {tok : Token}
    (hpre : WalkTracePrefix G arena t C) (htok : t.tokens[C.k]? = some tok)
    (hrec : TokenRecord G.bs arena r tok)
    (hk : Cd.k = C.k) (hev : Cd.events = C.events ++ [r]) :
    WalkPayloadStep G arena t C { Cd with k := Cd.k + 1 } r := by
  have hk' : ({ Cd with k := Cd.k + 1 } : WalkCarry G).k = C.k + 1 := by rw [hk]
  have hev' : ({ Cd with k := Cd.k + 1 } : WalkCarry G).events = C.events ++ [r] := hev
  exact ⟨WalkTraceStep.emit (C' := { Cd with k := Cd.k + 1 }) hpre htok hrec hk' hev', hev'⟩

/-- **A payload arm's revolution.**  The arm's counted run from the loop head to the
merge carry, that carry's two facts at the merge, and the step the loop takes from them.
The segment is the dispatch layer's (the number's and the two strings' paths compose
their own); the two facts are its endpoint's, and the step is `payloadStep_of_segment`'s
at the entry's record. -/
structure WalkPayloadRevolution {m0 : Mem} (G : WalkGeom m0) (arena : List UInt8)
    (t : Tape) (C : WalkCarry G) (s : State) (Cd : WalkCarry G) (sd : State) (p : Nat)
    (r : EventRecord) : Prop where
  /-- The arm's run, from the loop head to the merge carry. -/
  seg : WalkScope.WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p
  /-- The merge keeps the index. -/
  k : Cd.k = C.k
  /-- The arm appends exactly its one record. -/
  events : Cd.events = C.events ++ [r]
  /-- The step at those two facts: the merge carry's index advanced by the header. -/
  step : WalkPayloadStep G arena t C { Cd with k := Cd.k + 1 } r

/-- **The number arm's step.**  The head's byte is the numeral's (`-` or a digit), the
tape's token is the span's, and the arm's decomposition of that span's bytes is
`strtodSpec`'s.  The record is the one the arm appended, so the row reads the bits the
parser's payload names. -/
theorem payloadStep_number {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C Cd : WalkCarry G} {s : State} (arena : List UInt8) (hal : WalkAlign G t)
    (hInv : WalkInv G C s) (hklt : C.k < G.nep) {v : JSON.Value}
    (hdec : decodeTape t = some v) {b0 : UInt8} (hbyte : entryByte G C.k = b0)
    (hb : b0 = 0x2D ∨ IsDigitB b0 = true) {d : Decimal} (hwf : d.wellFormed)
    (hlex : ∀ sp : Span, t.tokens[C.k]? = some (.number sp) →
      d.lexeme.data.toList = (G.bs.drop sp.start).take (sp.stop - sp.start))
    (hpre : WalkTracePrefix G arena t C)
    (hk : Cd.k = C.k)
    (hev : Cd.events = C.events ++ [EventRecord.number (strtodSpec d).toBits]) :
    WalkPayloadStep G arena t C { Cd with k := Cd.k + 1 }
      (EventRecord.number (strtodSpec d).toBits) := by
  obtain ⟨sp, htok, hrec⟩ :=
    headTokenRecord_number hal hInv hklt hdec arena hbyte hb hwf hlex
  exact payloadStep_of_segment hpre htok hrec hk hev

/-- **A plain string's step.**  The head's byte is the quote, the token is the span's,
and the arm's read of the raw body — the bytes before the closing quote — is the
parser's body.  The record addresses that body through `plainSpan`. -/
theorem payloadStep_string_plain {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C Cd : WalkCarry G} {s : State} (arena : List UInt8) (hal : WalkAlign G t)
    (hInv : WalkInv G C s) (hklt : C.k < G.nep) {v : JSON.Value}
    (hdec : decodeTape t = some v) (hbyte : entryByte G C.k = 0x22)
    {sp : Span} (htokC : t.tokens[C.k]? = some (.string sp))
    {key : Bool} {len : Nat}
    (hspan : ∀ sp' : Span, t.tokens[C.k]? = some (.string sp') →
      sp'.stop = sp'.start + 2 + len)
    (hbody : ∀ sp' : Span, t.tokens[C.k]? = some (.string sp') → ∀ cs : List Nat,
      bodyCodePoints G.bs sp' = some cs →
      escapeCodePoints ((G.bs.drop (sp'.start + 1)).take len) = some cs)
    (hpre : WalkTracePrefix G arena t C)
    (hk : Cd.k = C.k)
    (hev : Cd.events = C.events ++ [EventRecord.str key len (plainSpan (sp.start + 1))]) :
    WalkPayloadStep G arena t C { Cd with k := Cd.k + 1 }
      (EventRecord.str key len (plainSpan (sp.start + 1))) := by
  obtain ⟨sp', cs, htok', hcode, hrec⟩ :=
    headTokenRecord_string_plain hal hInv hklt hdec arena hbyte hspan hbody
  have hsp : sp' = sp := by
    have h1 : Token.string sp = Token.string sp' :=
      Option.some.inj (htokC.symm.trans htok')
    exact ((Token.string.injEq sp sp').mp h1).symm
  rw [hsp] at hrec
  exact payloadStep_of_segment hpre htokC hrec hk hev

/-- **An arena string's step.**  The head's byte is the quote, the span holds both its
quotes, and the arm's read of the arena's slice at its offset is the parser's body.  The
record names the slice by that offset, which the walk's cursor keeps below `2 ^ 63`. -/
theorem payloadStep_string_arena {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C Cd : WalkCarry G} {s : State} (arena : List UInt8) (hal : WalkAlign G t)
    (hInv : WalkInv G C s) (hklt : C.k < G.nep) {v : JSON.Value}
    (hdec : decodeTape t = some v) (hbyte : entryByte G C.k = 0x22)
    {key : Bool} {len off : Nat}
    (hlen : ∀ sp : Span, t.tokens[C.k]? = some (.string sp) → sp.start + 2 ≤ sp.stop)
    (hoff : off < 2 ^ 63)
    (harena : ∀ sp : Span, t.tokens[C.k]? = some (.string sp) → ∀ cs : List Nat,
      bodyCodePoints G.bs sp = some cs →
      escapeCodePoints ((arena.drop off).take len) = some cs)
    (hpre : WalkTracePrefix G arena t C)
    (hk : Cd.k = C.k)
    (hev : Cd.events = C.events ++ [EventRecord.str key len off]) :
    WalkPayloadStep G arena t C { Cd with k := Cd.k + 1 } (EventRecord.str key len off) := by
  obtain ⟨sp, cs, htok, hcode, hrec⟩ :=
    headTokenRecord_string_arena hal hInv hklt hdec arena hbyte hlen hoff harena
  exact payloadStep_of_segment hpre htok hrec hk hev

/-! The three producers: the arm's segment, the merge's two facts and its payload premise
give the revolution.  `payloadStep_*` is the step they build. -/

/-- **The number arm's revolution.** -/
theorem payloadRevolution_number {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C Cd : WalkCarry G} {s sd : State} {p : Nat} (arena : List UInt8)
    (hal : WalkAlign G t) (hInv : WalkInv G C s) (hklt : C.k < G.nep)
    {v : JSON.Value} (hdec : decodeTape t = some v) {b0 : UInt8}
    (hbyte : entryByte G C.k = b0) (hb : b0 = 0x2D ∨ IsDigitB b0 = true)
    {d : Decimal} (hwf : d.wellFormed)
    (hlex : ∀ sp : Span, t.tokens[C.k]? = some (.number sp) →
      d.lexeme.data.toList = (G.bs.drop sp.start).take (sp.stop - sp.start))
    (hpre : WalkTracePrefix G arena t C)
    (hseg : WalkScope.WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p)
    (hk : Cd.k = C.k)
    (hev : Cd.events = C.events ++ [EventRecord.number (strtodSpec d).toBits]) :
    WalkPayloadRevolution G arena t C s Cd sd p
      (EventRecord.number (strtodSpec d).toBits) where
  seg := hseg
  k := hk
  events := hev
  step := payloadStep_number arena hal hInv hklt hdec hbyte hb hwf hlex hpre hk hev

/-- **A plain string's revolution.** -/
theorem payloadRevolution_string_plain {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C Cd : WalkCarry G} {s sd : State} {p : Nat} (arena : List UInt8)
    (hal : WalkAlign G t) (hInv : WalkInv G C s) (hklt : C.k < G.nep)
    {v : JSON.Value} (hdec : decodeTape t = some v) (hbyte : entryByte G C.k = 0x22)
    {sp : Span} (htokC : t.tokens[C.k]? = some (.string sp))
    {key : Bool} {len : Nat}
    (hspan : ∀ sp' : Span, t.tokens[C.k]? = some (.string sp') →
      sp'.stop = sp'.start + 2 + len)
    (hbody : ∀ sp' : Span, t.tokens[C.k]? = some (.string sp') → ∀ cs : List Nat,
      bodyCodePoints G.bs sp' = some cs →
      escapeCodePoints ((G.bs.drop (sp'.start + 1)).take len) = some cs)
    (hpre : WalkTracePrefix G arena t C)
    (hseg : WalkScope.WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p)
    (hk : Cd.k = C.k)
    (hev : Cd.events = C.events ++ [EventRecord.str key len (plainSpan (sp.start + 1))]) :
    WalkPayloadRevolution G arena t C s Cd sd p
      (EventRecord.str key len (plainSpan (sp.start + 1))) where
  seg := hseg
  k := hk
  events := hev
  step := payloadStep_string_plain arena hal hInv hklt hdec hbyte htokC hspan hbody hpre
    hk hev

/-- **An arena string's revolution.** -/
theorem payloadRevolution_string_arena {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C Cd : WalkCarry G} {s sd : State} {p : Nat} (arena : List UInt8)
    (hal : WalkAlign G t) (hInv : WalkInv G C s) (hklt : C.k < G.nep)
    {v : JSON.Value} (hdec : decodeTape t = some v) (hbyte : entryByte G C.k = 0x22)
    {key : Bool} {len off : Nat}
    (hlen : ∀ sp : Span, t.tokens[C.k]? = some (.string sp) → sp.start + 2 ≤ sp.stop)
    (hoff : off < 2 ^ 63)
    (harena : ∀ sp : Span, t.tokens[C.k]? = some (.string sp) → ∀ cs : List Nat,
      bodyCodePoints G.bs sp = some cs →
      escapeCodePoints ((arena.drop off).take len) = some cs)
    (hpre : WalkTracePrefix G arena t C)
    (hseg : WalkScope.WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd p)
    (hk : Cd.k = C.k)
    (hev : Cd.events = C.events ++ [EventRecord.str key len off]) :
    WalkPayloadRevolution G arena t C s Cd sd p (EventRecord.str key len off) where
  seg := hseg
  k := hk
  events := hev
  step := payloadStep_string_arena arena hal hInv hklt hdec hbyte hlen hoff harena hpre
    hk hev

/-! ### The payload documents

The separator documents with their payload revolutions proved.  `[1,2]` is the number's
document and `["ab","cd"]` the string's, in the plain and in the arena form.  Each
theorem fixes the document's bytes and the entry stream's positions, derives every byte
the containers and the payloads read, proves the numeral's decomposition of its own span
(`decimalOne`, `decimalTwo`), and leaves exactly what the row cannot supply: the tape's
acceptance, the walk's alignment, the opener's and the separator's carries, the two
heads' invariants, the two arms' `WalkSegment`s with the merge carries they end at.
The plain string row derives its raw-body read-back from the document's bytes at the
token's span; the arena row's slice read-back is a premise at that span, and its
literal instance proves it from `stringDocumentArena`. -/

/-- The document `[1,2]`'s bytes. -/
def numberDocumentBytes : List UInt8 := [0x5B, 0x31, 0x2C, 0x32, 0x5D]

/-- The document `["ab","cd"]`'s bytes. -/
def stringDocumentBytes : List UInt8 :=
  [0x5B, 0x22, 0x61, 0x62, 0x22, 0x2C, 0x22, 0x63, 0x64, 0x22, 0x5D]

/-- The document `["ab","cd"]`'s arena contents: its two decoded bodies, `"ab"` then
`"cd"`, at the offsets the literal record names.  Either body would sit here if the
walk had decoded it; this is the list the literal arena row's slices read. -/
def stringDocumentArena : List UInt8 := [0x61, 0x62, 0x63, 0x64]

/-- `1`'s decomposition: a one-digit `int` with no fraction and no exponent. -/
def decimalOne : Decimal := ⟨false, ByteString.cons 0x31 ByteString.empty, none, none⟩

/-- `2`'s decomposition. -/
def decimalTwo : Decimal := ⟨false, ByteString.cons 0x32 ByteString.empty, none, none⟩

/-- **`1`'s decomposition is the grammar's.** -/
theorem decimalOne_wellFormed : decimalOne.wellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · exact IntPart.lead (b := 0x31) (bs := ByteString.empty) (by decide) (by decide)
      Digits0.nil
  · intro fs h
    simp only [decimalOne] at h
    cases h
  · intro s ds h
    simp only [decimalOne] at h
    cases h

/-- **`2`'s decomposition is the grammar's.** -/
theorem decimalTwo_wellFormed : decimalTwo.wellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · exact IntPart.lead (b := 0x32) (bs := ByteString.empty) (by decide) (by decide)
      Digits0.nil
  · intro fs h
    simp only [decimalTwo] at h
    cases h
  · intro s ds h
    simp only [decimalTwo] at h
    cases h

/-- **`1`'s lexeme is its one byte.** -/
theorem decimalOne_lexeme : decimalOne.lexeme.data.toList = [0x31] := by
  simp only [decimalOne, Decimal.lexeme, Decimal.body, Decimal.signBytes_false,
    ByteString.empty_append, ByteString.data_toList_cons, ByteString.data_toList_empty]

/-- **`2`'s lexeme is its one byte.** -/
theorem decimalTwo_lexeme : decimalTwo.lexeme.data.toList = [0x32] := by
  simp only [decimalTwo, Decimal.lexeme, Decimal.body, Decimal.signBytes_false,
    ByteString.empty_append, ByteString.data_toList_cons, ByteString.data_toList_empty]

/-- **The document `[1,2]`'s row, its payloads proved.**  Both entries are numbers: at
each head the byte is a digit and the arm's segment reaches the merge with the numeral's
record appended.  The containers' records, the separator's silence and the row are
`row_commaBracket`'s; the span's lexeme and the decomposition are the document's. -/
theorem row_numberDocument {m0 : Mem} {G : WalkGeom m0} {t : Tape} {arena : List UInt8}
    {C₀ C₁ C₃ Cd₁ Cd₂ : WalkCarry G} {s₁ s₃ sd₁ sd₂ : State} {p₁ p₂ : Nat}
    {v : JSON.Value}
    (hal : WalkAlign G t) (hspans : spansWellFormed t = true)
    (hbs : G.bs = numberDocumentBytes) (hent : G.ent = [0, 1, 2, 3, 4])
    (htokens : t.tokens = [.punct .openBracket ⟨0, 1⟩, .number ⟨1, 2⟩,
      .punct .comma ⟨2, 3⟩, .number ⟨3, 4⟩, .punct .closeBracket ⟨4, 5⟩])
    (hdec : decodeTape t = some v)
    (hpre₀ : WalkTracePrefix G arena t C₀) (hk₀ : C₀.k = 0)
    (hk₁ : C₁.k = C₀.k + 1) (hev₁ : C₁.events = C₀.events ++ [EventRecord.tag 3])
    (hInv₁ : WalkInv G C₁ s₁)
    (hseg₁ : WalkScope.WalkSegment (stage2Calls stage2SubCalls) G C₁ s₁ Cd₁ sd₁ p₁)
    (hkc₁ : Cd₁.k = C₁.k)
    (hevc₁ : Cd₁.events = C₁.events ++ [EventRecord.number (strtodSpec decimalOne).toBits])
    (hk₃ : C₃.k = C₁.k + 2)
    (hev₃ : C₃.events = C₁.events ++ [EventRecord.number (strtodSpec decimalOne).toBits])
    (hInv₃ : WalkInv G C₃ s₃)
    (hseg₂ : WalkScope.WalkSegment (stage2Calls stage2SubCalls) G C₃ s₃ Cd₂ sd₂ p₂)
    (hkc₂ : Cd₂.k = C₃.k)
    (hevc₂ : Cd₂.events = C₃.events ++ [EventRecord.number (strtodSpec decimalTwo).toBits]) :
    WalkTraceRow G.bs arena t
      ([EventRecord.tag 3, EventRecord.number (strtodSpec decimalOne).toBits,
        EventRecord.number (strtodSpec decimalTwo).toBits,
        EventRecord.tag 4] : List EventRecord) := by
  let C₂ : WalkCarry G := { Cd₁ with k := Cd₁.k + 1 }
  let C₄ : WalkCarry G := { Cd₂ with k := Cd₂.k + 1 }
  have hk5 : G.nep = 5 := by simp [hal.tokens_length, htokens]
  have hC₂k : C₂.k = C₁.k + 1 := by
    show Cd₁.k + 1 = C₁.k + 1
    rw [hkc₁]
  have hC₄k : C₄.k = C₃.k + 1 := by
    show Cd₂.k + 1 = C₃.k + 1
    rw [hkc₂]
  -- the opener's byte, its record, and the correspondence at the first payload
  have hbyteo : entryByte G C₀.k = 0x5B := by
    have hk : C₀.k = 0 := hk₀
    simp only [entryByte, entryPos, hk, hent, hbs]
    decide
  have hpre₁ : WalkTracePrefix G arena t C₁ := by
    have htok₀ : t.tokens[C₀.k]? = some (.punct .openBracket ⟨0, 1⟩) := by
      rw [hk₀, htokens]
      rfl
    have hlt₀ : C₀.k < G.nep := by
      rw [hk₀, hk5]
      decide
    exact WalkTracePrefix.emit_advance hpre₀ htok₀
      (headTokenRecord_punct hal hlt₀ hspans arena (Or.inr (Or.inr (Or.inl rfl)))
        htok₀ hbyteo) hk₁ hev₁
  -- the first numeral
  have hbyte₁ : entryByte G C₁.k = 0x31 := by
    have hk : C₁.k = 1 := by omega
    simp only [entryByte, entryPos, hk, hent, hbs]
    decide
  have hlex₁ : ∀ sp : Span, t.tokens[C₁.k]? = some (.number sp) →
      decimalOne.lexeme.data.toList = (G.bs.drop sp.start).take (sp.stop - sp.start) := by
    intro sp hsp
    have hk : C₁.k = 1 := by omega
    rw [hk, htokens] at hsp
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
      Token.number.injEq] at hsp
    subst hsp
    rw [decimalOne_lexeme, hbs]
    rfl
  have hrev₁ := payloadRevolution_number arena hal hInv₁ (by rw [hk5]; omega) hdec hbyte₁
    (Or.inr (by decide)) decimalOne_wellFormed hlex₁ hpre₁ hseg₁ hkc₁ hevc₁
  have hpay₁ : WalkPayloadStep G arena t C₁ C₂
      (EventRecord.number (strtodSpec decimalOne).toBits) := hrev₁.step
  -- the separator's own step, and the correspondence at the second payload
  have hC₂e : C₂.events = C₁.events ++ [EventRecord.number (strtodSpec decimalOne).toBits] :=
    hevc₁
  have htok₂ : t.tokens[C₂.k]? = some (.punct .comma ⟨2, 3⟩) := by
    have hk : C₂.k = 2 := by omega
    rw [hk, htokens]
    rfl
  have hevS : C₃.events = C₂.events := by rw [hev₃, hC₂e]
  have hstepS : WalkTraceStep G arena t C₂ C₃ :=
    WalkTraceStep.separator hpay₁.1.trace htok₂ (Or.inl rfl) (by omega) hevS
  have hpre₃ : WalkTracePrefix G arena t C₃ := hstepS.trace
  -- the second numeral
  have hbyte₂ : entryByte G C₃.k = 0x32 := by
    have hk : C₃.k = 3 := by omega
    simp only [entryByte, entryPos, hk, hent, hbs]
    decide
  have hlex₂ : ∀ sp : Span, t.tokens[C₃.k]? = some (.number sp) →
      decimalTwo.lexeme.data.toList = (G.bs.drop sp.start).take (sp.stop - sp.start) := by
    intro sp hsp
    have hk : C₃.k = 3 := by omega
    rw [hk, htokens] at hsp
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
      Token.number.injEq] at hsp
    subst hsp
    rw [decimalTwo_lexeme, hbs]
    rfl
  have hrev₂ := payloadRevolution_number arena hal hInv₃ (by rw [hk5]; omega) hdec hbyte₂
    (Or.inr (by decide)) decimalTwo_wellFormed hlex₂ hpre₃ hseg₂ hkc₂ hevc₂
  have hpay₂ : WalkPayloadStep G arena t C₃ C₄
      (EventRecord.number (strtodSpec decimalTwo).toBits) := hrev₂.step
  -- the closer's byte, and the row
  have hbytec : entryByte G C₄.k = 0x5D := by
    have hk : C₄.k = 4 := by omega
    simp only [entryByte, entryPos, hk, hent, hbs]
    decide
  exact row_commaBracket (Cm := { C₄ with events := C₄.events ++ [EventRecord.tag 4] })
    hal hspans htokens hpre₀ hk₀ hbyteo hk₁ hev₁ hpay₁ (by omega) hevS hpay₂ hbytec
    rfl rfl

/-! ### The string rows at the staged entry stream

`["ab","cd"]`'s entries are `[0, 1, 4, 5, 6, 9, 10]` — seven lanes for five tokens,
each string's closing quote a lane of its own (`WalkAlignQuoted`).  The walk's carry
is at an entry while its trace is indexed by tokens, so the two indices travel side by
side: `WalkTracePrefixAt` is the trace correspondence with the token count named, and
each step below moves the entry index by one or two and the token index by one.

The string arm's readings are the entry stream's: `close = lane k + 1`, the body extent
`close - idxprom - 1` (`WalkAlignQuoted.stringExtent`), and the record's offset `p + 1`
— the arm's `%sub260.i` and `(p + 1) | 1 << 63` (`kernel/json/stage2.c`'s quote arm).
At this document those are `4 - 1 - 1 = 2` and `9 - 6 - 1 = 2`, the extents the two
records name, and the offsets `2` and `7`.  The body's read-back stays the arm's
premise, as the string record's statement says.

The row's steps are its premises': the opener's one-entry emit, each string's
two-entry back edge (the merge's kept index and one appended record), the comma's
silent advance and the closer's one-entry emit.  `stringPath_seg` supplies those
carries from the walk; the row reads them as the equations they leave, which is what
a row is about.
-/

/-- **The correspondence at a carry, indexed by the number of tokens consumed.**  The
records emitted so far are the record-carrying tokens before `j`.  `WalkTracePrefix`
is this at `j = C.k`, which is the token-start stream's reading; a quote-inclusive
stream's carry counts lanes, so the string rows name the token count beside it. -/
def WalkTracePrefixAt {m0 : Mem} (G : WalkGeom m0) (arena : List UInt8) (t : Tape)
    (C : WalkCarry G) (j : Nat) : Prop :=
  List.Forall₂ (TokenRecord G.bs arena) C.events (Token.recordTokens t.tokens j)

namespace WalkTracePrefixAt

/-- The seed: no tokens consumed and no records. -/
theorem of_seed {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C : WalkCarry G} {j : Nat} (hj : j = 0) (hev : C.events = []) :
    WalkTracePrefixAt G arena t C j := by
  unfold WalkTracePrefixAt
  rw [hj, hev]
  exact List.Forall₂.nil

/-- The carry form, read at the carry's own index. -/
theorem of_prefix {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C : WalkCarry G} (h : WalkTracePrefix G arena t C) :
    WalkTracePrefixAt G arena t C C.k := h

/-- The carry form, from the indexed one at the carry's index. -/
theorem to_prefix {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C : WalkCarry G} (h : WalkTracePrefixAt G arena t C C.k) :
    WalkTracePrefix G arena t C := h

/-- The correspondence at a carry with the same records. -/
theorem congr {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C C' : WalkCarry G} {j j' : Nat} (h : WalkTracePrefixAt G arena t C j)
    (hj : j' = j) (hev : C'.events = C.events) : WalkTracePrefixAt G arena t C' j' := by
  unfold WalkTracePrefixAt at *
  rw [hj, hev]
  exact h

/-- The record count. -/
theorem length {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C : WalkCarry G} {j : Nat} (h : WalkTracePrefixAt G arena t C j) :
    C.events.length = (Token.recordTokens t.tokens j).length := by
  unfold WalkTracePrefixAt at h
  exact forall₂_length h

/-- **An emitting entry's step**: one record, related to the token at the token index,
and the token index one on.  The *entry* index is the caller's — a string's arm moves
it by two — because the trace counts tokens and not lanes. -/
theorem emit_advance {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C C' : WalkCarry G} {j j' : Nat} {tok : Token} {r : EventRecord}
    (h : WalkTracePrefixAt G arena t C j) (htok : t.tokens[j]? = some tok)
    (hrec : TokenRecord G.bs arena r tok) (hj : j' = j + 1)
    (hev : C'.events = C.events ++ [r]) : WalkTracePrefixAt G arena t C' j' := by
  obtain ⟨hc, hd⟩ := hrec.not_separator
  unfold WalkTracePrefixAt at h ⊢
  rw [hj, hev, Token.recordTokens_succ_of_record htok hc hd]
  exact forall₂_append h (List.Forall₂.cons hrec List.Forall₂.nil)

/-- **A separator's step**: no record, the token index one on. -/
theorem advance_separator {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C C' : WalkCarry G} {j j' : Nat} {p : Punct} {s : Span}
    (h : WalkTracePrefixAt G arena t C j) (htok : t.tokens[j]? = some (.punct p s))
    (hp : p = .comma ∨ p = .colon) (hj : j' = j + 1) (hev : C'.events = C.events) :
    WalkTracePrefixAt G arena t C' j' := by
  unfold WalkTracePrefixAt at h ⊢
  rw [hj, hev, Token.recordTokens_succ_of_separator htok hp]
  exact h

/-- **The row at the end of the tokens.** -/
theorem toTraceRow {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8} {t : Tape}
    {C : WalkCarry G} {j : Nat} (h : WalkTracePrefixAt G arena t C j)
    (hj : j = t.tokens.length) : WalkTraceRow G.bs arena t C.events := by
  unfold WalkTracePrefixAt at h
  unfold WalkTraceRow
  rw [hj, Token.recordTokens_full] at h
  exact h

end WalkTracePrefixAt

/-- **A string entry's step.**  The arm's merge keeps the entry index and appends its
one record; the header's back edge then takes `%inc208.i` and moves the entry index by
two, while the token index moves by one.  This is the step the quote lanes make
different from a one-entry arm's. -/
theorem WalkTracePrefixAt.emit_two {m0 : Mem} {G : WalkGeom m0} {arena : List UInt8}
    {t : Tape} {C Cd C' : WalkCarry G} {j : Nat} {tok : Token} {r : EventRecord}
    (h : WalkTracePrefixAt G arena t C j) (htok : t.tokens[j]? = some tok)
    (hrec : TokenRecord G.bs arena r tok)
    (hkC : Cd.k = C.k) (hevC : Cd.events = C.events ++ [r])
    (hk' : C'.k = Cd.k + 2) (hev' : C'.events = Cd.events) :
    WalkTracePrefixAt G arena t C' (j + 1) ∧ C'.k = C.k + 2 := by
  refine ⟨WalkTracePrefixAt.emit_advance (j' := j + 1) h htok hrec rfl ?_, by omega⟩
  rw [hev', hevC]

/-- **The document `["ab","cd"]`'s row, its payloads plain, at the staged stream.**
The carries are at entries `0, 1, 3, 4, 6, 7` and the token counts `0, 1, 2, 3, 4, 5`;
each string's record names its body by the arm's own readings, `close - start - 1` for
the length and `start + 1` for the offset.

Both raw-body read-backs are derived from `hbs` at the tokens' spans (`⟨1,5⟩` and
`⟨6,10⟩`), so the row has no payload premise.  The earlier statement took them
quantified over every span, which `bodyCodePoints` makes false at spans that are not
tokens: `⟨3,5⟩` reads `some []` while the document's two bytes from `4` are `[34,44]`. -/
theorem row_stringPlainDocument {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {arena : List UInt8} {C₀ C₁ C₂ C₃ C₄ C₅ Cd₁ Cd₂ : WalkCarry G}
    {v : JSON.Value}
    (hal : WalkAlignQuoted G t)
    (hbs : G.bs = stringDocumentBytes) (hent : G.ent = [0, 1, 4, 5, 6, 9, 10])
    (htokens : t.tokens = [.punct .openBracket ⟨0, 1⟩, .string ⟨1, 5⟩,
      .punct .comma ⟨5, 6⟩, .string ⟨6, 10⟩, .punct .closeBracket ⟨10, 11⟩])
    (hdec : decodeTape t = some v)
    (hpre₀ : WalkTracePrefix G arena t C₀) (hk₀ : C₀.k = 0)
    (hk₁ : C₁.k = C₀.k + 1) (hev₁ : C₁.events = C₀.events ++ [EventRecord.tag 3])
    (hevc₁ : Cd₁.events = C₁.events ++
      [EventRecord.str false (entryPos G (C₁.k + 1) - entryPos G C₁.k - 1)
        (plainSpan (entryPos G C₁.k + 1))])
    (hkc₁ : Cd₁.k = C₁.k)
    (hk₂ : C₂.k = Cd₁.k + 2) (hev₂ : C₂.events = Cd₁.events)
    (hk₃ : C₃.k = C₂.k + 1) (hev₃ : C₃.events = C₂.events)
    (hevc₂ : Cd₂.events = C₃.events ++
      [EventRecord.str false (entryPos G (C₃.k + 1) - entryPos G C₃.k - 1)
        (plainSpan (entryPos G C₃.k + 1))])
    (hkc₂ : Cd₂.k = C₃.k)
    (hk₄ : C₄.k = Cd₂.k + 2) (hev₄ : C₄.events = Cd₂.events)
    (hk₅ : C₅.k = C₄.k + 1) (hev₅ : C₅.events = C₄.events ++ [EventRecord.tag 4]) :
    WalkTraceRow G.bs arena t
      ([EventRecord.tag 3, EventRecord.str false 2 (plainSpan 2),
        EventRecord.str false 2 (plainSpan 7), EventRecord.tag 4] : List EventRecord) := by
  -- the entries the carries stand at, from the four index equations
  have hk₁v : C₁.k = 1 := by omega
  have hk₂v : C₂.k = 3 := by omega
  have hk₃v : C₃.k = 4 := by omega
  have hk₄v : C₄.k = 6 := by omega
  have hk₅v : C₅.k = 7 := by omega
  -- the entry stream's positions, and the arm's two readings at each string
  have hp₁ : entryPos G C₁.k = 1 := by simp [entryPos, hk₁v, hent]
  have hp₁' : entryPos G (C₁.k + 1) = 4 := by
    have hk : C₁.k + 1 = 2 := by omega
    simp [entryPos, hk, hent]
  have hlen₁ : entryPos G (C₁.k + 1) - entryPos G C₁.k - 1 = 2 := by
    rw [hp₁', hp₁]
  have hp₃ : entryPos G C₃.k = 6 := by simp [entryPos, hk₃v, hent]
  have hp₃' : entryPos G (C₃.k + 1) = 9 := by
    have hk : C₃.k + 1 = 5 := by omega
    simp [entryPos, hk, hent]
  have hlen₂ : entryPos G (C₃.k + 1) - entryPos G C₃.k - 1 = 2 := by
    rw [hp₃', hp₃]
  -- the raw-body read-backs, at the token's own span: `hbs` fixes the bytes, so the
  -- document's scan and its body slice are both decided.  (The earlier statement
  -- quantified them over every span, which is false at spans that are not tokens —
  -- `⟨3,5⟩` reads `some []` against the two bytes from `4`, `[34,44]`.)
  have hbody₁ : ∀ cs : List Nat, bodyCodePoints G.bs ⟨1, 5⟩ = some cs →
      escapeCodePoints ((G.bs.drop 2).take 2) = some cs := by
    intro cs hcs
    rw [hbs] at hcs
    have h : bodyCodePoints stringDocumentBytes ⟨1, 5⟩ = some [97, 98] := by decide
    rw [h] at hcs
    have hcs' : ([97, 98] : List Nat) = cs := Option.some.inj hcs
    subst cs
    rw [hbs]
    decide
  have hbody₂ : ∀ cs : List Nat, bodyCodePoints G.bs ⟨6, 10⟩ = some cs →
      escapeCodePoints ((G.bs.drop 7).take 2) = some cs := by
    intro cs hcs
    rw [hbs] at hcs
    have h : bodyCodePoints stringDocumentBytes ⟨6, 10⟩ = some [99, 100] := by decide
    rw [h] at hcs
    have hcs' : ([99, 100] : List Nat) = cs := Option.some.inj hcs
    subst cs
    rw [hbs]
    decide
  -- the seed, and the opener's step
  have hs₀ : WalkTracePrefixAt G arena t C₀ 0 :=
    (WalkTracePrefixAt.of_prefix hpre₀).congr hk₀.symm rfl
  have htok₀ : t.tokens[0]? = some (.punct .openBracket ⟨0, 1⟩) := by rw [htokens]; rfl
  have hrec₀ : TokenRecord G.bs arena (.tag 3) (.punct .openBracket ⟨0, 1⟩) := by
    rw [hbs]
    exact TokenRecord.openBracket (by decide) (by decide)
  have hpre₁ : WalkTracePrefixAt G arena t C₁ 1 :=
    WalkTracePrefixAt.emit_advance (j' := 1) hs₀ htok₀ hrec₀ rfl hev₁
  -- the first string: the arm's record, and its two-entry back edge
  have hmem₁ : Token.string ⟨1, 5⟩ ∈ t.tokens := by rw [htokens]; simp
  obtain ⟨cs₁, hcode₁⟩ := tape_bodyCodePoints hdec hal.input hmem₁
  have hrec₁ : TokenRecord G.bs arena
      (EventRecord.str false (entryPos G (C₁.k + 1) - entryPos G C₁.k - 1)
        (plainSpan 2)) (.string ⟨1, 5⟩) := by
    refine tokenRecord_string_plain_of_tape (s := ⟨1, 5⟩) (key := false) (arena := arena)
      (len := entryPos G (C₁.k + 1) - entryPos G C₁.k - 1) hdec hal.input hmem₁ ?_ hcode₁ ?_
    · rw [hp₁', hp₁]
    · rw [hlen₁]
      exact hbody₁ cs₁ hcode₁
  have hevc₁' : Cd₁.events = C₁.events ++
      [EventRecord.str false (entryPos G (C₁.k + 1) - entryPos G C₁.k - 1) (plainSpan 2)] := by
    rw [hevc₁, hp₁]
  have htok₁ : t.tokens[1]? = some (.string ⟨1, 5⟩) := by rw [htokens]; rfl
  obtain ⟨hpre₂, -⟩ :=
    WalkTracePrefixAt.emit_two hpre₁ htok₁ hrec₁ hkc₁ hevc₁' hk₂ hev₂
  -- the comma's silent advance
  have htok₂ : t.tokens[2]? = some (.punct .comma ⟨5, 6⟩) := by rw [htokens]; rfl
  have hpre₃ : WalkTracePrefixAt G arena t C₃ 3 :=
    WalkTracePrefixAt.advance_separator (j' := 3) hpre₂ htok₂ (Or.inl rfl) rfl hev₃
  -- the second string
  have hmem₂ : Token.string ⟨6, 10⟩ ∈ t.tokens := by rw [htokens]; simp
  obtain ⟨cs₂, hcode₂⟩ := tape_bodyCodePoints hdec hal.input hmem₂
  have hrec₂ : TokenRecord G.bs arena
      (EventRecord.str false (entryPos G (C₃.k + 1) - entryPos G C₃.k - 1)
        (plainSpan 7)) (.string ⟨6, 10⟩) := by
    refine tokenRecord_string_plain_of_tape (s := ⟨6, 10⟩) (key := false) (arena := arena)
      (len := entryPos G (C₃.k + 1) - entryPos G C₃.k - 1) hdec hal.input hmem₂ ?_ hcode₂ ?_
    · rw [hp₃', hp₃]
    · rw [hlen₂]
      exact hbody₂ cs₂ hcode₂
  have hevc₂' : Cd₂.events = C₃.events ++
      [EventRecord.str false (entryPos G (C₃.k + 1) - entryPos G C₃.k - 1) (plainSpan 7)] := by
    rw [hevc₂, hp₃]
  have htok₃ : t.tokens[3]? = some (.string ⟨6, 10⟩) := by rw [htokens]; rfl
  obtain ⟨hpre₄, -⟩ :=
    WalkTracePrefixAt.emit_two hpre₃ htok₃ hrec₂ hkc₂ hevc₂' hk₄ hev₄
  -- the closer's step, and the row at the end of the tokens
  have htok₄ : t.tokens[4]? = some (.punct .closeBracket ⟨10, 11⟩) := by rw [htokens]; rfl
  have hrec₄ : TokenRecord G.bs arena (.tag 4) (.punct .closeBracket ⟨10, 11⟩) := by
    rw [hbs]
    exact TokenRecord.closeBracket (by decide) (by decide)
  have hpre₅ : WalkTracePrefixAt G arena t C₅ 5 :=
    WalkTracePrefixAt.emit_advance (j' := 5) hpre₄ htok₄ hrec₄ rfl hev₅
  have hrow : WalkTraceRow G.bs arena t C₅.events :=
    WalkTracePrefixAt.toTraceRow hpre₅ (by rw [htokens]; rfl)
  -- the trace is the four records, at the arms' own readings
  have hC₅ : C₅.events = [EventRecord.tag 3, EventRecord.str false 2 (plainSpan 2),
      EventRecord.str false 2 (plainSpan 7), EventRecord.tag 4] := by
    rw [hev₅, hev₄, hevc₂', hev₃, hev₂, hevc₁', hev₁,
      WalkTracePrefix.events_eq_nil hpre₀ hk₀, hlen₂, hlen₁]
    simp
  rw [hC₅] at hrow
  exact hrow

set_option linter.unusedVariables false in
/-- **The document `["ab","cd"]`'s row, its payloads in the arena, at the staged
stream.**  The records' lengths and offsets are the arms' own readings — the decoded
length `%outn.i` receives and the arena base `%z.val36` (`f.A.toNat`) — so the row
takes them as parameters `L₁`/`O₁` and `L₂`/`O₂` beside the escape unit's two
read-backs: the arena slice at the offset reads as the token's code points, and the
offset is below `2 ^ 63`.  Those are the counterparts of the plain row's raw-body
read-back and the number row's `f.ev`: what the walk cannot supply, because the body
is the callee's.

**The read-back is at the token's span, not over every span.**  `bodyCodePoints` is a
function of the document alone and scans from `sp.start + 1`, so it returns `some` at
spans that are not tokens: at `⟨3,5⟩` the document's scan is `some []` while the two
bytes from `4` read `[34,44]`, so a read-back quantified over all spans is false and
would state nothing.  The token's spans are the ones the row fixes (`⟨1,5⟩` and
`⟨6,10⟩`), and they are the ones every consumer instantiates (`tape_bodyCodePoints`).

**Why the fields are parameters and not the literal extent.**  The earlier statement
fixed both lengths at the entry extent and the offsets at `0` and `2`, and no walk
satisfies it: `LeafBlock29` selects the write-back arm only when the body's in-body
escape list is non-empty (`stage2StringBody`), and every escape shortens the decoded
length, so `L < extent`; and the record's offset is the arena's `%z.val36`, which
`WalkInv.log_alen` bounds below only by `G.ndst0`, not by `0`.  The fixed values are
the literal arm's instance, which the plain row states; they are kept as
`row_stringArenaDocument_literal` beside this row rather than as the row itself.

The entry positions and the carries' index equations are kept as the document's
identity, which the arm supplies; the proof no longer reads them, because the
records' fields are parameters rather than the lanes' extent. -/
theorem row_stringArenaDocument {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {arena : List UInt8} {C₀ C₁ C₂ C₃ C₄ C₅ Cd₁ Cd₂ : WalkCarry G}
    {v : JSON.Value} {L₁ O₁ L₂ O₂ : Nat}
    (hal : WalkAlignQuoted G t)
    (hbs : G.bs = stringDocumentBytes) (hent : G.ent = [0, 1, 4, 5, 6, 9, 10])
    (htokens : t.tokens = [.punct .openBracket ⟨0, 1⟩, .string ⟨1, 5⟩,
      .punct .comma ⟨5, 6⟩, .string ⟨6, 10⟩, .punct .closeBracket ⟨10, 11⟩])
    (hdec : decodeTape t = some v)
    (hpre₀ : WalkTracePrefix G arena t C₀) (hk₀ : C₀.k = 0)
    (hk₁ : C₁.k = C₀.k + 1) (hev₁ : C₁.events = C₀.events ++ [EventRecord.tag 3])
    (hevc₁ : Cd₁.events = C₁.events ++ [EventRecord.str false L₁ O₁])
    (hkc₁ : Cd₁.k = C₁.k)
    (hk₂ : C₂.k = Cd₁.k + 2) (hev₂ : C₂.events = Cd₁.events)
    (hoff₁ : O₁ < 2 ^ 63)
    (harena₁ : ∀ cs : List Nat, bodyCodePoints G.bs ⟨1, 5⟩ = some cs →
      escapeCodePoints ((arena.drop O₁).take L₁) = some cs)
    (hk₃ : C₃.k = C₂.k + 1) (hev₃ : C₃.events = C₂.events)
    (hevc₂ : Cd₂.events = C₃.events ++ [EventRecord.str false L₂ O₂])
    (hkc₂ : Cd₂.k = C₃.k)
    (hk₄ : C₄.k = Cd₂.k + 2) (hev₄ : C₄.events = Cd₂.events)
    (hoff₂ : O₂ < 2 ^ 63)
    (harena₂ : ∀ cs : List Nat, bodyCodePoints G.bs ⟨6, 10⟩ = some cs →
      escapeCodePoints ((arena.drop O₂).take L₂) = some cs)
    (hk₅ : C₅.k = C₄.k + 1) (hev₅ : C₅.events = C₄.events ++ [EventRecord.tag 4]) :
    WalkTraceRow G.bs arena t
      ([EventRecord.tag 3, EventRecord.str false L₁ O₁,
        EventRecord.str false L₂ O₂, EventRecord.tag 4] : List EventRecord) := by
  have hs₀ : WalkTracePrefixAt G arena t C₀ 0 :=
    (WalkTracePrefixAt.of_prefix hpre₀).congr hk₀.symm rfl
  have htok₀ : t.tokens[0]? = some (.punct .openBracket ⟨0, 1⟩) := by rw [htokens]; rfl
  have hrec₀ : TokenRecord G.bs arena (.tag 3) (.punct .openBracket ⟨0, 1⟩) := by
    rw [hbs]
    exact TokenRecord.openBracket (by decide) (by decide)
  have hpre₁ : WalkTracePrefixAt G arena t C₁ 1 :=
    WalkTracePrefixAt.emit_advance (j' := 1) hs₀ htok₀ hrec₀ rfl hev₁
  -- the first string: the span holds both quotes, and the arena's slice is its body
  have hmem₁ : Token.string ⟨1, 5⟩ ∈ t.tokens := by rw [htokens]; simp
  obtain ⟨cs₁, hcode₁⟩ := tape_bodyCodePoints hdec hal.input hmem₁
  have hrec₁ : TokenRecord G.bs arena (EventRecord.str false L₁ O₁)
        (.string ⟨1, 5⟩) := by
    refine tokenRecord_string_arena_of_tape (s := ⟨1, 5⟩) (key := false)
      (off := O₁) (len := L₁) hdec hal.input hmem₁ ?_ hoff₁ hcode₁ ?_
    · decide
    · exact harena₁ cs₁ hcode₁
  have htok₁ : t.tokens[1]? = some (.string ⟨1, 5⟩) := by rw [htokens]; rfl
  obtain ⟨hpre₂, -⟩ :=
    WalkTracePrefixAt.emit_two hpre₁ htok₁ hrec₁ hkc₁ hevc₁ hk₂ hev₂
  have htok₂ : t.tokens[2]? = some (.punct .comma ⟨5, 6⟩) := by rw [htokens]; rfl
  have hpre₃ : WalkTracePrefixAt G arena t C₃ 3 :=
    WalkTracePrefixAt.advance_separator (j' := 3) hpre₂ htok₂ (Or.inl rfl) rfl hev₃
  have hmem₂ : Token.string ⟨6, 10⟩ ∈ t.tokens := by rw [htokens]; simp
  obtain ⟨cs₂, hcode₂⟩ := tape_bodyCodePoints hdec hal.input hmem₂
  have hrec₂ : TokenRecord G.bs arena (EventRecord.str false L₂ O₂)
        (.string ⟨6, 10⟩) := by
    refine tokenRecord_string_arena_of_tape (s := ⟨6, 10⟩) (key := false)
      (off := O₂) (len := L₂) hdec hal.input hmem₂ ?_ hoff₂ hcode₂ ?_
    · decide
    · exact harena₂ cs₂ hcode₂
  have htok₃ : t.tokens[3]? = some (.string ⟨6, 10⟩) := by rw [htokens]; rfl
  obtain ⟨hpre₄, -⟩ :=
    WalkTracePrefixAt.emit_two hpre₃ htok₃ hrec₂ hkc₂ hevc₂ hk₄ hev₄
  have htok₄ : t.tokens[4]? = some (.punct .closeBracket ⟨10, 11⟩) := by rw [htokens]; rfl
  have hrec₄ : TokenRecord G.bs arena (.tag 4) (.punct .closeBracket ⟨10, 11⟩) := by
    rw [hbs]
    exact TokenRecord.closeBracket (by decide) (by decide)
  have hpre₅ : WalkTracePrefixAt G arena t C₅ 5 :=
    WalkTracePrefixAt.emit_advance (j' := 5) hpre₄ htok₄ hrec₄ rfl hev₅
  have hrow : WalkTraceRow G.bs arena t C₅.events :=
    WalkTracePrefixAt.toTraceRow hpre₅ (by rw [htokens]; rfl)
  have hC₅ : C₅.events = [EventRecord.tag 3, EventRecord.str false L₁ O₁,
      EventRecord.str false L₂ O₂, EventRecord.tag 4] := by
    rw [hev₅, hev₄, hevc₂, hev₃, hev₂, hevc₁, hev₁,
      WalkTracePrefix.events_eq_nil hpre₀ hk₀]
    simp
  rw [hC₅] at hrow
  exact hrow

/-- **The literal form of the arena row.**  The one instance the document's own
readings give when its bodies are recorded as arena slices: both lengths are the
entry extent (`2`) and both offsets are the arena's opening position (`0`, then `2`),
with the arena's contents fixed to the document's two decoded bodies.  Both offsets
are decided below `2 ^ 63` and both read-backs are decided at `stringDocumentArena` —
`[97,98]` at `(2,0)` and `[99,100]` at `(2,2)` — so this row has no payload premise at
all.  It is the literal instance of `row_stringArenaDocument`, not the arena row
itself. -/
theorem row_stringArenaDocument_literal {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C₀ C₁ C₂ C₃ C₄ C₅ Cd₁ Cd₂ : WalkCarry G} {v : JSON.Value}
    (hal : WalkAlignQuoted G t)
    (hbs : G.bs = stringDocumentBytes) (hent : G.ent = [0, 1, 4, 5, 6, 9, 10])
    (htokens : t.tokens = [.punct .openBracket ⟨0, 1⟩, .string ⟨1, 5⟩,
      .punct .comma ⟨5, 6⟩, .string ⟨6, 10⟩, .punct .closeBracket ⟨10, 11⟩])
    (hdec : decodeTape t = some v)
    (hpre₀ : WalkTracePrefix G stringDocumentArena t C₀) (hk₀ : C₀.k = 0)
    (hk₁ : C₁.k = C₀.k + 1) (hev₁ : C₁.events = C₀.events ++ [EventRecord.tag 3])
    (hevc₁ : Cd₁.events = C₁.events ++ [EventRecord.str false 2 0])
    (hkc₁ : Cd₁.k = C₁.k)
    (hk₂ : C₂.k = Cd₁.k + 2) (hev₂ : C₂.events = Cd₁.events)
    (hk₃ : C₃.k = C₂.k + 1) (hev₃ : C₃.events = C₂.events)
    (hevc₂ : Cd₂.events = C₃.events ++ [EventRecord.str false 2 2])
    (hkc₂ : Cd₂.k = C₃.k)
    (hk₄ : C₄.k = Cd₂.k + 2) (hev₄ : C₄.events = Cd₂.events)
    (hk₅ : C₅.k = C₄.k + 1) (hev₅ : C₅.events = C₄.events ++ [EventRecord.tag 4]) :
    WalkTraceRow G.bs stringDocumentArena t
      ([EventRecord.tag 3, EventRecord.str false 2 0,
        EventRecord.str false 2 2, EventRecord.tag 4] : List EventRecord) := by
  have hb₁ : ∀ cs : List Nat, bodyCodePoints G.bs ⟨1, 5⟩ = some cs →
      escapeCodePoints ((stringDocumentArena.drop 0).take 2) = some cs := by
    intro cs hcs
    rw [hbs] at hcs
    have h : bodyCodePoints stringDocumentBytes ⟨1, 5⟩ = some [97, 98] := by decide
    rw [h] at hcs
    have hcs' : ([97, 98] : List Nat) = cs := Option.some.inj hcs
    subst cs
    decide
  have hb₂ : ∀ cs : List Nat, bodyCodePoints G.bs ⟨6, 10⟩ = some cs →
      escapeCodePoints ((stringDocumentArena.drop 2).take 2) = some cs := by
    intro cs hcs
    rw [hbs] at hcs
    have h : bodyCodePoints stringDocumentBytes ⟨6, 10⟩ = some [99, 100] := by decide
    rw [h] at hcs
    have hcs' : ([99, 100] : List Nat) = cs := Option.some.inj hcs
    subst cs
    decide
  exact row_stringArenaDocument (L₁ := 2) (O₁ := 0) (L₂ := 2) (O₂ := 2)
    hal hbs hent htokens hdec hpre₀ hk₀ hk₁ hev₁ hevc₁ hkc₁ hk₂ hev₂
    (by decide) hb₁ hk₃ hev₃ hevc₂ hkc₂ hk₄ hev₄ (by decide) hb₂ hk₅ hev₅

/-- **The strings' arm readings at `["ab","cd"]`.**  The staged entries name each
string's closing quote one lane past its start lane, so the arm's `close` and the body
extent it forms are the document's: `4 - 1 - 1 = 2` and `9 - 6 - 1 = 2`, the lengths
the two records above carry, with the bodies opening at `2` and `7`.  This is the
concrete instance of `WalkAlignQuoted.stringExtent`. -/
theorem stringDocument_armReadings {m0 : Mem} {G : WalkGeom m0}
    (hent : G.ent = [0, 1, 4, 5, 6, 9, 10]) :
    entryPos G 1 = 1 ∧ entryPos G 2 = 4 ∧ entryPos G 2 - entryPos G 1 - 1 = 2 ∧
    entryPos G 4 = 6 ∧ entryPos G 5 = 9 ∧ entryPos G 5 - entryPos G 4 - 1 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [entryPos, hent] <;> decide

/-! ### Axiom footprints

Both list lemmas and the two tag selects are axiom-free, as are the closer's
merge-carry equation (`WalkScope.closeCEnd_events`) and the bracket's byte literal.
The three counting lemmas sit at `[propext, Quot.sound]` because they run `omega`;
the two opener revolutions and the two-entry rows sit at the development's ceiling,
`[propext, Classical.choice, Quot.sound]`, because they are the walk's own steps;
the rest of this layer sits at `propext` alone, and every row that reads a tape's
token facts is at one of those two.

The step layer splits the same way: `WalkTraceStep`, its two producers and its two
count readings, `WalkRevolution` with its projection, `WalkPayloadStep`, the chain,
`WalkTraceChain.carries` and `WalkTraceChain.traceRow` are at `propext` alone; the
chain's index arithmetic and the induction (`k_eq`, `of_steps`,
`walkTraceRow_of_revolutions`) are at `[propext, Quot.sound]` because they run
`omega`; and the two opener step producers are at the ceiling with the revolutions
they package.  The separator documents' rows (`row_separatedPayload` and its two
documents) are at `[propext, Quot.sound]`: they read the tape's token facts and the
indices with `omega`, and no `WalkInv` enters them.

The payload layer splits once more: `payloadStep_of_segment` is at `propext` alone (it
is `WalkTraceStep.emit`'s pair), the two numerals' well-formedness is axiom-free (the
`IntPart` and `Digits0` constructors), and everything that reads a tape's token facts —
`payloadStep_number`, the two string steps, the three `payloadRevolution_*` producers
and the three document rows — is at `[propext, Quot.sound]`; the numerals' lexeme
equations are there too, from `ByteString`'s append and list views.  Measured rather
than assumed. -/

/-- info: 'LeanLLVM.Refinement.Token.recordTokens' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Token.recordTokens

/-- info: 'LeanLLVM.Refinement.Token.recordTokens_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Token.recordTokens_zero

/-- info: 'LeanLLVM.Refinement.Token.recordTokens_full' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Token.recordTokens_full

/-- info: 'LeanLLVM.Refinement.Token.nonSeparators_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Token.nonSeparators_length_le

/-- info: 'LeanLLVM.Refinement.Token.recordTokens_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Token.recordTokens_length_le

/-- info: 'LeanLLVM.Refinement.Token.nonSeparators_cons_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Token.nonSeparators_cons_other

/-- info: 'LeanLLVM.Refinement.Token.nonSeparators_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Token.nonSeparators_append

/-- info: 'LeanLLVM.Refinement.Token.nonSeparators_comma' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Token.nonSeparators_comma

/-- info: 'LeanLLVM.Refinement.Token.nonSeparators_colon' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Token.nonSeparators_colon

/-- info: 'LeanLLVM.Refinement.Token.recordTokens_succ_of_separator' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Token.recordTokens_succ_of_separator

/-- info: 'LeanLLVM.Refinement.Token.recordTokens_succ_of_record' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Token.recordTokens_succ_of_record

/-- info: 'LeanLLVM.Refinement.forall₂_append' does not depend on any axioms -/
#guard_msgs in
#print axioms forall₂_append

/-- info: 'LeanLLVM.Refinement.forall₂_length' does not depend on any axioms -/
#guard_msgs in
#print axioms forall₂_length

/-- info: 'LeanLLVM.Refinement.TokenRecord.not_separator' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TokenRecord.not_separator

/-- info: 'LeanLLVM.Refinement.WalkTracePrefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTracePrefix

/-- info: 'LeanLLVM.Refinement.WalkTracePrefixEmit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTracePrefixEmit

/-- info: 'LeanLLVM.Refinement.WalkTracePrefix.of_seed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTracePrefix.of_seed

/-- info: 'LeanLLVM.Refinement.WalkTracePrefix.congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTracePrefix.congr

/-- info: 'LeanLLVM.Refinement.WalkTracePrefix.length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTracePrefix.length

/-- info: 'LeanLLVM.Refinement.WalkTracePrefix.events_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WalkTracePrefix.events_le

/-- info: 'LeanLLVM.Refinement.WalkTracePrefix.emit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTracePrefix.emit

/-- info: 'LeanLLVM.Refinement.WalkTracePrefix.advance' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTracePrefix.advance

/-- info: 'LeanLLVM.Refinement.WalkTracePrefix.emit_advance' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTracePrefix.emit_advance

/-- info: 'LeanLLVM.Refinement.WalkTracePrefix.advance_separator' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTracePrefix.advance_separator

/-- info: 'LeanLLVM.Refinement.WalkTracePrefix.toTraceRow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTracePrefix.toTraceRow

/-- info: 'LeanLLVM.Refinement.WalkTracePrefixEmit.congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTracePrefixEmit.congr

/-- info: 'LeanLLVM.Refinement.WalkAlign.traceRow_of_prefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkAlign.traceRow_of_prefix

/-- info: 'LeanLLVM.Refinement.prefix_not_enough' depends on axioms: [propext] -/
#guard_msgs in
#print axioms prefix_not_enough

/-- info: 'LeanLLVM.Refinement.nullTraceRow_of_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nullTraceRow_of_steps

/-- info: 'LeanLLVM.Refinement.WalkAlign.bs_getElem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkAlign.bs_getElem

/-- info: 'LeanLLVM.Refinement.headTokenRecord_punct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms headTokenRecord_punct

/-- info: 'LeanLLVM.Refinement.headTokenRecord_null' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms headTokenRecord_null

/-- info: 'LeanLLVM.Refinement.headTokenRecord_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms headTokenRecord_true

/-- info: 'LeanLLVM.Refinement.headTokenRecord_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms headTokenRecord_false

/-- info: 'LeanLLVM.Refinement.headTokenRecord_number' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms headTokenRecord_number

/-- info: 'LeanLLVM.Refinement.headTokenRecord_string_plain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms headTokenRecord_string_plain

/-- info: 'LeanLLVM.Refinement.headTokenRecord_string_arena' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms headTokenRecord_string_arena

/-- info: 'LeanLLVM.Refinement.ifEnd24St_openBrace' does not depend on any axioms -/
#guard_msgs in
#print axioms ifEnd24St_openBrace

/-- info: 'LeanLLVM.Refinement.ifEnd24St_openBracket' does not depend on any axioms -/
#guard_msgs in
#print axioms ifEnd24St_openBracket

/-- info: 'LeanLLVM.Refinement.headRow_openBrace' depends on axioms: [propext] -/
#guard_msgs in
#print axioms headRow_openBrace

/-- info: 'LeanLLVM.Refinement.headRow_openBracket' depends on axioms: [propext] -/
#guard_msgs in
#print axioms headRow_openBracket

/-- info: 'LeanLLVM.Refinement.bitVec_ofNat_entryByte_5B' does not depend on any axioms -/
#guard_msgs in
#print axioms bitVec_ofNat_entryByte_5B

/-- info: 'LeanLLVM.Refinement.WalkScope.closeCEnd_events' does not depend on any axioms -/
#guard_msgs in
#print axioms WalkScope.closeCEnd_events

/-- info: 'LeanLLVM.Refinement.WalkScope.openC₉_events' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkScope.openC₉_events

/-- info: 'LeanLLVM.Refinement.WalkTracePrefix.emit_merge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTracePrefix.emit_merge

/-- info: 'LeanLLVM.Refinement.WalkTracePrefix.keep_merge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTracePrefix.keep_merge

/-- info: 'LeanLLVM.Refinement.WalkTracePrefix.row_of_last' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTracePrefix.row_of_last

/-- info: 'LeanLLVM.Refinement.WalkTracePrefix.events_eq_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTracePrefix.events_eq_nil

/-- info: 'LeanLLVM.Refinement.bitVec_ofNat_entryByte' depends on axioms: [propext] -/
#guard_msgs in
#print axioms bitVec_ofNat_entryByte

/-- info: 'LeanLLVM.Refinement.ifEnd24St_entryByte_5B' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ifEnd24St_entryByte_5B

/-- info: 'LeanLLVM.Refinement.containerOpenEmit_bracket' depends on axioms: [propext] -/
#guard_msgs in
#print axioms containerOpenEmit_bracket

/-- info: 'LeanLLVM.Refinement.containerCloseEmit_bracket' depends on axioms: [propext] -/
#guard_msgs in
#print axioms containerCloseEmit_bracket

/-- info: 'LeanLLVM.Refinement.separatorHead' depends on axioms: [propext] -/
#guard_msgs in
#print axioms separatorHead

/-- info: 'LeanLLVM.Refinement.containerOpenLastRow_bracket' depends on axioms: [propext] -/
#guard_msgs in
#print axioms containerOpenLastRow_bracket

/-- info: 'LeanLLVM.Refinement.containerCloseLastRow_bracket' depends on axioms: [propext] -/
#guard_msgs in
#print axioms containerCloseLastRow_bracket

/-- info: 'LeanLLVM.Refinement.row_openBracketOnly' depends on axioms: [propext] -/
#guard_msgs in
#print axioms row_openBracketOnly

/-- info: 'LeanLLVM.Refinement.containerOpenRevolution_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms containerOpenRevolution_bracket

/-- info: 'LeanLLVM.Refinement.containerOpenRevolution_brace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms containerOpenRevolution_brace

/-- info: 'LeanLLVM.Refinement.row_openCloseBracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms row_openCloseBracket

/-- info: 'LeanLLVM.Refinement.WalkTraceStep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTraceStep

/-- info: 'LeanLLVM.Refinement.WalkTraceStep.emit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTraceStep.emit

/-- info: 'LeanLLVM.Refinement.WalkTraceStep.separator' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTraceStep.separator

/-- info: 'LeanLLVM.Refinement.WalkTraceStep.gain_of_separator' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTraceStep.gain_of_separator

/-- info: 'LeanLLVM.Refinement.WalkTraceStep.gain_of_record' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTraceStep.gain_of_record

/-- info: 'LeanLLVM.Refinement.WalkRevolution' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkRevolution

/-- info: 'LeanLLVM.Refinement.WalkRevolution.toTraceStep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkRevolution.toTraceStep

/-- info: 'LeanLLVM.Refinement.containerOpenRevolution_bracket_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms containerOpenRevolution_bracket_step

/-- info: 'LeanLLVM.Refinement.containerOpenRevolution_brace_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms containerOpenRevolution_brace_step

/-- info: 'LeanLLVM.Refinement.WalkPayloadStep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkPayloadStep

/-- info: 'LeanLLVM.Refinement.WalkTraceChain' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTraceChain

/-- info: 'LeanLLVM.Refinement.WalkTraceChain.k_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WalkTraceChain.k_eq

/-- info: 'LeanLLVM.Refinement.WalkTraceChain.carries' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTraceChain.carries

/-- info: 'LeanLLVM.Refinement.WalkTraceChain.traceRow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WalkTraceChain.traceRow

/-- info: 'LeanLLVM.Refinement.WalkTraceChain.of_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WalkTraceChain.of_steps

/-- info: 'LeanLLVM.Refinement.walkTraceRow_of_revolutions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms walkTraceRow_of_revolutions

/-- info: 'LeanLLVM.Refinement.row_separatedPayload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms row_separatedPayload

/-- info: 'LeanLLVM.Refinement.row_commaBracketPayload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms row_commaBracketPayload

/-- info: 'LeanLLVM.Refinement.row_commaBracket' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms row_commaBracket

/-- info: 'LeanLLVM.Refinement.row_colonBracePayload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms row_colonBracePayload

/-- info: 'LeanLLVM.Refinement.row_colonBrace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms row_colonBrace

/-- info: 'LeanLLVM.Refinement.payloadStep_of_segment' depends on axioms: [propext] -/
#guard_msgs in
#print axioms payloadStep_of_segment

/-- info: 'LeanLLVM.Refinement.payloadStep_number' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms payloadStep_number

/-- info: 'LeanLLVM.Refinement.payloadStep_string_plain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms payloadStep_string_plain

/-- info: 'LeanLLVM.Refinement.payloadStep_string_arena' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms payloadStep_string_arena

/-- info: 'LeanLLVM.Refinement.payloadRevolution_number' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms payloadRevolution_number

/-- info: 'LeanLLVM.Refinement.payloadRevolution_string_plain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms payloadRevolution_string_plain

/-- info: 'LeanLLVM.Refinement.payloadRevolution_string_arena' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms payloadRevolution_string_arena

/-- info: 'LeanLLVM.Refinement.decimalOne_wellFormed' does not depend on any axioms -/
#guard_msgs in
#print axioms decimalOne_wellFormed

/-- info: 'LeanLLVM.Refinement.decimalTwo_wellFormed' does not depend on any axioms -/
#guard_msgs in
#print axioms decimalTwo_wellFormed

/-- info: 'LeanLLVM.Refinement.decimalOne_lexeme' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decimalOne_lexeme

/-- info: 'LeanLLVM.Refinement.decimalTwo_lexeme' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decimalTwo_lexeme

/-- info: 'LeanLLVM.Refinement.row_numberDocument' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms row_numberDocument

/-- info: 'LeanLLVM.Refinement.row_stringPlainDocument' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms row_stringPlainDocument

/-- info: 'LeanLLVM.Refinement.row_stringArenaDocument' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms row_stringArenaDocument

/-- info: 'LeanLLVM.Refinement.row_stringArenaDocument_literal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms row_stringArenaDocument_literal

/-- info: 'LeanLLVM.Refinement.stringDocument_armReadings' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stringDocument_armReadings

end LeanLLVM.Refinement
