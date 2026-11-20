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

## What remains

The three residuals `ParserRows` names, at their own vocabulary:

* **the trace row** — the per-entry premise, with the first link family's glue:
  `WalkTracePrefix.of_seed` at the seed, `emit_merge`/`keep_merge` at each arm's
  merge, `row_of_last` at the last entry, and `WalkAlign.traceRow_of_prefix` at the
  exit.  The four containers' and the two separators' carries are read off
  `WalkScope`'s own definitions, and `containerOpenRevolution_*` runs the opener's
  nine links, the merge and the header's pass as one step from the seed — so `[`,
  `{`, `[]` and `{}` have their rows (`row_open*`, `row_openClose*`).  What remains
  is the induction over the walk's revolutions for the longer documents, and the
  string and number arms' payload premises: the escape body's read-back
  (`headTokenRecord_string_plain`/`_arena`) and the numeral's well-formed
  decomposition (`headTokenRecord_number`);
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
    (hbody : ∀ (sp : Span) (cs : List Nat), bodyCodePoints G.bs sp = some cs →
      escapeCodePoints ((G.bs.drop (sp.start + 1)).take len) = some cs) :
    ∃ (sp : Span) (cs : List Nat), t.tokens[C.k]? = some (.string sp) ∧
      bodyCodePoints G.bs sp = some cs ∧
      TokenRecord G.bs arena (.str key len (plainSpan (sp.start + 1))) (.string sp) := by
  obtain ⟨sp, htok, -⟩ := hal.head_string hInv hk hbyte
  obtain ⟨cs, hcode⟩ := tape_bodyCodePoints hdec hal.input (List.mem_of_getElem? htok)
  refine ⟨sp, cs, htok, hcode, ?_⟩
  exact tokenRecord_string_plain_of_tape hdec hal.input (List.mem_of_getElem? htok)
    (hspan sp htok) hcode (hbody sp cs hcode)

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
    (harena : ∀ (sp : Span) (cs : List Nat), bodyCodePoints G.bs sp = some cs →
      escapeCodePoints ((arena.drop off).take len) = some cs) :
    ∃ (sp : Span) (cs : List Nat), t.tokens[C.k]? = some (.string sp) ∧
      bodyCodePoints G.bs sp = some cs ∧
      TokenRecord G.bs arena (.str key len off) (.string sp) := by
  obtain ⟨sp, htok, -⟩ := hal.head_string hInv hk hbyte
  obtain ⟨cs, hcode⟩ := tape_bodyCodePoints hdec hal.input (List.mem_of_getElem? htok)
  refine ⟨sp, cs, htok, hcode, ?_⟩
  exact tokenRecord_string_arena_of_tape hdec hal.input (List.mem_of_getElem? htok)
    (hlen sp htok) hoff hcode (harena sp cs hcode)

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

/-! ### Axiom footprints

Both list lemmas and the two tag selects are axiom-free, as are the closer's
merge-carry equation (`WalkScope.closeCEnd_events`) and the bracket's byte literal.
The three counting lemmas sit at `[propext, Quot.sound]` because they run `omega`;
the two opener revolutions and the two-entry rows sit at the development's ceiling,
`[propext, Classical.choice, Quot.sound]`, because they are the walk's own steps;
the rest of this layer sits at `propext` alone, and every row that reads a tape's
token facts is at one of those two.  Measured rather than assumed. -/

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

end LeanLLVM.Refinement
