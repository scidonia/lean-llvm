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

* **the trace row** — now the per-entry premise: `WalkTracePrefix.of_seed` at the
  seed, one `emit`/`advance` pair per entry, and `WalkAlign.traceRow_of_prefix` at
  the exit.  What this module does not do is execute the loop: `WalkLink` relates
  two arbitrary carries, so it does not say that a link's carries differ by at most
  one record and one index.  The induction over a `WalkChain` therefore needs each
  link's own carry equation — the arms' `events := C.events ++ [r]` and the merge's
  `k + 1` — read at the link that makes the step.  That is glue between theorems
  that exist, not new mathematics;
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

/-! ### Axiom footprints

Both list lemmas and the two tag selects are axiom-free.  The three counting
lemmas sit at the development's ceiling, `[propext, Quot.sound]`, because they
run `omega`; the rest of the walk layer's own vocabulary sits at `propext` alone,
and every row that reads a tape's token facts sits at the ceiling.  Measured
rather than assumed. -/

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

end LeanLLVM.Refinement
