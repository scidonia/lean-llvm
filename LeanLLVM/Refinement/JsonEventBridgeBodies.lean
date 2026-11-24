/-
`hr`: the record bodies the byte reader needs are the bodies the run read.

`eventsOfBytes_flatten` (`JsonEventBridge`) reads a trace back to its consumer
events only when every string or key record satisfies `EventRecord.BodyReads bs
arena`: the reader's bounded slice of the source the record's field names
succeeds, and it yields the consumer's code points.  `Stage2Records` bounds
neither the source's extent nor the document's at the record (its `strArena`
clause ties `len` only to `escapeCodePoints ((arena.drop off).take len)`, and a
`take` past the end is a shorter slice that still decodes), so `hr` is not a
consequence of the trace relation.

This module derives it from what a run's post actually reports.  The premises
are exactly three:

* `hrel : Stage2Records bs arena rs toks` — the trace relation at the run's
  document, arena prefix, record list and the parser's tokens;
* the boundary row `hrow : obs = consumeRecords bs arena rs` — the identity
  `stage2Boundary_noEventConsumer` states at the run's post, connecting the
  events the run reports to the trace;
* the event-level clause `hwithin : ∀ e ∈ obs, e.BodiesWithin bs arena` — the
  used-extent statement at the run's events.

Nothing else enters.  In particular the width premise `Bounded` that
`eventsOfBytes_flatten` also takes is **not** used: `BodyReads`' bound comes
from `BodiesWithin`, and its decoded code points come from the relation's own
string construction, so the record's field width is irrelevant here.

The reduction is per record, and `hrow` is what makes it a statement about
records at all: `hwithin` at the event `stringConsumer bs arena key len field`
is `BodiesWithin` at that event, its tag is the key's or string's, and the
clause's own branch — chosen by the same top bit `stringConsumer` reads — gives
`field + len ≤ arena.length` or `(field - 2 ^ 63) + len ≤ bs.length`.  That is
exactly the extent guard `recordBodyCodePoints` checks, so the reader's slice
is the one the relation says decodes to the token's code points, and
`stringConsumer`'s `getD` returns those code points.  A tag or number record
carries no body and `BodyReads` is `True` there.

The plain form's field is `plainSpan (s.start + 1)`, i.e. `s.start + 1 + 2 ^ 63`,
so reading the record's `consume` at that field asks the elaborator to decide the
top-bit test on a numeral addition.  The plain step below names the field with
`generalize` and reasons at the resulting variable, then uses the relation it
records (`plainSpan (s.start + 1) = f`) to restore the arithmetic for the
document slice; the escaped form's field is already a variable and needs no
naming.

There is no `sorry`, `admit` or `native_decide`.
-/
import LeanLLVM.Refinement.JsonEventBridge
import LeanLLVM.Refinement.JsonStage2NoEvent

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The consumer's string event, field by field

`stringConsumer` picks its source by the field's top bit and returns a
`ConsumerEvent.str` either way, so the three fields `BodyReads` and
`BodiesWithin` read are the record's own: the tag is the key's or string's, the
`len` is the record's `len`, and the `payload` is the record's field. -/

theorem eventBridge_stringConsumer_tag (bs arena : List UInt8) (key : Bool)
    (len field : Nat) :
    (stringConsumer bs arena key len field).tag =
      (if key then EventRecord.tagKey else EventRecord.tagStr) := by
  unfold stringConsumer
  split <;> rfl

theorem eventBridge_stringConsumer_len (bs arena : List UInt8) (key : Bool)
    (len field : Nat) :
    (stringConsumer bs arena key len field).len = len := by
  unfold stringConsumer
  split <;> rfl

theorem eventBridge_stringConsumer_payload (bs arena : List UInt8) (key : Bool)
    (len field : Nat) :
    (stringConsumer bs arena key len field).payload = field := by
  unfold stringConsumer
  split <;> rfl

/-- **The clause at a string event is the extent guard.**  `BodiesWithin` at
`stringConsumer`'s event selects its branch by the record's field, so it states
exactly the bound `recordBodyCodePoints` tests before it slices. -/
theorem eventBridge_bodiesWithin_stringConsumer {bs arena : List UInt8} {key : Bool}
    {len field : Nat}
    (h : ConsumerEvent.BodiesWithin bs arena
      (stringConsumer bs arena key len field)) :
    (if field < 2 ^ 63 then field + len ≤ arena.length
     else (field - 2 ^ 63) + len ≤ bs.length) := by
  have htag : (stringConsumer bs arena key len field).tag = EventRecord.tagKey ∨
      (stringConsumer bs arena key len field).tag = EventRecord.tagStr := by
    rw [eventBridge_stringConsumer_tag]
    cases key <;> simp
  have hb := h htag
  rwa [eventBridge_stringConsumer_payload, eventBridge_stringConsumer_len] at hb

/-- **An escaped string's body reads back.**  The field is the arena offset (its
top bit clear), the clause bounds `off + len` by the arena prefix, and the
relation's `strArena` row says the slice decodes to the token's code points. -/
theorem eventBridge_bodyReads_str_arena {bs arena : List UInt8} {key : Bool}
    {len off : Nat} {cs : List Nat} (hbelow : off < 2 ^ 63)
    (hbnd : off + len ≤ arena.length)
    (hread : escapeCodePoints ((arena.drop off).take len) = some cs) :
    (EventRecord.str key len off).BodyReads bs arena := by
  refine ⟨cs, ?_, ?_⟩
  · unfold recordBodyCodePoints
    rw [ite_eq_left hbelow, ite_eq_left hbnd, hread]
  · unfold stringConsumer
    rw [ite_eq_left hbelow, hread]
    rfl

/-- **A plain string's body reads back.**  The field is the body's first
document byte with the top bit set, the clause bounds the document-relative
offset plus `len` by the document, and the relation's `strPlain` row says the
slice decodes to the token's code points. -/
theorem eventBridge_bodyReads_str_plain {bs arena : List UInt8} {key : Bool}
    {len field : Nat} {cs : List Nat} (hnot : ¬ field < 2 ^ 63)
    (hbnd : (field - 2 ^ 63) + len ≤ bs.length)
    (hread : escapeCodePoints ((bs.drop (field - 2 ^ 63)).take len) = some cs) :
    (EventRecord.str key len field).BodyReads bs arena := by
  refine ⟨cs, ?_, ?_⟩
  · unfold recordBodyCodePoints
    rw [ite_eq_right hnot, ite_eq_left hbnd, hread]
  · unfold stringConsumer
    rw [ite_eq_right hnot, hread]
    rfl

/-- The consumer's reading of a trace is a `map`, so its head is the head
record's event and its tail is the tail trace's.  Stated as an equation so the
per-record step below can name the two list positions separately. -/
theorem eventBridge_consumeRecords_cons (bs arena : List UInt8) (r : EventRecord)
    (rs : List EventRecord) :
    consumeRecords bs arena (r :: rs) =
      EventRecord.consume bs arena r :: consumeRecords bs arena rs := rfl

/-- **The clause at the events is the clause at the records.**  The two sides
are the same statement read at the trace's `map`, so a clause stated at
`consumeRecords` transfers to the records' own `consume` applications and back. -/
theorem eventBridge_forall_mem_consumeRecords {bs arena : List UInt8}
    {rs : List EventRecord} {P : ConsumerEvent → Prop} :
    (∀ e ∈ consumeRecords bs arena rs, P e) ↔
      ∀ r ∈ rs, P (EventRecord.consume bs arena r) := by
  induction rs with
  | nil => simp [consumeRecords]
  | cons r rs ih =>
      rw [eventBridge_consumeRecords_cons]
      constructor
      · intro h x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h _ List.mem_cons_self
        · exact ih.mp (fun e he => h e (List.mem_cons_of_mem _ he)) x hx
      · intro h e he
        rcases List.mem_cons.mp he with rfl | he
        · exact h _ List.mem_cons_self
        · exact ih.mpr (fun x hx => h x (List.mem_cons_of_mem _ hx)) e he

/-! ### `hr` from the clause

The induction is the trace relation's own record split: each constructor fixes
the head record's fields, so the clause at the head event yields that record's
`BodyReads`, and the tail's records are the induction hypothesis's.  The
separator constructors carry no record, so they pass the clause through
unchanged. -/

/-- **`hr` from the clause at the trace's events.**  A related trace whose every
consumer event's body lies inside the source its field names has every record's
body readable by the byte reader. -/
theorem bodyReads_of_bodiesWithin {bs arena : List UInt8} {rs : List EventRecord}
    {toks : List Token} (hrel : Stage2Records bs arena rs toks) :
    (∀ e ∈ consumeRecords bs arena rs, e.BodiesWithin bs arena) →
      ∀ r ∈ rs, r.BodyReads bs arena := by
  induction hrel with
  | nil =>
      intro _ r hr
      simp at hr
  | comma _ ih => intro hw; exact ih hw
  | colon _ ih => intro hw; exact ih hw
  | openBrace _ _ _ ih =>
      intro hw r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · trivial
      · exact ih (fun e he => hw e (by
          rw [eventBridge_consumeRecords_cons]
          exact List.mem_cons_of_mem _ he)) r hr
  | closeBrace _ _ _ ih =>
      intro hw r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · trivial
      · exact ih (fun e he => hw e (by
          rw [eventBridge_consumeRecords_cons]
          exact List.mem_cons_of_mem _ he)) r hr
  | openBracket _ _ _ ih =>
      intro hw r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · trivial
      · exact ih (fun e he => hw e (by
          rw [eventBridge_consumeRecords_cons]
          exact List.mem_cons_of_mem _ he)) r hr
  | closeBracket _ _ _ ih =>
      intro hw r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · trivial
      · exact ih (fun e he => hw e (by
          rw [eventBridge_consumeRecords_cons]
          exact List.mem_cons_of_mem _ he)) r hr
  | trueTag _ _ _ ih =>
      intro hw r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · trivial
      · exact ih (fun e he => hw e (by
          rw [eventBridge_consumeRecords_cons]
          exact List.mem_cons_of_mem _ he)) r hr
  | falseTag _ _ _ ih =>
      intro hw r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · trivial
      · exact ih (fun e he => hw e (by
          rw [eventBridge_consumeRecords_cons]
          exact List.mem_cons_of_mem _ he)) r hr
  | nullTag _ _ _ ih =>
      intro hw r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · trivial
      · exact ih (fun e he => hw e (by
          rw [eventBridge_consumeRecords_cons]
          exact List.mem_cons_of_mem _ he)) r hr
  | number _ _ _ _ ih =>
      intro hw r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · trivial
      · exact ih (fun e he => hw e (by
          rw [eventBridge_consumeRecords_cons]
          exact List.mem_cons_of_mem _ he)) r hr
  | strPlain hq hs hbody hcode h ih =>
      rename_i key s rs' toks' len cs
      intro hw r hr
      rcases List.mem_cons.mp hr with heq | hr
      · rw [heq]
        generalize hf : plainSpan (s.start + 1) = f at hw ⊢
        have hcon : ∀ x ∈ EventRecord.str key len f :: rs',
            ConsumerEvent.BodiesWithin bs arena (EventRecord.consume bs arena x) :=
          (eventBridge_forall_mem_consumeRecords
            (P := fun e => e.BodiesWithin bs arena)).mp hw
        have hhead := hcon _ List.mem_cons_self
        have hcons : EventRecord.consume bs arena (EventRecord.str key len f) =
            stringConsumer bs arena key len f := rfl
        rw [hcons] at hhead
        have hb := eventBridge_bodiesWithin_stringConsumer (field := f) hhead
        have hlt : ¬ f < 2 ^ 63 := by
          rw [← hf]
          unfold plainSpan
          omega
        have hsub : f - 2 ^ 63 = s.start + 1 := by
          rw [← hf]
          unfold plainSpan
          omega
        rw [ite_eq_right hlt] at hb
        exact eventBridge_bodyReads_str_plain hlt hb (by rw [hsub]; exact hbody)
      · exact ih (fun e he => hw e (by
          rw [eventBridge_consumeRecords_cons]
          exact List.mem_cons_of_mem _ he)) r hr
  | strArena hq hs hcode hbelow harena h ih =>
      rename_i key s rs' toks' len off cs
      intro hw r hr
      have hcon : ∀ x ∈ EventRecord.str key len off :: rs',
          ConsumerEvent.BodiesWithin bs arena (EventRecord.consume bs arena x) :=
        (eventBridge_forall_mem_consumeRecords
          (P := fun e => e.BodiesWithin bs arena)).mp hw
      rcases List.mem_cons.mp hr with heq | hr
      · have hhead := hcon r (by rw [heq]; exact List.mem_cons_self)
        rw [heq] at hhead
        have hcons : EventRecord.consume bs arena (EventRecord.str key len off) =
            stringConsumer bs arena key len off := rfl
        rw [hcons] at hhead
        rw [heq]
        have hb := eventBridge_bodiesWithin_stringConsumer
          (field := off) hhead
        rw [ite_eq_left hbelow] at hb
        exact eventBridge_bodyReads_str_arena hbelow hb harena
      · exact ih (fun e he => hw e (by
          rw [eventBridge_consumeRecords_cons]
          exact List.mem_cons_of_mem _ he)) r hr

/-- **`hr` at the run's post.**  The boundary row `stage2Boundary_noEventConsumer`
states (`obs = consumeRecords bs arena rs`) identifies the events the clause is
stated over with the trace's, so the clause at `obs` is the clause at the trace
and `bodyReads_of_bodiesWithin` applies. -/
theorem bodyReads_of_boundaryRow {bs arena : List UInt8} {rs : List EventRecord}
    {toks : List Token} {obs : List ConsumerEvent}
    (hrel : Stage2Records bs arena rs toks)
    (hrow : obs = consumeRecords bs arena rs)
    (hwithin : ∀ e ∈ obs, e.BodiesWithin bs arena) :
    ∀ r ∈ rs, r.BodyReads bs arena := by
  rw [hrow] at hwithin
  exact bodyReads_of_bodiesWithin hrel hwithin

end LeanLLVM.Refinement
