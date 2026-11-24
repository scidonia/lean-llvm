/-
The bridges from the emitted stream to the value the entry returns.

`JsonEventValue` states the pipeline's value transfer conditionally: the two
decoder bridges `hE` and `hT` and the canonicalisation's domain `hcanon` are
named premises, and the theorem applies them.  This module proves two of the four, states `hT` and `hE` here, and `hT` is
proved in `JsonEventBridgeTokenB`; `hE` remains the remaining obligation:

* **`hD` — proved.**  `eventsOfBytes_flatten` / `eventsOfBytes_stage2Records`:
  on the records' own encoding, the byte reader returns the trace's consumer
  events.  The stream is not an independent decoder argument here:
  `EventRecord.encodedBytes` is what the emitters write and `eventsOfBytes`
  inverts that same encoding, so the obligation is the walk's agreement with the
  encoding on the trace, record for record;
* **`hcanon` — proved.**  `canonValue_isSome_of_decodeTape`: every number lexeme
  of a value the tape decodes has a canonical rendering, so the transfer's
  right-hand side is never a silent `none`;
* **`hT` — proved in `JsonEventBridgeTokenB`.**  `parseValueT_eq_decodeTape`:
  `parseBytes Limits.default bs = .ok t → parseValueT t = decodeTape t`.  The
  statement is not the bare `parseValueT t = decodeTape t` over every tape: that
  is false, because `decodeValue` checks each token's span against its cursor
  while `parseValueTB` reads the span alone.  With `t.input = " 1"` and
  `t.tokens = [.number ⟨0,1⟩]`, `parseValueT t = some (.number " ")` (the span's
  bytes) and `decodeTape t = none` (`skipFrom` starts at 1, so the number guard
  wants `⟨1,2⟩`).  At the parser's own tape the equality holds, and `hparse` is
  already a transfer premise.  The proof is the structural decoder's
  correspondence with the tape's descent, value for value and tail for tail; the
  value direction needs at least the tokens a value consumes as fuel (the
  container cases' fuel arithmetic is where that obligation sits);
* **`hE` — owed.**  `EventsParseValue` as stated at `JsonEventValue.lean`: with
  `Stage2Records bs arena rs toks`, `parseBytes Limits.default (ByteString.literal bs)
  = .ok t`, `t.tokens = toks` and `hcanon`, the event decoder's value is the
  token decoder's value after `canonValue`.  The proof is a bisimulation between
  `valueOfEvents` and a canonicalising token decoder (`parseValueK` below): the
  token parser's structural cases are the event parser's, separators carry no
  event, and the number arm's only difference is the canonical rendering the
  relation's `strtodSpec` decomposition fixes.

# What the record hypotheses are, and why they are not the relation's

`hD`'s two lower bounds are `consumeBytes_flatten`'s: a record's tags are the
seven one-byte ones and its payload fields fit their words (`EventRecord.Bounded`
and `EventRecord.Tagged`, the latter a consequence of `Stage2Records`).  Beyond
those, the byte reader must be able to read each key's or string's body where the
record says it lies.  `Stage2Records` does **not** imply that: its arena form
ties `len` only to `escapeCodePoints ((arena.drop off).take len)`, and a `take`
past the end of the arena is a shorter slice that still decodes — with
`arena = [0x61]`, a record `.str true 2 0` is related by `strArena`, the reader's
`off + len ≤ arena.length` check fails, and `eventsOfBytes` answers `none` while
`consumeRecords` yields the event.  `EventRecord.BodyReads` is therefore a
premise rather than a derived fact: the walk's `recordBodyCodePoints` returns the
code points the consumer reads.  On the walk's own arena (the used prefix, with
each escaped body written in full and `len` its written length) it holds; the
route's premise set (`Stage2BoundaryFacts`, `stage2Records_at_accept`) does not
state it, so the obligation is incomplete until a walk fact bounds each escaped
record's `off + len` by the used prefix.  The plain form needs the same bound on
`s.start + 1 + len` against the document.

`hcanon` follows the accepted document: `tape_valid` gives `ValidDocument`, the
grammar's number clause is the RFC's number lexeme (`NumberAt`), and
`StrtodReader.reader` accepts exactly those (`reader_complete`).  Its elements are
subterms of the value, so a strong induction on the value's size covers the
containers without a mutual recursion over the grammar.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are in
`LeanLLVMTest/Refinement.lean`.
-/
import LeanLLVM.Refinement.JsonEventBytes
import LeanLLVM.Refinement.JsonEventDecode
import LeanLLVM.JSON.Tape
import LeanLLVM.Refinement.JsonEventValue
import LeanLLVM.StrtodReader

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### `hD`: the encoding round trip

`EventRecord.BodyReads` is the body-extent premise the byte reader needs from
each key or string record: the walk's read of the record's body is the code
points the consumer reads.  It is true of every record the walk wrote — the
arena is its used prefix and `len` is the written length — and it is not a
consequence of `Stage2Records`, which bounds neither the arena's extent nor the
document's at the record. -/

/-- **The walk reads a string record's body the way the consumer does.**  The
record names its source (the arena for the clear top bit, the document for the
set one) and its length; this says the walk's bounded read of that source
succeeds and yields the consumer's code points.  The other record classes carry
no body. -/
def EventRecord.BodyReads (bs arena : List UInt8) : EventRecord → Prop
  | .str key len span =>
      ∃ cps : List Nat,
        recordBodyCodePoints bs arena len span = some cps ∧
          stringConsumer bs arena key len span = .str key len span cps
  | _ => True

/-- **One record's emitted bytes walk to its event.**  Each class's width is the
reader's step and the payload fields are the record's own; a string's body is
`BodyReads`' clause, which is exactly the branch that would otherwise answer
`none`. -/
theorem walkRecords_encoded {bs arena : List UInt8} {r : EventRecord}
    {rest : List UInt8} (hb : r.Bounded) (ht : r.Tagged)
    (hp : r.BodyReads bs arena) :
    walkRecords bs arena (r.encodedBytes ++ rest) =
      (r.consume bs arena :: ·) <$> walkRecords bs arena rest := by
  cases r with
  | tag t =>
      have hlt : t < 256 := hb
      have htag : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 8 ∨ t = 9 ∨ t = 10 := ht
      simp only [EventRecord.encodedBytes, EventRecord.consume, List.cons_append,
        List.nil_append]
      rw [walkRecords, ofNat_toNat_of_lt hlt]
      rcases htag with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  | number bits =>
      have hbits : bits < 2 ^ 64 := hb
      have hbyte : (UInt8.ofNat stage2TagNum).toNat = 7 := by decide
      simp only [EventRecord.encodedBytes, EventRecord.consume, numberRecord,
        List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
        List.append_nil]
      rw [walkRecords]
      simp only [hbyte]
      have hlen : ¬ ((wordBytes 8 bits ++ rest).length < 8) := by
        simp only [List.length_append, wordBytes, natToBytes_length]
        omega
      rw [ite_eq_right hlen, take_wordBytes, drop_wordBytes,
        bytesToNat_wordBytes (w := 8)
          (by rw [show (256 : Nat) ^ 8 = 2 ^ 64 from by decide]; exact hbits)]
  | str key len span =>
      obtain ⟨hlen, hspan⟩ := hb
      obtain ⟨cps, hread, hconsume⟩ := hp
      have hdrop4 := drop_wordBytes len 4 (wordBytes 8 span ++ rest)
      have htake8 : ((wordBytes 4 len ++ (wordBytes 8 span ++ rest)).drop 4).take 8 =
          wordBytes 8 span := by rw [hdrop4]; exact take_wordBytes span 8 rest
      have hdrop12 : (wordBytes 4 len ++ (wordBytes 8 span ++ rest)).drop 12 = rest := by
        rw [show (12 : Nat) = 4 + 8 from rfl, ← List.drop_drop (i := 8) (j := 4), hdrop4]
        exact drop_wordBytes span 8 rest
      have hlen4 : bytesToNat (wordBytes 4 len) = len :=
        bytesToNat_wordBytes (w := 4)
          (by rw [show (256 : Nat) ^ 4 = 2 ^ 32 from by decide]; exact hlen)
      have hspan8 : bytesToNat (wordBytes 8 span) = span :=
        bytesToNat_wordBytes (w := 8)
          (by rw [show (256 : Nat) ^ 8 = 2 ^ 64 from by decide]; exact hspan)
      have hlen12 : ¬ ((wordBytes 4 len ++ (wordBytes 8 span ++ rest)).length < 12) := by
        simp only [List.length_append, wordBytes, natToBytes_length]
        omega
      cases key with
      | false =>
          have hbyte : (UInt8.ofNat EventRecord.tagStr).toNat = 6 := by decide
          simp only [EventRecord.encodedBytes, EventRecord.consume,
            Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append,
            List.append_assoc]
          rw [walkRecords]
          simp only [hbyte]
          rw [ite_eq_right hlen12, take_wordBytes, htake8, hdrop12,
            hlen4, hspan8, hread, hconsume]
      | true =>
          have hbyte : (UInt8.ofNat EventRecord.tagKey).toNat = 5 := by decide
          simp only [EventRecord.encodedBytes, EventRecord.consume,
            ↓reduceIte, List.cons_append, List.nil_append,
            List.append_assoc]
          rw [walkRecords]
          simp only [hbyte]
          rw [ite_eq_right hlen12, take_wordBytes, htake8, hdrop12,
            hlen4, hspan8, hread, hconsume]

/-- **A trace's encoding walks back to the trace's events.**  The induction is
the stream's own record split: `List.flatten_cons` puts the head record's bytes
in front of the tail's stream. -/
theorem walkRecords_flatten {bs arena : List UInt8} (rs : List EventRecord)
    (hb : ∀ r ∈ rs, r.Bounded) (ht : ∀ r ∈ rs, r.Tagged)
    (hr : ∀ r ∈ rs, r.BodyReads bs arena) :
    walkRecords bs arena (rs.map EventRecord.encodedBytes).flatten =
      some (rs.map (EventRecord.consume bs arena)) := by
  induction rs with
  | nil => simp only [List.map_nil, List.flatten_nil, walkRecords]
  | cons r rs ih =>
      have hbr : r.Bounded := hb r (by simp)
      have htr : r.Tagged := ht r (by simp)
      have hrr : r.BodyReads bs arena := hr r (by simp)
      have hb' : ∀ x ∈ rs, x.Bounded := fun x hx => hb x (by simp [hx])
      have ht' : ∀ x ∈ rs, x.Tagged := fun x hx => ht x (by simp [hx])
      have hr' : ∀ x ∈ rs, x.BodyReads bs arena := fun x hx => hr x (by simp [hx])
      simp only [List.map_cons, List.flatten_cons]
      rw [walkRecords_encoded hbr htr hrr, ih hb' ht' hr']
      rfl

/-- **`hD`.**  On the encoding of a trace whose records carry their tags, their
field bounds and their string bodies, the byte reader returns the trace's
consumer events.  The emitted bytes decode to the trace's own events. -/
theorem eventsOfBytes_flatten {bs arena : List UInt8} (rs : List EventRecord)
    (hb : ∀ r ∈ rs, r.Bounded) (ht : ∀ r ∈ rs, r.Tagged)
    (hr : ∀ r ∈ rs, r.BodyReads bs arena) :
    eventsOfBytes bs (rs.map EventRecord.encodedBytes).flatten arena =
      some (consumeRecords bs arena rs) := by
  unfold eventsOfBytes consumeRecords
  exact walkRecords_flatten rs hb ht hr

/-- **`hD` at the record relation.**  A related trace's tags are the relation's
(`Stage2Records.tagged`); its field bounds and body extents are stated beside it,
because the relation bounds neither. -/
theorem eventsOfBytes_stage2Records {bs arena : List UInt8}
    {rs : List EventRecord} {toks : List Token}
    (hrel : Stage2Records bs arena rs toks)
    (hb : ∀ r ∈ rs, r.Bounded) (hr : ∀ r ∈ rs, r.BodyReads bs arena) :
    eventsOfBytes bs (rs.map EventRecord.encodedBytes).flatten arena =
      some (consumeRecords bs arena rs) :=
  eventsOfBytes_flatten rs hb (Stage2Records.tagged hrel) hr


/-! ### `hcanon`: the canonicalisation's domain

`canonValue` refuses exactly where a number lexeme has no `reader` decomposition,
so the domain is "every number's lexeme is a number lexeme the emitted scanner
reads".  It is written as a structural predicate beside `canonValue`, so the
canonicalisation's recursion consumes it branch for branch. -/

mutual
/-- The value predicate: a number's lexeme is one `StrtodReader.reader` reads, an
array's elements and an object's member values satisfy it. -/
def NumberReadable : JSON.Value → Prop
  | .null => True
  | .bool _ => True
  | .string _ => True
  | .number lexeme => (StrtodReader.reader lexeme).isSome = true
  | .array elems => NumberReadableAll elems
  | .object members => NumberReadableMembers members

/-- The element lists' half, so the recursion reads a list rather than the
array's field. -/
def NumberReadableAll : List JSON.Value → Prop
  | [] => True
  | v :: vs => NumberReadable v ∧ NumberReadableAll vs

/-- The member lists' half, for the pair projection the structural recursion
cannot see through. -/
def NumberReadableMembers : List (List Nat × JSON.Value) → Prop
  | [] => True
  | (_, v) :: ms => NumberReadable v ∧ NumberReadableMembers ms
end

/-- The element lists' half in the form the decode's tails state it. -/
theorem numberReadableAll_iff (vs : List JSON.Value) :
    NumberReadableAll vs ↔ ∀ v ∈ vs, NumberReadable v := by
  induction vs with
  | nil => simp [NumberReadableAll]
  | cons v vs ih =>
      simp only [NumberReadableAll, List.mem_cons, forall_eq_or_imp, ih]

/-- The member lists' half in the form the decode's tails state it. -/
theorem numberReadableMembers_iff (ms : List (List Nat × JSON.Value)) :
    NumberReadableMembers ms ↔ ∀ m ∈ ms, NumberReadable m.2 := by
  induction ms with
  | nil => simp [NumberReadableMembers]
  | cons m ms ih =>
      obtain ⟨k, v⟩ := m
      simp only [NumberReadableMembers, List.mem_cons, forall_eq_or_imp, ih]

/-- A `some` behind a true `isSome`: the form the canonicalisation's branches
consume. -/
theorem exists_some_of_isSome {α : Type} {o : Option α} (h : o.isSome = true) :
    ∃ a, o = some a := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl⟩

mutual
theorem canonValue_isSome : ∀ (v : JSON.Value), NumberReadable v →
    (canonValue v).isSome
  | .null, _ => rfl
  | .bool _, _ => rfl
  | .string _, _ => rfl
  | .number lexeme, h => by
      simp only [canonValue, canonLexeme, Option.isSome_map]
      exact h
  | .array elems, h => by
      obtain ⟨elems', h'⟩ := exists_some_of_isSome (canonValues_isSome elems h)
      simp only [canonValue, h']
      rfl
  | .object members, h => by
      obtain ⟨members', h'⟩ := exists_some_of_isSome (canonMembers_isSome members h)
      simp only [canonValue, h']
      rfl

/-- The element list's canonicalisation, from the readable predicate. -/
theorem canonValues_isSome : ∀ (vs : List JSON.Value),
    NumberReadableAll vs → (canonValues vs).isSome
  | [], _ => rfl
  | v :: vs, h => by
      obtain ⟨hv, hvs⟩ := h
      obtain ⟨v', hv'⟩ := exists_some_of_isSome (canonValue_isSome v hv)
      obtain ⟨vs', hvs'⟩ := exists_some_of_isSome (canonValues_isSome vs hvs)
      simp only [canonValues, hv', hvs']
      rfl

/-- The member list's canonicalisation, from the readable predicate. -/
theorem canonMembers_isSome : ∀ (ms : List (List Nat × JSON.Value)),
    NumberReadableMembers ms → (canonMembers ms).isSome
  | [], _ => rfl
  | (k, v) :: ms, h => by
      obtain ⟨hv, hms⟩ := h
      obtain ⟨v', hv'⟩ := exists_some_of_isSome (canonValue_isSome v hv)
      obtain ⟨ms', hms'⟩ := exists_some_of_isSome (canonMembers_isSome ms hms)
      simp only [canonMembers, hv', hms']
      rfl
end


/-! #### The elements and members of a valid container

The size-bound hypotheses are what a strong induction on the value's size
supplies: an element or member value is a strict subterm of the container, so the
induction hypothesis covers it.  The recursive statements carry the bound `N` on
the container's own child list, which is the threshold every child is below. -/

/-- The elements of an `Elems` derivation are readable, given a threshold above
every child's size. -/
theorem elems_numberReadable {m : Strictness} {bs : Bytes} {N : Nat}
    (ih : ∀ (w : JSON.Value), sizeOf w < N → ∀ (m : Strictness) (bs : Bytes)
      (i j : Nat), ValueAt m bs i w j → NumberReadable w) :
    ∀ {i : Nat} {vs : List JSON.Value} {j : Nat}, Elems m bs i vs j → (∀ v ∈ vs, sizeOf v < N) →
      ∀ v ∈ vs, NumberReadable v
  | _, _, _, .last hv hw, hsz, v, hv' => by
      rw [List.mem_singleton] at hv'
      subst hv'
      exact ih v (hsz v (by simp)) m bs _ _ hv
  | _, _, _, .cons hv hw1 hc hw2 hr, hsz, v, hv' => by
      rcases List.mem_cons.mp hv' with h0 | h0
      · subst h0
        exact ih v (hsz v (by simp)) m bs _ _ hv
      · exact elems_numberReadable ih hr (fun w hw => hsz w (by simp [hw])) v h0

/-- The members of a `Members` derivation have readable values, given a threshold
above every member's value size. -/
theorem members_numberReadable {m : Strictness} {bs : Bytes} {N : Nat}
    (ih : ∀ (w : JSON.Value), sizeOf w < N → ∀ (m : Strictness) (bs : Bytes)
      (i j : Nat), ValueAt m bs i w j → NumberReadable w) :
    ∀ {i : Nat} {ms : List (List Nat × JSON.Value)} {j : Nat}, Members m bs i ms j → (∀ p ∈ ms, sizeOf p.2 < N) →
      ∀ p ∈ ms, NumberReadable p.2
  | _, _, _, .last hm hw, hsz, p, hp => by
      rw [List.mem_singleton] at hp
      subst hp
      have h2 : sizeOf p.2 < N := hsz p (by simp)
      cases hm with
      | mk hk hw1 hc hw2 hval =>
          exact ih _ (by simpa using h2) m bs _ _ hval
  | _, _, _, .cons hm hw1 hc hw2 hr, hsz, p, hp => by
      rcases List.mem_cons.mp hp with h0 | h0
      · subst h0
        have h2 : sizeOf p.2 < N := hsz p (by simp)
        cases hm with
        | mk hk hw1' hc' hw2' hval =>
            exact ih _ (by simpa using h2) m bs _ _ hval
      · exact members_numberReadable ih hr (fun q hq => hsz q (by simp [hq])) p h0

/-- An array body's elements are readable. -/
theorem arrBody_numberReadable {m : Strictness} {bs : Bytes} {i : Nat} {vs : List JSON.Value} {k : Nat}
    (hb : ArrBody m bs i vs k) {N : Nat}
    (ih : ∀ (w : JSON.Value), sizeOf w < N → ∀ (m : Strictness) (bs : Bytes)
      (i j : Nat), ValueAt m bs i w j → NumberReadable w)
    (hN : sizeOf (JSON.Value.array vs) ≤ N) : NumberReadable (JSON.Value.array vs) := by
  refine (numberReadableAll_iff vs).mpr ?_
  have hsz : ∀ v ∈ vs, sizeOf v < N := fun v hv => by
    have h1 := List.sizeOf_lt_of_mem hv
    have h2 : sizeOf vs ≤ sizeOf (JSON.Value.array vs) := by simp <;> omega
    omega
  cases hb with
  | empty => intro v hv; simp at hv
  | elems he hcl => exact elems_numberReadable ih he hsz

/-- An object body's member values are readable. -/
theorem objBody_numberReadable {m : Strictness} {bs : Bytes} {i : Nat} {ms : List (List Nat × JSON.Value)} {k : Nat}
    (hb : ObjBody m bs i ms k) {N : Nat}
    (ih : ∀ (w : JSON.Value), sizeOf w < N → ∀ (m : Strictness) (bs : Bytes)
      (i j : Nat), ValueAt m bs i w j → NumberReadable w)
    (hN : sizeOf (JSON.Value.object ms) ≤ N) : NumberReadable (JSON.Value.object ms) := by
  refine (numberReadableMembers_iff ms).mpr ?_
  have hsz : ∀ p ∈ ms, sizeOf p.2 < N := fun p hp => by
    have h1 := List.sizeOf_lt_of_mem hp
    have h2 : sizeOf p.2 ≤ sizeOf p := by
      obtain ⟨a, b⟩ := p
      simp
    have h3 : sizeOf ms ≤ sizeOf (JSON.Value.object ms) := by simp <;> omega
    omega
  cases hb with
  | empty => intro p hp; simp at hp
  | members hm h => exact members_numberReadable ih hm hsz

/-- **A valid document's value is readable.**  The grammar's number clause is the
RFC's number lexeme (`NumberAt`), and the reader accepts exactly those
(`reader_complete`); the containers' elements are subterms of the value, so the
strong induction on the value's size supplies their readability. -/
theorem valueAt_numberReadable_aux (n : Nat) :
    ∀ (v : JSON.Value), sizeOf v ≤ n → ∀ (m : Strictness) (bs : Bytes) (i j : Nat),
      ValueAt m bs i v j → NumberReadable v := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro v hv m bs i j hva
    cases hva with
    | null => exact trivial
    | true => exact trivial
    | false => exact trivial
    | number hn => exact StrtodReader.reader_complete hn.2
    | string hs => exact trivial
    | array hl hb hr =>
        exact arrBody_numberReadable (N := n) hb
          (fun w hw m bs i j hwv => ih (sizeOf w) hw w (le_refl _) m bs i j hwv) hv
    | object hl hb hr =>
        exact objBody_numberReadable (N := n) hb
          (fun w hw m bs i j hwv => ih (sizeOf w) hw w (le_refl _) m bs i j hwv) hv

/-- **A valid document's value is readable.** -/
theorem valueAt_numberReadable {m : Strictness} {bs : Bytes} {i j : Nat} {v : JSON.Value}
    (h : ValueAt m bs i v j) : NumberReadable v :=
  valueAt_numberReadable_aux (sizeOf v) v (le_refl _) m bs i j h

/-- **`hcanon`.**  Every value the tape decodes has a canonical rendering: the
tape's own validity (`tape_valid`) gives the accepted document's grammar, and the
grammar's values are readable. -/
theorem canonValue_isSome_of_decodeTape (t : JSON.Tape) {v : JSON.Value}
    (h : decodeTape t = some v) : (canonValue v).isSome := by
  obtain ⟨-, hvalid⟩ := tape_valid t v h
  obtain ⟨hrfc, -⟩ := hvalid
  obtain ⟨i, j, -, hva, -⟩ := hrfc
  exact canonValue_isSome v (valueAt_numberReadable hva)



/-- **The used-extent clause, stated at the events a run reports.**  A key's or
string's body lies inside the source its field names: the field's top bit selects
the document (the plain form) or the arena prefix (the escaped form), and `len`
is the body's extent in it.  This is the shape a walk report carries — the
no-event run's report has `arena`, `obs` and `bs` and no record list, so the
clause cannot be a per-record field there.  From it and `Stage2Records` the
record premise `hr` follows: the relation names the source and gives the decoded
code points, and the clause bounds the `len` bytes inside it.  Deriving `hr` from
it is the remaining obligation, not a change to `eventsOfBytes`.  The clause is
stated on the **events** because the run reports events, not records; the identity
that would connect the two — `obs = consumeRecords bs arena rs` — is not a
consequence of the relations (`stage2NoEvent_str_len_free` shows `obs` is not a
function of the token list), it is `stage2Boundary_noEventConsumer`'s own row, and
the remaining link from the clause to `hr` is the string-case proof recorded as
C13. -/
def ConsumerEvent.BodiesWithin (bs arena : List UInt8) (e : ConsumerEvent) : Prop :=
  (e.tag = EventRecord.tagKey ∨ e.tag = EventRecord.tagStr) →
    (if e.payload < 2 ^ 63 then e.payload + e.len ≤ arena.length
     else (e.payload - 2 ^ 63) + e.len ≤ bs.length)

/-- **The relation does not determine its event list.**  The arena form's `len`
is free above the decoded slice: the same token has a derivation at every `len`
whose `take` decodes.  Two such lengths give two different events (their `terms`
differ), so `obs` is not a function of `toks` and the clause at a run's `obs` is
not yet a statement about a record trace `rs`.  The identity that connects them —
`obs = consumeRecords bs arena rs` — is the boundary projection's own row
(`stage2Boundary_noEventConsumer`'s conclusion), not a consequence of
`Stage2Records` and `Stage2NoEvent` together. -/
theorem stage2NoEvent_str_len_free {bs arena : List UInt8} {key : Bool} {s : Span}
    {es : List ConsumerEvent} {toks : List Token} {len off : Nat} {cs : List Nat}
    (hquote : bs[s.start]? = some 0x22) (hspan : s.start + 2 ≤ s.stop)
    (hcode : bodyCodePoints bs s = some cs) (hbelow : off < 2 ^ 63)
    (h : Stage2NoEvent bs arena es toks) {len' : Nat}
    (harena : escapeCodePoints ((arena.drop off).take len') = some cs) :
    Stage2NoEvent bs arena (.str key len' off cs :: es) (.string s :: toks) :=
  Stage2NoEvent.strArena hquote hspan hcode hbelow harena h

/-- The token decoder and the tape decoder agree on a tape the reference parser
produced.  Conditional because a tape whose spans disagree with its cursor is
read by the first and rejected by the second. -/
def TokenDecoderAgrees (t : LeanLLVM.JSON.Tape) : Prop :=
  LeanLLVM.Refinement.parseValueT t = LeanLLVM.JSON.decodeTape t

end LeanLLVM.Refinement
