/-
The event decoder against the canonicalised token decoder, proved.

`JsonEventValue` states the transfer `EventsParseValue`: a related record trace's
consumer events decode to the token decoder's value once the token decoder's
number lexemes are canonicalised.  `JsonEventBridgeEvents` supplies the
canonicalising token decoder (`parseValueKB`, `parseValueK`) and its
correspondence with the token decoder; this module supplies the missing half,
the event-side bisimulation, as a proof of `EventsParseValue`.

The proof is a simulation of the consumer decoder over the record trace, driven
by the token decoder's own decode of the same tokens:

* `decodeValue` fixes each record's class, so the event stream's head tag is the
  record's tag and the structural cases line up one record at a time;
* the separators (`Stage2Records.comma`, `.colon`) carry no event, so the
  event-side recursion meets them only through the token-side remainder, and the
  relation's inversion removes exactly one separator at a time;
* the number arm's canonical rendering is the relation's own payload
  (`strtodSpec d`'s bits) read back through `canonLexeme`, and the string arm's
  code points are the body both sides read from the token's span.

The statement is proved at every fuel the caller may supply above the consumed
records' own count, not only at one choice of fuel: each conjunct concludes a
`∀ f, f ≥ p.length + 1 → ...`, so the caller's `valueOfEvents` fuel (the event
list's length plus one) is covered and no fuel-monotonicity lemma is needed.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonEventBridgeEvents
import LeanLLVM.Refinement.JsonStage2Hsem
import LeanLLVM.Refinement.JsonEventValue
import LeanLLVM.Refinement.JsonEventBridgeDecode
import LeanLLVM.JSON.Correct
import LeanLLVM.StrtodReader

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### Inversions and evaluations the simulation needs

A relation with an empty token list has no records: every other constructor
consumes a token.  A string record's consumer event is the code points the
relation's body decoded to, in either record form. -/

/-- **No records relate to no tokens.** -/
theorem stage2Records_tokens_nil {bs arena : List UInt8} {rs : List EventRecord}
    (h : Stage2Records bs arena rs []) : rs = [] := by
  cases h with
  | nil => rfl

/-- A separator-headed token list relates to the same records as its tail: the
separator constructors are the only ones whose token is a comma or a colon. -/
theorem stage2Records_comma_tail {bs arena : List UInt8} {rs : List EventRecord}
    {s : Span} {toks : List Token}
    (h : Stage2Records bs arena rs (JSON.Token.punct .comma s :: toks)) :
    Stage2Records bs arena rs toks := by
  cases h with
  | comma h => exact h

/-- The colon separator's tail. -/
theorem stage2Records_colon_tail {bs arena : List UInt8} {rs : List EventRecord}
    {s : Span} {toks : List Token}
    (h : Stage2Records bs arena rs (JSON.Token.punct .colon s :: toks)) :
    Stage2Records bs arena rs toks := by
  cases h with
  | colon h => exact h

/-- A string record's consumer event when the field addresses the document:
the body the consumer reads. -/
theorem consume_str_document {bs arena : List UInt8} {key : Bool} {len field : Nat}
    {cs : List Nat} {bodyStart : Nat}
    (hge : ¬ field < 2 ^ 63) (hfield : field - 2 ^ 63 = bodyStart)
    (hbody : escapeCodePoints ((bs.drop bodyStart).take len) = some cs) :
    EventRecord.consume bs arena (EventRecord.str key len field) =
      ConsumerEvent.str key len field cs := by
  simp only [EventRecord.consume, stringConsumer]
  rw [ite_eq_right hge, hfield, hbody]
  rfl

/-- A string record's consumer event when the field addresses the arena: the
slice the relation decoded. -/
theorem consume_str_arena {bs arena : List UInt8} {key : Bool} {len off : Nat}
    {cs : List Nat}
    (hbelow : off < 2 ^ 63)
    (harena : escapeCodePoints ((arena.drop off).take len) = some cs) :
    EventRecord.consume bs arena (EventRecord.str key len off) =
      ConsumerEvent.str key len off cs := by
  simp only [EventRecord.consume, stringConsumer]
  rw [ite_eq_left hbelow, harena]
  rfl

/-- **The plain form's consumer event.**  The record's field sets the top bit, so
the consumer reads the document's body, which the relation decoded. -/
theorem consume_str_plain {bs arena : List UInt8} {key : Bool} {s : Span}
    {len : Nat} {cs : List Nat}
    (hbody : escapeCodePoints ((bs.drop (s.start + 1)).take len) = some cs) :
    EventRecord.consume bs arena (EventRecord.str key len (plainSpan (s.start + 1))) =
      ConsumerEvent.str key len (plainSpan (s.start + 1)) cs :=
  consume_str_document (by simp only [plainSpan]; omega) (by simp only [plainSpan]; omega) hbody

/-- The number run from a position is a prefix of the bytes there, as a list. -/
private theorem numRun_toList (b : Bytes) :
    (numRun b).toList = b.toList.take (numRun b).length := by
  conv_lhs => rw [← (numRun_spec b).1]
  rw [ByteString.toList_take]

/-- **The decoded number's lexeme is the relation's lexeme.**  The decoder's run
from the cursor and the relation's span cover the same bytes, so the decode's
value is the lexeme the relation's record was built from. -/
private theorem number_lexeme_eq {bs : List UInt8} {i : Nat} {s : Span}
    {d0 : Decimal}
    (hguard : s = ⟨i, i + (numRunFrom (ByteString.literal bs) i).length⟩)
    (hlexeme : (bs.drop s.start).take (s.stop - s.start) = d0.lexeme.data.toList) :
    numRunFrom (ByteString.literal bs) i = d0.lexeme := by
  have hstart : s.start = i := by rw [hguard]
  have hstop : s.stop = i + (numRunFrom (ByteString.literal bs) i).length := by
    rw [hguard]
  have hlex2 : (bs.drop s.start).take (s.stop - s.start) = d0.lexeme.toList := by
    rw [ByteString.toList_eq_data_toList, hlexeme]
  apply ByteString.eq_of_toList_eq
  rw [← hlex2, hstart, hstop]
  simp only [Nat.add_sub_cancel_left]
  rw [numRunFrom_eq, numRun_toList, ByteString.toList_drop, ByteString.toList_literal]

/-- `bodyCodePoints` is the scan of the token's span, so it exposes the code
points and the stop index. -/
theorem bodyCodePoints_scan {bs : List UInt8} {s : Span} {cs : List Nat}
    (h : bodyCodePoints bs s = some cs) :
    ∃ stop, scanCharsEnd (ByteString.literal bs) (s.start + 1) 0 = .ok (cs, stop) := by
  unfold bodyCodePoints at h
  cases hs : scanCharsEnd (ByteString.literal bs) (s.start + 1) 0 with
  | error e => rw [hs] at h; cases h
  | ok p =>
      obtain ⟨c, st⟩ := p
      rw [hs] at h
      injection h with h'
      subst h'
      exact ⟨st, rfl⟩

/-- `canonValue` of a number whose lexeme the reader reads: the canonical
rendering of that lexeme's binary64 value. -/
theorem canonValue_number_eq {lexeme : Bytes} {d : Decimal}
    (h : StrtodReader.reader lexeme = some d) :
    canonValue (.number lexeme) =
      some (.number (ByteString.literal (bitsLexeme (strtodSpec d).toBits))) := by
  simp only [canonValue, canonLexeme, h, Option.map_some]

/-- `canonValue` of the decoded number: the canonical rendering of the relation's
own payload. -/
theorem canonValue_number_of_rel {bs : List UInt8} {i : Nat} {s : Span}
    {d0 : Decimal}
    (hguard : s = ⟨i, i + (numRunFrom (ByteString.literal bs) i).length⟩)
    (hwf : d0.wellFormed)
    (hlexeme : (bs.drop s.start).take (s.stop - s.start) = d0.lexeme.data.toList) :
    canonValue (.number (numRunFrom (ByteString.literal bs) i)) =
      some (.number (ByteString.literal (bitsLexeme (strtodSpec d0).toBits))) := by
  apply canonValue_number_eq
  rw [number_lexeme_eq hguard hlexeme]
  exact StrtodReader.reader_lexeme hwf


/-! ### The relation's head inversions

Each token kind forces the head record's class, because every constructor's token
head is that token.  The inversions are stated with the record equation explicit,
so the simulation can choose the consumed prefix without reverting the goal. -/

theorem inv_null {bs arena : List UInt8} {rs : List EventRecord} {s : Span}
    {toks : List Token} (h : Stage2Records bs arena rs (.null s :: toks)) :
    ∃ rs0, rs = EventRecord.tag 10 :: rs0 ∧ Stage2Records bs arena rs0 toks := by
  cases h with
  | nullTag hb hs h' => exact ⟨_, rfl, h'⟩

theorem inv_true {bs arena : List UInt8} {rs : List EventRecord} {s : Span}
    {toks : List Token} (h : Stage2Records bs arena rs (.bool true s :: toks)) :
    ∃ rs0, rs = EventRecord.tag 8 :: rs0 ∧ Stage2Records bs arena rs0 toks := by
  cases h with
  | trueTag hb hs h' => exact ⟨_, rfl, h'⟩

theorem inv_false {bs arena : List UInt8} {rs : List EventRecord} {s : Span}
    {toks : List Token} (h : Stage2Records bs arena rs (.bool false s :: toks)) :
    ∃ rs0, rs = EventRecord.tag 9 :: rs0 ∧ Stage2Records bs arena rs0 toks := by
  cases h with
  | falseTag hb hs h' => exact ⟨_, rfl, h'⟩

theorem inv_openBracket {bs arena : List UInt8} {rs : List EventRecord} {s : Span}
    {toks : List Token} (h : Stage2Records bs arena rs (.punct .openBracket s :: toks)) :
    ∃ rs0, rs = EventRecord.tag 3 :: rs0 ∧ Stage2Records bs arena rs0 toks := by
  cases h with
  | openBracket hb hs h' => exact ⟨_, rfl, h'⟩

theorem inv_closeBracket {bs arena : List UInt8} {rs : List EventRecord} {s : Span}
    {toks : List Token} (h : Stage2Records bs arena rs (.punct .closeBracket s :: toks)) :
    ∃ rs0, rs = EventRecord.tag 4 :: rs0 ∧ Stage2Records bs arena rs0 toks := by
  cases h with
  | closeBracket hb hs h' => exact ⟨_, rfl, h'⟩

theorem inv_openBrace {bs arena : List UInt8} {rs : List EventRecord} {s : Span}
    {toks : List Token} (h : Stage2Records bs arena rs (.punct .openBrace s :: toks)) :
    ∃ rs0, rs = EventRecord.tag 1 :: rs0 ∧ Stage2Records bs arena rs0 toks := by
  cases h with
  | openBrace hb hs h' => exact ⟨_, rfl, h'⟩

theorem inv_closeBrace {bs arena : List UInt8} {rs : List EventRecord} {s : Span}
    {toks : List Token} (h : Stage2Records bs arena rs (.punct .closeBrace s :: toks)) :
    ∃ rs0, rs = EventRecord.tag 2 :: rs0 ∧ Stage2Records bs arena rs0 toks := by
  cases h with
  | closeBrace hb hs h' => exact ⟨_, rfl, h'⟩

/-- A number head: the decode's lexeme is the relation's own. -/
theorem inv_number {bs arena : List UInt8} {rs : List EventRecord} {s : Span}
    {toks : List Token} (h : Stage2Records bs arena rs (.number s :: toks)) :
    ∃ (rs0 : List EventRecord) (d0 : Decimal),
      rs = EventRecord.number (strtodSpec d0).toBits :: rs0 ∧ d0.wellFormed ∧
      s.stop = s.start + d0.lexeme.length ∧
      (bs.drop s.start).take (s.stop - s.start) = d0.lexeme.data.toList ∧
      Stage2Records bs arena rs0 toks := by
  cases h with
  | number hwf hs hlex h' => exact ⟨_, _, rfl, hwf, hs, hlex, h'⟩

/-- A string head: the token is a key or a value in either record form, and the
relation fixes the code points both forms decode. -/
theorem inv_string {bs arena : List UInt8} {rs : List EventRecord} {s : Span}
    {toks : List Token} (h : Stage2Records bs arena rs (.string s :: toks)) :
    (∃ (key : Bool) (len : Nat) (cs : List Nat) (rs0 : List EventRecord),
        rs = EventRecord.str key len (plainSpan (s.start + 1)) :: rs0 ∧
        s.stop = s.start + 2 + len ∧
        escapeCodePoints ((bs.drop (s.start + 1)).take len) = some cs ∧
        bodyCodePoints bs s = some cs ∧
        Stage2Records bs arena rs0 toks)
    ∨ (∃ (key : Bool) (len off : Nat) (cs : List Nat) (rs0 : List EventRecord),
        rs = EventRecord.str key len off :: rs0 ∧
        s.start + 2 ≤ s.stop ∧
        bodyCodePoints bs s = some cs ∧ off < 2 ^ 63 ∧
        escapeCodePoints ((arena.drop off).take len) = some cs ∧
        Stage2Records bs arena rs0 toks) := by
  cases h with
  | strPlain hquote hspan hbody hcode h' =>
      exact Or.inl ⟨_, _, _, _, rfl, hspan, hbody, hcode, h'⟩
  | strArena hquote hspan hcode hbelow harena h' =>
      exact Or.inr ⟨_, _, _, _, _, rfl, hspan, hcode, hbelow, harena, h'⟩


/-! ### The event parser at a known head tag

The consumers branch on the head event's tag, so each branch is stated once. -/

private theorem parseValueF_tag10 (f : Nat) (e : ConsumerEvent) (es : List ConsumerEvent)
    (h : e.tag = 10) : parseValueF (f + 1) (e :: es) = some (.null, es) := by
  simp only [parseValueF.eq_3, h]

private theorem parseValueF_tag8 (f : Nat) (e : ConsumerEvent) (es : List ConsumerEvent)
    (h : e.tag = 8) : parseValueF (f + 1) (e :: es) = some (.bool true, es) := by
  simp only [parseValueF.eq_3, h]

private theorem parseValueF_tag9 (f : Nat) (e : ConsumerEvent) (es : List ConsumerEvent)
    (h : e.tag = 9) : parseValueF (f + 1) (e :: es) = some (.bool false, es) := by
  simp only [parseValueF.eq_3, h]

private theorem parseValueF_tag7 (f : Nat) (e : ConsumerEvent) (es : List ConsumerEvent)
    (h : e.tag = 7) :
    parseValueF (f + 1) (e :: es) =
      some (.number (ByteString.literal (bitsLexeme e.payload)), es) := by
  simp only [parseValueF.eq_3, h]

private theorem parseValueF_tag56 (f : Nat) (e : ConsumerEvent) (es : List ConsumerEvent)
    (h : e.tag = 5 ∨ e.tag = 6) :
    parseValueF (f + 1) (e :: es) = some (.string e.cps, es) := by
  rcases h with h | h <;> simp only [parseValueF.eq_3, h]

private theorem parseValueF_tag3 (f : Nat) (e : ConsumerEvent) (es : List ConsumerEvent)
    (vs : List JSON.Value) (rest : List ConsumerEvent)
    (h : e.tag = 3) (hp : parseElemsF f es = some (vs, rest)) :
    parseValueF (f + 1) (e :: es) = some (.array vs, rest) := by
  simp only [parseValueF.eq_3, h, hp]

private theorem parseValueF_tag1 (f : Nat) (e : ConsumerEvent) (es : List ConsumerEvent)
    (ms : List (List Nat × JSON.Value)) (rest : List ConsumerEvent)
    (h : e.tag = 1) (hp : parseMembersF f es = some (ms, rest)) :
    parseValueF (f + 1) (e :: es) = some (.object ms, rest) := by
  simp only [parseValueF.eq_3, h, hp]

private theorem parseElemsF_tag4 (f : Nat) (e : ConsumerEvent) (es : List ConsumerEvent)
    (h : e.tag = 4) : parseElemsF (f + 1) (e :: es) = some ([], es) := by
  simp only [parseElemsF.eq_3, h, ite_true]

private theorem parseElemsF_step (f : Nat) (e : ConsumerEvent) (es : List ConsumerEvent)
    (v : JSON.Value) (rest : List ConsumerEvent) (vs : List JSON.Value)
    (rest' : List ConsumerEvent)
    (h : e.tag ≠ 4) (hv : parseValueF f (e :: es) = some (v, rest))
    (hr : parseElemsF f rest = some (vs, rest')) :
    parseElemsF (f + 1) (e :: es) = some (v :: vs, rest') := by
  simp only [parseElemsF.eq_3, h, ite_false, hv, hr]

private theorem parseMembersF_tag2 (f : Nat) (e : ConsumerEvent) (es : List ConsumerEvent)
    (h : e.tag = 2) : parseMembersF (f + 1) (e :: es) = some ([], es) := by
  cases es with
  | nil => simp only [parseMembersF.eq_3, h, ite_true]
  | cons v vs => simp only [parseMembersF.eq_4, h, ite_true]

private theorem parseMembersF_step (f : Nat) (e : ConsumerEvent) (v : ConsumerEvent)
    (vs : List ConsumerEvent) (val : JSON.Value) (rest : List ConsumerEvent)
    (ms : List (List Nat × JSON.Value)) (rest' : List ConsumerEvent)
    (h2 : e.tag ≠ 2) (h56 : e.tag = 5 ∨ e.tag = 6)
    (hv : parseValueF f (v :: vs) = some (val, rest))
    (hr : parseMembersF f rest = some (ms, rest')) :
    parseMembersF (f + 1) (e :: v :: vs) = some ((e.cps, val) :: ms, rest') := by
  rw [parseMembersF.eq_4]
  simp only [h2, ite_false]
  rw [ite_eq_left h56]
  simp only [hv, hr]


/-- A string record's event is never the end-of-array tag. -/
private theorem consume_str_tag_ne4 {bs arena : List UInt8} {key : Bool} {len field : Nat} :
    (EventRecord.consume bs arena (EventRecord.str key len field)).tag ≠ 4 := by
  show (stringConsumer bs arena key len field).tag ≠ 4
  rw [stringConsumer]
  split <;> (cases key <;> simp [ConsumerEvent.str, EventRecord.tagKey, EventRecord.tagStr])

private theorem parseElemsF_tag4_any {g : Nat} (hg : 1 ≤ g) (e : ConsumerEvent)
    (es : List ConsumerEvent) (h : e.tag = 4) :
    parseElemsF g (e :: es) = some ([], es) := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  exact parseElemsF_tag4 g' e es h

private theorem parseMembersF_tag2_any {g : Nat} (hg : 1 ≤ g) (e : ConsumerEvent)
    (es : List ConsumerEvent) (h : e.tag = 2) :
    parseMembersF g (e :: es) = some ([], es) := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  exact parseMembersF_tag2 g' e es h

/-! ### The simulation statement

The three conjuncts are the three decoders.  Each concludes, for the records it
consumed (an explicit prefix `p` of the relation's record list) and the records
left, a value correspondence and a parse at *every* fuel above `p.length + 1`.
The quantification over fuels is what lets a caller's own fuel — the event list's
length plus one in `valueOfEvents` — be used directly, without a monotonicity
lemma about the decoders. -/

private def AgreeAt (bs arena : List UInt8) (N : Nat) : Prop :=
  (∀ (L : List Token) (rs : List EventRecord) (i : Nat) (d : Decoded L),
      L.length ≤ N → Stage2Records bs arena rs L →
      decodeValue (ByteString.literal bs) i L = some d →
      ∃ (p rs' : List EventRecord) (v : JSON.Value),
        rs = p ++ rs' ∧ p ≠ [] ∧ Stage2Records bs arena rs' d.rest ∧
        canonValue d.value = some v ∧
        ∀ f, f ≥ p.length + 1 →
          parseValueF f (consumeRecords bs arena rs) =
            some (v, consumeRecords bs arena rs'))
  ∧ (∀ (S : List Token) (rs : List EventRecord) (j : Nat) (t : ElemsTail S)
        (cb : Span) (ra : List Token),
      S.length ≤ N → Stage2Records bs arena rs S →
      decodeElemsTail (ByteString.literal bs) j S = some t →
      t.rest = JSON.Token.punct .closeBracket cb :: ra →
      ∃ (p rs' : List EventRecord) (vs : List JSON.Value),
        rs = p ++ rs' ∧ p ≠ [] ∧ Stage2Records bs arena rs' ra ∧
        canonValues t.values = some vs ∧
        ∀ g, g ≥ p.length + 1 →
          parseElemsF g (consumeRecords bs arena rs) =
            some (vs, consumeRecords bs arena rs'))
  ∧ (∀ (S : List Token) (rs : List EventRecord) (j : Nat) (t : MembersTail S)
        (cb : Span) (ra : List Token),
      S.length ≤ N → Stage2Records bs arena rs S →
      decodeMembersTail (ByteString.literal bs) j S = some t →
      t.rest = JSON.Token.punct .closeBrace cb :: ra →
      ∃ (p rs' : List EventRecord) (ms : List (List Nat × JSON.Value)),
        rs = p ++ rs' ∧ p ≠ [] ∧ Stage2Records bs arena rs' ra ∧
        canonMembers t.members = some ms ∧
        ∀ g, g ≥ p.length + 1 →
          parseMembersF g (consumeRecords bs arena rs) =
            some (ms, consumeRecords bs arena rs'))

/-- **The element tail's recursive step.**  The value's own simulation runs on
the remaining tokens, the tail's on the remainder after that value, and the two
prefixes concatenate.  The head record is given only to evaluate the event
tag the consumer branches on. -/
private theorem agreeE_step (bs arena : List UInt8) (N : Nat)
    (ih : ∀ M, M < N → AgreeAt bs arena M)
    {rest : List Token} {rs : List EventRecord} {cb : Span} {ra : List Token}
    {i1 : Nat} {d1 : Decoded rest} {t_rec : ElemsTail d1.rest}
    {r : EventRecord} {rs0 : List EventRecord}
    (hrs : rs = r :: rs0)
    (htag : (EventRecord.consume bs arena r).tag ≠ 4)
    (hlt : rest.length < N)
    (hlt2 : d1.rest.length < N)
    (hrel0 : Stage2Records bs arena rs rest)
    (hdec1 : decodeValue (ByteString.literal bs) i1 rest = some d1)
    (hrec : decodeElemsTail (ByteString.literal bs) d1.cursor d1.rest = some t_rec)
    (hrest_rec : t_rec.rest = JSON.Token.punct .closeBracket cb :: ra) :
    ∃ (p rs' : List EventRecord) (vs : List JSON.Value),
      rs = p ++ rs' ∧ p ≠ [] ∧ Stage2Records bs arena rs' ra ∧
      canonValues (d1.value :: t_rec.values) = some vs ∧
      ∀ g, g ≥ p.length + 1 →
        parseElemsF g (consumeRecords bs arena rs) =
          some (vs, consumeRecords bs arena rs') := by
  obtain ⟨pV, rsV, v1, hrsV, hpV, hrelV, hcanonV, hforallV⟩ :=
    (ih rest.length hlt).1 rest rs i1 d1 (le_refl _) hrel0 hdec1
  obtain ⟨pE, rsRec, vsRec, hrsE, hpE, hrelE, hcanonE, hforallE⟩ :=
    (ih d1.rest.length hlt2).2.1 d1.rest rsV d1.cursor t_rec cb ra (le_refl _)
      hrelV hrec hrest_rec
  have hpVpos : 1 ≤ pV.length := by
    cases pV with
    | nil => exact absurd rfl hpV
    | cons a b => simp
  have hpEpos : 1 ≤ pE.length := by
    cases pE with
    | nil => exact absurd rfl hpE
    | cons a b => simp
  have hlenV : pV.length + 1 ≤ pV.length + pE.length := by omega
  rw [hrs] at hforallV
  simp only [consumeRecords, List.map_cons] at hforallV
  refine ⟨pV ++ pE, rsRec, v1 :: vsRec, ?_, ?_, hrelE, ?_, ?_⟩
  · rw [hrsV, hrsE, List.append_assoc]
  · intro h
    rw [List.append_eq_nil_iff] at h
    exact hpV h.1
  · simp only [canonValues_cons, hcanonV, hcanonE, Option.bind_some, Option.map_some]
  · intro g hg
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have hgApp : g' + 1 ≥ pV.length + pE.length + 1 := by
      simpa only [List.length_append] using hg
    have hgV : g' ≥ pV.length + 1 := by omega
    have hgE : g' ≥ pE.length + 1 := by omega
    rw [hrs]
    simp only [consumeRecords, List.map_cons]
    rw [parseElemsF.eq_3]
    rw [ite_eq_right htag]
    rw [hforallV g' hgV]
    dsimp only
    simp only [consumeRecords] at hforallE ⊢
    rw [hforallE g' hgE]


/-- **The member tail's recursive step.**  The key event is read off the record
directly — the consumer takes a key's code points from the event, not from a
value parse — and the member's value and the tail are the two simulations. -/
private theorem agreeM_step (bs arena : List UInt8) (N : Nat)
    (ih : ∀ M, M < N → AgreeAt bs arena M)
    {rest1 : List Token} {rs rs0 : List EventRecord} {cb : Span} {ra : List Token}
    {cs : List Nat} {key : Bool} {len field : Nat}
    {i1 : Nat} {d : Decoded rest1} {t_rec : MembersTail d.rest}
    {r : EventRecord}
    (hrs : rs = r :: rs0)
    (hkey : EventRecord.consume bs arena r = ConsumerEvent.str key len field cs)
    (hlt1 : rest1.length < N)
    (hlt2 : d.rest.length < N)
    (hrel0 : Stage2Records bs arena rs0 rest1)
    (hdecV : decodeValue (ByteString.literal bs) i1 rest1 = some d)
    (hrec : decodeMembersTail (ByteString.literal bs) d.cursor d.rest = some t_rec)
    (hrest_rec : t_rec.rest = JSON.Token.punct .closeBrace cb :: ra) :
    ∃ (p rs' : List EventRecord) (ms : List (List Nat × JSON.Value)),
      rs = p ++ rs' ∧ p ≠ [] ∧ Stage2Records bs arena rs' ra ∧
      canonMembers ((cs, d.value) :: t_rec.members) = some ms ∧
      ∀ g, g ≥ p.length + 1 →
        parseMembersF g (consumeRecords bs arena rs) =
          some (ms, consumeRecords bs arena rs') := by
  obtain ⟨pV, rsV, v1, hrsV, hpV, hrelV, hcanonV, hforallV⟩ :=
    (ih rest1.length hlt1).1 rest1 rs0 i1 d (le_refl _) hrel0 hdecV
  obtain ⟨pE, rsRec, msRec, hrsE, hpE, hrelE, hcanonE, hforallE⟩ :=
    (ih d.rest.length hlt2).2.2 d.rest rsV d.cursor t_rec cb ra (le_refl _)
      hrelV hrec hrest_rec
  have hpVpos : 1 ≤ pV.length := by
    cases pV with
    | nil => exact absurd rfl hpV
    | cons a b => simp
  have hpEpos : 1 ≤ pE.length := by
    cases pE with
    | nil => exact absurd rfl hpE
    | cons a b => simp
  -- the key event
  have htag2 : ¬ ((ConsumerEvent.str key len field cs).tag = 2) := by
    cases key <;> simp [ConsumerEvent.str, EventRecord.tagKey, EventRecord.tagStr]
  have htag56 : (ConsumerEvent.str key len field cs).tag = 5 ∨
      (ConsumerEvent.str key len field cs).tag = 6 := by
    cases key <;> simp [ConsumerEvent.str, EventRecord.tagKey, EventRecord.tagStr]
  have hcps : (ConsumerEvent.str key len field cs).cps = cs := rfl
  -- the value list is nonempty, so the member parser's cons branch applies
  obtain ⟨ph, pt, hpVeq⟩ : ∃ ph pt, pV = ph :: pt := by
    cases pV with
    | nil => exact absurd rfl hpV
    | cons a b => exact ⟨a, b, rfl⟩
  have hrs0 : rs0 = ph :: (pt ++ rsV) := by rw [hrsV, hpVeq]; simp
  rw [hrs0] at hforallV
  simp only [consumeRecords, List.map_cons, List.map_append] at hforallV
  refine ⟨r :: (pV ++ pE), rsRec, (cs, v1) :: msRec, ?_, by simp, hrelE, ?_, ?_⟩
  · rw [hrs, hrsV, hrsE]
    simp only [List.cons_append, List.append_assoc]
  · simp only [canonMembers_cons, hcanonV, hcanonE, Option.bind_some,
      Option.map_some]
  · intro g hg
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have hgApp : g' + 1 ≥ 1 + (pV.length + pE.length) + 1 := by
      simp only [List.length_append, List.length_cons] at hg
      omega
    have hgV : g' ≥ pV.length + 1 := by omega
    have hgE : g' ≥ pE.length + 1 := by omega
    rw [hrs]
    simp only [consumeRecords, List.map_cons]
    rw [hkey]
    rw [hrs0]
    simp only [List.map_cons, List.map_append]
    rw [parseMembersF_step g' (ConsumerEvent.str key len field cs)
      (EventRecord.consume bs arena ph)
      (pt.map (EventRecord.consume bs arena) ++ rsV.map (EventRecord.consume bs arena))
      v1 (consumeRecords bs arena rsV) msRec (consumeRecords bs arena rsRec)
      htag2 htag56 (hforallV g' hgV) (hforallE g' hgE)]
    rw [hcps]
    rfl


/-- **The array value's step.**  The body's element simulation consumes the
records after the opening record, and the value wraps its element list. -/
private theorem agreeV_array_step (bs arena : List UInt8) (N : Nat)
    (ih : ∀ M, M < N → AgreeAt bs arena M)
    {i : Nat} {rr : List Token} {rs rs1 : List EventRecord}
    {d1 : Decoded rr} {t : ElemsTail d1.rest} {c : Span} {rest' : List Token}
    (hrs : rs = EventRecord.tag 3 :: rs1)
    (hrel1 : Stage2Records bs arena rs1 rr)
    (hlt : rr.length < N)
    (hlt2 : d1.rest.length < N)
    (hdec1 : decodeValue (ByteString.literal bs) (skipFrom (ByteString.literal bs) (i + 1)) rr
      = some d1)
    (hdt : decodeElemsTail (ByteString.literal bs) d1.cursor d1.rest = some t)
    (hC : t.rest = JSON.Token.punct .closeBracket c :: rest')
    {r : EventRecord} {rs0 : List EventRecord}
    (hsplit : rs1 = r :: rs0)
    (htag : (EventRecord.consume bs arena r).tag ≠ 4) :
    ∃ (p rs' : List EventRecord) (v : JSON.Value),
      rs = p ++ rs' ∧ p ≠ [] ∧ Stage2Records bs arena rs' rest' ∧
      canonValue (.array (d1.value :: t.values)) = some v ∧
      ∀ f, f ≥ p.length + 1 →
        parseValueF f (consumeRecords bs arena rs) = some (v, consumeRecords bs arena rs') := by
  obtain ⟨pE, rsRec, vs, hrsE, hpE, hrelE, hcanonE, hforallE⟩ :=
    agreeE_step bs arena N ih hsplit htag hlt hlt2 hrel1 hdec1 hdt hC
  have hpEpos : 1 ≤ pE.length := by
    cases pE with
    | nil => exact absurd rfl hpE
    | cons a b => simp
  refine ⟨EventRecord.tag 3 :: pE, rsRec, .array vs, ?_, by simp, hrelE, ?_, ?_⟩
  · rw [hrs, hrsE]; rfl
  · simp only [canonValue_array, hcanonE, Option.map_some]
  · intro f hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hg : f' ≥ pE.length + 1 := by
      simp only [List.length_cons] at hf
      omega
    rw [hrs]
    simp only [consumeRecords, List.map_cons, EventRecord.consume, ConsumerEvent.kind]
    simp only [consumeRecords] at hforallE ⊢
    rw [parseValueF_tag3 f' ⟨3, 0, 0, []⟩ (List.map (EventRecord.consume bs arena) rs1)
      vs (List.map (EventRecord.consume bs arena) rsRec) rfl (hforallE f' hg)]

/-- **The simulation.**  Strong induction on the token list's length: every
recursive call is on strictly fewer tokens, and the record relation's head
inversion supplies the record the event stream's head event came from. -/
private theorem decodeValue_string_head {bs : Bytes} {i : Nat} {L : List Token}
    {k : Decoded L} {cs : List Nat}
    (h : decodeValue bs i L = some k) (hv : k.value = .string cs) :
    ∃ (s : Span) (rest : List Token), L = .string s :: rest := by
  cases L with
  | nil => rw [decodeValue.eq_1] at h; cases h
  | cons tok rest =>
    cases tok with
    | string s => exact ⟨s, rest, rfl⟩
    | null s =>
      rw [decodeValue.eq_2] at h
      split at h
      · injection h with hd; subst hd; cases hv
      · cases h
    | bool b s =>
      rw [decodeValue.eq_3] at h
      split at h
      · rename_i hb; subst hb
        split at h
        · injection h with hd; subst hd; cases hv
        · cases h
      · rename_i hb
        have hbf : b = false := by cases b <;> simp_all
        subst hbf
        split at h
        · injection h with hd; subst hd; cases hv
        · cases h
    | number s =>
      rw [decodeValue.eq_4] at h
      split at h
      · injection h with hd; subst hd; cases hv
      · cases h
    | punct pp s =>
      cases pp with
      | openBracket =>
        by_cases hcl : ∃ (c : Span) (r' : List Token),
            rest = Token.punct .closeBracket c :: r'
        · obtain ⟨c, r', rfl⟩ := hcl
          rw [decodeValue.eq_6 bs i s c r'] at h
          split at h
          · injection h with hd; subst hd; cases hv
          · cases h
        · rw [decodeValue.eq_7 bs i s rest
            (by intro c r' hh; exact hcl ⟨c, r', hh⟩)] at h
          split at h
          · rename_i hc
            dsimp only at h
            cases hdv : decodeValue bs (skipFrom bs (i + 1)) rest with
            | none => rw [hdv] at h; cases h
            | some d =>
              rw [hdv] at h
              dsimp only at h
              cases hdt : decodeElemsTail bs d.cursor d.rest with
              | none => rw [hdt] at h; cases h
              | some t =>
                rw [hdt] at h
                dsimp only at h
                split at h
                · rename_i c rest' hC
                  split at h
                  · rename_i hc2
                    injection h with hd; subst hd; cases hv
                  · cases h
                · cases h
          · cases h
      | closeBracket => simp [decodeValue] at h
      | openBrace =>
        by_cases hcl : ∃ (c : Span) (r' : List Token),
            rest = Token.punct .closeBrace c :: r'
        · obtain ⟨c, r', rfl⟩ := hcl
          rw [decodeValue.eq_8 bs i s c r'] at h
          split at h
          · injection h with hd; subst hd; cases hv
          · cases h
        · rw [decodeValue.eq_9 bs i s rest
            (by intro c r' hh; exact hcl ⟨c, r', hh⟩)] at h
          split at h
          · rename_i hc
            dsimp only at h
            cases hkv : decodeValue bs (skipFrom bs (i + 1)) rest with
            | none => rw [hkv] at h; cases h
            | some kk =>
              rw [hkv] at h
              dsimp only at h
              cases hkv2 : kk.value with
              | null => rw [hkv2] at h; cases h
              | bool bb => rw [hkv2] at h; cases h
              | number l => rw [hkv2] at h; cases h
              | array vs => rw [hkv2] at h; cases h
              | object ms => rw [hkv2] at h; cases h
              | string csK =>
                rw [hkv2] at h
                dsimp only at h
                split at h
                · rename_i sc rest1 hColon
                  split at h
                  · rename_i hc2
                    cases hdd : decodeValue bs (skipFrom bs (skipFrom bs kk.cursor + 1)) rest1 with
                    | none => rw [hdd] at h; cases h
                    | some d =>
                      rw [hdd] at h
                      dsimp only at h
                      cases hdt : decodeMembersTail bs d.cursor d.rest with
                      | none => rw [hdt] at h; cases h
                      | some t =>
                        rw [hdt] at h
                        dsimp only at h
                        split at h
                        · rename_i c rest' hC
                          split at h
                          · rename_i hc3
                            injection h with hd; subst hd; cases hv
                          · cases h
                        · cases h
                  · cases h
                · cases h
          · cases h
      | closeBrace => simp [decodeValue] at h
      | comma => simp [decodeValue] at h
      | colon => simp [decodeValue] at h

/-- **The object value's step.**  The member simulation consumes the records after
the opening record; the value wraps its member list. -/
private theorem agreeV_object_step (bs arena : List UInt8) (N : Nat)
    (ih : ∀ M, M < N → AgreeAt bs arena M)
    {i : Nat} {rs rs1 : List EventRecord}
    {keyRec : EventRecord} {rs0 : List EventRecord}
    {key : Bool} {len field : Nat} {csK : List Nat}
    {rest1 : List Token} {d2 : Decoded rest1} {t : MembersTail d2.rest}
    {c : Span} {rest' : List Token}
    (hrs : rs = EventRecord.tag 1 :: rs1)
    (hsplit : rs1 = keyRec :: rs0)
    (hkey : EventRecord.consume bs arena keyRec = ConsumerEvent.str key len field csK)
    (hrel0 : Stage2Records bs arena rs0 rest1)
    (hlt : rest1.length < N)
    (hlt2 : d2.rest.length < N)
    (hdecV : decodeValue (ByteString.literal bs) i rest1 = some d2)
    (hdt : decodeMembersTail (ByteString.literal bs) d2.cursor d2.rest = some t)
    (hC : t.rest = JSON.Token.punct .closeBrace c :: rest') :
    ∃ (p rs' : List EventRecord) (v : JSON.Value),
      rs = p ++ rs' ∧ p ≠ [] ∧ Stage2Records bs arena rs' rest' ∧
      canonValue (.object ((csK, d2.value) :: t.members)) = some v ∧
      ∀ f, f ≥ p.length + 1 →
        parseValueF f (consumeRecords bs arena rs) =
          some (v, consumeRecords bs arena rs') := by
  obtain ⟨pM, rsRec, ms, hrsM, hpM, hrelM, hcanonM, hforallM⟩ :=
    agreeM_step bs arena N ih hsplit hkey hlt hlt2 hrel0 hdecV hdt hC
  have hpMpos : 1 ≤ pM.length := by
    cases pM with
    | nil => exact absurd rfl hpM
    | cons a b => simp
  refine ⟨EventRecord.tag 1 :: pM, rsRec, .object ms, ?_, by simp, hrelM, ?_, ?_⟩
  · rw [hrs, hrsM]
    rfl
  · simp only [canonValue_object, hcanonM, Option.map_some]
  · intro f hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hg : f' ≥ pM.length + 1 := by
      simp only [List.length_cons] at hf
      omega
    rw [hrs]
    simp only [consumeRecords, List.map_cons, EventRecord.consume, ConsumerEvent.kind]
    simp only [consumeRecords] at hforallM ⊢
    rw [parseValueF_tag1 f' ⟨1, 0, 0, []⟩ (List.map (EventRecord.consume bs arena) rs1)
      ms (List.map (EventRecord.consume bs arena) rsRec) rfl (hforallM f' hg)]

/-- **The simulation.**  Strong induction on the token list's length: every
recursive call is on strictly fewer tokens, and the record relation's head
inversion supplies the record the event stream's head event came from. -/
private theorem agree (bs arena : List UInt8) : ∀ N, AgreeAt bs arena N := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    refine ⟨?_, ?_, ?_⟩
    · -- the value
      intro L rs i d hlen hrel hdec
      rcases L with _ | ⟨tok, rest⟩
      · rw [decodeValue.eq_1] at hdec; cases hdec
      · cases tok with
        | null s =>
          obtain ⟨rs0, hrs, hrel1⟩ := inv_null hrel
          rw [decodeValue.eq_2] at hdec
          split at hdec
          · rename_i hcond
            injection hdec with hd; subst hd
            refine ⟨[EventRecord.tag 10], rs0, .null, ?_, by simp, hrel1, by simp, ?_⟩
            · rw [hrs]; rfl
            · intro f hf
              obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
              rw [hrs]
              simp only [consumeRecords, List.map_cons, EventRecord.consume,
                ConsumerEvent.kind, parseValueF.eq_3]
          · cases hdec
        | bool b s =>
          rw [decodeValue.eq_3] at hdec
          split at hdec
          · rename_i hb; subst hb
            split at hdec
            · rename_i hcond
              injection hdec with hd; subst hd
              obtain ⟨rs0, hrs, hrel1⟩ := inv_true hrel
              refine ⟨[EventRecord.tag 8], rs0, .bool true, ?_, by simp, hrel1, by simp, ?_⟩
              · rw [hrs]; rfl
              · intro f hf
                obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
                rw [hrs]
                simp only [consumeRecords, List.map_cons, EventRecord.consume,
                  ConsumerEvent.kind, parseValueF.eq_3]
            · cases hdec
          · rename_i hb
            have hbf : b = false := by cases b <;> simp_all
            subst hbf
            split at hdec
            · rename_i hcond
              injection hdec with hd; subst hd
              obtain ⟨rs0, hrs, hrel1⟩ := inv_false hrel
              refine ⟨[EventRecord.tag 9], rs0, .bool false, ?_, by simp, hrel1, by simp, ?_⟩
              · rw [hrs]; rfl
              · intro f hf
                obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
                rw [hrs]
                simp only [consumeRecords, List.map_cons, EventRecord.consume,
                  ConsumerEvent.kind, parseValueF.eq_3]
            · cases hdec
        | number s =>
          obtain ⟨rs0, d0, hrs, hwf, hspan, hlex, hrel1⟩ := inv_number hrel
          rw [decodeValue.eq_4] at hdec
          split at hdec
          · rename_i hcond
            injection hdec with hd; subst hd
            obtain ⟨hguard, -⟩ := by
              simpa only [Bool.and_eq_true, beq_iff_eq] using hcond
            refine ⟨[EventRecord.number (strtodSpec d0).toBits], rs0,
              .number (ByteString.literal (bitsLexeme (strtodSpec d0).toBits)),
              ?_, by simp, hrel1, canonValue_number_of_rel hguard hwf hlex, ?_⟩
            · rw [hrs]; rfl
            · intro f hf
              obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
              rw [hrs]
              simp only [consumeRecords, List.map_cons, EventRecord.consume,
                ConsumerEvent.number, stage2TagNum, parseValueF.eq_3]
          · cases hdec
        | string s =>
          rw [decodeValue.eq_5] at hdec
          split at hdec
          · cases hdec
          · rename_i cps stop hs
            split at hdec
            · rename_i hcond
              injection hdec with hd
              subst hd
              obtain ⟨-, hspan_eq⟩ := by
                simpa only [Bool.and_eq_true, decide_eq_true_eq] using hcond
              have hstart : s.start = i := by rw [hspan_eq]
              rcases inv_string hrel with
                ⟨key, len, csRel, rs0, hrs, hspan, hbody, hcode, hrel1⟩ |
                ⟨key, len, off, csRel, rs0, hrs, hspan, hcode, hbelow, harena, hrel1⟩
              · obtain ⟨stopRel, hscanRel⟩ := bodyCodePoints_scan hcode
                have hcs : cps = csRel := by
                  rw [hstart] at hscanRel
                  rw [hs] at hscanRel
                  injection hscanRel with hp
                  injection hp with h1 h2
                refine ⟨[EventRecord.str key len (plainSpan (s.start + 1))], rs0,
                  .string csRel, ?_, ?_, hrel1, ?_, ?_⟩
                · simp [hrs]
                · simp
                · simp only [canonValue_string, hcs]
                · intro f hf
                  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
                  rw [hrs]
                  simp only [consumeRecords, List.map_cons]
                  rw [consume_str_plain hbody]
                  have htag : (ConsumerEvent.str key len (plainSpan (s.start + 1)) csRel).tag = 5 ∨
                      (ConsumerEvent.str key len (plainSpan (s.start + 1)) csRel).tag = 6 := by
                    cases key <;>
                      simp [ConsumerEvent.str, EventRecord.tagKey, EventRecord.tagStr]
                  rw [parseValueF_tag56 f' _ _ htag]
                  rfl
              · obtain ⟨stopRel, hscanRel⟩ := bodyCodePoints_scan hcode
                have hcs : cps = csRel := by
                  rw [hstart] at hscanRel
                  rw [hs] at hscanRel
                  injection hscanRel with hp
                  injection hp with h1 h2
                refine ⟨[EventRecord.str key len off], rs0,
                  .string csRel, ?_, ?_, hrel1, ?_, ?_⟩
                · simp [hrs]
                · simp
                · simp only [canonValue_string, hcs]
                · intro f hf
                  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
                  rw [hrs]
                  simp only [consumeRecords, List.map_cons]
                  rw [consume_str_arena hbelow harena]
                  have htag : (ConsumerEvent.str key len off csRel).tag = 5 ∨
                      (ConsumerEvent.str key len off csRel).tag = 6 := by
                    cases key <;>
                      simp [ConsumerEvent.str, EventRecord.tagKey, EventRecord.tagStr]
                  rw [parseValueF_tag56 f' _ _ htag]
                  rfl
            · cases hdec
        | punct k s =>
          cases k with
          | openBracket =>
            by_cases hclose : ∃ (c : Span) (r' : List Token),
                rest = JSON.Token.punct .closeBracket c :: r'
            · obtain ⟨c, r', rfl⟩ := hclose
              rw [decodeValue.eq_6] at hdec
              split at hdec
              · rename_i hcond
                injection hdec with hd; subst hd
                obtain ⟨rs1, hrs, hrel1⟩ := inv_openBracket hrel
                obtain ⟨rs2, hrs1, hrel2⟩ := inv_closeBracket hrel1
                refine ⟨[EventRecord.tag 3, EventRecord.tag 4], rs2, .array [],
                  ?_, by simp, hrel2, by simp, ?_⟩
                · simp [hrs, hrs1]
                · intro f hf
                  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
                  have hg : 1 ≤ f' := by simp only [List.length_cons] at hf; omega
                  rw [hrs, hrs1]
                  simp only [consumeRecords, List.map_cons, EventRecord.consume,
                    ConsumerEvent.kind]
                  rw [parseValueF_tag3 f' ⟨3, 0, 0, []⟩
                    (⟨4, 0, 0, []⟩ :: List.map (EventRecord.consume bs arena) rs2)
                    [] (List.map (EventRecord.consume bs arena) rs2) rfl
                    (parseElemsF_tag4_any hg ⟨4, 0, 0, []⟩
                      (List.map (EventRecord.consume bs arena) rs2) rfl)]
              · cases hdec
            · have hn : ∀ (c : Span) (r' : List Token),
                  rest ≠ JSON.Token.punct .closeBracket c :: r' := by
                intro c r' hh; exact hclose ⟨c, r', hh⟩
              rw [decodeValue.eq_7 (ByteString.literal bs) i s rest hn] at hdec
              split at hdec
              · rename_i hcond
                dsimp only at hdec
                cases hdv : decodeValue (ByteString.literal bs)
                    (skipFrom (ByteString.literal bs) (i + 1)) rest with
                | none => rw [hdv] at hdec; cases hdec
                | some d1 =>
                  rw [hdv] at hdec
                  dsimp only at hdec
                  cases hdt : decodeElemsTail (ByteString.literal bs) d1.cursor d1.rest with
                  | none => rw [hdt] at hdec; cases hdec
                  | some t =>
                    rw [hdt] at hdec
                    dsimp only at hdec
                    split at hdec
                    · rename_i c rest' hC
                      split at hdec
                      · rename_i hcond2
                        injection hdec with hd; subst hd
                        obtain ⟨rs1, hrs, hrel1⟩ := inv_openBracket hrel
                        have hlt : rest.length < N := by
                          simp only [List.length_cons] at hlen; omega
                        have hlt2 : d1.rest.length < N := by
                          have := d1.shrunk; omega
                        rcases rest with _ | ⟨tok2, rest2⟩
                        · rw [decodeValue.eq_1] at hdv; cases hdv
                        · cases tok2 with
                          | null s2 =>
                            obtain ⟨r0, hsplit, -⟩ := inv_null hrel1
                            exact agreeV_array_step bs arena N ih hrs hrel1 hlt hlt2 hdv hdt hC
                              hsplit (by simp [EventRecord.consume, ConsumerEvent.kind])
                          | bool b2 s2 =>
                            cases b2 with
                            | true =>
                              obtain ⟨r0, hsplit, -⟩ := inv_true hrel1
                              exact agreeV_array_step bs arena N ih hrs hrel1 hlt hlt2 hdv hdt hC
                                hsplit (by simp [EventRecord.consume, ConsumerEvent.kind])
                            | false =>
                              obtain ⟨r0, hsplit, -⟩ := inv_false hrel1
                              exact agreeV_array_step bs arena N ih hrs hrel1 hlt hlt2 hdv hdt hC
                                hsplit (by simp [EventRecord.consume, ConsumerEvent.kind])
                          | number s2 =>
                            obtain ⟨r0, d0, hsplit, -, -, -, -⟩ := inv_number hrel1
                            exact agreeV_array_step bs arena N ih hrs hrel1 hlt hlt2 hdv hdt hC
                              hsplit (by simp [EventRecord.consume, ConsumerEvent.number, stage2TagNum])
                          | string s2 =>
                            rcases inv_string hrel1 with
                              ⟨key, len, cs, r0, hsplit, -, -, -, -⟩ |
                              ⟨key, len, off, cs, r0, hsplit, -, -, -, -, -⟩
                            · exact agreeV_array_step bs arena N ih hrs hrel1 hlt hlt2 hdv hdt hC
                                hsplit consume_str_tag_ne4
                            · exact agreeV_array_step bs arena N ih hrs hrel1 hlt hlt2 hdv hdt hC
                                hsplit consume_str_tag_ne4
                          | punct k2 s2 =>
                            cases k2 with
                            | openBracket =>
                              obtain ⟨r0, hsplit, -⟩ := inv_openBracket hrel1
                              exact agreeV_array_step bs arena N ih hrs hrel1 hlt hlt2 hdv hdt hC
                                hsplit (by simp [EventRecord.consume, ConsumerEvent.kind])
                            | openBrace =>
                              obtain ⟨r0, hsplit, -⟩ := inv_openBrace hrel1
                              exact agreeV_array_step bs arena N ih hrs hrel1 hlt hlt2 hdv hdt hC
                                hsplit (by simp [EventRecord.consume, ConsumerEvent.kind])
                            | closeBracket => simp [decodeValue] at hdv
                            | closeBrace => simp [decodeValue] at hdv
                            | comma => simp [decodeValue] at hdv
                            | colon => simp [decodeValue] at hdv
                      · cases hdec
                    · cases hdec
              · cases hdec
          | openBrace =>
            by_cases hclose : ∃ (c : Span) (r' : List Token),
                rest = JSON.Token.punct .closeBrace c :: r'
            · obtain ⟨c, r', rfl⟩ := hclose
              rw [decodeValue.eq_8] at hdec
              split at hdec
              · rename_i hcond
                injection hdec with hd; subst hd
                obtain ⟨rs1, hrs, hrel1⟩ := inv_openBrace hrel
                obtain ⟨rs2, hrs1, hrel2⟩ := inv_closeBrace hrel1
                refine ⟨[EventRecord.tag 1, EventRecord.tag 2], rs2, .object [],
                  ?_, by simp, hrel2, by simp, ?_⟩
                · simp [hrs, hrs1]
                · intro f hf
                  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
                  have hg : 1 ≤ f' := by simp only [List.length_cons] at hf; omega
                  rw [hrs, hrs1]
                  simp only [consumeRecords, List.map_cons, EventRecord.consume,
                    ConsumerEvent.kind]
                  rw [parseValueF_tag1 f' ⟨1, 0, 0, []⟩
                    (⟨2, 0, 0, []⟩ :: List.map (EventRecord.consume bs arena) rs2)
                    [] (List.map (EventRecord.consume bs arena) rs2) rfl
                    (parseMembersF_tag2_any hg ⟨2, 0, 0, []⟩
                      (List.map (EventRecord.consume bs arena) rs2) rfl)]
              · cases hdec
            · have hn : ∀ (c : Span) (r' : List Token),
                  rest ≠ JSON.Token.punct .closeBrace c :: r' := by
                intro c r' hh; exact hclose ⟨c, r', hh⟩
              rw [decodeValue.eq_9 (ByteString.literal bs) i s rest hn] at hdec
              split at hdec
              · rename_i hcond
                dsimp only at hdec
                cases hk : decodeValue (ByteString.literal bs)
                    (skipFrom (ByteString.literal bs) (i + 1)) rest with
                | none => rw [hk] at hdec; cases hdec
                | some k =>
                  rw [hk] at hdec
                  dsimp only at hdec
                  cases hkv : k.value with
                  | null => rw [hkv] at hdec; cases hdec
                  | bool bb => rw [hkv] at hdec; cases hdec
                  | number l => rw [hkv] at hdec; cases hdec
                  | array vs => rw [hkv] at hdec; cases hdec
                  | object ms => rw [hkv] at hdec; cases hdec
                  | string csK =>
                    rw [hkv] at hdec
                    dsimp only at hdec
                    obtain ⟨s2, rest2, hrestEq⟩ := decodeValue_string_head hk hkv
                    subst hrestEq
                    rw [decodeValue.eq_5 (ByteString.literal bs)
                      (skipFrom (ByteString.literal bs) (i + 1)) s2 rest2] at hk
                    split at hk
                    · cases hk
                    · rename_i cpsK stopK hsk
                      split at hk
                      · rename_i hcondK
                        injection hk with hkval
                        obtain ⟨-, hspanK⟩ := by
                          simpa only [Bool.and_eq_true, decide_eq_true_eq] using hcondK
                        have hrest2 : k.rest = rest2 := by
                          rw [← hkval]
                        have hcsK : csK = cpsK := by
                          rw [← hkval] at hkv
                          injection hkv with h; exact h.symm
                        split at hdec
                        · rename_i sc rest1 hColon
                          split at hdec
                          · rename_i hcond2
                            cases hd2 : decodeValue (ByteString.literal bs)
                                (skipFrom (ByteString.literal bs) (skipFrom (ByteString.literal bs) k.cursor + 1)) rest1 with
                            | none => rw [hd2] at hdec; cases hdec
                            | some d2 =>
                              rw [hd2] at hdec
                              dsimp only at hdec
                              cases hdt : decodeMembersTail (ByteString.literal bs)
                                  d2.cursor d2.rest with
                              | none => rw [hdt] at hdec; cases hdec
                              | some t =>
                                rw [hdt] at hdec
                                dsimp only at hdec
                                split at hdec
                                · rename_i c2 rest' hC
                                  split at hdec
                                  · rename_i hcond3
                                    injection hdec with hd; subst hd
                                    obtain ⟨rs1, hrs, hrel1⟩ := inv_openBrace hrel
                                    have h2 : rest2 = JSON.Token.punct .colon sc :: rest1 := by
                                      rw [← hrest2, hColon]
                                    have hlt : rest1.length < N := by
                                      have h1 : ((JSON.Token.punct .openBrace s ::
                                        JSON.Token.string s2 :: rest2)).length ≤ N := hlen
                                      rw [h2] at h1
                                      simp only [List.length_cons] at h1
                                      omega
                                    have hlt2 : d2.rest.length < N := by
                                      have := d2.shrunk; omega
                                    rcases inv_string hrel1 with
                                      ⟨key, len, csRel, rs0, hsplit, hsp, hbody, hcode, hrel0⟩ |
                                      ⟨key, len, off, csRel, rs0, hsplit, hsp, hcode, hbelow, harena, hrel0⟩
                                    · obtain ⟨stopRel, hscanRel⟩ := bodyCodePoints_scan hcode
                                      have hstart : s2.start =
                                          skipFrom (ByteString.literal bs) (i + 1) := by
                                        rw [hspanK]
                                      have hcsRel : csRel = cpsK := by
                                        rw [hstart] at hscanRel
                                        rw [hsk] at hscanRel
                                        injection hscanRel with hp
                                        injection hp with h1 h2
                                        exact h1.symm
                                      have hrelz : Stage2Records bs arena rs0 rest1 := by
                                        rw [← hrest2, hColon] at hrel0
                                        exact stage2Records_colon_tail hrel0
                                      have hkey : EventRecord.consume bs arena
                                          (EventRecord.str key len (plainSpan (s2.start + 1))) =
                                          ConsumerEvent.str key len (plainSpan (s2.start + 1)) csK := by
                                        rw [consume_str_plain hbody, hcsRel, hcsK]
                                      exact agreeV_object_step bs arena N ih hrs hsplit hkey hrelz
                                        hlt hlt2 hd2 hdt hC
                                    · obtain ⟨stopRel, hscanRel⟩ := bodyCodePoints_scan hcode
                                      have hstart : s2.start =
                                          skipFrom (ByteString.literal bs) (i + 1) := by
                                        rw [hspanK]
                                      have hcsRel : csRel = cpsK := by
                                        rw [hstart] at hscanRel
                                        rw [hsk] at hscanRel
                                        injection hscanRel with hp
                                        injection hp with h1 h2
                                        exact h1.symm
                                      have hrelz : Stage2Records bs arena rs0 rest1 := by
                                        rw [← hrest2, hColon] at hrel0
                                        exact stage2Records_colon_tail hrel0
                                      have hkey : EventRecord.consume bs arena
                                          (EventRecord.str key len off) =
                                          ConsumerEvent.str key len off csK := by
                                        rw [consume_str_arena hbelow harena, hcsRel, hcsK]
                                      exact agreeV_object_step bs arena N ih hrs hsplit hkey hrelz
                                        hlt hlt2 hd2 hdt hC
                                  · cases hdec
                                · cases hdec
                          · cases hdec
                        · cases hdec
                      · cases hk
              · cases hdec
          | closeBracket => simp [decodeValue] at hdec
          | closeBrace => simp [decodeValue] at hdec
          | comma => simp [decodeValue] at hdec
          | colon => simp [decodeValue] at hdec

    · -- the element tail
      intro S rs j t cb ra hlen hrel hdec hrest
      rcases S with _ | ⟨tok, rest⟩
      · rw [decodeElemsTail.eq_2 (ByteString.literal bs) j _ (by intro s0 r0 hh; cases hh)] at hdec
        injection hdec with ht
        subst ht
        simp at hrest
      · cases tok with
        | punct k s =>
          cases k with
          | comma =>
            rw [decodeElemsTail.eq_1] at hdec
            split at hdec
            · rename_i hcond
              cases hd1 : decodeValue (ByteString.literal bs)
                  (skipFrom (ByteString.literal bs) (skipFrom (ByteString.literal bs) j + 1)) rest with
              | none => rw [hd1] at hdec; cases hdec
              | some d1 =>
                rw [hd1] at hdec
                dsimp only at hdec
                cases hdt : decodeElemsTail (ByteString.literal bs) d1.cursor d1.rest with
                | none => rw [hdt] at hdec; cases hdec
                | some t_rec =>
                  rw [hdt] at hdec
                  dsimp only at hdec
                  injection hdec with ht
                  subst ht
                  have hrel0 : Stage2Records bs arena rs rest := stage2Records_comma_tail hrel
                  have hlt : rest.length < N := by
                    simp only [List.length_cons] at hlen; omega
                  have hlt2 : d1.rest.length < N := by
                    have := d1.shrunk; omega
                  rcases rest with _ | ⟨tok2, rest2⟩
                  · rw [decodeValue.eq_1] at hd1; cases hd1
                  · cases tok2 with
                    | null s2 =>
                      obtain ⟨r0, hrs0, -⟩ := inv_null hrel0
                      exact agreeE_step bs arena N ih hrs0
                        (by simp [EventRecord.consume, ConsumerEvent.kind]) hlt hlt2 hrel0 hd1 hdt hrest
                    | bool b2 s2 =>
                      cases b2 with
                      | true =>
                        obtain ⟨r0, hrs0, -⟩ := inv_true hrel0
                        exact agreeE_step bs arena N ih hrs0
                          (by simp [EventRecord.consume, ConsumerEvent.kind]) hlt hlt2 hrel0 hd1 hdt hrest
                      | false =>
                        obtain ⟨r0, hrs0, -⟩ := inv_false hrel0
                        exact agreeE_step bs arena N ih hrs0
                          (by simp [EventRecord.consume, ConsumerEvent.kind]) hlt hlt2 hrel0 hd1 hdt hrest
                    | number s2 =>
                      obtain ⟨r0, d0, hrs0, -, -, -, -⟩ := inv_number hrel0
                      exact agreeE_step bs arena N ih hrs0
                        (by simp [EventRecord.consume, ConsumerEvent.number, stage2TagNum])
                        hlt hlt2 hrel0 hd1 hdt hrest
                    | string s2 =>
                      rcases inv_string hrel0 with
                        ⟨key, len, cs, r0, hrs0, -, -, -, -⟩ |
                        ⟨key, len, off, cs, r0, hrs0, -, -, -, -, -⟩
                      · exact agreeE_step bs arena N ih hrs0 consume_str_tag_ne4 hlt hlt2 hrel0 hd1 hdt hrest
                      · exact agreeE_step bs arena N ih hrs0 consume_str_tag_ne4 hlt hlt2 hrel0 hd1 hdt hrest
                    | punct k2 s2 =>
                      cases k2 with
                      | openBracket =>
                        obtain ⟨r0, hrs0, -⟩ := inv_openBracket hrel0
                        exact agreeE_step bs arena N ih hrs0
                          (by simp [EventRecord.consume, ConsumerEvent.kind]) hlt hlt2 hrel0 hd1 hdt hrest
                      | closeBracket => simp [decodeValue] at hd1
                      | openBrace =>
                        obtain ⟨r0, hrs0, -⟩ := inv_openBrace hrel0
                        exact agreeE_step bs arena N ih hrs0
                          (by simp [EventRecord.consume, ConsumerEvent.kind]) hlt hlt2 hrel0 hd1 hdt hrest
                      | closeBrace => simp [decodeValue] at hd1
                      | comma => simp [decodeValue] at hd1
                      | colon => simp [decodeValue] at hd1
            · cases hdec
          | closeBracket =>
            rw [decodeElemsTail.eq_2 (ByteString.literal bs) j _ (by intro s0 r0 hh; cases hh)] at hdec
            injection hdec with ht
            subst ht
            injection hrest with hs' hr'
            subst hr'
            obtain ⟨rs0, hrs, hrel0⟩ := inv_closeBracket hrel
            refine ⟨[EventRecord.tag 4], rs0, [], ?_, by simp, hrel0, by simp, ?_⟩
            · simp [hrs]
            · intro g hg
              obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
              rw [hrs]
              simp only [consumeRecords, List.map_cons, EventRecord.consume, ConsumerEvent.kind]
              exact parseElemsF_tag4 g' ⟨4, 0, 0, []⟩
                (List.map (EventRecord.consume bs arena) rs0) rfl
          | openBracket =>
            rw [decodeElemsTail.eq_2 (ByteString.literal bs) j _ (by intro s0 r0 hh; cases hh)] at hdec
            injection hdec with ht
            subst ht
            simp at hrest
          | openBrace =>
            rw [decodeElemsTail.eq_2 (ByteString.literal bs) j _ (by intro s0 r0 hh; cases hh)] at hdec
            injection hdec with ht
            subst ht
            simp at hrest
          | closeBrace =>
            rw [decodeElemsTail.eq_2 (ByteString.literal bs) j _ (by intro s0 r0 hh; cases hh)] at hdec
            injection hdec with ht
            subst ht
            simp at hrest
          | colon =>
            rw [decodeElemsTail.eq_2 (ByteString.literal bs) j _ (by intro s0 r0 hh; cases hh)] at hdec
            injection hdec with ht
            subst ht
            simp at hrest
        | null s =>
          rw [decodeElemsTail.eq_2 (ByteString.literal bs) j _ (by intro s0 r0 hh; cases hh)] at hdec
          injection hdec with ht
          subst ht
          simp at hrest
        | bool b s =>
          rw [decodeElemsTail.eq_2 (ByteString.literal bs) j _ (by intro s0 r0 hh; cases hh)] at hdec
          injection hdec with ht
          subst ht
          simp at hrest
        | number s =>
          rw [decodeElemsTail.eq_2 (ByteString.literal bs) j _ (by intro s0 r0 hh; cases hh)] at hdec
          injection hdec with ht
          subst ht
          simp at hrest
        | string s =>
          rw [decodeElemsTail.eq_2 (ByteString.literal bs) j _ (by intro s0 r0 hh; cases hh)] at hdec
          injection hdec with ht
          subst ht
          simp at hrest
    · -- the member tail
      intro S rs j t cb ra hlen hrel hdec hrest
      rcases S with _ | ⟨tok, rest⟩
      · rw [decodeMembersTail.eq_2 (ByteString.literal bs) j _ (by intro s0 r0 hh; cases hh)] at hdec
        injection hdec with ht
        subst ht
        simp at hrest
      · cases tok with
        | punct k s =>
          cases k with
          | comma =>
            rw [decodeMembersTail.eq_1] at hdec
            split at hdec
            · rename_i hcond
              cases hk : decodeValue (ByteString.literal bs)
                  (skipFrom (ByteString.literal bs) (skipFrom (ByteString.literal bs) j + 1)) rest with
              | none => rw [hk] at hdec; cases hdec
              | some k =>
                rw [hk] at hdec
                dsimp only at hdec
                cases hkv : k.value with
                | null => rw [hkv] at hdec; cases hdec
                | bool bb => rw [hkv] at hdec; cases hdec
                | number l => rw [hkv] at hdec; cases hdec
                | array vs => rw [hkv] at hdec; cases hdec
                | object ms => rw [hkv] at hdec; cases hdec
                | string csK =>
                  rw [hkv] at hdec
                  dsimp only at hdec
                  obtain ⟨s2, rest2, hrestEq⟩ := decodeValue_string_head hk hkv
                  subst hrestEq
                  rw [decodeValue.eq_5 (ByteString.literal bs)
                    (skipFrom (ByteString.literal bs) (skipFrom (ByteString.literal bs) j + 1))
                    s2 rest2] at hk
                  split at hk
                  · cases hk
                  · rename_i cpsK stopK hsk
                    split at hk
                    · rename_i hcondK
                      injection hk with hkval
                      obtain ⟨-, hspanK⟩ := by
                        simpa only [Bool.and_eq_true, decide_eq_true_eq] using hcondK
                      have hrest2 : k.rest = rest2 := by
                        rw [← hkval]
                      have hcsK : csK = cpsK := by
                        rw [← hkval] at hkv
                        injection hkv with h; exact h.symm
                      split at hdec
                      · rename_i sc rest1 hColon
                        split at hdec
                        · rename_i hcond2
                          cases hd : decodeValue (ByteString.literal bs)
                              (skipFrom (ByteString.literal bs) (skipFrom (ByteString.literal bs) k.cursor + 1)) rest1 with
                          | none => rw [hd] at hdec; cases hdec
                          | some d =>
                            rw [hd] at hdec
                            dsimp only at hdec
                            cases hdt : decodeMembersTail (ByteString.literal bs) d.cursor d.rest with
                            | none => rw [hdt] at hdec; cases hdec
                            | some t_rec =>
                              rw [hdt] at hdec
                              dsimp only at hdec
                              injection hdec with ht
                              subst ht
                              have hrel0 : Stage2Records bs arena rs (JSON.Token.string s2 :: rest2) := stage2Records_comma_tail hrel
                              have h2 : rest2 = JSON.Token.punct .colon sc :: rest1 := by
                                rw [← hrest2, hColon]
                              have hlt : rest1.length < N := by
                                have h1 : (JSON.Token.punct .comma s ::
                                  JSON.Token.string s2 :: rest2).length ≤ N := hlen
                                rw [h2] at h1
                                simp only [List.length_cons] at h1
                                omega
                              have hlt2 : d.rest.length < N := by
                                have := d.shrunk; omega
                              rcases inv_string hrel0 with
                                ⟨key, len, csRel, rs0, hsplit, hsp, hbody, hcode, hrelz0⟩ |
                                ⟨key, len, off, csRel, rs0, hsplit, hsp, hcode, hbelow, harena, hrelz0⟩
                              · obtain ⟨stopRel, hscanRel⟩ := bodyCodePoints_scan hcode
                                have hstart : s2.start =
                                    skipFrom (ByteString.literal bs) (skipFrom (ByteString.literal bs) j + 1) := by
                                  rw [hspanK]
                                have hcsRel : csRel = cpsK := by
                                  rw [hstart] at hscanRel
                                  rw [hsk] at hscanRel
                                  injection hscanRel with hp
                                  injection hp with h1 h2
                                  exact h1.symm
                                have hrelz : Stage2Records bs arena rs0 rest1 := by
                                  rw [← hrest2, hColon] at hrelz0
                                  exact stage2Records_colon_tail hrelz0
                                have hkey : EventRecord.consume bs arena
                                    (EventRecord.str key len (plainSpan (s2.start + 1))) =
                                    ConsumerEvent.str key len (plainSpan (s2.start + 1)) csK := by
                                  rw [consume_str_plain hbody, hcsRel, hcsK]
                                exact agreeM_step bs arena N ih hsplit hkey hlt hlt2 hrelz hd hdt hrest
                              · obtain ⟨stopRel, hscanRel⟩ := bodyCodePoints_scan hcode
                                have hstart : s2.start =
                                    skipFrom (ByteString.literal bs) (skipFrom (ByteString.literal bs) j + 1) := by
                                  rw [hspanK]
                                have hcsRel : csRel = cpsK := by
                                  rw [hstart] at hscanRel
                                  rw [hsk] at hscanRel
                                  injection hscanRel with hp
                                  injection hp with h1 h2
                                  exact h1.symm
                                have hrelz : Stage2Records bs arena rs0 rest1 := by
                                  rw [← hrest2, hColon] at hrelz0
                                  exact stage2Records_colon_tail hrelz0
                                have hkey : EventRecord.consume bs arena
                                    (EventRecord.str key len off) =
                                    ConsumerEvent.str key len off csK := by
                                  rw [consume_str_arena hbelow harena, hcsRel, hcsK]
                                exact agreeM_step bs arena N ih hsplit hkey hlt hlt2 hrelz hd hdt hrest
                        · cases hdec
                      · cases hdec
                    · cases hk
            · cases hdec
          | closeBrace =>
            rw [decodeMembersTail.eq_2 (ByteString.literal bs) j _ (by intro a0 r0 hh; cases hh)] at hdec
            injection hdec with ht
            subst ht
            injection hrest with hs' hr'
            subst hr'
            obtain ⟨rs0, hrs, hrel0⟩ := inv_closeBrace hrel
            refine ⟨[EventRecord.tag 2], rs0, [], ?_, by simp, hrel0, by simp, ?_⟩
            · simp [hrs]
            · intro g hg
              obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
              rw [hrs]
              simp only [consumeRecords, List.map_cons, EventRecord.consume, ConsumerEvent.kind]
              exact parseMembersF_tag2 g' ⟨2, 0, 0, []⟩
                (List.map (EventRecord.consume bs arena) rs0) rfl
          | openBracket =>
            rw [decodeMembersTail.eq_2 (ByteString.literal bs) j _ (by intro a0 r0 hh; cases hh)] at hdec
            injection hdec with ht
            subst ht
            simp at hrest
          | openBrace =>
            rw [decodeMembersTail.eq_2 (ByteString.literal bs) j _ (by intro a0 r0 hh; cases hh)] at hdec
            injection hdec with ht
            subst ht
            simp at hrest
          | closeBracket =>
            rw [decodeMembersTail.eq_2 (ByteString.literal bs) j _ (by intro a0 r0 hh; cases hh)] at hdec
            injection hdec with ht
            subst ht
            simp at hrest
          | colon =>
            rw [decodeMembersTail.eq_2 (ByteString.literal bs) j _ (by intro a0 r0 hh; cases hh)] at hdec
            injection hdec with ht
            subst ht
            simp at hrest
        | null s =>
          rw [decodeMembersTail.eq_2 (ByteString.literal bs) j _ (by intro a0 r0 hh; cases hh)] at hdec
          injection hdec with ht
          subst ht
          simp at hrest
        | bool b s =>
          rw [decodeMembersTail.eq_2 (ByteString.literal bs) j _ (by intro a0 r0 hh; cases hh)] at hdec
          injection hdec with ht
          subst ht
          simp at hrest
        | number s =>
          rw [decodeMembersTail.eq_2 (ByteString.literal bs) j _ (by intro a0 r0 hh; cases hh)] at hdec
          injection hdec with ht
          subst ht
          simp at hrest
        | string s =>
          rw [decodeMembersTail.eq_2 (ByteString.literal bs) j _ (by intro a0 r0 hh; cases hh)] at hdec
          injection hdec with ht
          subst ht
          simp at hrest

/-! ### The bridge

The simulation at the parser's own tape: the tape decoder's result is unique, and
the record trace's event parse at the event list's own fuel gives the same value
after canonicalisation. -/

/-- **The event-side bridge, proved.**  `EventsParseValue` at every related
trace: the consumer events decode to the token decoder's value after
`canonValue`, so the transfer theorem's `hE` is discharged. -/
theorem eventsParseValue (bs arena : List UInt8) (rs : List EventRecord)
    (toks : List JSON.Token) (t : JSON.Tape) : EventsParseValue bs arena rs toks t := by
  intro hrel hparse htoks hcanon
  obtain ⟨v0, hdecTape, hin, -⟩ :=
    decodeTape_correct Limits.default (ByteString.literal bs) t hparse
  rcases t with ⟨input, tokens⟩
  simp only at hin htoks
  subst hin
  subst htoks
  unfold decodeTape at hdecTape
  split at hdecTape
  · rename_i d hdv
    split at hdecTape
    · rename_i hcond
      injection hdecTape with hv
      subst hv
      obtain ⟨hrest, hcur⟩ := by
        simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using hcond
      obtain ⟨p, rs', v, hrsplit, hp, hrel', hcanonv, hforall⟩ :=
        (agree bs arena tokens.length).1 tokens rs (skipFrom (ByteString.literal bs) 0) d
          (le_refl _) hrel hdv
      have hrnil : rs' = [] := by
        have h0 : Stage2Records bs arena rs' [] := by
          rw [← hrest]
          exact hrel'
        exact stage2Records_tokens_nil h0
      have hplen : p.length ≤ rs.length := by
        rw [hrsplit, List.length_append]
        omega
      have hparseF : parseValueF (rs.length + 1) (consumeRecords bs arena rs) =
          some (v, []) := by
        have h1 := hforall (rs.length + 1) (by omega)
        simp only [hrnil, consumeRecords, List.map_nil] at h1
        exact h1
      have hlen : (consumeRecords bs arena rs).length = rs.length := by
        simp only [consumeRecords, List.length_map]
      have hval : valueOfEvents (consumeRecords bs arena rs) = some v := by
        unfold valueOfEvents
        rw [hlen, hparseF]
        simp
      have hparseK : parseValueK ⟨ByteString.literal bs, tokens⟩ = canonValue d.value := by
        obtain ⟨r1, hr1⟩ := parseValueTB_value_at hdv
        obtain ⟨w, hw⟩ := parseValueTB_remainder_at hdv
        have hrw : r1 = d.rest := by
          have h := Option.some.inj (hr1 ▸ hw)
          exact congrArg Prod.snd h
        rw [hrw, hrest] at hr1
        unfold parseValueK
        dsimp only
        rw [hr1]
      rw [hval, ← parseValueK_eq_bind, hparseK]
      exact hcanonv.symm
    · cases hdecTape
  · cases hdecTape

/--
info: 'LeanLLVM.Refinement.eventsParseValue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Refinement.eventsParseValue

end LeanLLVM.Refinement
