/-
The record supply's producer, at the relation this tree carries.

`Stage2Records` (`JsonStage2Hsem`) keeps its name and its thirteen constructors;
two of its rows are stated at the readings a parsed document can actually fill.
The plain string row asks the token's own escape-aware scan (`bodyCodePoints`)
instead of the raw body's UTF-8 decode, and the number row names the span's bytes
as a lexeme and asks the tree's reader of it (`StrtodReader.reader`, which
normalises `E`/`+`) instead of a `Decimal` whose own lexeme those bytes are.
`Stage2NoEvent` and the consumer's plain read (`stringConsumer` /
`recordBodyCodePoints`) are stated at the same reading, so
`Stage2Records.toNoEvent` still projects.

This module supplies the producer the accept arm needs:
`parseBytes … = .ok t → Nonempty (Stage2NoEventWalkRecordsSupply bs arena t)`.
The per-token facts are the strengthened `TokenBytes` (the punctuation byte is
in it) and the tape's span discipline; `records_exists` builds the trace, its
widths and its extent clause.  The refutation's witness `"\/"` is a theorem
here (`escapeDoc_supply`), the old positive control `null` still holds, and the
exponent spelling `1E5` is absorbed through the reader.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkSupplies
import LeanLLVM.Refinement.JsonStage2WalkAlignment
import LeanLLVM.StrtodReader

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1600000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.JSON.ByteString

/-! ### Strings: the document span and its code points -/

/-- **A string literal is at least its two quotes wide.**  The body's strict
derivation loses at least one byte before the closing quote, and the span ends
where that quote starts. -/
theorem stringAt_two_le {m : Strictness} {b : Bytes} {i j : Nat} {cs : List Nat}
    (h : StringAt m b i j cs) (hj : j ≤ b.length) : i + 2 ≤ j := by
  obtain ⟨hq, rest, hstr, hdrop⟩ := h
  have hi : i < b.length := (ByteString.getElem?_eq_some_iff.mp hq).1
  have hlt := strChars_suffix_lt hstr
  rw [ByteString.length_drop] at hlt
  have hrest : rest.length = b.length - j := by
    rw [← hdrop, ByteString.length_drop]
  rw [hrest] at hlt
  omega

/-- **The escape-aware reader at a strict literal.**  `StringAt`'s derivation is
the scanner's, so `bodyCodePoints` returns its code points. -/
theorem stringAt_bodyCodePoints {bs : List UInt8} {i j : Nat} {cs : List Nat}
    (h : StringAt .strict (ByteString.literal bs) i j cs) :
    bodyCodePoints bs ⟨i, j⟩ = some cs := by
  obtain ⟨-, rest, hstr, -⟩ := h
  have hok : scanChars ((ByteString.literal bs).drop (i + 1)) = .ok (cs, rest) :=
    (scanChars_iff _ _ _).mpr hstr
  have hfrom : scanCharsFrom 0 ((ByteString.literal bs).drop (i + 1)) = .ok (cs, rest) := by
    rw [← scanChars_eq]; exact hok
  obtain ⟨stop, hstop, -⟩ := scanCharsEnd_ok_of_scanCharsFrom hfrom
  unfold bodyCodePoints bodyCodePointsAt
  rw [hstop]

/-! ### Consumer-side facts for the non-string record values -/

/-- A non-string event satisfies the extent clause vacuously. -/
theorem bodiesWithin_of_tag_ne {bs arena : List UInt8} {e : ConsumerEvent}
    (h1 : e.tag ≠ EventRecord.tagKey) (h2 : e.tag ≠ EventRecord.tagStr) :
    e.BodiesWithin bs arena := by
  unfold ConsumerEvent.BodiesWithin
  intro hmem
  rcases hmem with hmem | hmem
  · exact absurd hmem h1
  · exact absurd hmem h2

/-! ### The producer

One record per record-carrying token, in order, from the parse's own per-token
facts.  The hypotheses are the strengthened `TokenBytes` and the span
discipline, both of which a successful parse supplies. -/

theorem records_exists {bs arena : List UInt8} (hlen : bs.length ≤ 2 ^ 20) :
    ∀ toks : List Token,
      (∀ tok ∈ toks, TokenBytes (ByteString.literal bs) tok) →
      (∀ tok ∈ toks, tok.span.start < tok.span.stop ∧ tok.span.stop ≤ bs.length) →
      ∃ rs, Stage2Records bs arena rs toks ∧
        (∀ r ∈ rs, r.Bounded) ∧
        (∀ e ∈ consumeRecords bs arena rs, e.BodiesWithin bs arena) := by
  intro toks
  induction toks with
  | nil =>
      intro _ _
      exact ⟨[], .nil, by simp, by simp [consumeRecords]⟩
  | cons tok rest ih =>
      intro htb hsp
      obtain ⟨rs, hrel, hbnd, hwit⟩ :=
        ih (fun t ht => htb t (List.mem_cons_of_mem _ ht))
           (fun t ht => hsp t (List.mem_cons_of_mem _ ht))
      cases tok with
      | punct p s =>
          cases p with
          | comma => exact ⟨rs, .comma hrel, hbnd, hwit⟩
          | colon => exact ⟨rs, .colon hrel, hbnd, hwit⟩
          | openBrace =>
              obtain ⟨hstop, hbyte⟩ := htb _ List.mem_cons_self
              have hbyte' : bs[s.start]? = some 0x7B := by
                simpa [Punct.byte] using hbyte
              refine ⟨EventRecord.tag 1 :: rs, .openBrace hbyte' hstop hrel, ?_, ?_⟩
              · intro r hr
                rcases List.mem_cons.mp hr with rfl | hr
                · show (1 : Nat) < 256; decide
                · exact hbnd r hr
              · intro e he
                rw [consumeRecords, List.map_cons] at he
                rcases List.mem_cons.mp he with rfl | he
                · exact bodiesWithin_of_tag_ne (by simp [EventRecord.consume, ConsumerEvent.kind, stage2TagNum, EventRecord.tagKey]) (by simp [EventRecord.consume, ConsumerEvent.kind, stage2TagNum, EventRecord.tagStr])
                · exact hwit e he
          | closeBrace =>
              obtain ⟨hstop, hbyte⟩ := htb _ List.mem_cons_self
              have hbyte' : bs[s.start]? = some 0x7D := by
                simpa [Punct.byte] using hbyte
              refine ⟨EventRecord.tag 2 :: rs, .closeBrace hbyte' hstop hrel, ?_, ?_⟩
              · intro r hr
                rcases List.mem_cons.mp hr with rfl | hr
                · show (2 : Nat) < 256; decide
                · exact hbnd r hr
              · intro e he
                rw [consumeRecords, List.map_cons] at he
                rcases List.mem_cons.mp he with rfl | he
                · exact bodiesWithin_of_tag_ne (by simp [EventRecord.consume, ConsumerEvent.kind, stage2TagNum, EventRecord.tagKey]) (by simp [EventRecord.consume, ConsumerEvent.kind, stage2TagNum, EventRecord.tagStr])
                · exact hwit e he
          | openBracket =>
              obtain ⟨hstop, hbyte⟩ := htb _ List.mem_cons_self
              have hbyte' : bs[s.start]? = some 0x5B := by
                simpa [Punct.byte] using hbyte
              refine ⟨EventRecord.tag 3 :: rs, .openBracket hbyte' hstop hrel, ?_, ?_⟩
              · intro r hr
                rcases List.mem_cons.mp hr with rfl | hr
                · show (3 : Nat) < 256; decide
                · exact hbnd r hr
              · intro e he
                rw [consumeRecords, List.map_cons] at he
                rcases List.mem_cons.mp he with rfl | he
                · exact bodiesWithin_of_tag_ne (by simp [EventRecord.consume, ConsumerEvent.kind, stage2TagNum, EventRecord.tagKey]) (by simp [EventRecord.consume, ConsumerEvent.kind, stage2TagNum, EventRecord.tagStr])
                · exact hwit e he
          | closeBracket =>
              obtain ⟨hstop, hbyte⟩ := htb _ List.mem_cons_self
              have hbyte' : bs[s.start]? = some 0x5D := by
                simpa [Punct.byte] using hbyte
              refine ⟨EventRecord.tag 4 :: rs, .closeBracket hbyte' hstop hrel, ?_, ?_⟩
              · intro r hr
                rcases List.mem_cons.mp hr with rfl | hr
                · show (4 : Nat) < 256; decide
                · exact hbnd r hr
              · intro e he
                rw [consumeRecords, List.map_cons] at he
                rcases List.mem_cons.mp he with rfl | he
                · exact bodiesWithin_of_tag_ne (by simp [EventRecord.consume, ConsumerEvent.kind, stage2TagNum, EventRecord.tagKey]) (by simp [EventRecord.consume, ConsumerEvent.kind, stage2TagNum, EventRecord.tagStr])
                · exact hwit e he
      | null s =>
          obtain ⟨hbytes, hstop⟩ := htb _ List.mem_cons_self
          have hbytes' : (bs.drop s.start).take 4 = [0x6E, 0x75, 0x6C, 0x6C] := by
            have := congrArg ByteArray.toList hbytes
            simpa [ByteString.toList_take, ByteString.toList_drop,
              ByteString.toList_literal] using this
          refine ⟨EventRecord.tag 10 :: rs, .nullTag hbytes' hstop hrel, ?_, ?_⟩
          · intro r hr
            rcases List.mem_cons.mp hr with rfl | hr
            · show (10 : Nat) < 256; decide
            · exact hbnd r hr
          · intro e he
            rw [consumeRecords, List.map_cons] at he
            rcases List.mem_cons.mp he with rfl | he
            · exact bodiesWithin_of_tag_ne (by simp [EventRecord.consume, ConsumerEvent.kind, stage2TagNum, EventRecord.tagKey]) (by simp [EventRecord.consume, ConsumerEvent.kind, stage2TagNum, EventRecord.tagStr])
            · exact hwit e he
      | bool b s =>
          cases b with
          | true =>
              obtain ⟨hbytes, hstop⟩ := htb _ List.mem_cons_self
              have hbytes' : (bs.drop s.start).take 4 = [0x74, 0x72, 0x75, 0x65] := by
                have := congrArg ByteArray.toList hbytes
                simpa [ByteString.toList_take, ByteString.toList_drop,
                  ByteString.toList_literal] using this
              refine ⟨EventRecord.tag 8 :: rs, .trueTag hbytes' hstop hrel, ?_, ?_⟩
              · intro r hr
                rcases List.mem_cons.mp hr with rfl | hr
                · show (8 : Nat) < 256; decide
                · exact hbnd r hr
              · intro e he
                rw [consumeRecords, List.map_cons] at he
                rcases List.mem_cons.mp he with rfl | he
                · exact bodiesWithin_of_tag_ne (by simp [EventRecord.consume, ConsumerEvent.kind, stage2TagNum, EventRecord.tagKey]) (by simp [EventRecord.consume, ConsumerEvent.kind, stage2TagNum, EventRecord.tagStr])
                · exact hwit e he
          | false =>
              obtain ⟨hbytes, hstop⟩ := htb _ List.mem_cons_self
              have hbytes' : (bs.drop s.start).take 5 = [0x66, 0x61, 0x6C, 0x73, 0x65] := by
                have := congrArg ByteArray.toList hbytes
                simpa [ByteString.toList_take, ByteString.toList_drop,
                  ByteString.toList_literal] using this
              refine ⟨EventRecord.tag 9 :: rs, .falseTag hbytes' hstop hrel, ?_, ?_⟩
              · intro r hr
                rcases List.mem_cons.mp hr with rfl | hr
                · show (9 : Nat) < 256; decide
                · exact hbnd r hr
              · intro e he
                rw [consumeRecords, List.map_cons] at he
                rcases List.mem_cons.mp he with rfl | he
                · exact bodiesWithin_of_tag_ne (by simp [EventRecord.consume, ConsumerEvent.kind, stage2TagNum, EventRecord.tagKey]) (by simp [EventRecord.consume, ConsumerEvent.kind, stage2TagNum, EventRecord.tagStr])
                · exact hwit e he
      | number s =>
          obtain ⟨lex, hslice, hlen', hrfc, -⟩ := htb _ List.mem_cons_self
          obtain ⟨hlt0, -⟩ := hsp _ List.mem_cons_self
          have hlt : s.start < s.stop := by simpa only [Token.span] using hlt0
          obtain ⟨d, hread⟩ : ∃ d, StrtodReader.reader lex = some d := by
            have his := StrtodReader.reader_complete hrfc
            cases hrd : StrtodReader.reader lex with
            | none => rw [hrd] at his; cases his
            | some d => exact ⟨d, rfl⟩
          have hspan : s.stop = s.start + lex.length := by omega
          have hlex : (bs.drop s.start).take (s.stop - s.start) = lex.data.toList := by
            have h1 : ((bs.drop s.start).take (s.stop - s.start)) = lex.toList := by
              have := congrArg ByteArray.toList hslice
              simpa [ByteString.toList_take, ByteString.toList_drop,
                ByteString.toList_literal] using this
            simpa [ByteString.toList_eq_data_toList] using h1
          refine ⟨EventRecord.number (strtodSpec d).toBits :: rs,
            .number hread hspan hlex hrel, ?_, ?_⟩
          · intro r hr
            rcases List.mem_cons.mp hr with rfl | hr
            · exact toBits_lt_two_pow_64 _ (strtodSpec_isCode d)
            · exact hbnd r hr
          · intro e he
            rw [consumeRecords, List.map_cons] at he
            rcases List.mem_cons.mp he with rfl | he
            · exact bodiesWithin_of_tag_ne (by simp [EventRecord.consume, ConsumerEvent.kind, ConsumerEvent.number, stage2TagNum, EventRecord.tagKey]) (by simp [EventRecord.consume, ConsumerEvent.kind, ConsumerEvent.number, stage2TagNum, EventRecord.tagStr])
            · exact hwit e he
      | string s =>
          obtain ⟨hq, cs, hstr⟩ := htb _ List.mem_cons_self
          obtain ⟨hlt0, hstop_le0⟩ := hsp _ List.mem_cons_self
          have hlt : s.start < s.stop := by simpa only [Token.span] using hlt0
          have hstop_le : s.stop ≤ bs.length := by simpa only [Token.span] using hstop_le0
          have hq' : bs[s.start]? = some 0x22 := by simpa using hq
          have htwo : s.start + 2 ≤ s.stop := stringAt_two_le hstr hstop_le
          have hcode : bodyCodePoints bs s = some cs := stringAt_bodyCodePoints hstr
          let len := s.stop - s.start - 2
          have hspan : s.stop = s.start + 2 + len := by omega
          refine ⟨EventRecord.str false len (plainSpan (s.start + 1)) :: rs,
            .strPlain hq' hspan hcode hrel, ?_, ?_⟩
          · intro r hr
            rcases List.mem_cons.mp hr with rfl | hr
            · refine ⟨?_, ?_⟩
              · show s.stop - s.start - 2 < 2 ^ 32
                omega
              · show plainSpan (s.start + 1) < 2 ^ 64
                unfold plainSpan
                omega
            · exact hbnd r hr
          · intro e he
            rw [consumeRecords, List.map_cons] at he
            rcases List.mem_cons.mp he with hhead | he
            · rw [hhead]
              unfold EventRecord.consume ConsumerEvent.BodiesWithin
              intro _
              rw [eventBridge_stringConsumer_payload, eventBridge_stringConsumer_len]
              rw [ite_eq_right (by unfold plainSpan; omega)]
              unfold plainSpan
              omega
            · exact hwit e he

/-- **The producer.**  Every document the reference parser accepts at the default
limits has a record supply at `Stage2Records`: the relation's per-class
premises are exactly the parse's per-token facts. -/
theorem stage2NoEventWalkRecordsSupply_of_parse {bs : List UInt8} {arena : List UInt8}
    {t : Tape} (h : parseBytes Limits.default (ByteString.literal bs) = .ok t) :
    Nonempty (Stage2NoEventWalkRecordsSupply bs arena t) := by
  obtain ⟨v, hdec, hin, -⟩ :=
    decodeTape_correct Limits.default (ByteString.literal bs) t h
  have hinputlen : bs.length ≤ 2 ^ 20 := by
    have hlit : (ByteString.literal bs).length = bs.length := by simp
    have hmax : (ByteString.literal bs).length ≤ Limits.default.maxInput := by
      unfold parseBytes at h
      split at h
      · cases h
      · rename_i hle
        omega
    have : Limits.default.maxInput = 2 ^ 20 := rfl
    omega
  have hspans : spansWellFormed t = true := (tape_valid t v hdec).1
  have htb0 : ∀ tok ∈ t.tokens, TokenBytes t.input tok := tape_tokenBytes t v hdec
  have htb : ∀ tok ∈ t.tokens, TokenBytes (ByteString.literal bs) tok := by
    intro tok htok
    rw [← hin]
    exact htb0 tok htok
  have hsp : ∀ tok ∈ t.tokens, tok.span.start < tok.span.stop ∧ tok.span.stop ≤ bs.length := by
    intro tok htok
    obtain ⟨h1, h2, -⟩ := checkSpans_mem (prev := 0) hspans htok
    have hlen : t.input.length = bs.length := by rw [hin]; simp
    exact ⟨h1, by omega⟩
  obtain ⟨rs, hrel, hbnd, hwit⟩ := records_exists hinputlen t.tokens htb hsp
  exact ⟨⟨rs, hrel, hbnd, hwit⟩⟩

/-! ### The witness `"\/"` is absorbed

`"\/"` — quote, backslash, slash, quote.  Its body is the two-character escape
`\/`, so the tape's escape-aware scan reads one code point, `0x2F`, while the raw
UTF-8 decoder reads two, `0x5C, 0x2F`.  `Stage2Records`'s plain row asks only the
former. -/

/-- The document `"\/"`. -/
def escapeDoc : List UInt8 := [0x22, 0x5C, 0x2F, 0x22]

/-- The tape's own reader sees the one escaped code point. -/
theorem escapeDoc_bodyCodePoints : bodyCodePoints escapeDoc ⟨0, 4⟩ = some [0x2F] := by
  decide

/-- The UTF-8 decoder over the raw body sees two, and that is the divergence the
old plain row required the two to bridge. -/
theorem escapeDoc_rawCodePoints :
    escapeCodePoints (((escapeDoc.drop ((⟨0, 4⟩ : Span).start + 1)).take 2)) =
      some [0x5C, 0x2F] := by
  decide

/-- **The witness is absorbed.**  The restated plain row takes the escape-aware
reading, so the document's one string token has a record at the empty arena. -/
theorem escapeDoc_records :
    Stage2Records escapeDoc [] [EventRecord.str false 2 (plainSpan 1)]
      [.string ⟨0, 4⟩] := by
  refine .strPlain (key := false) (s := ⟨0, 4⟩) (len := 2) (cs := [0x2F]) ?_ ?_ ?_ .nil
  · decide
  · decide
  · exact escapeDoc_bodyCodePoints

/-- **The supply at the witness.**  The record is inside its field widths and the
body's extent is inside the document. -/
theorem escapeDoc_supply :
    Nonempty (Stage2NoEventWalkRecordsSupply escapeDoc []
      ⟨ByteString.literal escapeDoc, [.string ⟨0, 4⟩]⟩) := by
  refine ⟨⟨[EventRecord.str false 2 (plainSpan 1)], escapeDoc_records, ?_, ?_⟩⟩
  · intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    refine ⟨?_, ?_⟩
    · show 2 < 2 ^ 32; decide
    · show plainSpan (1 : Nat) < 2 ^ 64
      unfold plainSpan
      decide
  · intro e he
    rw [consumeRecords, List.map_cons, List.map_nil, List.mem_singleton] at he
    subst he
    unfold EventRecord.consume ConsumerEvent.BodiesWithin
    intro _
    rw [eventBridge_stringConsumer_payload, eventBridge_stringConsumer_len]
    rw [ite_eq_right (by unfold plainSpan; decide)]
    unfold plainSpan
    decide

/-! ### The positive control -/

/-- **`null` is still absorbed.**  The literal rows are unchanged. -/
theorem nullDoc_supply :
    Nonempty (Stage2NoEventWalkRecordsSupply nullDoc []
      ⟨ByteString.literal nullDoc, [.null ⟨0, 4⟩]⟩) := by
  refine ⟨⟨[EventRecord.tag 10], ?_, ?_, ?_⟩⟩
  · exact .nullTag (by decide) (by decide) .nil
  · intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    show (10 : Nat) < 256
    decide
  · intro e he
    rw [consumeRecords, List.map_cons, List.map_nil, List.mem_singleton] at he
    subst he
    exact bodiesWithin_of_tag_ne (by simp [EventRecord.consume, ConsumerEvent.kind, stage2TagNum, EventRecord.tagKey]) (by simp [EventRecord.consume, ConsumerEvent.kind, stage2TagNum, EventRecord.tagStr])

/-! ### The exponent spelling is absorbed

`1E5`: the scanner accepts `E` and `+`, and the reader normalises them.  The old
number row asked for a `Decimal` whose `lexeme` is the span's bytes, which no
`Decimal` supplies; the restated row asks for the reader's decimal instead. -/

/-- The document `1E5`. -/
def eDoc : List UInt8 := [0x31, 0x45, 0x35]

/-- The reader's normalised decimal for `1E5`. -/
def eDecimal : Decimal :=
  { neg := false, ip := ByteString.literal [0x31], fr := none,
    ex := some (false, ByteString.literal [0x35]) }

/-- The reader normalises `E` to its own decomposition. -/
theorem eDoc_reader : StrtodReader.reader (ByteString.literal eDoc) = some eDecimal := by
  decide

/-- `1E5` is an RFC 8259 number, so the boundary admits it. -/
theorem eDoc_rfcNumber : RfcNumber (ByteString.literal eDoc) := by
  refine RfcNumber.pos ?_
  have hip : IntPart (ByteString.literal [0x31]) :=
    IntPart.lead (b := 0x31) (bs := empty) (by decide) (by decide) Digits0.nil
  have hexp : ExpPart (ByteString.literal [0x45, 0x35]) :=
    ExpPart.mk (e := 0x45) (sign := empty) (ds := 0x35 +: empty)
      (Or.inr rfl) (Or.inl rfl) (Digits.one (by decide))
  have hcat : ByteString.literal [0x31] ++ ByteString.literal [0x45, 0x35] =
      ByteString.literal eDoc := by
    apply ByteString.eq_of_toList_eq
    simp [eDoc, ByteString.toList_append]
  have hbody : NumBody (ByteString.literal [0x31] ++ ByteString.literal [0x45, 0x35]) :=
    NumBody.exp hip hexp
  rw [hcat] at hbody
  exact hbody

/-- **`1E5` is absorbed.** -/
theorem eDoc_records :
    Stage2Records eDoc [] [EventRecord.number (strtodSpec eDecimal).toBits]
      [.number ⟨0, 3⟩] := by
  refine .number (d := eDecimal) (lex := ByteString.literal eDoc) eDoc_reader ?_ ?_ .nil
  · decide
  · decide

/-- **The supply at `1E5`.** -/
theorem eDoc_supply :
    Nonempty (Stage2NoEventWalkRecordsSupply eDoc []
      ⟨ByteString.literal eDoc, [.number ⟨0, 3⟩]⟩) := by
  refine ⟨⟨[EventRecord.number (strtodSpec eDecimal).toBits], eDoc_records, ?_, ?_⟩⟩
  · intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    exact toBits_lt_two_pow_64 _ (strtodSpec_isCode eDecimal)
  · intro e he
    rw [consumeRecords, List.map_cons, List.map_nil, List.mem_singleton] at he
    subst he
    exact bodiesWithin_of_tag_ne (by simp [EventRecord.consume, ConsumerEvent.kind, ConsumerEvent.number, stage2TagNum, EventRecord.tagKey]) (by simp [EventRecord.consume, ConsumerEvent.kind, ConsumerEvent.number, stage2TagNum, EventRecord.tagStr])

/-- **The accept arm's records obligation, discharged.**  An admitted document is
accepted by the reference, and its parse supplies the trace at the tape admission
names. -/
theorem Stage2NoEventAdmitted.referenceRecords {bs arena : List UInt8}
    (h : Stage2NoEventAdmitted bs) : Stage2NoEventReferenceRecords bs arena := by
  obtain ⟨t, ht⟩ := h.referenceAccepts
  exact ⟨t, ht, stage2NoEventWalkRecordsSupply_of_parse ht⟩

/-! ### Axiom footprints -/

#print axioms stringAt_two_le
#print axioms stringAt_bodyCodePoints
#print axioms records_exists
#print axioms stage2NoEventWalkRecordsSupply_of_parse
#print axioms escapeDoc_records
#print axioms escapeDoc_supply
#print axioms nullDoc_supply
#print axioms eDoc_reader
#print axioms eDoc_records
#print axioms eDoc_supply
#print axioms Stage2NoEventAdmitted.referenceRecords

end LeanLLVM.Refinement
