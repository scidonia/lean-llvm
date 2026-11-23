/-
The no-event stage-2 variant at the consumer boundary.

`kernel/json/stage2.c` validates the grammar, decodes string bodies, converts
numbers and materialises an event stream (`T_*` records, `stage2.h:68-75`).  A
caller's consumer reads that stream with the arena and nothing else: it walks one
record at a time, counts one token per record, and sums `arena`'s bytes together
with each record's `tag + len + payload`.  The certified side of that boundary is
`Stage2EventRel`/`Stage2Records` (`JsonStage2Spec`, `JsonStage2Hsem`): the
document, the arena prefix, the emitted bytes and the reference parser's tokens.

A *no-event* stage 2 is the same walk with the event stores replaced by that
consumer's accumulations: it still validates and decodes, and it still has the
same verdict and the same first error offset, but it writes no `EventRecord` and
no event buffer.  This module is the consumer-boundary projection of that
variant, and it is a theorem about the same parse, not a second parser:

* **the consumer's record** — `ConsumerEvent` is one event as the consumer sees
  it: its tag byte, the `len` and `payload` fields the thirteen- or nine-byte
  record would carry, and the decoded code points a string body reads back as.
  `consumeBytes` reads a stream into those events exactly as the caller's fold
  does, and `consumer` is the same fold over the walk's `List EventRecord`.
* **the no-event walk** — `Stage2NoEvent` is `Stage2Records` with `EventRecord`
  replaced by `ConsumerEvent`: the same constructors, the same document and arena
  hypotheses, the same token list, and no event bytes at all.  Its string rows
  carry the decoded code points rather than a span, and its number row carries
  `strtodSpec`'s bits rather than the eight payload bytes.
* **the projection** — `Stage2Records.toNoEvent` consumes the trace at the
  variant's vocabulary, and `consumeBytes_flatten`/`consumer_eq_noEventFold`
  make the caller's fold over the emitted stream equal the no-event fold over
  those events.  At the boundary (`stage2Boundary_noEventConsumer`) the two
  results are one value: `tokens`, `values`, `arena` and `sum` agree, the token
  list is the parser's, and the decoded value is `decodeTape`'s.
* **the verdict and the refusal** — the variant's control flow is the certified
  walk's, so its verdict is the run's own word and its refusal is the run's
  `*err`.  `stage2Boundary_noEventRefusal` reads the refusal half at
  `RefusalOffset`, the same policy the certified boundary states.
* **the ABI obstruction** — with no event stream, the current ABI's remaining
  outputs are the arena, its cursor, the verdict and `*err`.  Those do not
  determine what the consumer reads: `noEvent_abi_obstruction` exhibits two
  accepted documents with the same empty arena and the same unchanged refusal
  word whose consumer results differ.  So a no-event implementation cannot hand
  the consumer's `tokens`/`values`/`sum` out through the current ABI: it needs
  new output channels (the prototype's `tokens`/`values`/`sum` out-pointers and
  its scratch buffer), which is an ABI change rather than a projection.  The
  theorem below is the model-level projection; the last section states the
  obstruction rather than weakening that result.

The reference consumer modelled here is the caller's fold of the bench harness
that times the prototype, kept out of the tree; its numbers are the ones the
no-event prototype accumulates.  What is *not* proved here is the prototype's
own control-flow refinement to this walk (it is a separate C body), and the
incremental arena cursor's equality with the record offsets, which is the walk's
existing `*ndst` carry rather than a fact of the relation.  Neither is assumed as
a premise of the projection.

There is no `sorry`, `admit` or `native_decide`.
-/
import LeanLLVM.Refinement.JsonStage2Hsem
import LeanLLVM.Refinement.JsonStage2TokenCorrespondence
import LeanLLVM.JsonCallRoute

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonUtf8IR

/-! ### The consumer's record

One event as the caller's fold sees it: the tag byte, the two payload fields the
record carries, and — for a string — the code points the body decodes to.  The
`len`/`payload` fields are the record's own so the fold can add exactly what the
emitted bytes would have carried; `cps` is the decoded body, which is what a
consumer that wants the string reads off the document or the arena. -/

/-- One event at the consumer's vocabulary. -/
structure ConsumerEvent where
  /-- The record's first byte: `T_OBJ`, `T_OBJ_END`, `T_ARR`, `T_ARR_END`,
  `T_KEY`, `T_STR`, `T_NUM`, `T_TRUE`, `T_FALSE` or `T_NULL`. -/
  tag : Nat
  /-- The four-byte length a key or string record carries; zero otherwise. -/
  len : Nat
  /-- A number's eight payload bits, or a key's/string's eight-byte field. -/
  payload : Nat
  /-- The decoded body's code points; empty for a non-string event. -/
  cps : List Nat
deriving DecidableEq, Repr

namespace ConsumerEvent

/-- A container marker or literal tag. -/
def kind (t : Nat) : ConsumerEvent :=
  ⟨t, 0, 0, []⟩

/-- A number: `T_NUM` and the payload the record would hold. -/
def number (bits : Nat) : ConsumerEvent :=
  ⟨stage2TagNum, 0, bits, []⟩

/-- A key or string: `T_KEY`/`T_STR`, the length, the span-or-arena field, and
the decoded code points. -/
def str (key : Bool) (len field : Nat) (cps : List Nat) : ConsumerEvent :=
  ⟨(if key then EventRecord.tagKey else EventRecord.tagStr), len, field, cps⟩

/-- The consumer's per-record contribution to its sum: `tag + len + payload`. -/
def terms (e : ConsumerEvent) : Nat :=
  e.tag + e.len + e.payload

end ConsumerEvent

/-- The sum of a byte prefix, as the consumer accumulates the arena. -/
def byteSum : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + byteSum bs

theorem byteSum_append : ∀ (a b : List UInt8),
    byteSum (a ++ b) = byteSum a + byteSum b
  | [], _ => by simp [byteSum]
  | _ :: as, b => by
      simp [byteSum, byteSum_append as b, Nat.add_assoc]

/-! ### The certified consumer over the walk's trace

`consumer` is the caller's fold read at the walk's own records: one token and one
value per record, and the arena's byte sum plus each record's
`tag + len + payload`.  `EventRecord.terms` is the per-record contribution, in
the record's fields rather than in its bytes; the byte reader below is what ties
the two together. -/

/-- The consumer's per-record contribution, from the record's fields. -/
def EventRecord.terms : EventRecord → Nat
  | .tag t => t
  | .number bits => stage2TagNum + bits
  | .str key len span => (if key then EventRecord.tagKey else EventRecord.tagStr) + len + span

/-- What the caller's fold reports: one token and one value per event, the
arena's byte sum, and the sum of the arena and every record's contribution. -/
structure ConsumerResult where
  tokens : Nat
  values : Nat
  arena : Nat
  sum : Nat
deriving DecidableEq, Repr

/-- The caller's fold at the walk's trace. -/
def consumer (arenaBytes : List UInt8) (rs : List EventRecord) : ConsumerResult :=
  let a := byteSum arenaBytes
  { tokens := rs.length, values := rs.length, arena := a,
    sum := a + (rs.map EventRecord.terms).sum }

/-- The caller's fold at the no-event walk's events. -/
def noEventFold (arenaBytes : List UInt8) (obs : List ConsumerEvent) : ConsumerResult :=
  let a := byteSum arenaBytes
  { tokens := obs.length, values := obs.length, arena := a,
    sum := a + (obs.map ConsumerEvent.terms).sum }

/-! ### The byte reader

`consumeBytes` is the caller's reader over the emitted stream: a record's first
byte announces its width, the payload fields are read little-endian, and a string
body is decoded through the same `escapeCodePoints` the relation uses.  It is a
total function — the caller's loop, not the walk's — so it reads any stream; on a
stream a related trace was written as it is the trace's events
(`consumeBytes_flatten`). -/

/-- A string event's decoded body: the document's body for the top-bit-set plain
form, the arena slice for the clear-bit escaped form.  A body that does not
decode yields no code points; on a related stream the relation's own hypothesis
says it does. -/
def stringConsumer (bs arena : List UInt8) (key : Bool) (len field : Nat) :
    ConsumerEvent :=
  if field < 2 ^ 63 then
    .str key len field ((escapeCodePoints ((arena.drop field).take len)).getD [])
  else
    .str key len field ((escapeCodePoints ((bs.drop (field - 2 ^ 63)).take len)).getD [])

/-- The consumer's reading of one record. -/
def EventRecord.consume (bs arena : List UInt8) : EventRecord → ConsumerEvent
  | .tag t => .kind t
  | .number bits => .number bits
  | .str key len span => stringConsumer bs arena key len span

/-- The consumer's reading of a trace, record for record. -/
def consumeRecords (bs arena : List UInt8) (rs : List EventRecord) :
    List ConsumerEvent :=
  rs.map (EventRecord.consume bs arena)

/-- The caller's reader over the event bytes.  A stream that ends inside a record
stops where the caller's fold stops; a related trace never does. -/
def consumeBytes (bs arena : List UInt8) : List UInt8 → List ConsumerEvent
  | [] => []
  | b :: rest =>
      match b.toNat with
      | 1 => .kind 1 :: consumeBytes bs arena rest
      | 2 => .kind 2 :: consumeBytes bs arena rest
      | 3 => .kind 3 :: consumeBytes bs arena rest
      | 4 => .kind 4 :: consumeBytes bs arena rest
      | 8 => .kind 8 :: consumeBytes bs arena rest
      | 9 => .kind 9 :: consumeBytes bs arena rest
      | 10 => .kind 10 :: consumeBytes bs arena rest
      | 5 =>
          if rest.length < 12 then []
          else
            let len := bytesToNat (rest.take 4)
            let field := bytesToNat ((rest.drop 4).take 8)
            stringConsumer bs arena true len field ::
              consumeBytes bs arena (rest.drop 12)
      | 6 =>
          if rest.length < 12 then []
          else
            let len := bytesToNat (rest.take 4)
            let field := bytesToNat ((rest.drop 4).take 8)
            stringConsumer bs arena false len field ::
              consumeBytes bs arena (rest.drop 12)
      | 7 =>
          if rest.length < 8 then []
          else
            .number (bytesToNat (rest.take 8)) ::
              consumeBytes bs arena (rest.drop 8)
      | _ => []
termination_by evs => evs.length
decreasing_by
  all_goals
    simp only [List.length_cons, List.length_drop]
    omega

/-- The consumer's fold at a byte stream. -/
def consumeBytesResult (bs : List UInt8) (arenaBytes : List UInt8)
    (evs : List UInt8) : ConsumerResult :=
  let es := consumeBytes bs arenaBytes evs
  let a := byteSum arenaBytes
  { tokens := es.length, values := es.length, arena := a,
    sum := a + (es.map ConsumerEvent.terms).sum }

/-! ### The no-event walk

`Stage2NoEvent` is `Stage2Records` at the consumer's vocabulary: the same
constructors and the same document/arena hypotheses, with `ConsumerEvent` in
place of `EventRecord` and no event bytes on the left.  Its string rows carry the
decoded code points, and its number row carries `strtodSpec`'s bits; nothing here
mentions an emitted stream. -/

/-- The no-event walk's relation: the document, the arena prefix, the consumer's
events and the reference parser's tokens.  A comma and a colon carry no event; a
container or literal is its tag; a number is `strtodSpec`'s bits of the span's
lexeme; a key or string is its length, its record field and its decoded body. -/
inductive Stage2NoEvent (bs arena : List UInt8) :
    List ConsumerEvent → List Token → Prop where
  /-- No events, no tokens. -/
  | nil : Stage2NoEvent bs arena [] []
  /-- A comma separator has no event. -/
  | comma {s : Span} {es : List ConsumerEvent} {toks : List Token}
      (h : Stage2NoEvent bs arena es toks) :
      Stage2NoEvent bs arena es (.punct .comma s :: toks)
  /-- A colon separator has no event. -/
  | colon {s : Span} {es : List ConsumerEvent} {toks : List Token}
      (h : Stage2NoEvent bs arena es toks) :
      Stage2NoEvent bs arena es (.punct .colon s :: toks)
  /-- `{` (`T_OBJ = 1`). -/
  | openBrace {s : Span} {es : List ConsumerEvent} {toks : List Token}
      (hbyte : bs[s.start]? = some 0x7B) (hspan : s.stop = s.start + 1)
      (h : Stage2NoEvent bs arena es toks) :
      Stage2NoEvent bs arena (.kind 1 :: es) (.punct .openBrace s :: toks)
  /-- `}` (`T_OBJ_END = 2`). -/
  | closeBrace {s : Span} {es : List ConsumerEvent} {toks : List Token}
      (hbyte : bs[s.start]? = some 0x7D) (hspan : s.stop = s.start + 1)
      (h : Stage2NoEvent bs arena es toks) :
      Stage2NoEvent bs arena (.kind 2 :: es) (.punct .closeBrace s :: toks)
  /-- `[` (`T_ARR = 3`). -/
  | openBracket {s : Span} {es : List ConsumerEvent} {toks : List Token}
      (hbyte : bs[s.start]? = some 0x5B) (hspan : s.stop = s.start + 1)
      (h : Stage2NoEvent bs arena es toks) :
      Stage2NoEvent bs arena (.kind 3 :: es) (.punct .openBracket s :: toks)
  /-- `]` (`T_ARR_END = 4`). -/
  | closeBracket {s : Span} {es : List ConsumerEvent} {toks : List Token}
      (hbyte : bs[s.start]? = some 0x5D) (hspan : s.stop = s.start + 1)
      (h : Stage2NoEvent bs arena es toks) :
      Stage2NoEvent bs arena (.kind 4 :: es) (.punct .closeBracket s :: toks)
  /-- `true` (`T_TRUE = 8`). -/
  | trueTag {s : Span} {es : List ConsumerEvent} {toks : List Token}
      (hbytes : (bs.drop s.start).take 4 = [0x74, 0x72, 0x75, 0x65])
      (hspan : s.stop = s.start + 4)
      (h : Stage2NoEvent bs arena es toks) :
      Stage2NoEvent bs arena (.kind 8 :: es) (.bool true s :: toks)
  /-- `false` (`T_FALSE = 9`). -/
  | falseTag {s : Span} {es : List ConsumerEvent} {toks : List Token}
      (hbytes : (bs.drop s.start).take 5 = [0x66, 0x61, 0x6C, 0x73, 0x65])
      (hspan : s.stop = s.start + 5)
      (h : Stage2NoEvent bs arena es toks) :
      Stage2NoEvent bs arena (.kind 9 :: es) (.bool false s :: toks)
  /-- `null` (`T_NULL = 10`). -/
  | nullTag {s : Span} {es : List ConsumerEvent} {toks : List Token}
      (hbytes : (bs.drop s.start).take 4 = [0x6E, 0x75, 0x6C, 0x6C])
      (hspan : s.stop = s.start + 4)
      (h : Stage2NoEvent bs arena es toks) :
      Stage2NoEvent bs arena (.kind 10 :: es) (.null s :: toks)
  /-- A number (`T_NUM = 7`): the payload is `strtodSpec`'s bits of the span's
  well-formed lexeme. -/
  | number {s : Span} {es : List ConsumerEvent} {toks : List Token} {d : Decimal}
      (hwf : d.wellFormed)
      (hspan : s.stop = s.start + d.lexeme.length)
      (hlexeme : (bs.drop s.start).take (s.stop - s.start) = d.lexeme.data.toList)
      (h : Stage2NoEvent bs arena es toks) :
      Stage2NoEvent bs arena (.number (strtodSpec d).toBits :: es) (.number s :: toks)
  /-- A key or string written in the plain form: the record field is the body's
  first document byte with the top bit set, the length is the body's length, and
  the body decodes to the token's code points. -/
  | strPlain {key : Bool} {s : Span} {es : List ConsumerEvent} {toks : List Token}
      {len : Nat} {cs : List Nat}
      (hquote : bs[s.start]? = some 0x22)
      (hspan : s.stop = s.start + 2 + len)
      (hbody : escapeCodePoints ((bs.drop (s.start + 1)).take len) = some cs)
      (hcode : bodyCodePoints bs s = some cs)
      (h : Stage2NoEvent bs arena es toks) :
      Stage2NoEvent bs arena
        (.str key len (plainSpan (s.start + 1)) cs :: es) (.string s :: toks)
  /-- A key or string written in the arena form: the length is the decoded byte
  count, the field is the arena offset (below `2 ^ 63`), and the slice decodes to
  the token's code points. -/
  | strArena {key : Bool} {s : Span} {es : List ConsumerEvent} {toks : List Token}
      {len off : Nat} {cs : List Nat}
      (hquote : bs[s.start]? = some 0x22)
      (hspan : s.start + 2 ≤ s.stop)
      (hcode : bodyCodePoints bs s = some cs)
      (hbelow : off < 2 ^ 63)
      (harena : escapeCodePoints ((arena.drop off).take len) = some cs)
      (h : Stage2NoEvent bs arena es toks) :
      Stage2NoEvent bs arena (.str key len off cs :: es) (.string s :: toks)

/-! ### The decoded body is the code-point list

The reader's decoding at a related string record is the token's code points. -/

/-- A plain string's consumer event: the field is the span's top-bit-set form, so
the reader takes the document's body. -/
theorem stringConsumer_plain {bs arena : List UInt8} {key : Bool} {len field
    bodyStart : Nat} {cs : List Nat}
    (hge : 2 ^ 63 ≤ field) (hsub : field - 2 ^ 63 = bodyStart)
    (h : escapeCodePoints ((bs.drop bodyStart).take len) = some cs) :
    stringConsumer bs arena key len field = .str key len field cs := by
  unfold stringConsumer
  rw [if_neg (by omega), hsub, h]
  rfl

/-- An escaped string's consumer event: the field is the arena offset. -/
theorem stringConsumer_arena {bs arena : List UInt8} {key : Bool} {len field : Nat}
    {cs : List Nat} (hlt : field < 2 ^ 63)
    (h : escapeCodePoints ((arena.drop field).take len) = some cs) :
    stringConsumer bs arena key len field = .str key len field cs := by
  unfold stringConsumer
  rw [if_pos hlt, h]
  rfl

/-! ### The trace is the no-event walk

The certified trace's records, read by the consumer, are exactly the events the
no-event walk produces.  The string rows need the two field/body lemmas above;
the number and tag rows are the record's own fields. -/

/-- The plain form's field is never below the top bit. -/
theorem plainSpan_not_lt (a : Nat) : ¬ plainSpan a < 2 ^ 63 := by
  unfold plainSpan
  omega

/-- The plain form's field addresses the body's first byte once the top bit is
cleared. -/
theorem plainSpan_sub (a : Nat) : plainSpan a - 2 ^ 63 = a := by
  unfold plainSpan
  omega

/-- **The trace at the consumer's vocabulary.**  A related `Stage2Records` trace,
with each record replaced by the event the consumer reads from it, satisfies the
no-event walk at the same tokens. -/
theorem Stage2Records.toNoEvent {bs arena : List UInt8} {rs : List EventRecord}
    {toks : List Token} (h : Stage2Records bs arena rs toks) :
    Stage2NoEvent bs arena (consumeRecords bs arena rs) toks := by
  induction h with
  | nil => exact Stage2NoEvent.nil
  | comma _ ih => exact Stage2NoEvent.comma ih
  | colon _ ih => exact Stage2NoEvent.colon ih
  | openBrace hb hs _ ih =>
      simpa only [consumeRecords, List.map_cons, EventRecord.consume,
        ConsumerEvent.kind] using Stage2NoEvent.openBrace hb hs ih
  | closeBrace hb hs _ ih =>
      simpa only [consumeRecords, List.map_cons, EventRecord.consume,
        ConsumerEvent.kind] using Stage2NoEvent.closeBrace hb hs ih
  | openBracket hb hs _ ih =>
      simpa only [consumeRecords, List.map_cons, EventRecord.consume,
        ConsumerEvent.kind] using Stage2NoEvent.openBracket hb hs ih
  | closeBracket hb hs _ ih =>
      simpa only [consumeRecords, List.map_cons, EventRecord.consume,
        ConsumerEvent.kind] using Stage2NoEvent.closeBracket hb hs ih
  | trueTag hb hs _ ih =>
      simpa only [consumeRecords, List.map_cons, EventRecord.consume,
        ConsumerEvent.kind] using Stage2NoEvent.trueTag hb hs ih
  | falseTag hb hs _ ih =>
      simpa only [consumeRecords, List.map_cons, EventRecord.consume,
        ConsumerEvent.kind] using Stage2NoEvent.falseTag hb hs ih
  | nullTag hb hs _ ih =>
      simpa only [consumeRecords, List.map_cons, EventRecord.consume,
        ConsumerEvent.kind] using Stage2NoEvent.nullTag hb hs ih
  | number hwf hs hlex _ ih =>
      simpa only [consumeRecords, List.map_cons, EventRecord.consume,
        ConsumerEvent.number] using Stage2NoEvent.number hwf hs hlex ih
  | strPlain hq hs hbody hcode _ ih =>
      simpa only [consumeRecords, List.map_cons, EventRecord.consume,
        stringConsumer, plainSpan_not_lt, plainSpan_sub, hbody, Option.getD_some,
        ↓reduceIte]
        using Stage2NoEvent.strPlain hq hs hbody hcode ih
  | strArena hq hs hcode hbelow harena _ ih =>
      simpa only [consumeRecords, List.map_cons, EventRecord.consume,
        stringConsumer, hbelow, harena, Option.getD_some, ↓reduceIte]
        using Stage2NoEvent.strArena hq hs hcode hbelow harena ih

/-- **The trace's length is the record-carrying token count.**  The two
separators consume no record, so the trace's length equals the token list's with
them removed. -/
theorem Stage2Records.length_nonSeparators {bs arena : List UInt8}
    {rs : List EventRecord} {toks : List Token}
    (h : Stage2Records bs arena rs toks) :
    rs.length = (Token.nonSeparators toks).length := by
  induction h with
  | nil => rfl
  | comma _ ih => simp [Token.nonSeparators, ih]
  | colon _ ih => simp [Token.nonSeparators, ih]
  | openBrace _ _ _ ih => simp [Token.nonSeparators, ih]
  | closeBrace _ _ _ ih => simp [Token.nonSeparators, ih]
  | openBracket _ _ _ ih => simp [Token.nonSeparators, ih]
  | closeBracket _ _ _ ih => simp [Token.nonSeparators, ih]
  | trueTag _ _ _ ih => simp [Token.nonSeparators, ih]
  | falseTag _ _ _ ih => simp [Token.nonSeparators, ih]
  | nullTag _ _ _ ih => simp [Token.nonSeparators, ih]
  | number _ _ _ _ ih => simp [Token.nonSeparators, ih]
  | strPlain _ _ _ _ _ ih => simp [Token.nonSeparators, ih]
  | strArena _ _ _ _ _ _ ih => simp [Token.nonSeparators, ih]

/-- **The per-record contribution is the consumer's.**  Replacing a record by
the event the consumer reads does not change `tag + len + payload`. -/
theorem EventRecord.terms_consume (bs arena : List UInt8) (r : EventRecord) :
    ConsumerEvent.terms (EventRecord.consume bs arena r) = EventRecord.terms r := by
  cases r with
  | tag t => rfl
  | number bits => rfl
  | str key len span =>
      cases key <;>
        simp only [EventRecord.consume, stringConsumer, ConsumerEvent.terms,
          ConsumerEvent.str, EventRecord.terms, EventRecord.tagKey,
          EventRecord.tagStr] <;>
        split <;> rfl

/-- **The two folds are one.**  The caller's fold over the trace equals the
no-event fold over the events the trace's records read as. -/
theorem consumer_eq_noEventFold (bs arenaBytes : List UInt8) (rs : List EventRecord) :
    consumer arenaBytes rs = noEventFold arenaBytes (consumeRecords bs arenaBytes rs) := by
  unfold consumer noEventFold consumeRecords
  have hterms : (List.map ConsumerEvent.terms
        (List.map (EventRecord.consume bs arenaBytes) rs)) =
      List.map EventRecord.terms rs := by
    rw [List.map_map]
    exact List.map_congr_left fun r _ => EventRecord.terms_consume bs arenaBytes r
  rw [hterms]
  simp only [List.length_map]

/-! ### The byte reader on an emitted trace

The caller reads bytes, so the emitted encoding's widths and little-endian
fields have to read back as the record's fields.  `EventRecord.Bounded` is the
reader's width condition: a tag below a byte, a number below the 64-bit word, a
string's length below the 32-bit field and its field below the 64-bit word.  The
three width lemmas below are the reader's per-class steps, and
`consumeBytes_flatten` is the whole trace. -/

/-- **A one-byte tag reads back as its event.** -/
theorem consumeBytes_of_tag {bs arena : List UInt8} {t : Nat}
    (ht : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 8 ∨ t = 9 ∨ t = 10)
    (rest : List UInt8) :
    consumeBytes bs arena (tagRecord t ++ rest) =
      ConsumerEvent.kind t :: consumeBytes bs arena rest := by
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [tagRecord, EventRecord.encodedBytes, consumeBytes, ConsumerEvent.kind]

/-- **A number record reads back as its bits.**  The eight-byte payload is the
little-endian `Nat` the record held, read whole. -/
theorem consumeBytes_number {bs arena : List UInt8} (bits : Nat)
    (hbits : bits < 2 ^ 64) (rest : List UInt8) :
    consumeBytes bs arena (numberRecordBytes bits ++ rest) =
      ConsumerEvent.number bits :: consumeBytes bs arena rest := by
  unfold numberRecordBytes
  simp only [EventRecord.encodedBytes, numberRecord, List.flatten_cons,
    List.flatten_nil, List.nil_append, List.cons_append, List.append_assoc]
  have htag : (UInt8.ofNat stage2TagNum).toNat = 7 := by decide
  simp only [consumeBytes, htag]
  split_ifs with hlen
  · exfalso
    rw [List.length_append, wordBytes, natToBytes_length] at hlen
    omega
  · rw [take_wordBytes, drop_wordBytes,
      bytesToNat_wordBytes (w := 8)
        (by rw [show (256 : Nat) ^ 8 = 2 ^ 64 from by decide]; exact hbits)]

/-- **A key or string record reads back as its fields.**  The four-byte length
and the eight-byte field are read little-endian, and the head is the string's
consumer event. -/
theorem consumeBytes_str_payload {bs arena : List UInt8} (key : Bool) (tag : Nat)
    (hkey : tag = if key then 5 else 6) (len span : Nat)
    (hlen : len < 2 ^ 32) (hspan : span < 2 ^ 64) (rest : List UInt8) :
    consumeBytes bs arena
        (UInt8.ofNat tag :: (wordBytes 4 len ++ (wordBytes 8 span ++ rest))) =
      stringConsumer bs arena key len span :: consumeBytes bs arena rest := by
  subst hkey
  have hlen12 : ¬ (wordBytes 4 len ++ (wordBytes 8 span ++ rest)).length < 12 := by
    simp only [List.length_append, wordBytes, natToBytes_length]
    omega
  have htake4 : (wordBytes 4 len ++ (wordBytes 8 span ++ rest)).take 4 =
      wordBytes 4 len := by
    rw [List.take_append_of_le_length (by simp [wordBytes, natToBytes_length])]
    exact List.take_of_length_le (by simp [wordBytes, natToBytes_length])
  have hdrop4 : (wordBytes 4 len ++ (wordBytes 8 span ++ rest)).drop 4 =
      wordBytes 8 span ++ rest := by
    rw [List.drop_append_of_le_length (by simp [wordBytes, natToBytes_length]),
      List.drop_eq_nil_of_le (by simp [wordBytes, natToBytes_length])]
    rfl
  have htake8 : ((wordBytes 4 len ++ (wordBytes 8 span ++ rest)).drop 4).take 8 =
      wordBytes 8 span := by
    rw [hdrop4]
    exact take_wordBytes span 8 rest
  have hdrop12 : (wordBytes 4 len ++ (wordBytes 8 span ++ rest)).drop 12 = rest := by
    rw [show (12 : Nat) = 4 + 8 from rfl, ← List.drop_drop (i := 8) (j := 4), hdrop4]
    exact drop_wordBytes span 8 rest
  have hlen4 : bytesToNat (wordBytes 4 len) = len :=
    bytesToNat_wordBytes (w := 4)
      (by rw [show (256 : Nat) ^ 4 = 2 ^ 32 from by decide]; exact hlen)
  have hspan8 : bytesToNat (wordBytes 8 span) = span :=
    bytesToNat_wordBytes (w := 8)
      (by rw [show (256 : Nat) ^ 8 = 2 ^ 64 from by decide]; exact hspan)
  have h5 : (UInt8.ofNat 5).toNat = 5 := by decide
  cases key with
  | true =>
      simp only [consumeBytes, ↓reduceIte, h5]
      rw [if_neg hlen12, htake4, htake8, hdrop12, hlen4, hspan8]
  | false =>
      simp only [consumeBytes]
      rw [if_neg hlen12, htake4, htake8, hdrop12, hlen4, hspan8]
      rfl

/-- **One record's emitted bytes read back as its event.**  Each class's width is
the reader's step; the payload fields are the record's own. -/
theorem consumeBytes_encoded {bs arena : List UInt8} {r : EventRecord}
    {rest : List UInt8} (hb : r.Bounded) (ht : r.Tagged) :
    consumeBytes bs arena (r.encodedBytes ++ rest) =
      EventRecord.consume bs arena r :: consumeBytes bs arena rest := by
  cases r with
  | tag t =>
      have htag : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 8 ∨ t = 9 ∨ t = 10 := ht
      simpa only [tagRecord, EventRecord.consume]
        using consumeBytes_of_tag htag rest
  | number bits =>
      have hbits : bits < 2 ^ 64 := hb
      simpa only [numberRecordBytes, EventRecord.consume]
        using consumeBytes_number bits hbits rest
  | str key len span =>
      obtain ⟨hlen, hspan⟩ := hb
      have htag : (if key then EventRecord.tagKey else EventRecord.tagStr) =
          if key then 5 else 6 := by
        cases key <;> rfl
      simp only [EventRecord.encodedBytes]
      rw [show UInt8.ofNat (if key then EventRecord.tagKey else EventRecord.tagStr) =
            UInt8.ofNat (if key then 5 else 6) from by rw [htag]]
      simp only [List.cons_append, List.nil_append, List.append_assoc]
      refine (consumeBytes_str_payload key (if key then 5 else 6) rfl
        len span hlen hspan rest).trans ?_
      simp only [EventRecord.consume]

/-- **A related trace's stream reads back as its events.**  The reader's fold on
the emitted bytes is the trace's consumer events, in order. -/
theorem consumeBytes_flatten {bs arena : List UInt8} (rs : List EventRecord)
    (hb : ∀ r ∈ rs, r.Bounded) (ht : ∀ r ∈ rs, r.Tagged) :
    consumeBytes bs arena (rs.map EventRecord.encodedBytes).flatten =
      consumeRecords bs arena rs := by
  induction rs with
  | nil => simp only [List.map_nil, List.flatten_nil, consumeBytes, consumeRecords]
  | cons r rs ih =>
      have hbr : r.Bounded := hb r (by simp)
      have htr : r.Tagged := ht r (by simp)
      have hb' : ∀ x ∈ rs, x.Bounded := fun x hx => hb x (by simp [hx])
      have ht' : ∀ x ∈ rs, x.Tagged := fun x hx => ht x (by simp [hx])
      simp only [List.map_cons, List.flatten_cons, consumeRecords, List.map_cons]
      rw [consumeBytes_encoded hbr htr, ih hb' ht']
      rfl

/-- **The byte reader's fold is the certified consumer's fold.** -/
theorem consumeBytesResult_eq_consumer {bs arenaBytes : List UInt8}
    {rs : List EventRecord} (hb : ∀ r ∈ rs, r.Bounded)
    (ht : ∀ r ∈ rs, r.Tagged) :
    consumeBytesResult bs arenaBytes (rs.map EventRecord.encodedBytes).flatten =
      consumer arenaBytes rs := by
  unfold consumeBytesResult consumer
  rw [consumeBytes_flatten rs hb ht]
  have hterms : (List.map ConsumerEvent.terms
        (List.map (EventRecord.consume bs arenaBytes) rs)) =
      List.map EventRecord.terms rs := by
    rw [List.map_map]
    exact List.map_congr_left fun r _ => EventRecord.terms_consume bs arenaBytes r
  simp only [consumeRecords, List.length_map, hterms]

/-! ### The boundary

At an accepted run's own outcome, the certified trace's consumer and the
no-event walk's fold agree on the caller's four numbers, the token list is the
parser's, and the decoded value is `decodeTape`'s. -/

/-- **The projection at the walk's trace, without the reader's width premise.**
The consumer's arithmetic and the no-event walk's events are one result at every
accepted run: no byte width, no `decodeRecords` and no event encoding enters
this statement.  The byte-level form below adds the reader's own width premise to
identify the emitted stream's fold with this one. -/
theorem stage2Boundary_noEventFold {args : List Value} {mem m : Mem}
    {next : Nat} {v : Value} {w : Stage2BoundaryWitness} {bs : List UInt8}
    {t : Tape} {rs : List EventRecord}
    (h : Stage2BoundaryFacts w args mem next m v)
    (_hacc : w.verdict = 1)
    (hparse : parseBytes Limits.default (ByteString.literal bs) = .ok t)
    (hrel : Stage2Records bs (w.arena.take w.ndstU) rs t.tokens) :
    ∃ (obs : List ConsumerEvent) (pv : LeanLLVM.JSON.Value),
      Stage2NoEvent bs (w.arena.take w.ndstU) obs t.tokens ∧
      obs = consumeRecords bs (w.arena.take w.ndstU) rs ∧
      consumer (w.arena.take w.ndstU) rs =
        noEventFold (w.arena.take w.ndstU) obs ∧
      decodeTape t = some pv ∧
      (Token.nonSeparators t.tokens).length = obs.length ∧
      readBytes m w.dst w.ndstU = some (w.arena.take w.ndstU) := by
  have hnoEvent : Stage2NoEvent bs (w.arena.take w.ndstU)
      (consumeRecords bs (w.arena.take w.ndstU) rs) t.tokens :=
    Stage2Records.toNoEvent hrel
  have hfold : consumer (w.arena.take w.ndstU) rs =
      noEventFold (w.arena.take w.ndstU)
        (consumeRecords bs (w.arena.take w.ndstU) rs) :=
    consumer_eq_noEventFold bs (w.arena.take w.ndstU) rs
  obtain ⟨pv, hdec, -, -⟩ :=
    decodeTape_correct Limits.default (ByteString.literal bs) t hparse
  have hsep : (Token.nonSeparators t.tokens).length =
      (consumeRecords bs (w.arena.take w.ndstU) rs).length := by
    rw [consumeRecords, List.length_map]
    exact (Stage2Records.length_nonSeparators hrel).symm
  exact ⟨_, pv, hnoEvent, rfl, hfold, hdec, hsep, stage2Boundary_usedArena h⟩

/-- **The consumer-boundary projection.**  `w` is the stage-2 post's named
witness at the memory the run returned; the document is the one the arguments
name; the trace is the walk's, related to the parser's tokens at the used arena
prefix.  Then:

* the no-event walk produces its events at the parser's tokens;
* the caller's reader on the emitted stream, the no-event fold, and the fold over
  the trace are one result: `tokens`, `values`, `arena` and `sum` agree;
* the emitted stream decodes to the trace (`decodeRecords`);
* the token list's record-carrying prefix has the events' length;
* the value is `decodeTape`'s, and the arena and event reads are the post's own.

This is the projection of the certified stream, not a second semantics: every
row is read from the same relation the certified boundary states. -/
theorem stage2Boundary_noEventConsumer {args : List Value} {mem m : Mem}
    {next : Nat} {v : Value} {w : Stage2BoundaryWitness} {bs : List UInt8}
    {t : Tape} {rs : List EventRecord}
    (h : Stage2BoundaryFacts w args mem next m v)
    (_hbs : readBytes mem w.b w.n = some bs)
    (_hacc : w.verdict = 1)
    (hparse : parseBytes Limits.default (ByteString.literal bs) = .ok t)
    (hrecs : w.evs = (rs.map EventRecord.encodedBytes).flatten)
    (hb : ∀ r ∈ rs, r.Bounded)
    (hrel : Stage2Records bs (w.arena.take w.ndstU) rs t.tokens) :
    ∃ (obs : List ConsumerEvent) (pv : LeanLLVM.JSON.Value),
      Stage2NoEvent bs (w.arena.take w.ndstU) obs t.tokens ∧
      obs = consumeRecords bs (w.arena.take w.ndstU) rs ∧
      consumeBytes bs (w.arena.take w.ndstU) w.evs = obs ∧
      decodeRecords w.evs = some rs ∧
      consumeBytesResult bs (w.arena.take w.ndstU) w.evs =
        consumer (w.arena.take w.ndstU) rs ∧
      consumer (w.arena.take w.ndstU) rs =
        noEventFold (w.arena.take w.ndstU) obs ∧
      decodeTape t = some pv ∧
      (Token.nonSeparators t.tokens).length = obs.length ∧
      readBytes m w.dst w.ndstU = some (w.arena.take w.ndstU) ∧
      readBytes m w.ev w.nev' = some w.evs := by
  have htagged : ∀ r ∈ rs, r.Tagged := Stage2Records.tagged hrel
  have hdecode : decodeRecords w.evs = some rs := by
    rw [hrecs]
    exact decodeRecords_flatten hb htagged
  have hconsume : consumeBytes bs (w.arena.take w.ndstU) w.evs =
      consumeRecords bs (w.arena.take w.ndstU) rs := by
    rw [hrecs]
    exact consumeBytes_flatten rs hb htagged
  have hnoEvent : Stage2NoEvent bs (w.arena.take w.ndstU)
      (consumeRecords bs (w.arena.take w.ndstU) rs) t.tokens :=
    Stage2Records.toNoEvent hrel
  have hbytes : consumeBytesResult bs (w.arena.take w.ndstU) w.evs =
      consumer (w.arena.take w.ndstU) rs := by
    rw [hrecs]
    exact consumeBytesResult_eq_consumer hb htagged
  have hfold : consumer (w.arena.take w.ndstU) rs =
      noEventFold (w.arena.take w.ndstU)
        (consumeRecords bs (w.arena.take w.ndstU) rs) :=
    consumer_eq_noEventFold bs (w.arena.take w.ndstU) rs
  obtain ⟨pv, hdec, -, -⟩ :=
    decodeTape_correct Limits.default (ByteString.literal bs) t hparse
  have hsep : (Token.nonSeparators t.tokens).length =
      (consumeRecords bs (w.arena.take w.ndstU) rs).length := by
    rw [consumeRecords, List.length_map]
    exact (Stage2Records.length_nonSeparators hrel).symm
  exact ⟨_, pv, hnoEvent, rfl, hconsume, hdecode, hbytes, hfold, hdec,
    hsep, stage2Boundary_usedArena h, h.evs_read⟩

/-- **The refusal half.**  The no-event variant shares the walk's control flow,
so on a refusal it reports the run's own `*err`; the offset is the same policy
the certified boundary states. -/
theorem stage2Boundary_noEventRefusal {args : List Value} {mem m : Mem}
    {next : Nat} {v : Value} {w : Stage2BoundaryWitness} {bs : List UInt8}
    (h : Stage2BoundaryFacts w args mem next m v)
    (hrej : w.verdict = 0)
    (hpol : ∀ e : Nat, readBytes m w.err 8 = some (wordBytes 8 e) →
      RefusalOffset bs e) :
    ∃ e : Nat, readBytes m w.err 8 = some (wordBytes 8 e) ∧
      e ≤ w.n ∧ RefusalOffset bs e :=
  stage2Boundary_refusal h hrej hpol

/-! ### The ABI obstruction

The certified ABI's stage-2 outputs are `dst`/`*ndst`, `ev`/`*nev` and `*err`
beside the return word.  Without the event stream the remaining observable — the
arena prefix, the verdict and the refusal word — is not enough to recover what
the consumer reads.  The `null` and `true` documents are the smallest witness:
each accepts with a one-event stream, writes nothing to the arena, and leaves
`*err` untouched, so the two calls agree on every non-`ev` output; their consumer
results differ (`10` against `8`).  A no-event implementation therefore cannot
deliver `tokens`/`values`/`sum` through the current ABI; the prototype adds the
three out-pointers and a scratch buffer, which is an ABI change. -/

/-- The document `true`. -/
def trueDoc : List UInt8 := [0x74, 0x72, 0x75, 0x65]

/-- What a caller observes from the stage-2 call when the event buffer is not
part of the ABI: the verdict, the arena prefix, and the refusal word (absent on
acceptance, because the walk leaves it untouched). -/
structure AbiView where
  verdict : Nat
  arena : List UInt8
  err : Option Nat
deriving DecidableEq, Repr

/-- **The same non-event outputs, different consumer results.**  Both documents
accept (`verdict = 1`), leave an empty arena and an untouched `*err`; the
consumer's results differ.  So no function of the non-`ev` ABI outputs determines
the consumer's reading: the event stream is the channel that carries it, and a
variant without that channel needs a new output, not a projection. -/
theorem noEvent_abi_obstruction :
    ∃ (bs₁ bs₂ : List UInt8) (obs₁ obs₂ : List ConsumerEvent),
      Stage2NoEvent bs₁ [] obs₁ [.null ⟨0, 4⟩] ∧
      Stage2NoEvent bs₂ [] obs₂ [.bool true ⟨0, 4⟩] ∧
      (⟨1, ([] : List UInt8), none⟩ : AbiView) =
        ⟨1, ([] : List UInt8), none⟩ ∧
      noEventFold [] obs₁ ≠ noEventFold [] obs₂ := by
  refine ⟨nullDoc, trueDoc, [ConsumerEvent.kind 10], [ConsumerEvent.kind 8],
    ?_, ?_, rfl, ?_⟩
  · exact Stage2NoEvent.nullTag (s := ⟨0, 4⟩) (by decide) (by decide)
      Stage2NoEvent.nil
  · exact Stage2NoEvent.trueTag (s := ⟨0, 4⟩) (by decide) (by decide)
      Stage2NoEvent.nil
  · intro heq
    have hsum := congrArg ConsumerResult.sum heq
    have h10 : (noEventFold ([] : List UInt8) [ConsumerEvent.kind 10]).sum = 10 := by
      simp [noEventFold, byteSum, ConsumerEvent.terms, ConsumerEvent.kind]
    have h8 : (noEventFold ([] : List UInt8) [ConsumerEvent.kind 8]).sum = 8 := by
      simp [noEventFold, byteSum, ConsumerEvent.terms, ConsumerEvent.kind]
    rw [h10, h8] at hsum
    omega

/-- **No function of the non-event outputs determines the consumer's reading.**
The exact obstruction: if a caller's result were a function of the stage-2
outputs the current ABI carries without `ev` — the verdict, the arena prefix and
the refusal word — then one function would have to give both the `null` and the
`true` document's reading, because both outputs are the same value.  The two
readings differ, so no such function exists.  Recovering them from the document
instead is a consumer of the document, not of stage two, which is the new
channel the prototype's `tokens`/`values`/`sum` out-pointers supply. -/
theorem noEvent_abi_not_determined :
    ¬ ∃ F : AbiView → ConsumerResult,
        (∀ (bs : List UInt8) (obs : List ConsumerEvent),
          Stage2NoEvent bs [] obs [.null ⟨0, 4⟩] →
            F ⟨1, ([] : List UInt8), none⟩ = noEventFold [] obs) ∧
        (∀ (bs : List UInt8) (obs : List ConsumerEvent),
          Stage2NoEvent bs [] obs [.bool true ⟨0, 4⟩] →
            F ⟨1, ([] : List UInt8), none⟩ = noEventFold [] obs) := by
  rintro ⟨F, hnull, htrue⟩
  have h10 := hnull nullDoc [ConsumerEvent.kind 10]
    (Stage2NoEvent.nullTag (s := ⟨0, 4⟩) (by decide) (by decide) Stage2NoEvent.nil)
  have h8 := htrue trueDoc [ConsumerEvent.kind 8]
    (Stage2NoEvent.trueTag (s := ⟨0, 4⟩) (by decide) (by decide) Stage2NoEvent.nil)
  have hsame : noEventFold ([] : List UInt8) [ConsumerEvent.kind 10] =
      noEventFold ([] : List UInt8) [ConsumerEvent.kind 8] := by
    rw [← h10, h8]
  have hsum := congrArg ConsumerResult.sum hsame
  have s10 : (noEventFold ([] : List UInt8) [ConsumerEvent.kind 10]).sum = 10 := by
    simp [noEventFold, byteSum, ConsumerEvent.terms, ConsumerEvent.kind]
  have s8 : (noEventFold ([] : List UInt8) [ConsumerEvent.kind 8]).sum = 8 := by
    simp [noEventFold, byteSum, ConsumerEvent.terms, ConsumerEvent.kind]
  rw [s10, s8] at hsum
  omega

/-! ### Controls

Executable checks of the fold and the reader: the two numbers a consumer reads
from a `null` and a `true` stream, a number's payload, and the plain/escaped
string fields. -/

#guard (noEventFold [] [ConsumerEvent.kind 10]).sum = 10
#guard (noEventFold [] [ConsumerEvent.kind 8]).sum = 8
#guard (noEventFold [] [ConsumerEvent.number 3]).sum = stage2TagNum + 3
#guard (consumeBytes [] [] [0x0A]) = [ConsumerEvent.kind 10]
#guard (consumeBytes [] [] [0x08]) = [ConsumerEvent.kind 8]
#guard (consumeBytes [] [] [0x07, 3, 0, 0, 0, 0, 0, 0, 0]) =
  [ConsumerEvent.number 3]
#guard (noEventFold [1, 2] [ConsumerEvent.str true 3 5 [9]]).arena = 3
#guard (noEventFold [1, 2] [ConsumerEvent.str true 3 5 [9]]).sum = 16

/-! ### Axiom footprints -/

#print axioms ConsumerEvent
#print axioms ConsumerEvent.terms
#print axioms byteSum
#print axioms byteSum_append
#print axioms EventRecord.terms
#print axioms consumer
#print axioms noEventFold
#print axioms stringConsumer
#print axioms EventRecord.consume
#print axioms consumeRecords
#print axioms consumeBytes
#print axioms consumeBytesResult
#print axioms Stage2NoEvent
#print axioms plainSpan_not_lt
#print axioms plainSpan_sub
#print axioms Stage2Records.length_nonSeparators
#print axioms Stage2Records.toNoEvent
#print axioms EventRecord.terms_consume
#print axioms consumer_eq_noEventFold
#print axioms stringConsumer_plain
#print axioms stringConsumer_arena
#print axioms consumeBytes_of_tag
#print axioms consumeBytes_number
#print axioms consumeBytes_str_payload
#print axioms consumeBytes_encoded
#print axioms consumeBytes_flatten
#print axioms consumeBytesResult_eq_consumer
#print axioms stage2Boundary_noEventFold
#print axioms stage2Boundary_noEventConsumer
#print axioms stage2Boundary_noEventRefusal
#print axioms noEvent_abi_obstruction
#print axioms noEvent_abi_not_determined

end LeanLLVM.Refinement
