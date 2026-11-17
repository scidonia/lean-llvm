/-
The stage-2 event stream's meaning: `EventStreamRel` instantiated.

`JsonPipelineSpec` states the pipeline's specification at a parameter
`eventRel : EventStreamRel` and names the instantiation as C95's
`JsonStage2Spec`.  This module is that instantiation.  It defines the relation
between the document, the arena the decoder filled, the event bytes the walk
wrote and the reference parser's tokens, and proves what the relation says at
the three places a consumer reads it:

* **the record encoding is the emitted one.**  `tagRecord`, `numberRecordBytes`
  and `strRecordBytes` are `stage2.h:68-75`'s bytes — the `EventRecord` shape
  `JsonStage2Body` already carries — and `Stage2EventRel`'s constructors consume
  exactly those bytes.  A consumer therefore reads the same encoding the
  emitted body writes, not a second description of it;
* **the payloads are tied to the parser's own tokens.**  A number record's
  eight payload bytes are `bitsBytes (strtodSpec d).toBits` for a well-formed
  `Decimal d` whose lexeme is the token's span (`Strtod`'s number arm); a plain
  string or key record is span-addressed and its body's code points are the
  token's; an escaped string or key record's arena slice reads back as those
  code points (`escapeCodePoints`, `JsonEscapeSpec`); the scalar and container
  records are the ABI's tag bytes;
* **the relation is at an actual outcome.**  `stage2Boundary_eventRel` is stated
  at `Stage2BoundaryFacts` — the named witnesses of the stage-2 post at a
  returned memory — and reads the arena at the **used** extent `ndstU`, deriving
  that read from the post's reserved read `ndst'` and `ndstU ≤ ndst'`
  (`usedPrefix_of_reserved`).  The larger extent stays where it belongs: presence,
  capacity and the frame are the post's `ndst'`, and nothing here narrows them.

The accepted value is the parser's own: `decodeTape` of the token stream the
events name, with `strtodSpec` as the binary64 observation of a number record.
Strings and containers need no second decoder because `Tape`'s spans already
carry their meaning; the relation binds the records to those spans.

The refusal policy is `JsonPipelineSpec.RefusalOffset` read on both sides: the
parser's first error offset for a walk-owned refusal, and the document's end for
a UTF-8-owned refusal.  `refusalOffset_walk` and `refusalOffset_utf8` are the two
clauses.  The resource policy is `Stage2ResourcePolicy`: the input bound and the
two parser limits the pipeline's ABI does not carry, and
`pipelineSpecPre_resourcePolicy` derives it from the specification's
precondition so both sides state one policy.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonPipelineSpec
import LeanLLVM.Refinement.JsonStage2Body
import LeanLLVM.Refinement.JsonUtf8IR
import LeanLLVM.JSON.Strtod
import LeanLLVM.JSON.TapeCorrect
import LeanLLVM.JSON.Correct

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonUtf8IR

/-! ### The emitted record encoding -/

/-- A one-byte tag record (`out_tag`). -/
def tagRecord (t : Nat) : List UInt8 :=
  (EventRecord.tag t).encodedBytes

/-- The number record: `T_NUM` (`7`) and the eight payload bytes. -/
def numberRecordBytes (bits : Nat) : List UInt8 :=
  (EventRecord.number bits).encodedBytes

/-- A key or string record: the tag (`T_KEY = 5`, `T_STR = 6`), the four-byte
little-endian length and the eight-byte span-or-arena field. -/
def strRecordBytes (key : Bool) (len span : Nat) : List UInt8 :=
  (EventRecord.str key len span).encodedBytes

-- The record bytes are the emitted body's own trace entries.
#guard tagRecord 1 = [1]
#guard numberRecordBytes 0 = [7, 0, 0, 0, 0, 0, 0, 0, 0]
#guard strRecordBytes false 3 5 =
  [6, 3, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0]

/-- The plain form's span field: the opening quote's successor in the top bit's
set form (`stage2.c`'s `rec = (uint64_t)(p + 1) | (1ULL << 63)`). -/
def plainSpan (bodyStart : Nat) : Nat := bodyStart + 2 ^ 63

/-- The body's code points as the reference tape's own decoder reads them from
the token's span.  This is the string side of the relation's bridge: a record's
arena slice must decode to the same code points the tape's span does. -/
def bodyCodePoints (bs : List UInt8) (s : Span) : Option (List Nat) :=
  match scanCharsEnd (ByteString.literal bs) (s.start + 1) 0 with
  | .ok (cs, _) => some cs
  | .error _ => none

/-! ### The relation

An inductive relation, so every constructor is a producer and an inversion is a
`cases`: the event bytes are consumed in the emitted encoding's own records, and
the token list the records name is the parser's, separators included.  The
comma and colon tokens have no record (`stage2.h:68-75` emits tags only for the
four container bytes, the three literals, numbers and strings), so their
constructors consume no event bytes.

The relation is stated over the **document's bytes** (spans index it), the
**arena prefix** (the escaped bodies' decoded bytes), the **event bytes** and the
**parser's tokens**.  The escape form's offset is below `2 ^ 63`, which is what
distinguishes it from the plain form's top-bit-set span at the record; the
emitted walk's arena cursor is a document-sized number and satisfies it.

The key/string tag is a parameter of the string constructor: the same token is a
member name in one grammar position and a value in another, the tape's own
grammar decides which, and the value correspondence is the token's span either
way.  The emitted walk picks the tag from its container state, so both
constructors are encodings of the same token rather than two meanings of it.

The numeric clause binds the record to `strtodSpec`; that the emitted
`num_fast`/`strtod` path computes that function is `NumberArmOwed` in
`LeanLLVM/JSON/Strtod.lean`, not proved here or by this relation.  What is
proved is the semantic side: a number record satisfying the relation carries
the binary64 encoding of the token's lexeme under the stated rounding. -/

/-- The stage-2 event stream's relation: the document `bs`, the arena prefix the
decoder wrote, the event bytes and the reference parser's tokens.  A number
record's payload is the binary64 encoding `strtodSpec` assigns to the token's
lexeme; a plain string/key record addresses its body in the document and an
escaped one addresses the well-formed UTF-8 in the arena; the scalar and
container records are the ABI's tags at the token's span. -/
inductive Stage2EventRel (bs arena : List UInt8) : List UInt8 → List Token → Prop where
  /-- No events, no tokens. -/
  | nil : Stage2EventRel bs arena [] []
  /-- A comma separator has no record. -/
  | comma {s : Span} {evs : List UInt8} {toks : List Token}
      (h : Stage2EventRel bs arena evs toks) :
      Stage2EventRel bs arena evs (.punct .comma s :: toks)
  /-- A colon separator has no record. -/
  | colon {s : Span} {evs : List UInt8} {toks : List Token}
      (h : Stage2EventRel bs arena evs toks) :
      Stage2EventRel bs arena evs (.punct .colon s :: toks)
  /-- `{` (`T_OBJ = 1`) at a one-byte span. -/
  | openBrace {s : Span} {evs : List UInt8} {toks : List Token}
      (hbyte : bs[s.start]? = some 0x7B) (hspan : s.stop = s.start + 1)
      (h : Stage2EventRel bs arena evs toks) :
      Stage2EventRel bs arena (tagRecord 1 ++ evs) (.punct .openBrace s :: toks)
  /-- `}` (`T_OBJ_END = 2`). -/
  | closeBrace {s : Span} {evs : List UInt8} {toks : List Token}
      (hbyte : bs[s.start]? = some 0x7D) (hspan : s.stop = s.start + 1)
      (h : Stage2EventRel bs arena evs toks) :
      Stage2EventRel bs arena (tagRecord 2 ++ evs) (.punct .closeBrace s :: toks)
  /-- `[` (`T_ARR = 3`). -/
  | openBracket {s : Span} {evs : List UInt8} {toks : List Token}
      (hbyte : bs[s.start]? = some 0x5B) (hspan : s.stop = s.start + 1)
      (h : Stage2EventRel bs arena evs toks) :
      Stage2EventRel bs arena (tagRecord 3 ++ evs) (.punct .openBracket s :: toks)
  /-- `]` (`T_ARR_END = 4`). -/
  | closeBracket {s : Span} {evs : List UInt8} {toks : List Token}
      (hbyte : bs[s.start]? = some 0x5D) (hspan : s.stop = s.start + 1)
      (h : Stage2EventRel bs arena evs toks) :
      Stage2EventRel bs arena (tagRecord 4 ++ evs) (.punct .closeBracket s :: toks)
  /-- `true` (`T_TRUE = 8`) at the four-byte literal span. -/
  | trueTag {s : Span} {evs : List UInt8} {toks : List Token}
      (hbytes : (bs.drop s.start).take 4 = [0x74, 0x72, 0x75, 0x65])
      (hspan : s.stop = s.start + 4)
      (h : Stage2EventRel bs arena evs toks) :
      Stage2EventRel bs arena (tagRecord 8 ++ evs) (.bool true s :: toks)
  /-- `false` (`T_FALSE = 9`) at the five-byte literal span. -/
  | falseTag {s : Span} {evs : List UInt8} {toks : List Token}
      (hbytes : (bs.drop s.start).take 5 = [0x66, 0x61, 0x6C, 0x73, 0x65])
      (hspan : s.stop = s.start + 5)
      (h : Stage2EventRel bs arena evs toks) :
      Stage2EventRel bs arena (tagRecord 9 ++ evs) (.bool false s :: toks)
  /-- `null` (`T_NULL = 10`) at the four-byte literal span. -/
  | nullTag {s : Span} {evs : List UInt8} {toks : List Token}
      (hbytes : (bs.drop s.start).take 4 = [0x6E, 0x75, 0x6C, 0x6C])
      (hspan : s.stop = s.start + 4)
      (h : Stage2EventRel bs arena evs toks) :
      Stage2EventRel bs arena (tagRecord 10 ++ evs) (.null s :: toks)
  /-- A number (`T_NUM = 7`): the eight payload bytes are `strtodSpec`'s encoding
  of the token's lexeme, and the lexeme is the token's own span. -/
  | number {s : Span} {evs : List UInt8} {toks : List Token} {d : Decimal}
      (hwf : d.wellFormed)
      (hspan : s.stop = s.start + d.lexeme.length)
      (hlexeme : (bs.drop s.start).take (s.stop - s.start) = d.lexeme.data.toList)
      (h : Stage2EventRel bs arena evs toks) :
      Stage2EventRel bs arena
        (numberRecordBytes (strtodSpec d).toBits ++ evs) (.number s :: toks)
  /-- A key or string written in the plain form: the span field is the body's
  first document byte with the top bit set, the length is the body's length, and
  the body reads as the token's code points. -/
  | strPlain {key : Bool} {s : Span} {evs : List UInt8} {toks : List Token}
      {len : Nat} {cs : List Nat}
      (hquote : bs[s.start]? = some 0x22)
      (hspan : s.stop = s.start + 2 + len)
      (hbody : escapeCodePoints ((bs.drop (s.start + 1)).take len) = some cs)
      (hcode : bodyCodePoints bs s = some cs)
      (h : Stage2EventRel bs arena evs toks) :
      Stage2EventRel bs arena
        (strRecordBytes key len (plainSpan (s.start + 1)) ++ evs)
        (.string s :: toks)
  /-- A key or string written in the arena form: the length is the decoded byte
  count, the span field is the arena offset (below `2 ^ 63`), and the slice
  reads back as the token's code points. -/
  | strArena {key : Bool} {s : Span} {evs : List UInt8} {toks : List Token}
      {len off : Nat} {cs : List Nat}
      (hquote : bs[s.start]? = some 0x22)
      (hspan : s.start + 2 ≤ s.stop)
      (hcode : bodyCodePoints bs s = some cs)
      (hbelow : off < 2 ^ 63)
      (harena : escapeCodePoints ((arena.drop off).take len) = some cs)
      (h : Stage2EventRel bs arena evs toks) :
      Stage2EventRel bs arena
        (strRecordBytes key len off ++ evs) (.string s :: toks)

/-- **The instantiated `EventStreamRel`.**  This is C95's relation, not a
parameter: the specification record below is stated at it. -/
def stage2EventRel : EventStreamRel :=
  fun bs arena evs toks => Stage2EventRel bs arena evs toks

/-- The specification record at the instantiated relation. -/
def Γ_pipeline_stage2 (tab base : Nat) : MemContract :=
  Γ_pipeline stage2EventRel tab base

/-! ### The relation composes over token lists

The array and object constructors would otherwise repeat the induction over the
inner token list.  `Stage2EventRel.append` is that induction once. -/

/-- Concatenating two related event/token pairs concatenates both sides. -/
theorem Stage2EventRel.append {bs arena : List UInt8} {evs₁ : List UInt8}
    {toks₁ : List Token} (h₁ : Stage2EventRel bs arena evs₁ toks₁)
    {evs₂ : List UInt8} {toks₂ : List Token}
    (h₂ : Stage2EventRel bs arena evs₂ toks₂) :
    Stage2EventRel bs arena (evs₁ ++ evs₂) (toks₁ ++ toks₂) :=
  Stage2EventRel.rec
    (motive := fun evs toks _ =>
      Stage2EventRel bs arena (evs ++ evs₂) (toks ++ toks₂))
    h₂
    (fun _ ih => Stage2EventRel.comma ih)
    (fun _ ih => Stage2EventRel.colon ih)
    (fun hb hs _ ih => Stage2EventRel.openBrace hb hs ih)
    (fun hb hs _ ih => Stage2EventRel.closeBrace hb hs ih)
    (fun hb hs _ ih => Stage2EventRel.openBracket hb hs ih)
    (fun hb hs _ ih => Stage2EventRel.closeBracket hb hs ih)
    (fun hb hs _ ih => Stage2EventRel.trueTag hb hs ih)
    (fun hb hs _ ih => Stage2EventRel.falseTag hb hs ih)
    (fun hb hs _ ih => Stage2EventRel.nullTag hb hs ih)
    (fun hwf hs hlex _ ih => Stage2EventRel.number hwf hs hlex ih)
    (fun hq hs hbody hcode _ ih => Stage2EventRel.strPlain hq hs hbody hcode ih)
    (fun hq hs hcode hbelow harena _ ih =>
      Stage2EventRel.strArena hq hs hcode hbelow harena ih)
    h₁

/-! ### Coverage of the value classes -/

/-- Scalars: `null`, `true` and `false` are the ABI's tags at their literal
spans. -/
theorem stage2EventRel_scalars {bs arena : List UInt8} {snull strue sfalse : Span}
    {evs : List UInt8} {toks : List Token}
    (hnull : (bs.drop snull.start).take 4 = [0x6E, 0x75, 0x6C, 0x6C])
    (hnullspan : snull.stop = snull.start + 4)
    (htrue : (bs.drop strue.start).take 4 = [0x74, 0x72, 0x75, 0x65])
    (htruespan : strue.stop = strue.start + 4)
    (hfalse : (bs.drop sfalse.start).take 5 = [0x66, 0x61, 0x6C, 0x73, 0x65])
    (hfalsespan : sfalse.stop = sfalse.start + 5)
    (h : Stage2EventRel bs arena evs toks) :
    Stage2EventRel bs arena
      (tagRecord 8 ++ tagRecord 9 ++ tagRecord 10 ++ evs)
      (.bool true strue :: .bool false sfalse :: .null snull :: toks) :=
  Stage2EventRel.trueTag htrue htruespan
    (Stage2EventRel.falseTag hfalse hfalsespan
      (Stage2EventRel.nullTag hnull hnullspan h))

/-- Containers: an array's open and close tags bracket the element records, and
the token stream is the open token, the elements and the close token. -/
theorem stage2EventRel_array {bs arena : List UInt8} {sopen sclose : Span}
    {evs : List UInt8} {toks : List Token}
    (hopen : bs[sopen.start]? = some 0x5B) (hopenspan : sopen.stop = sopen.start + 1)
    (hclose : bs[sclose.start]? = some 0x5D) (hclosespan : sclose.stop = sclose.start + 1)
    (h : Stage2EventRel bs arena evs toks) :
    Stage2EventRel bs arena
      (tagRecord 3 ++ evs ++ tagRecord 4)
      (.punct .openBracket sopen :: toks ++ [.punct .closeBracket sclose]) := by
  have hcloseRel : Stage2EventRel bs arena (tagRecord 4)
      [.punct .closeBracket sclose] :=
    Stage2EventRel.closeBracket hclose hclosespan Stage2EventRel.nil
  have hinner : Stage2EventRel bs arena (evs ++ tagRecord 4)
      (toks ++ [.punct .closeBracket sclose]) :=
    Stage2EventRel.append h hcloseRel
  simpa only [List.cons_append, List.append_assoc] using
    Stage2EventRel.openBracket hopen hopenspan hinner

/-- Containers: an object's open and close tags bracket its member records. -/
theorem stage2EventRel_object {bs arena : List UInt8} {sopen sclose : Span}
    {evs : List UInt8} {toks : List Token}
    (hopen : bs[sopen.start]? = some 0x7B) (hopenspan : sopen.stop = sopen.start + 1)
    (hclose : bs[sclose.start]? = some 0x7D) (hclosespan : sclose.stop = sclose.start + 1)
    (h : Stage2EventRel bs arena evs toks) :
    Stage2EventRel bs arena
      (tagRecord 1 ++ evs ++ tagRecord 2)
      (.punct .openBrace sopen :: toks ++ [.punct .closeBrace sclose]) := by
  have hcloseRel : Stage2EventRel bs arena (tagRecord 2)
      [.punct .closeBrace sclose] :=
    Stage2EventRel.closeBrace hclose hclosespan Stage2EventRel.nil
  have hinner : Stage2EventRel bs arena (evs ++ tagRecord 2)
      (toks ++ [.punct .closeBrace sclose]) :=
    Stage2EventRel.append h hcloseRel
  simpa only [List.cons_append, List.append_assoc] using
    Stage2EventRel.openBrace hopen hopenspan hinner

/-- Strings in the arena form: the constructor is the producer, so a code-point
list read off the token's span and its encoded arena slice relate the record to
the token.  `escapeCodePoints_encode` supplies the arena side for
`(cs.map utf8Encode).flatten`. -/
theorem stage2EventRel_string_arena {bs arena : List UInt8} {key : Bool}
    {s : Span} {len off : Nat} {cs : List Nat}
    {evs : List UInt8} {toks : List Token}
    (hquote : bs[s.start]? = some 0x22)
    (hspan : s.start + 2 ≤ s.stop)
    (hcode : bodyCodePoints bs s = some cs)
    (hbelow : off < 2 ^ 63)
    (harena : escapeCodePoints ((arena.drop off).take len) = some cs)
    (h : Stage2EventRel bs arena evs toks) :
    Stage2EventRel bs arena
      (strRecordBytes key len off ++ evs) (.string s :: toks) :=
  Stage2EventRel.strArena hquote hspan hcode hbelow harena h

/-- Strings in the plain form: the record's span field is the body's first
document byte with the top bit set, and the body reads as the token's code
points. -/
theorem stage2EventRel_string_plain {bs arena : List UInt8} {key : Bool}
    {s : Span} {len : Nat} {cs : List Nat}
    {evs : List UInt8} {toks : List Token}
    (hquote : bs[s.start]? = some 0x22)
    (hspan : s.stop = s.start + 2 + len)
    (hbody : escapeCodePoints ((bs.drop (s.start + 1)).take len) = some cs)
    (hcode : bodyCodePoints bs s = some cs)
    (h : Stage2EventRel bs arena evs toks) :
    Stage2EventRel bs arena
      (strRecordBytes key len (plainSpan (s.start + 1)) ++ evs)
      (.string s :: toks) :=
  Stage2EventRel.strPlain hquote hspan hbody hcode h

/-- The arena side of the string class is inhabited: the UTF-8 encoding of a
code-point list reads back as that list (`escapeCodePoints_encode`), so a
record's escaped form has an arena witness for every code-point payload. -/
theorem stage2EventRel_string_arena_inhabited (cs : List Nat)
    (h : ∀ c ∈ cs, c ≤ 0x10FFFF) :
    ∃ arena : List UInt8,
      escapeCodePoints ((arena.drop 0).take ((cs.map utf8Encode).flatten).length) =
        some cs := by
  refine ⟨(cs.map utf8Encode).flatten, ?_⟩
  rw [List.drop_zero, List.take_of_length_le (Nat.le_refl _)]
  exact escapeCodePoints_encode cs h

/-- Numbers: `bitsBytes (strtodSpec d).toBits` is the record payload for a
well-formed lexeme, and the token's span is that lexeme. -/
theorem stage2EventRel_number {bs arena : List UInt8} {s : Span} {d : Decimal}
    {evs : List UInt8} {toks : List Token}
    (hwf : d.wellFormed)
    (hspan : s.stop = s.start + d.lexeme.length)
    (hlexeme : (bs.drop s.start).take (s.stop - s.start) = d.lexeme.data.toList)
    (h : Stage2EventRel bs arena evs toks) :
    Stage2EventRel bs arena
      (numberRecordBytes (strtodSpec d).toBits ++ evs) (.number s :: toks) :=
  Stage2EventRel.number hwf hspan hlexeme h

/-! ### The used-prefix read

The post supplies the arena at the **reserved** extent `ndst'`; the caller's
cursor holds the **used** extent `ndstU`, and a consumer interprets only that
prefix.  The derivation is `readBytes_split` at the two extents. -/

/-- A read at a shorter extent is the longer read's prefix. -/
theorem usedPrefix_of_reserved {m : Mem} {addr n n' : Nat} {bs : List UInt8}
    (h : readBytes m addr n' = some bs) (hn : n ≤ n') :
    readBytes m addr n = some (bs.take n) := by
  obtain ⟨h1, -⟩ := readBytes_split m addr n (n' - n) (by
    rwa [Nat.add_sub_of_le hn])
  exact h1

/-- **The arena at the used extent, from the boundary's reserved read.**  The
reserved read is the memory the run may have written (the frame and capacity are
stated there); the used prefix is the decoded output the caller interprets. -/
theorem stage2Boundary_usedArena {args : List Value} {mem m : Mem} {next : Nat}
    {v : Value} {w : Stage2BoundaryWitness}
    (h : Stage2BoundaryFacts w args mem next m v) :
    readBytes m w.dst w.ndstU = some (w.arena.take w.ndstU) :=
  usedPrefix_of_reserved h.arena_read h.U_le_ndst

/-- **Semantic output correspondence at an actual outcome.**  `w` is the
stage-2 post's named witness at the memory the run returned; the arena is read
at the used prefix, the event stream at the reported cursor, and the event
relation names the parser's own tokens.  The value is `decodeTape`'s, and a
number record's payload is `strtodSpec`'s encoding by the relation's number
constructor; strings and containers are the tape's spans and the event
relation's constructors. -/
theorem stage2Boundary_eventRel {args : List Value} {mem m : Mem} {next : Nat}
    {v : Value} {w : Stage2BoundaryWitness} {bs : List UInt8} {t : Tape}
    {pv : LeanLLVM.JSON.Value}
    (h : Stage2BoundaryFacts w args mem next m v)
    (_hbs : readBytes mem w.b w.n = some bs)
    (_hacc : w.verdict = 1)
    (hrel : Stage2EventRel bs (w.arena.take w.ndstU) w.evs t.tokens)
    (hdec : decodeTape t = some pv) :
    readBytes m w.dst w.ndstU = some (w.arena.take w.ndstU) ∧
      readBytes m w.ev w.nev' = some w.evs ∧
      Stage2EventRel bs (w.arena.take w.ndstU) w.evs t.tokens ∧
      decodeTape t = some pv :=
  ⟨stage2Boundary_usedArena h, h.evs_read, hrel, hdec⟩

/-- **The accepted value at an actual outcome.**  The parser's own correctness
theorem supplies the decoded value, its input and the accepted language; the
stage-2 post supplies the used-prefix arena read and the event cursor; and the
relation names the tokens.  This is the accepted-value half of the semantic
replacement at the run's own outcome, with the number record's payload being
`strtodSpec`'s encoding (the relation's number constructor). -/
theorem stage2Boundary_acceptedValue {args : List Value} {mem m : Mem} {next : Nat}
    {v : Value} {w : Stage2BoundaryWitness} {bs : List UInt8} {t : Tape}
    (h : Stage2BoundaryFacts w args mem next m v)
    (_hbs : readBytes mem w.b w.n = some bs)
    (_hacc : w.verdict = 1)
    (hrel : Stage2EventRel bs (w.arena.take w.ndstU) w.evs t.tokens)
    (ht : parseBytes Limits.default (ByteString.literal bs) = .ok t) :
    ∃ pv : LeanLLVM.JSON.Value,
      decodeTape t = some pv ∧
      t.input = ByteString.literal bs ∧
      ValidDocument (ByteString.literal bs) pv ∧
      readBytes m w.dst w.ndstU = some (w.arena.take w.ndstU) ∧
      readBytes m w.ev w.nev' = some w.evs ∧
      Stage2EventRel bs (w.arena.take w.ndstU) w.evs t.tokens := by
  obtain ⟨pv, hdec, hin, hvalid⟩ :=
    decodeTape_correct Limits.default (ByteString.literal bs) t ht
  exact ⟨pv, hdec, hin, hvalid, stage2Boundary_usedArena h, h.evs_read, hrel⟩

/-- **Refusal correspondence at an actual outcome.**  The post supplies the
refusal word's presence and bound at the returned memory; the policy relation
`RefusalOffset` is its semantic half, read at that word and the document's
bytes.  The two sides are the same predicate `refusalOffset_walk` and
`refusalOffset_utf8` read. -/
theorem stage2Boundary_refusal {args : List Value} {mem m : Mem} {next : Nat}
    {v : Value} {w : Stage2BoundaryWitness} {bs : List UInt8}
    (h : Stage2BoundaryFacts w args mem next m v)
    (hrej : w.verdict = 0)
    (hpol : ∀ e : Nat, readBytes m w.err 8 = some (wordBytes 8 e) →
      RefusalOffset bs e) :
    ∃ e : Nat, readBytes m w.err 8 = some (wordBytes 8 e) ∧
      e ≤ w.n ∧ RefusalOffset bs e := by
  obtain ⟨e, he, hread⟩ := h.refuse_word hrej
  exact ⟨e, hread, he, hpol e hread⟩

/-- **The execution-indexed parser bridge at the instantiated relation.**  This
is `pipeline_satisfies_of_parser` at `stage2EventRel`: the premise `hsem` is
indexed by the actual outcome, returned memory and extent pair, and its parser
half now carries the concrete arena/event relation rather than a parameter. -/
theorem pipeline_satisfies_stage2 {calls : Calls} {f : Function}
    {tab base : Nat}
    (hunits : Satisfies calls f (Γ_pipeline_units tab base))
    (hsem : ∀ (args : List Value) (mem : Mem) (next : Nat) (o : Outcome)
      (ndst' nev' : Nat),
      pipelineStaging tab base args mem →
      BehFromState calls f (EntryState f args mem next) o →
      pipelineOutputExtents args o ndst' nev' →
      ParserHalfForOutcome stage2EventRel base args mem ndst' nev' o) :
    Satisfies calls f (Γ_pipeline_stage2 tab base) :=
  pipeline_satisfies_of_parser (eventRel := stage2EventRel) hunits hsem

/-! ### Refusal and resource policy, on both sides -/

/-- **The walk-owned refusal offset is the parser's.**  For a UTF-8-valid
document whose parser refusal is an `.invalid r`, the reported offset is the
constructor's position (`byteOrderMark` alone has none). -/
theorem refusalOffset_walk {bs : List UInt8} {e : Nat}
    (h : RefusalOffset bs e)
    (hutf8 : utf8WinPrefix (utf8Window bs bs.length (pipelineBlocks bs.length)))
    {r : Reject}
    (hparse : parseBytes Limits.default (ByteString.literal bs) = .error (.invalid r)) :
    match rejectPos r with
    | some p => e = p
    | none => True :=
  h.1 hutf8 r hparse

/-- **The UTF-8-owned refusal offset is the document's end.**  When the staged
window is not a valid UTF-8 prefix the caller reports `n`, because the stage's
word says only that the document is invalid. -/
theorem refusalOffset_utf8 {bs : List UInt8} {e : Nat}
    (h : RefusalOffset bs e)
    (hbad : ¬ utf8WinPrefix (utf8Window bs bs.length (pipelineBlocks bs.length))) :
    e = bs.length :=
  h.2 hbad

/-- **The resource policy, stated at the parser's own limits.**  The input bound
is `Limits.default.maxInput`; the depth and token limits are the parser's and the
pipeline's ABI does not carry them, so the specification excludes their
outcomes rather than promising a pipeline answer at them. -/
def Stage2ResourcePolicy (bs : List UInt8) : Prop :=
  bs.length ≤ (Limits.default).maxInput ∧
    ∀ err : ParseError,
      parseBytes Limits.default (ByteString.literal bs) = .error err →
        err ≠ .depthExceeded ∧ err ≠ .outOfCapacity

/-- **The specification's precondition carries the resource policy.**  The
staging carries the input bound and `pipelineSpecPre`'s own clause carries the
two excluded outcomes, so a consumer reads one policy on both sides. -/
theorem pipelineSpecPre_resourcePolicy {tab base : Nat} {args : List Value}
    {mem : Mem} {next : Nat} (h : pipelineSpecPre tab base args mem next) :
    ∃ bs : List UInt8, pipelineDocLength args = some bs.length ∧
      Stage2ResourcePolicy bs := by
  obtain ⟨hstaging, -, -, hspec⟩ := h
  obtain ⟨bs, _nev0, _evcap, _nev, hdocLen, _hevCap, _hnevSlot, _hread,
    _hnevRead, hexcl⟩ := hspec
  refine ⟨bs, hdocLen, ?_⟩
  -- The staging's own document has the same length, so its bound transfers.
  obtain ⟨sc, mk, entw, ep, nk, xp, nxp, xcarry, dst, ndst, ev, nev, err,
    nxp0, ndst0, nev0, n, epcap, xpcap, dstcap, evcap, arm, bs', hargs, hlen,
    hbound, rest⟩ := hstaging
  refine ⟨?_, hexcl⟩
  unfold pipelineDocLength at hdocLen
  rw [hargs] at hdocLen
  simp only [Option.some.injEq] at hdocLen
  have : bs'.length = bs.length := by omega
  rwa [this] at hbound

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.tagRecord' does not depend on any axioms -/
#guard_msgs in
#print axioms tagRecord

/-- info: 'LeanLLVM.Refinement.numberRecordBytes' does not depend on any axioms -/
#guard_msgs in
#print axioms numberRecordBytes

/-- info: 'LeanLLVM.Refinement.strRecordBytes' does not depend on any axioms -/
#guard_msgs in
#print axioms strRecordBytes

/-- info: 'LeanLLVM.Refinement.Stage2EventRel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Stage2EventRel

/-- info: 'LeanLLVM.Refinement.stage2EventRel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2EventRel

/-- info: 'LeanLLVM.Refinement.Stage2EventRel.append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Stage2EventRel.append

/-- info: 'LeanLLVM.Refinement.stage2EventRel_scalars' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2EventRel_scalars

/-- info: 'LeanLLVM.Refinement.stage2EventRel_array' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2EventRel_array

/-- info: 'LeanLLVM.Refinement.stage2EventRel_object' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2EventRel_object

/-- info: 'LeanLLVM.Refinement.stage2EventRel_string_arena' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2EventRel_string_arena

/-- info: 'LeanLLVM.Refinement.stage2EventRel_string_plain' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2EventRel_string_plain

/-- info: 'LeanLLVM.Refinement.stage2EventRel_string_arena_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2EventRel_string_arena_inhabited

/-- info: 'LeanLLVM.Refinement.stage2EventRel_number' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2EventRel_number

/-- info: 'LeanLLVM.Refinement.usedPrefix_of_reserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms usedPrefix_of_reserved

/-- info: 'LeanLLVM.Refinement.stage2Boundary_usedArena' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Boundary_usedArena

/-- info: 'LeanLLVM.Refinement.stage2Boundary_eventRel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Boundary_eventRel

/-- info: 'LeanLLVM.Refinement.stage2Boundary_acceptedValue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Boundary_acceptedValue

/-- info: 'LeanLLVM.Refinement.stage2Boundary_refusal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Boundary_refusal

/-- info: 'LeanLLVM.Refinement.pipeline_satisfies_stage2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_satisfies_stage2

/-- info: 'LeanLLVM.Refinement.refusalOffset_walk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalOffset_walk

/-- info: 'LeanLLVM.Refinement.refusalOffset_utf8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refusalOffset_utf8

/-- info: 'LeanLLVM.Refinement.pipelineSpecPre_resourcePolicy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipelineSpecPre_resourcePolicy

end LeanLLVM.Refinement
