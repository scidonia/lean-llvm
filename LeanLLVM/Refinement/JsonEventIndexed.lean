/-
The indexed event reader's specification, and its equivalence with the list walk.

`eventsOfBytes` (`JsonEventBytes`) reads the emitted stream as a list of
suffixes: each record's payload is the next bytes of the remaining list, and a
string body is a slice of the document or of the arena.  An indexed reader holds
the same three buffers and a cursor into the stream instead.  It reads the tag at
the cursor, the payload fields at fixed offsets, and advances by the record's
width.

This module fixes that reader's contract and proves the two parts `JsonEventBytes`
leaves to this side:

* **the record step.**  `cursorStep` is the record a cursor position reads, in
  the encoding `walkRecords` reads: the same eleven tags, the same widths, the
  same truncation checks, and the same two string-body sources.
  `walkRecords_drop_cursor` proves that reading the suffix at a cursor is that
  record followed by the walk of the remaining stream — one theorem covers every
  tag and every failure case.
* **the induction.**  `walkFrom` is the cursor loop at a step function.
  `walkFrom_cursor_eq` proves it computes `walkRecords` at any cursor, and
  `indexedReader_eq_eventsOfBytes` states the reader's contract
  (`IndexedStepAgrees`) and derives the equivalence with `eventsOfBytes`.

The index arithmetic is separate from the step's meaning.  `bytesToNatAt` reads a
little-endian field at an offset without rebuilding a suffix, and
`cursorStepIndexed` is the same step written with offsets, offsets' truncation
checks and `bytesToNatAt`; `cursorStepIndexed_eq_cursorStep` proves the two
agree, so an implementation that holds a `ByteArray` and a cursor only has to
match `cursorStepIndexed`.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonEventBytes
import LeanLLVM.JSON.ByteString

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### Indexed little-endian fields

A record's payload is a little-endian word at a fixed offset from the tag.  The
list walk spells that as `bytesToNat ((rest.drop k).take n)`; an indexed reader
spells it as `bytesToNatAt evs (i + k) n`, with no suffix in sight.  `drop` and
`take` are the carrier's list-shaped interface (`ByteString`), not a fast path,
so both spellings are the same bytes by construction. -/

/-- The little-endian `n`-byte word at offset `i`. -/
def bytesToNatAt (bs : List UInt8) (i n : Nat) : Nat :=
  bytesToNat ((bs.drop i).take n)

theorem bytesToNatAt_eq (bs : List UInt8) (i n : Nat) :
    bytesToNatAt bs i n = bytesToNat ((bs.drop i).take n) := rfl

/-- An offset read and a suffix read are the same word: dropping further is
adding the offsets. -/
theorem bytesToNatAt_drop (bs : List UInt8) (i k n : Nat) :
    bytesToNatAt bs (i + k) n = bytesToNatAt (bs.drop i) k n := by
  rw [bytesToNatAt, bytesToNatAt, List.drop_drop]

/-- The indexed read is the carrier's own slice of the same bytes.  This is the
step a `ByteArray` reader takes through `ByteString.toList_getElem?_eq_getElem?`
and `ByteString.toList_take`/`toList_drop`. -/
theorem bytesToNatAt_slice (bs : ByteString) (i n : Nat) :
    bytesToNatAt bs.toList i n = bytesToNat (ByteString.take (ByteString.drop bs i) n).toList := by
  rw [bytesToNatAt, ByteString.toList_take, ByteString.toList_drop]

/-- A checked slice of the arena's list view is the carrier's slice of it. -/
theorem arena_slice_toList (arena : ByteString) (field len : Nat) :
    (arena.toList.drop field).take len =
      (ByteString.take (ByteString.drop arena field) len).toList := by
  rw [ByteString.toList_take, ByteString.toList_drop]

/-! ### The record step

`cursorStep` is one record at the cursor, in the encoding's own widths: a
container or literal tag is one byte, a number is the tag and eight payload
bytes, a key or string is the tag, four length bytes, eight field bytes and then
its decoded body.  The truncation checks are the walk's: a record whose payload
does not fit the remaining stream has no step, and a body that names no readable
slice has no step. -/

/-- One record at cursor `i`: its width and the event it denotes, or `none`
where the record is truncated or its body is unreadable.  The string body is
`recordBodyCodePoints`, so both sources — the arena prefix for the clear-bit
escaped form and the document for the top-bit-set plain form — are the walk's. -/
def cursorStep (bs arena evs : List UInt8) (i : Nat) : Option (Nat × ConsumerEvent) :=
  match evs.drop i with
  | [] => none
  | b :: rest =>
      match b.toNat with
      | 1 => some (1, ConsumerEvent.kind 1)
      | 2 => some (1, ConsumerEvent.kind 2)
      | 3 => some (1, ConsumerEvent.kind 3)
      | 4 => some (1, ConsumerEvent.kind 4)
      | 8 => some (1, ConsumerEvent.kind 8)
      | 9 => some (1, ConsumerEvent.kind 9)
      | 10 => some (1, ConsumerEvent.kind 10)
      | 5 =>
          if rest.length < 12 then none
          else
            let len := bytesToNat (rest.take 4)
            let field := bytesToNat ((rest.drop 4).take 8)
            match recordBodyCodePoints bs arena len field with
            | some cps => some (13, ConsumerEvent.str true len field cps)
            | none => none
      | 6 =>
          if rest.length < 12 then none
          else
            let len := bytesToNat (rest.take 4)
            let field := bytesToNat ((rest.drop 4).take 8)
            match recordBodyCodePoints bs arena len field with
            | some cps => some (13, ConsumerEvent.str false len field cps)
            | none => none
      | 7 =>
          if rest.length < 8 then none
          else some (9, ConsumerEvent.number (bytesToNat (rest.take 8)))
      | _ => none

/-- **One cursor step is one record of the walk.**  At a cursor inside the
stream, the walk of the suffix is the event the step reads, followed by the walk
of the stream the step's width skips; a step that reads nothing is a walk that
fails.  This is the step the induction runs on. -/
theorem walkRecords_drop_cursor {bs arena evs : List UInt8} {i : Nat} (hi : i < evs.length) :
    walkRecords bs arena (evs.drop i) =
      (match cursorStep bs arena evs i with
       | none => none
       | some (w, e) => (e :: ·) <$> walkRecords bs arena (evs.drop (i + w))) := by
  have hhead : evs.drop i = evs[i] :: evs.drop (i + 1) := List.drop_eq_getElem_cons hi
  rw [cursorStep, hhead]
  simp only []
  rw [walkRecords.eq_2]
  split
  all_goals
    simp only [List.drop_drop, Nat.add_assoc]
    try split
    all_goals
      try split
      all_goals
        simp_all [List.drop_drop, Nat.add_assoc]
        try
          obtain ⟨h1, h2⟩ := ‹1 = _ ∧ ConsumerEvent.kind 1 = _›
          rw [← h1, h2]
        try omega

/-! ### Widths

Every step that reads advances by at least one byte and never past the end of
the stream.  The first is what lets the cursor loop be fuelled by the stream's
length; the second is the bounds check on the event buffer, stated at the step's
own vocabulary. -/

theorem cursorStep_width_pos {bs arena evs : List UInt8} {i w : Nat} {e : ConsumerEvent}
    (h : cursorStep bs arena evs i = some (w, e)) : 1 ≤ w := by
  have hi : i < evs.length := by
    by_cases hlt : i < evs.length
    · exact hlt
    · exfalso
      have hnil : evs.drop i = [] := List.drop_eq_nil_of_le (by omega)
      unfold cursorStep at h
      rw [hnil] at h
      simp at h
  have hhead : evs.drop i = evs[i] :: evs.drop (i + 1) := List.drop_eq_getElem_cons hi
  unfold cursorStep at h
  rw [hhead] at h
  simp only [] at h
  split at h <;>
    (simp at h <;>
      first
      | omega
      | (split at h <;> (simp at h <;> omega)))

theorem cursorStep_width_le {bs arena evs : List UInt8} {i w : Nat} {e : ConsumerEvent}
    (h : cursorStep bs arena evs i = some (w, e)) : w ≤ evs.length - i := by
  have hi : i < evs.length := by
    by_cases hlt : i < evs.length
    · exact hlt
    · exfalso
      have hnil : evs.drop i = [] := List.drop_eq_nil_of_le (by omega)
      unfold cursorStep at h
      rw [hnil] at h
      simp at h
  have hhead : evs.drop i = evs[i] :: evs.drop (i + 1) := List.drop_eq_getElem_cons hi
  unfold cursorStep at h
  rw [hhead] at h
  simp only [] at h
  split at h <;>
    (simp [List.length_drop] at h <;>
      first
      | omega
      | (split at h <;> (simp [List.length_drop] at h <;> omega)))

/-! ### The cursor loop

`walkFrom` is any indexed reader's loop: at each cursor, take the step's record,
append its event, and continue after its width.  It is fuelled, so it is a total
function and the well-founded measure is not the reader's concern. -/

/-- Run `step` from cursor `i`, spending one unit of fuel per record. -/
def walkFrom (step : List UInt8 → List UInt8 → List UInt8 → Nat → Option (Nat × ConsumerEvent))
    (bs arena evs : List UInt8) : Nat → Nat → Option (List ConsumerEvent)
  | 0, _ => none
  | fuel + 1, i =>
      if evs.length ≤ i then some []
      else
        match step bs arena evs i with
        | none => none
        | some (w, e) => (e :: ·) <$> walkFrom step bs arena evs fuel (i + w)

/-- **The cursor loop is the walk.**  With one unit of fuel per remaining byte —
a record is never empty — the loop at cursor `i` is `walkRecords` on the suffix
at `i`.  The step lemma above is the only fact about the encoding this uses. -/
theorem walkFrom_cursor_eq (bs arena evs : List UInt8) :
    ∀ (fuel i : Nat), evs.length - i < fuel →
      walkFrom cursorStep bs arena evs fuel i = walkRecords bs arena (evs.drop i) := by
  intro fuel
  induction fuel with
  | zero => intro i h; omega
  | succ fuel ih =>
      intro i h
      simp only [walkFrom]
      by_cases hi : evs.length ≤ i
      · rw [if_pos hi, List.drop_eq_nil_of_le hi, walkRecords.eq_1]
      · rw [if_neg hi]
        have hilt : i < evs.length := Nat.lt_of_not_le hi
        rw [walkRecords_drop_cursor hilt]
        cases hcs : cursorStep bs arena evs i with
        | none => rfl
        | some we =>
            obtain ⟨w, e⟩ := we
            simp only [hcs]
            have hle : w ≤ evs.length - i := cursorStep_width_le hcs
            have hpos : 1 ≤ w := cursorStep_width_pos hcs
            rw [ih (i + w) (by omega)]

/-- The indexed walk from the stream's start is the list walk's events. -/
theorem eventsOfIndexed_eq_eventsOfBytes (bs arena evs : List UInt8) :
    walkFrom cursorStep bs arena evs (evs.length + 1) 0 = eventsOfBytes bs evs arena := by
  rw [eventsOfBytes, walkFrom_cursor_eq bs arena evs (evs.length + 1) 0 (by simp),
    List.drop_zero]

/-! ### The reader's contract

An implementation supplies a step over its own buffers.  The contract is that the
step reads the record `cursorStep` reads at that cursor; the theorem below turns
that contract into the event list `eventsOfBytes` returns on the very same
buffers, malformed records included. -/

/-- **The `Prop` an indexed reader states.**  Its step, at every cursor and on
every buffer triple, is the specification's record step.  Nothing here mentions
the reader's representation: a `ByteArray` step enters through
`ByteString.toList_getElem?_eq_getElem?` and `bytesToNatAt_slice`. -/
def IndexedStepAgrees
    (step : List UInt8 → List UInt8 → List UInt8 → Nat → Option (Nat × ConsumerEvent)) : Prop :=
  ∀ (bs arena evs : List UInt8) (i : Nat), step bs arena evs i = cursorStep bs arena evs i

/-- Two loops whose steps agree at every cursor are the same loop. -/
theorem walkFrom_eq_of_step
    {step : List UInt8 → List UInt8 → List UInt8 → Nat → Option (Nat × ConsumerEvent)}
    (h : IndexedStepAgrees step) (bs arena evs : List UInt8) :
    ∀ (fuel i : Nat),
      walkFrom step bs arena evs fuel i = walkFrom cursorStep bs arena evs fuel i := by
  intro fuel
  induction fuel with
  | zero => intro i; rfl
  | succ fuel ih =>
      intro i
      simp only [walkFrom]
      rw [h bs arena evs i]
      cases hcs : cursorStep bs arena evs i with
      | none => rfl
      | some we =>
          obtain ⟨w, e⟩ := we
          simp only [hcs]
          rw [ih (i + w)]

/-- **The reader's equivalence.**  An indexed reader whose step agrees with the
specification computes the events `eventsOfBytes` reads from the same document,
event bytes and arena — on every stream, including one whose records are
truncated or whose string bodies are unreadable.  Composing with
`eventsOfBytes_valueOfEvents_scalar` (`JsonEventBridgeFinal`) carries the result
to the canonical value. -/
theorem indexedReader_eq_eventsOfBytes
    {step : List UInt8 → List UInt8 → List UInt8 → Nat → Option (Nat × ConsumerEvent)}
    (h : IndexedStepAgrees step) (bs arena evs : List UInt8) :
    walkFrom step bs arena evs (evs.length + 1) 0 = eventsOfBytes bs evs arena := by
  rw [walkFrom_eq_of_step h, eventsOfIndexed_eq_eventsOfBytes]

/-- **The walker invariant a reader discharges.**  A loop whose step agrees with
the specification at every cursor reads, at cursor `i`, the events of the list
suffix `drop i`.  This is `WalkerAgrees` (`JsonEventCursor`) at the reader's own
step and fuel: an implementation whose recursion unfolds to `walkFrom` and whose
step satisfies `IndexedStepAgrees` has the invariant, and
`eventsOfIndexed_eq_eventsOfBytes` is its index-zero case. -/
theorem walker_agrees_of_step
    {step : List UInt8 → List UInt8 → List UInt8 → Nat → Option (Nat × ConsumerEvent)}
    (h : IndexedStepAgrees step) (bs arena evs : List UInt8) (i : Nat) :
    walkFrom step bs arena evs (evs.length - i + 1) i =
      walkRecords bs arena (evs.drop i) := by
  rw [walkFrom_eq_of_step h,
    walkFrom_cursor_eq bs arena evs (evs.length - i + 1) i (by omega)]

/-! ### The same step with offsets

`cursorStepIndexed` is `cursorStep` with the suffix replaced by the cursor and the
offsets that name the same bytes: the tag at `evs[i]?`, the payload at `i + 1`,
the field at `i + 5` (four length bytes after the tag), and the truncation checks
against the bytes left of the stream.  It is the step an array reader states;
`cursorStepIndexed_eq_cursorStep` is the index arithmetic that carries it to the
specification. -/

/-- One record at cursor `i`, read by offset rather than by suffix. -/
def cursorStepIndexed (bs arena evs : List UInt8) (i : Nat) :
    Option (Nat × ConsumerEvent) :=
  match evs[i]? with
  | none => none
  | some b =>
      match b.toNat with
      | 1 => some (1, ConsumerEvent.kind 1)
      | 2 => some (1, ConsumerEvent.kind 2)
      | 3 => some (1, ConsumerEvent.kind 3)
      | 4 => some (1, ConsumerEvent.kind 4)
      | 8 => some (1, ConsumerEvent.kind 8)
      | 9 => some (1, ConsumerEvent.kind 9)
      | 10 => some (1, ConsumerEvent.kind 10)
      | 5 =>
          if evs.length - i < 13 then none
          else
            let len := bytesToNatAt evs (i + 1) 4
            let field := bytesToNatAt evs (i + 5) 8
            match recordBodyCodePoints bs arena len field with
            | some cps => some (13, ConsumerEvent.str true len field cps)
            | none => none
      | 6 =>
          if evs.length - i < 13 then none
          else
            let len := bytesToNatAt evs (i + 1) 4
            let field := bytesToNatAt evs (i + 5) 8
            match recordBodyCodePoints bs arena len field with
            | some cps => some (13, ConsumerEvent.str false len field cps)
            | none => none
      | 7 =>
          if evs.length - i < 9 then none
          else some (9, ConsumerEvent.number (bytesToNatAt evs (i + 1) 8))
      | _ => none

/-- **The index arithmetic.**  At an in-stream cursor, the offset step reads
exactly the record the suffix step reads: the tag at `evs[i]?` is the suffix's
head, the checks `evs.length - i < 13`/`< 9` are the suffix's `rest.length <
12`/`< 8`, and the payload offsets are the suffix's slices. -/
theorem cursorStepIndexed_eq_cursorStep {bs arena evs : List UInt8} {i : Nat}
    (hi : i < evs.length) :
    cursorStepIndexed bs arena evs i = cursorStep bs arena evs i := by
  have hhead : evs.drop i = evs[i] :: evs.drop (i + 1) := List.drop_eq_getElem_cons hi
  have hget : evs[i]? = some evs[i] := List.getElem?_eq_getElem hi
  rw [cursorStep, hhead, cursorStepIndexed, hget]
  simp only []
  split
  all_goals
    simp only [bytesToNatAt, List.length_drop, List.drop_drop, Nat.add_assoc]
    first
    | rfl
    | (try rw [show (evs.length - i < 13) = (evs.length - (i + 1) < 12) from
          propext (by omega)])
      (try rw [show (evs.length - i < 9) = (evs.length - (i + 1) < 8) from
          propext (by omega)])
      (try rw [show i + 1 + 4 = i + 5 from by omega])
      (try rfl)
      (try (split <;> simp_all [bytesToNatAt, List.length_drop, List.drop_drop]
             <;> omega))
    | (split <;> simp_all [bytesToNatAt, List.length_drop, List.drop_drop]
         <;> omega)

/-! ### The string lookup's bounds

A string record names a body by a length and a field.  The clear-bit form is an
arena slice; the top-bit-set form is a document slice at the offset the field
clears to.  A successful lookup has already passed the check its form needs, and
the reader's check is a fact about the same two buffers. -/

theorem recordBodyCodePoints_arena {bs arena : List UInt8} {len field : Nat}
    (hf : field < 2 ^ 63) :
    recordBodyCodePoints bs arena len field =
      (if field + len ≤ arena.length then escapeCodePoints ((arena.drop field).take len)
       else none) := by
  unfold recordBodyCodePoints
  rw [if_pos hf]

theorem recordBodyCodePoints_plain {bs arena : List UInt8} {len field : Nat}
    (hf : ¬ field < 2 ^ 63) :
    recordBodyCodePoints bs arena len field =
      (if field - 2 ^ 63 + len ≤ bs.length then bodyCodePointsAt bs (field - 2 ^ 63)
       else none) := by
  unfold recordBodyCodePoints
  rw [if_neg hf]

/-- **A readable body lies inside the buffer its field names.**  The clear-bit
form is inside the arena prefix; the top-bit-set form is inside the document. -/
theorem recordBodyCodePoints_some_bounds {bs arena : List UInt8} {len field : Nat}
    {cps : List Nat} (h : recordBodyCodePoints bs arena len field = some cps) :
    (field < 2 ^ 63 ∧ field + len ≤ arena.length) ∨
      (2 ^ 63 ≤ field ∧ field - 2 ^ 63 + len ≤ bs.length) := by
  by_cases hf : field < 2 ^ 63
  · rw [recordBodyCodePoints_arena hf] at h
    by_cases hin : field + len ≤ arena.length
    · rw [if_pos hin] at h
      exact Or.inl ⟨hf, hin⟩
    · rw [if_neg hin] at h
      simp at h
  · rw [recordBodyCodePoints_plain hf] at h
    by_cases hin : field - 2 ^ 63 + len ≤ bs.length
    · rw [if_pos hin] at h
      exact Or.inr ⟨Nat.le_of_not_lt hf, hin⟩
    · rw [if_neg hin] at h
      simp at h

/-! ### Axiom pins

The declarations above use only the three axioms the project admits. -/

/-- info: 'LeanLLVM.Refinement.bytesToNatAt_slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bytesToNatAt_slice
/-- info: 'LeanLLVM.Refinement.walkRecords_drop_cursor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms walkRecords_drop_cursor
/-- info: 'LeanLLVM.Refinement.cursorStep_width_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cursorStep_width_pos
/-- info: 'LeanLLVM.Refinement.cursorStep_width_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cursorStep_width_le
/-- info: 'LeanLLVM.Refinement.walkFrom_cursor_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms walkFrom_cursor_eq
/-- info: 'LeanLLVM.Refinement.eventsOfIndexed_eq_eventsOfBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eventsOfIndexed_eq_eventsOfBytes
/-- info: 'LeanLLVM.Refinement.indexedReader_eq_eventsOfBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms indexedReader_eq_eventsOfBytes
/-- info: 'LeanLLVM.Refinement.walker_agrees_of_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms walker_agrees_of_step
/-- info: 'LeanLLVM.Refinement.cursorStepIndexed_eq_cursorStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cursorStepIndexed_eq_cursorStep
/-- info: 'LeanLLVM.Refinement.recordBodyCodePoints_some_bounds' depends on axioms: [propext] -/
#guard_msgs in
#print axioms recordBodyCodePoints_some_bounds

end LeanLLVM.Refinement
