/-
The consumer's event stream read by index.

`eventsOfBytes` (`JsonEventBytes`) is the reader over lists: it consumes the
event bytes a record at a time and, for a key or string, takes a list slice of
the arena prefix or reads the document's body with the escape-aware scan.  That
is the executable specification, and its `rest.length` truncation checks make it
quadratic on a long stream: every number record recomputes the length of the
suffix it is about to drop, so an array of `n` numbers costs `n²` list steps.

This module is the same reading with a cursor.  The record at the cursor is
`stepR1` (`JsonEventIndexedStep`): the tag is read at the index, a number's and a
record's fields are read little-endian from the caller's `ByteArray`, a record's
truncation check is the additive `i + 13 ≤ evs.size`, and a string body is read
from a checked byte range of the buffer its field names.  This module supplies
the loop around that step — fuelled by the bytes left, so a record is never
empty and the cursor leaves the stream before the fuel does — and relates it to
`walkFrom` (`JsonEventIndexed`), the schema's proved loop over the literal list
buffers.

# The equivalence

`JsonEventIndexedStep` proves the step is the specification's (`stepR1_eq_cursorStep`,
`indexedStepAgrees_stepR1`) and `JsonEventIndexed` proves `walkFrom` at that step
is `eventsOfBytes` (`walkFrom_stepR1_eq_eventsOfBytes`).  The one thing between
them and this module's `ByteArray` loop is the buffer representation:
`stepR1List_toList` rewrites the literal list buffers back to the buffers, and
`walkRecordsIndexedFuel_eq_walkFrom` is the induction that carries the loop.
`JsonEventCursorInterface` states the two `Prop`s that induction discharges.
-/
import LeanLLVM.Refinement.JsonEventIndexedStep

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The loop -/

/-- Run the reader's record step from cursor `i`, spending one unit of fuel per
record.  The shape is `walkFrom`'s (`JsonEventIndexed`), over the reader's own
buffers: a cursor at or past the end reads the empty event list, a truncated or
unreadable record reads nothing, and a record advances the cursor by its width.
The zero-fuel state reads nothing; the wrapper below never supplies one before
the cursor has left the stream. -/
def walkRecordsIndexedFuel (bs arena evs : ByteString) : Nat → Nat →
    Option (List ConsumerEvent)
  | 0, _ => none
  | fuel + 1, i =>
      if evs.size ≤ i then some []
      else
        match stepR1 bs arena evs i with
        | none => none
        | some (w, e) =>
            (e :: ·) <$> walkRecordsIndexedFuel bs arena evs fuel (i + w)

/-- The walk at a cursor, fuelled by the bytes left plus one: a record's width is
at least one byte, so the cursor leaves the stream before the fuel runs out. -/
def walkRecordsIndexed (bs arena evs : ByteString) (i : Nat) :
    Option (List ConsumerEvent) :=
  walkRecordsIndexedFuel bs arena evs (evs.size - i + 1) i

/-- **The consumer's events read back from the emitted stream, by index.**  `bs`
is the document, `evs` the event bytes and `arena` the arena prefix; the result
is the events `eventsOfBytes` would read from the same three, or `none` where a
record is truncated or a string body cannot be read from the source its field
names. -/
def eventsOfBytesIndexed (bs evs arena : ByteString) : Option (List ConsumerEvent) :=
  walkRecordsIndexed bs arena evs 0

/-! ### The loop against the schema's -/

/-- The reader's step over the literal list buffers is the reader's step over the
buffers: `literal bs.toList` is `bs`, by `ByteString.literal_toList`. -/
theorem stepR1List_toList (bs arena evs : ByteString) (i : Nat) :
    stepR1List bs.toList arena.toList evs.toList i = stepR1 bs arena evs i := by
  unfold stepR1List
  rw [ByteString.literal_toList, ByteString.literal_toList, ByteString.literal_toList]

/-- **The reader's loop is `walkFrom` at the same step.**  Only the buffer
representation differs: `stepR1List_toList` is the step and
`ByteString.toList_length` is the end-of-stream check. -/
theorem walkRecordsIndexedFuel_eq_walkFrom (bs arena evs : ByteString) :
    ∀ fuel i,
      walkRecordsIndexedFuel bs arena evs fuel i =
        walkFrom stepR1List bs.toList arena.toList evs.toList fuel i := by
  intro fuel
  induction fuel with
  | zero => intro i; rfl
  | succ fuel ih =>
      intro i
      simp only [walkRecordsIndexedFuel, walkFrom, ByteString.toList_length]
      by_cases hi : evs.size ≤ i
      · simp only [if_pos hi]
      · simp only [if_neg hi]
        rw [stepR1List_toList]
        cases hstep : stepR1 bs arena evs i with
        | none => rfl
        | some we =>
            obtain ⟨w, e⟩ := we
            simp only [hstep]
            rw [ih (i + w)]

/-- The fuelled walk at a cursor is `walkFrom` at the same step and cursor. -/
theorem walkRecordsIndexed_eq_walkFrom (bs arena evs : ByteString) (i : Nat) :
    walkRecordsIndexed bs arena evs i =
      walkFrom stepR1List bs.toList arena.toList evs.toList (evs.size - i + 1) i := by
  unfold walkRecordsIndexed
  rw [walkRecordsIndexedFuel_eq_walkFrom]

end LeanLLVM.Refinement
