/-
The indexed reader's equivalence interface.

`JsonEventCursor` reads the emitted stream by index; `JsonEventBytes`'
`eventsOfBytes` is the list specification.  This module is the surface a proof
or a caller consumes: the whole-reader statement `EventsOfBytesIndexedAgrees`,
the walker state `WalkerAgrees` the induction is carried on, and both as proved
theorems.

# Why the walker state, and not only the whole reader

The proof inducts on the remaining event bytes: at cursor `i` the indexed walk
must read what `walkRecords` reads from the list suffix `drop i`.  Stating only
the two whole functions would leave the induction step without a hypothesis at
a nonzero cursor, so `WalkerAgrees` is the interface's primary form;
`EventsOfBytesIndexedAgrees` is its instance at index zero, and
`eventsOfBytesIndexedAgrees_iff_walker` is the definitional bridge between them.

Both statements are over arbitrary buffers, so they cover the streams an
accepted document emits and the malformed ones a route never sees: a truncated
final record, a span past either source, an unknown tag and a body that does not
decode.

# How they are proved

The reader's loop is related to the schema's `walkFrom` at `stepR1`
(`walkRecordsIndexedFuel_eq_walkFrom`, `JsonEventCursor`), and
`JsonEventIndexedStep` proves `stepR1` is the specification's record step.  The
walker state is then `walker_agrees_of_step` at that step, and the whole-reader
statement is `walkFrom_stepR1_eq_eventsOfBytes` at the same step and fuel.
-/
import LeanLLVM.Refinement.JsonEventCursor

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-- **The cursor's state against the list specification's suffix.**  At index
`i` the indexed walk reads the same events as `walkRecords` over the list
suffix `drop i`.  This is the induction invariant: the base case is the empty
suffix, and a step consumes one record from both sides. -/
def WalkerAgrees (bs evs arena : ByteString) (i : Nat) : Prop :=
  walkRecordsIndexed bs arena evs i =
    walkRecords bs.toList arena.toList (evs.toList.drop i)

/-- **The indexed reader equals the list specification**, on the whole buffers:
the statement the reader's callers consume.  Stated over arbitrary buffers, so
it covers malformed streams — truncated records, out-of-range spans, unknown
tags and undecodable bodies — and not only the streams an accepted document
emits. -/
def EventsOfBytesIndexedAgrees (bs evs arena : ByteString) : Prop :=
  eventsOfBytesIndexed bs evs arena = eventsOfBytes bs.toList evs.toList arena.toList

/-- **The walker state, at every cursor.**  The reader's loop is the schema's
`walkFrom` at `stepR1` (`walkRecordsIndexed_eq_walkFrom`), `stepR1` is the
specification's record step (`indexedStepAgrees_stepR1`), and the schema's
induction (`walker_agrees_of_step`) carries the loop to `walkRecords` on the
list suffix. -/
theorem walkerAgrees {bs evs arena : ByteString} (i : Nat) :
    WalkerAgrees bs evs arena i := by
  unfold WalkerAgrees
  rw [walkRecordsIndexed_eq_walkFrom]
  have hfuel : evs.size - i + 1 = evs.toList.length - i + 1 := by simp
  rw [hfuel]
  exact walker_agrees_of_step indexedStepAgrees_stepR1 bs.toList arena.toList evs.toList i

/-- **The indexed reader equals the list specification.**  The loop is
`walkFrom` at `stepR1`, and `walkFrom_stepR1_eq_eventsOfBytes` reads that loop as
`eventsOfBytes` on the same three buffers. -/
theorem eventsOfBytesIndexedAgrees {bs evs arena : ByteString} :
    EventsOfBytesIndexedAgrees bs evs arena := by
  unfold EventsOfBytesIndexedAgrees eventsOfBytesIndexed
  rw [walkRecordsIndexed_eq_walkFrom]
  have hfuel : evs.size - 0 + 1 = evs.toList.length + 1 := by simp
  rw [hfuel]
  exact walkFrom_stepR1_eq_eventsOfBytes bs.toList arena.toList evs.toList

/-- The whole-reader statement is the walker state at index zero. -/
theorem eventsOfBytesIndexedAgrees_iff_walker {bs evs arena : ByteString} :
    EventsOfBytesIndexedAgrees bs evs arena ↔ WalkerAgrees bs evs arena 0 := by
  unfold EventsOfBytesIndexedAgrees WalkerAgrees eventsOfBytesIndexed eventsOfBytes
  rfl

/-! ### Axiom pins

The interface's declarations use only the three axioms the project admits. -/

/-- info: 'LeanLLVM.Refinement.walkerAgrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms walkerAgrees

/-- info: 'LeanLLVM.Refinement.eventsOfBytesIndexedAgrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventsOfBytesIndexedAgrees

/-- info: 'LeanLLVM.Refinement.eventsOfBytesIndexedAgrees_iff_walker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eventsOfBytesIndexedAgrees_iff_walker

end LeanLLVM.Refinement
