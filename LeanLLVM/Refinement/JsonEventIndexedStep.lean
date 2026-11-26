/-
The indexed reader's record step against the specification's cursor step.

`JsonEventIndexed` states the contract an indexed reader owes: `IndexedStepAgrees`
says its step, at every cursor and on every buffer triple, is `cursorStep`, and
`cursorStepIndexed` is that step written with a cursor and byte offsets rather
than a list suffix.  This module supplies the step an indexed reader uses and
discharges the contract for it, against the specification alone.

# The step

`stepR1` is the indexed record read that the reader module being added alongside
this one (`JsonEventCursor`, whose `walkRecordsIndexed` is the walk over it) will
use: the tag is looked up at the cursor, a number's and a record's fields are
read little-endian from the caller's `ByteArray` by `leNatAt`, a record's
truncation check is the additive `i + 13 ≤ evs.size` rather than a suffix length,
and a string body is `recordBodyCodePointsIndexed`.  The four operations are
carried in this module (`leNatAt`, `arenaBodyCodePoints`,
`documentBodyCodePoints`, `recordBodyCodePointsIndexed`) so that every statement
here is complete on its own; the reader module's definitions of them are these.
Nothing below depends on that module, and **What the reader module owes** at the
end is the reader's remaining obligation, not this module's.

# The bridges

Each bridge is between one of the reader's `ByteArray` operations and the list
specification's spelling of the same bytes, and each is phrased with the schema's
own lemma:

* `leNatAt_eq_bytesToNatAt` and `leNatAt_eq_slice` — the reader's little-endian
  field is `bytesToNatAt` and therefore `bytesToNatAt_slice`'s carrier slice;
* `arenaBodyCodePoints_eq` and `arenaBodyCodePoints_slice` — a checked `extract`
  of the arena is `(arena.toList.drop off).take len`, which is
  `arena_slice_toList`'s carrier slice;
* `documentBodyCodePoints_eq` — the reader's document body is `bodyCodePointsAt`
  on the same bytes;
* `recordBodyCodePointsIndexed_eq`, with the branch lemmas
  `recordBodyCodePointsIndexed_arena`/`_plain` — assembling the two under
  `recordBodyCodePoints`'s own branch order and at its own bounds, the reader's
  counterparts of `recordBodyCodePoints_arena`/`_plain`;
* `length_sub_lt_13`/`length_sub_lt_9` — the guard arithmetic, the same
  inequalities `cursorStepIndexed_eq_cursorStep` performs, in the reader's
  additive spelling.

`cursorStepIndexed_eq_cursorStep` (`JsonEventIndexed`) then carries the step to
`cursorStep`, so `IndexedStepAgrees stepR1List` — the statement the equivalence
`indexedReader_eq_eventsOfBytes` consumes — is proved, not assumed, and
`walkFrom_stepR1_eq_eventsOfBytes` is the event equality at that step.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonEventIndexed

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The reader's operations

The indexed record read's operations, one at a time: the reader module
(`JsonEventCursor`) uses these, and carrying them here keeps this module's
statements complete without depending on that module's loop. -/

/-- The little-endian natural number in the `n` bytes at `off`, read through the
array's accessor.  Past the end the accessor answers `0`, which is the field's
value there as well. -/
def leNatAt (bs : ByteString) (off : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (bs.get! off).toNat + 256 * leNatAt bs (off + 1) n

/-- The code points of the arena's `len` bytes at `off`, as the checked `extract`
the caller's bounds check licenses. -/
def arenaBodyCodePoints (arena : ByteString) (off len : Nat) : Option (List Nat) :=
  escapeCodePoints (arena.extract off (off + len)).toList

/-- The code points of a document body starting at `off`, read by the
escape-aware scan the reference's token decoder uses. -/
def documentBodyCodePoints (bs : ByteString) (off : Nat) : Option (List Nat) :=
  match scanCharsEnd bs off 0 with
  | .ok (cs, _) => some cs
  | .error _ => none

/-- A string or key record's decoded body, from the source its field names.  The
branch order and the two range checks are `recordBodyCodePoints`'s. -/
def recordBodyCodePointsIndexed (bs arena : ByteString) (len field : Nat) :
    Option (List Nat) :=
  if field < 2 ^ 63 then
    if field + len ≤ arena.size then
      arenaBodyCodePoints arena field len
    else none
  else
    let off := field - 2 ^ 63
    if off + len ≤ bs.size then
      documentBodyCodePoints bs off
    else none

/-! ### The carrier's `get!`

`leNatAt` reads a field through `ByteArray.get!`, whose out-of-bounds answer is
the inhabitant `0`; the specification reads the same bytes as a `List` slice.
The three lemmas below are the only place the accessor's bounds policy is used. -/

/-- In bounds, `get!` is the byte there. -/
theorem get!_eq_getElem_of_lt {bs : ByteString} {i : Nat} (h : i < bs.size) :
    bs.get! i = bs[i] := by
  have h' : i < bs.data.size := h
  show bs.data[i]! = bs.data[i]
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h']
  rfl

/-- Past the end, `get!` is the inhabitant, which for bytes is `0`. -/
theorem get!_eq_zero_of_le {bs : ByteString} {i : Nat} (h : bs.size ≤ i) :
    bs.get! i = 0 := by
  have h' : bs.data.size ≤ i := h
  show bs.data[i]! = 0
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h']
  rfl

/-- The reader's accessor is the list's byte, the form the specification's
slices produce. -/
theorem get!_eq_toList_getElem {bs : ByteString} {i : Nat} (h : i < bs.size) :
    bs.get! i = bs.toList[i]'(by simpa using h) := by
  rw [get!_eq_getElem_of_lt h]
  have h1 : bs.toList[i]? = some bs[i] := by
    rw [ByteString.toList_getElem?_eq_getElem?, ByteString.getElem?_eq_getElem h]
  exact ((List.getElem?_eq_some_iff.mp h1).2).symm

/-! ### The little-endian field -/

/-- **The reader's field read is the specification's offset read.**  `leNatAt`
walks the array with `get!`; `bytesToNatAt` takes the corresponding `List` slice,
and the two agree past the end as well, where both answer zero. -/
theorem leNatAt_eq_bytesToNatAt (bs : ByteString) (off n : Nat) :
    leNatAt bs off n = bytesToNatAt bs.toList off n := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih =>
      simp only [leNatAt, bytesToNatAt]
      rw [ih (off + 1)]
      by_cases h : off < bs.size
      · have hlen : off < bs.toList.length := by simpa using h
        rw [List.drop_eq_getElem_cons hlen, List.take_succ_cons,
          get!_eq_toList_getElem h]
        simp only [bytesToNat]
        rfl
      · have hge : bs.size ≤ off := Nat.le_of_not_lt h
        have hlen : bs.toList.length ≤ off := by simpa using hge
        have hlen1 : bs.toList.length ≤ off + 1 := by omega
        have h0 : bytesToNatAt bs.toList (off + 1) n = 0 := by
          simp only [bytesToNatAt, List.drop_eq_nil_of_le hlen1, List.take_nil,
            bytesToNat]
        rw [List.drop_eq_nil_of_le hlen, h0, get!_eq_zero_of_le hge]
        rfl

/-- **The reader's field read is the carrier's slice.**  Composing with the
schema's `bytesToNatAt_slice`: the field is `bytesToNat` of the `ByteString` take
of the drop, which is the read an array implementation states. -/
theorem leNatAt_eq_slice (bs : ByteString) (off n : Nat) :
    leNatAt bs off n = bytesToNat (ByteString.take (ByteString.drop bs off) n).toList := by
  rw [leNatAt_eq_bytesToNatAt, bytesToNatAt_slice]

/-! ### The two string-body sources -/

/-- A checked `extract` is the `List` slice the specification takes. -/
theorem extract_toList_take_drop (bs : ByteString) (i j : Nat) :
    (bs.extract i j).toList = (bs.toList.drop i).take (Nat.sub j i) := by
  rw [ByteString.toList_eq_data_toList, ByteArray.data_extract, ByteString.extract_toList,
    ByteString.toList_eq_data_toList]

/-- **The arena body is the specification's arena slice.**  The reader's checked
`extract` and `escapeCodePoints` are `(arena.drop field).take len` under the
carrier's list view. -/
theorem arenaBodyCodePoints_eq (arena : ByteString) (off len : Nat) :
    arenaBodyCodePoints arena off len
      = escapeCodePoints ((arena.toList.drop off).take len) := by
  unfold arenaBodyCodePoints
  rw [extract_toList_take_drop,
    show Nat.sub (off + len) off = len from Nat.add_sub_cancel_left off len]

/-- **The arena body is the carrier's slice.**  Composing with the schema's
`arena_slice_toList`: the reader's arena source is the same bytes as
`ByteString.take (ByteString.drop arena field) len`. -/
theorem arenaBodyCodePoints_slice (arena : ByteString) (off len : Nat) :
    arenaBodyCodePoints arena off len
      = escapeCodePoints (ByteString.take (ByteString.drop arena off) len).toList := by
  rw [arenaBodyCodePoints_eq, arena_slice_toList]

/-- **The document body is the specification's scan of the same bytes.**  The
reader scans the array; the specification scans the literal of its list, which
is the array again. -/
theorem bodyCodePointsAt_eq_document (bs : ByteString) (off : Nat) :
    bodyCodePointsAt bs.toList off
      = documentBodyCodePoints (ByteString.literal bs.toList) off := by
  unfold bodyCodePointsAt documentBodyCodePoints
  cases h : scanCharsEnd (ByteString.literal bs.toList) off 0 <;> rfl

theorem documentBodyCodePoints_eq (bs : ByteString) (off : Nat) :
    documentBodyCodePoints bs off = bodyCodePointsAt bs.toList off := by
  have h := congrArg (fun x => documentBodyCodePoints x off)
    (ByteString.literal_toList bs)
  rw [← h]
  exact (bodyCodePointsAt_eq_document bs off).symm

/-- The reader's branch at the clear-bit form, its counterpart of
`recordBodyCodePoints_arena`. -/
theorem recordBodyCodePointsIndexed_arena {bs arena : ByteString} {len field : Nat}
    (hf : field < 2 ^ 63) :
    recordBodyCodePointsIndexed bs arena len field =
      (if field + len ≤ arena.size then arenaBodyCodePoints arena field len else none) := by
  unfold recordBodyCodePointsIndexed
  rw [ite_eq_left hf]

/-- The reader's branch at the top-bit-set form, its counterpart of
`recordBodyCodePoints_plain`. -/
theorem recordBodyCodePointsIndexed_plain {bs arena : ByteString} {len field : Nat}
    (hf : ¬ field < 2 ^ 63) :
    recordBodyCodePointsIndexed bs arena len field =
      (if field - 2 ^ 63 + len ≤ bs.size then
        documentBodyCodePoints bs (field - 2 ^ 63)
       else none) := by
  unfold recordBodyCodePointsIndexed
  rw [ite_eq_right hf]

/-- **The reader's body lookup is the specification's.**  The two branch orders
coincide, the two range checks are the same two bounds on the same buffers, and
the two bodies are `arenaBodyCodePoints_eq`/`documentBodyCodePoints_eq`. -/
theorem recordBodyCodePointsIndexed_eq (bs arena : ByteString) (len field : Nat) :
    recordBodyCodePointsIndexed bs arena len field
      = recordBodyCodePoints bs.toList arena.toList len field := by
  by_cases hf : field < 2 ^ 63
  · rw [recordBodyCodePointsIndexed_arena hf, recordBodyCodePoints_arena hf,
      arenaBodyCodePoints_eq]
    simp only [ByteString.toList_length]
  · rw [recordBodyCodePointsIndexed_plain hf, recordBodyCodePoints_plain hf,
      documentBodyCodePoints_eq]
    simp only [ByteString.toList_length]

/-! ### The record step

The record read that the reader's walk (`walkRecordsIndexed`) will run, as a
step: the tag by index, the widths the encoding fixes, the additive truncation
checks, and the body read above.  `walkFrom` (`JsonEventIndexed`) runs exactly
this step. -/

/-- One record at cursor `i`, the read the reader's walk (`walkRecordsIndexed`)
will run.  The
widths are the encoding's (`1`, `9` and `13`), the truncation checks are
`i + w ≤ evs.size`, and a key or string body is `recordBodyCodePointsIndexed`. -/
def stepR1 (bs arena evs : ByteString) (i : Nat) : Option (Nat × ConsumerEvent) :=
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
          if i + 13 ≤ evs.size then
            let len := leNatAt evs (i + 1) 4
            let field := leNatAt evs (i + 5) 8
            match recordBodyCodePointsIndexed bs arena len field with
            | some cps => some (13, ConsumerEvent.str true len field cps)
            | none => none
          else none
      | 6 =>
          if i + 13 ≤ evs.size then
            let len := leNatAt evs (i + 1) 4
            let field := leNatAt evs (i + 5) 8
            match recordBodyCodePointsIndexed bs arena len field with
            | some cps => some (13, ConsumerEvent.str false len field cps)
            | none => none
          else none
      | 7 =>
          if i + 9 ≤ evs.size then
            some (9, ConsumerEvent.number (leNatAt evs (i + 1) 8))
          else none
      | _ => none

/-! ### The guard arithmetic

The schema's indexed step checks `evs.length - i < 13`; the reader checks
`i + 13 ≤ evs.size`, which is the same inequality written forwards. -/

/-- The two spellings of the record's truncation check. -/
theorem length_sub_lt_13 (evs : ByteString) (i : Nat) :
    (evs.toList.length - i < 13) = ¬ (i + 13 ≤ evs.size) := by
  have h : evs.toList.length = evs.size := by simp
  rw [h]
  exact propext (by omega)

/-- The two spellings of the number's truncation check. -/
theorem length_sub_lt_9 (evs : ByteString) (i : Nat) :
    (evs.toList.length - i < 9) = ¬ (i + 9 ≤ evs.size) := by
  have h : evs.toList.length = evs.size := by simp
  rw [h]
  exact propext (by omega)

/-- **One record read two ways.**  At an in-stream cursor the reader's step is
the schema's offset step on the same bytes: the tag, the widths, the additive
truncation checks, the `leNatAt`/`bytesToNatAt` fields, and the body. -/
theorem stepR1_eq_cursorStepIndexed {bs arena evs : ByteString} {i : Nat}
    (hi : i < evs.size) :
    stepR1 bs arena evs i = cursorStepIndexed bs.toList arena.toList evs.toList i := by
  have hgetL : evs.toList[i]? = some evs[i] := by
    rw [ByteString.toList_getElem?_eq_getElem?, ByteString.getElem?_eq_getElem hi]
  unfold stepR1 cursorStepIndexed
  rw [ByteString.getElem?_eq_getElem hi, hgetL]
  simp only []
  split
  all_goals
    simp_all only [length_sub_lt_13, length_sub_lt_9, ite_not,
      leNatAt_eq_bytesToNatAt, recordBodyCodePointsIndexed_eq]
    try (repeat (first | rfl | split))

/-- **The reader's step is the specification's.**  Inside the stream this is the
schema's index arithmetic on top of `stepR1_eq_cursorStepIndexed`; past the end
both read nothing. -/
theorem stepR1_eq_cursorStep (bs arena evs : ByteString) (i : Nat) :
    stepR1 bs arena evs i = cursorStep bs.toList arena.toList evs.toList i := by
  by_cases hi : i < evs.size
  · rw [stepR1_eq_cursorStepIndexed hi,
      cursorStepIndexed_eq_cursorStep (by simpa using hi)]
  · have hge : evs.size ≤ i := Nat.le_of_not_lt hi
    have hnone : evs[i]? = none := by
      rw [ByteString.getElem?_eq_data, Array.getElem?_eq_none (by simpa using hge)]
    have hdrop : evs.toList.drop i = [] := by
      apply List.drop_eq_nil_of_le
      simpa using hge
    unfold stepR1 cursorStep
    rw [hnone, hdrop]

/-! ### The contract, in the schema's list vocabulary -/

/-- The same read over the schema's list buffers: the reader's step on the
literals, whose list view is the list it was given. -/
def stepR1List (bs arena evs : List UInt8) (i : Nat) : Option (Nat × ConsumerEvent) :=
  stepR1 (ByteString.literal bs) (ByteString.literal arena) (ByteString.literal evs) i

/-- **`IndexedStepAgrees` at the reader's step.**  This is the fact
`indexedReader_eq_eventsOfBytes` consumes, proved for the step the reader uses. -/
theorem indexedStepAgrees_stepR1 : IndexedStepAgrees stepR1List := by
  intro bs arena evs i
  unfold stepR1List
  rw [stepR1_eq_cursorStep]
  simp

/-- **The reader's event list is `eventsOfBytes`'s.**  With the contract
discharged, the schema's induction applies unchanged on every stream, malformed
included. -/
theorem walkFrom_stepR1_eq_eventsOfBytes (bs arena evs : List UInt8) :
    walkFrom stepR1List bs arena evs (evs.length + 1) 0 = eventsOfBytes bs evs arena :=
  indexedReader_eq_eventsOfBytes indexedStepAgrees_stepR1 bs arena evs

/-! ### What the reader module owes

The reader module being added alongside this one (`JsonEventCursor`) will supply
`walkRecordsIndexed`, the well-founded walk that runs `stepR1` at each record.
Its one obligation will be the unfolding at an in-stream cursor:

    walkRecordsIndexed bs arena evs i =
      (match stepR1 bs arena evs i with
       | none => none
       | some (w, e) => (e :: ·) <$> walkRecordsIndexed bs arena evs (i + w))

together with the observation that its loop is `walkFrom stepR1List` (its
recursion, read as the schema's fuel).  Given that unfolding,
`stepR1_eq_cursorStep` above and `walkRecords_drop_cursor`'s width bounds turn it
into `WalkerAgrees` and hence `EventsOfBytesIndexedAgrees` for the walk.  The
event equality at the step itself is already
`walkFrom_stepR1_eq_eventsOfBytes`.

Nothing about the specification's side is left open here: `IndexedStepAgrees
stepR1List` and `walkFrom_stepR1_eq_eventsOfBytes` are proved directly against
`cursorStep` and `eventsOfBytes`, independent of any implementation.

One observation about a candidate, which was never committed and so is not
repository state: a candidate `walkRecordsIndexed` definition failed its
termination check with a deterministic `whnf` timeout at heartbeat budgets up to
1,000,000 on this toolchain.  That is a note about an uncommitted candidate, not
about the reader module that lands, and the reader module's own prose — where its
choice of a fuelled loop is motivated — is where it belongs; it is repeated here
only so the obligation above is not mistaken for an unfinished proof on this
module's side. -/

/-! ### Axiom pins

The declarations above use only the three axioms the project admits. -/

/-- info: 'LeanLLVM.Refinement.leNatAt_eq_bytesToNatAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms leNatAt_eq_bytesToNatAt
/-- info: 'LeanLLVM.Refinement.arenaBodyCodePoints_slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms arenaBodyCodePoints_slice
/-- info: 'LeanLLVM.Refinement.documentBodyCodePoints_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms documentBodyCodePoints_eq
/-- info: 'LeanLLVM.Refinement.recordBodyCodePointsIndexed_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms recordBodyCodePointsIndexed_eq
/-- info: 'LeanLLVM.Refinement.stepR1_eq_cursorStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepR1_eq_cursorStep
/-- info: 'LeanLLVM.Refinement.indexedStepAgrees_stepR1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms indexedStepAgrees_stepR1
/-- info: 'LeanLLVM.Refinement.walkFrom_stepR1_eq_eventsOfBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms walkFrom_stepR1_eq_eventsOfBytes

end LeanLLVM.Refinement
