/-
The parser's own run at `[1]`, computed.

`JsonEventPremisesOne` leaves premise 5 — `parseBytes Limits.default (ByteString.literal
evbDoc) = .ok t` — as a hypothesis, because `parseBytes` reaches `parseValue`, a
well-founded recursion, which neither `decide` nor `native_decide` may evaluate
(the latter is excluded outright).  This module computes it by casing the
generated equations branch by branch.  The document is three bytes, so the
recursion is three steps: the opener's array branch, the number's `parseNumber`
(plain, not well founded), and the element tail's stop at the closer.  Each
branch is chosen by a `decide`d byte test on the literal document; the branches
the bytes rule out are closed by the same literal.

With this, the decoder theorem's premise 5 is a theorem at `[1]`, and the only
open premises of the slice are the two the emitter's run supplies
(`EvbEmission`).

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonEventPremisesOne

set_option autoImplicit false
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option maxHeartbeats 1600000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The literal document's byte tests

Every branch the three unfoldings take is one of these, and each is a closed
computation on `ByteString.literal evbDoc`. -/

/-- The document's own spelling, so a branch hypothesis mentioning `evbDoc` can
be read as the literal list. -/
theorem evbDoc_def : evbDoc = [0x5B, 0x31, 0x5D] := rfl

theorem evbDoc_get0 : (ByteString.literal evbDoc)[0]? = some 0x5B := by decide

theorem evbDoc_get1 : (ByteString.literal evbDoc)[1]? = some 0x31 := by decide

theorem evb_numRun : numRunFrom (ByteString.literal evbDoc) 1 = evbLex := by decide

theorem evb_numLex : numLexB evbLex = true := by decide

/-! ### The number's record

`parseNumber` is a plain definition over the run's bytes, so its result is a
closed computation: one lexeme byte, the scanner's accept, and the token at
`1..2`. -/

theorem evb_parseNumber :
    parseNumber (ByteString.literal evbDoc) 1 =
      .done { tokens := [.number ⟨1, 2⟩], value := .number evbLex, next := 2,
              consumed := by decide } := by
  unfold parseNumber
  simp [evb_numRun, evb_numLex]
  decide

/-- The element tail's stop: the closer is not a comma, so the tail returns
without an element and its cursor is the closer's index. -/
theorem evb_parseElemsTail :
    parseElemsTail (ByteString.literal evbDoc) 2 127 =
      .done { tokens := [], values := [], next := 2, moved := by decide } := by
  rw [parseElemsTail.eq_def]
  rfl

/-- The number as a value.  `split` cases the byte match; every branch but the
catch-all contradicts the document's byte at `1`, and in the catch-all the
hypothesis fixes that byte to `0x31`, which is a digit, so the value parser
calls `parseNumber`. -/
theorem evb_parseValue_one :
    parseValue (ByteString.literal evbDoc) 1 127 =
      .done { tokens := [.number ⟨1, 2⟩], value := .number evbLex, next := 2,
              consumed := by decide } := by
  rw [parseValue.eq_def]
  split
  · exfalso; rename_i heq; rw [evbDoc_get1] at heq; simp at heq
  · exfalso; rename_i heq; rw [evbDoc_get1] at heq; simp at heq
  · exfalso; rename_i heq; rw [evbDoc_get1] at heq; simp at heq
  · exfalso; rename_i heq; rw [evbDoc_get1] at heq; simp at heq
  · exfalso; rename_i heq; rw [evbDoc_get1] at heq; simp at heq
  · exfalso; rename_i heq; rw [evbDoc_get1] at heq; simp at heq
  · exfalso; rename_i heq; rw [evbDoc_get1] at heq; simp at heq
  · rename_i heq
    rw [evbDoc_get1] at heq
    simp at heq
    rw [← heq]
    exact evb_parseNumber

/-- The number parser at the opener branch's own argument spelling: `first` is
`skipFrom bs (0 + 1)` and the depth is `128 - 1`, which the branch's simp step
reduces to `127`.  Definitionally the same application as `evb_parseValue_one`;
it is stated in the goal's spelling so the branch's inner match rewrites with
`rw`. -/
theorem evb_parseValue_one_at :
    parseValue (ByteString.literal evbDoc)
        (skipFrom (ByteString.literal evbDoc) (0 + 1)) 127 =
      .done { tokens := [.number ⟨1, 2⟩], value := .number evbLex, next := 2,
              consumed := by decide } :=
  evb_parseValue_one

/-! ### The opener's array record

The array branch: depth 128 is not zero, the first element starts at `1`, the
byte at `1` is not the closing bracket, the first element parses (above), the
tail stops at `2`, and the byte at `2` is the closing bracket. -/

theorem evb_parseValue_zero :
    parseValue (ByteString.literal evbDoc) 0 128 =
      .done { tokens := evbTokens, value := .array [.number evbLex], next := 3,
              consumed := by decide } := by
  rw [parseValue.eq_def]
  split
  · exfalso; rename_i heq; simp [evbDoc_def] at heq
  · simp only [show (128 : Nat) - 1 = 127 from rfl]
    rw [ite_eq_right (by decide)]
    rw [evb_parseValue_one_at]
    dsimp only
    rw [evb_parseElemsTail]
    dsimp only
    rfl
  · exfalso; rename_i heq; rw [evbDoc_get0] at heq; simp at heq
  · exfalso; rename_i heq; rw [evbDoc_get0] at heq; simp at heq
  · exfalso; rename_i heq; rw [evbDoc_get0] at heq; simp at heq
  · exfalso; rename_i heq; rw [evbDoc_get0] at heq; simp at heq
  · exfalso; rename_i heq; rw [evbDoc_get0] at heq; simp at heq
  · exfalso; rename_i heq; rw [evbDoc_get0] at heq; simp at heq; subst heq; simp_all

/-! ### The whole-document parse

The length and byte-order-mark branches are both false, the value parser returns
the record above, the parse consumed the document, and the token count fits. -/

/-- **Premise 5 at `[1]`, computed.**  The reference parser returns exactly
`evbTape`: the document's bytes and the three tokens the trace is related to. -/
theorem evb_parse :
    parseBytes Limits.default (ByteString.literal evbDoc) = .ok evbTape := by
  unfold parseBytes
  rw [ite_eq_right (by decide :
    ¬ (ByteString.literal evbDoc).length > Limits.default.maxInput)]
  rw [ite_eq_right (by decide :
    ¬ (ByteString.literal evbDoc).take 3 = ByteString.literal [0xEF, 0xBB, 0xBF])]
  rw [show parseValue (ByteString.literal evbDoc)
        (skipFrom (ByteString.literal evbDoc) 0) Limits.default.maxDepth =
      .done { tokens := evbTokens, value := .array [.number evbLex], next := 3,
              consumed := by decide } from evb_parseValue_zero]
  dsimp only
  rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  rfl

/-! ### The slice with premise 5 discharged -/

/-- **The interface's consumer, with the parser's tape a theorem.**  The emitted
stream's value is the reference's canonical value at `[1]`, conditional only on
the emitter's two buffer identities. -/
theorem evb_value_of_emission {arena events : List UInt8} (hemit : EvbEmission arena events) :
    (eventsOfBytes evbDoc events arena).bind valueOfEvents =
      scalarCanonValueOfBytes evbDoc :=
  evb_value hemit evb_parse

/-- **The slice's value, unconditionally.**  At the buffers the trace names — the
empty arena and the three-record stream — the event decoder's value is the
reference parser's canonical value.  No premise remains: the three decoder-side
premises are `evb_within`, `evb_bounded` and the definitional row (row 2 is
`rfl`), the two reference-side premises are `evb_parse` and `evb_tokens`, and the
two emitter-side ones (`records`, `events`) are instated at the buffers the slice
names — `records` from the document's spelling (`evb_records`), `events` at the
concrete stream. -/
theorem evb_sliceOne_value_closed :
    (eventsOfBytes evbDoc evbEvents []).bind valueOfEvents =
      scalarCanonValueOfBytes evbDoc :=
  evb_sliceOne_value evb_parse

/-- The bundle, inhabited at the concrete buffers. -/
theorem evb_premises_closed :
    EvbPremises evbDoc [] evbEvents evbRecords evbTokens evbTape
      (consumeRecords evbDoc [] evbRecords) :=
  EvbPremises.ofTrace evb_records evb_within evb_bounded evb_parse evb_tokens evb_events

/-- info: 'LeanLLVM.Refinement.evbDoc_get0' does not depend on any axioms -/
#guard_msgs in
#print axioms evbDoc_get0

/-- info: 'LeanLLVM.Refinement.evb_numRun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_numRun

/-- info: 'LeanLLVM.Refinement.evb_parseNumber' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_parseNumber

/-- info: 'LeanLLVM.Refinement.evb_parseElemsTail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_parseElemsTail

/-- info: 'LeanLLVM.Refinement.evb_parseValue_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_parseValue_one

/-- info: 'LeanLLVM.Refinement.evb_parseValue_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_parseValue_zero

/-- info: 'LeanLLVM.Refinement.evb_parse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_parse

/-- info: 'LeanLLVM.Refinement.evb_value_of_emission' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evb_value_of_emission

/-- info: 'LeanLLVM.Refinement.evb_sliceOne_value_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evb_sliceOne_value_closed

/-- info: 'LeanLLVM.Refinement.evb_premises_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_premises_closed

end LeanLLVM.Refinement
