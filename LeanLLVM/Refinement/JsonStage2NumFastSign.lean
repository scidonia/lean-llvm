/-
`num_fast_el1`'s sign at the merge: `%tobool274.not` is the lexeme's sign, and
nothing on the scan's path rebinds it.

`if.end`'s first `phi` is the sign's bit: `%cmp1 = (%0 != '-')` from
`land.lhs.true`.  The merge block `cleanup282.thread` reads that same register
through the select `%cond266`, so the store's sign is the sign of the lexeme's
first byte — provided the scan between the two blocks never writes the register.

Two statements make that tie available, and this module states the second.

1. **The transport.**  `JsonStage2NumFastCells` carries the sign across a run:
   `%tobool274.not` is `if.end`'s destination and no other block's
   (`numFast_tobool_written_at_if_end`), so a `NumFastChain` whose steps avoid
   `if.end` leaves the cell where it found it (`NumFastChain.sign`), and the
   dispatch establishes it at `if.end` in three steps
   (`JsonStage2NumFastCarried.sign_at_ifEnd6`).  The sign's *value* is therefore
   `evalICmp .ne (%0) '-'` at every later state of the route, which is what the
   tie below reads.
2. **The tie at the model.**  `sign_tie` reads a well-formed lexeme's first byte
   as `d.neg`: `-` exactly at a negative sign, so `%tobool274.not = 1 ↔ ¬d.neg`.
   `sign_tie_of_read` is the same statement at the register the block's
   comparison leaves, which is the form a body-level statement reads.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastTier1
import LeanLLVM.Refinement.JsonStage2NumFastArm
import LeanLLVM.Refinement.JsonStage2NumFastCells
import LeanLLVM.Refinement.JsonEntrySteps

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.JSON
open LeanLLVM.StrtodRefine
open LeanLLVM.StrtodTier1

namespace NumFastSign

/-! ### The lexeme's first byte

`d.lexeme` is `signBytes d.neg ++ d.body`, and `d.body` starts with the `int`
part, which is never empty and never begins with `-`.  So the first byte is `-`
exactly at `d.neg = true`. -/

/-- An `IntPart` starts with a byte that is not `-`. -/
theorem intPart_head_ne {bs : Bytes} (h : IntPart bs) :
    ∃ b rest, bs.toList = b :: rest ∧ b ≠ 0x2D := by
  cases h with
  | zero => exact ⟨0x30, [], by simp [ByteString.toList_cons], by decide⟩
  | lead h1 h2 hr =>
      exact ⟨_, _, by rw [ByteString.toList_cons], by
        intro hb
        rw [hb] at h1
        exact absurd h1 (by decide)⟩

/-- The lexeme's body starts with its `int` part. -/
theorem body_eq_ip_append (d : Decimal) : ∃ t, d.body = d.ip ++ t := by
  cases hf : d.fr with
  | none =>
      cases he : d.ex with
      | none => exact ⟨ByteString.empty, by
          simp only [Decimal.body, hf, he, ByteString.append_empty]⟩
      | some p =>
          obtain ⟨s, ds⟩ := p
          exact ⟨0x65 +: (Decimal.signBytes s ++ ds), by
            simp only [Decimal.body, hf, he, ByteString.append_empty]⟩
  | some fs =>
      cases he : d.ex with
      | none => exact ⟨0x2E +: fs, by simp [Decimal.body, hf, he]⟩
      | some p =>
          obtain ⟨s, ds⟩ := p
          exact ⟨(0x2E +: fs) ++ (0x65 +: (Decimal.signBytes s ++ ds)), by
            simp only [Decimal.body, hf, he, ByteString.append_assoc,
              ByteString.cons_append]⟩

/-- A well-formed lexeme's body starts with a byte that is not `-`. -/
theorem body_head_ne {d : Decimal} (hd : d.wellFormed) :
    ∃ b rest, d.body.toList = b :: rest ∧ b ≠ 0x2D := by
  obtain ⟨b, rest, hb, hne⟩ := intPart_head_ne hd.1
  obtain ⟨t, ht⟩ := body_eq_ip_append d
  refine ⟨b, rest ++ t.toList, ?_, hne⟩
  rw [ht, ByteString.toList_append, hb, List.cons_append]

/-- A positive lexeme starts with a byte that is not `-`. -/
theorem lexeme_head_pos {d : Decimal} (hd : d.wellFormed) (h : d.neg = false) :
    ∃ b rest, d.lexeme.toList = b :: rest ∧ b ≠ 0x2D := by
  obtain ⟨b, rest, hb, hne⟩ := body_head_ne hd
  refine ⟨b, rest, ?_, hne⟩
  rw [Decimal.lexeme, h, Decimal.signBytes_false, ByteString.toList_append,
    ByteString.toList_empty, List.nil_append]
  exact hb

/-- A negative lexeme starts with `-`. -/
theorem lexeme_head_neg {d : Decimal} (h : d.neg = true) :
    d.lexeme.toList.head? = some 0x2D := by
  simp only [Decimal.lexeme, h, Decimal.signBytes_true, ByteString.toList_append,
    ByteString.toList_cons, ByteString.toList_empty, List.nil_append,
    List.singleton_append, List.head?_cons]

/-- **The sign tie.**  A well-formed lexeme's first byte is `-` exactly when its
sign is, so the body's `(%0 != '-')` reading is `1` exactly at a positive lexeme.
This is the `hsign` `t1_store_bits` reads. -/
theorem sign_tie {d : Decimal} {b : UInt8} (hd : d.wellFormed)
    (hb : d.lexeme.toList.head? = some b) :
    (evalICmp .ne (JsonScanLane.vByte b) 0x2d#8 = (1 : BitVec 1)) ↔ d.neg = false := by
  by_cases h : d.neg = false
  · have hp := lexeme_head_pos hd h
    obtain ⟨b', rest, hbx, hne⟩ := hp
    have hbb : b = b' := by
      rw [hbx] at hb
      simp only [List.head?_cons, Option.some.injEq] at hb
      exact hb.symm
    subst hbb
    constructor
    · intro _; exact h
    · intro _
      rw [NumFastStarts.evalICmp_ne_minus]
      exact if_neg hne
  · have htrue : d.neg = true := by cases hd' : d.neg <;> simp_all
    have hn := lexeme_head_neg htrue
    have hbb : b = 0x2D := by
      rw [hn] at hb
      simp only [Option.some.injEq] at hb
      exact hb.symm
    subst hbb
    constructor
    · intro hc
      rw [NumFastStarts.evalICmp_ne_minus, if_pos rfl] at hc
      exact absurd hc (by decide)
    · intro hf; exact absurd hf h

/-- **The tie at the read byte.**  The register `if.end`'s `phi` carries is the
lexeme's sign test, so its `1` is exactly the lexeme's `¬d.neg`. -/
theorem sign_tie_of_read {d : Decimal} {b : UInt8} (hd : d.wellFormed)
    (hb : d.lexeme.toList.head? = some b) {sign : BitVec 1}
    (hs : sign = evalICmp .ne (JsonScanLane.vByte b) 0x2d#8) :
    (sign = 1) ↔ d.neg = false := by
  subst hs
  exact sign_tie hd hb

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.NumFastSign.sign_tie' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sign_tie

/-- info: 'LeanLLVM.Refinement.NumFastSign.body_head_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms body_head_ne

/-- info: 'LeanLLVM.Refinement.NumFastSign.sign_tie_of_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sign_tie_of_read

end NumFastSign

end LeanLLVM.Refinement
