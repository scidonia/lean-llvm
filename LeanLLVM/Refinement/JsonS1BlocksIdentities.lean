/-
The body's words against the classifier's: the identities that let the loop's
composition be stated in the mask unit's vocabulary.

The body computes the classifier's arithmetic at its own registers, and two of
them differ in spelling rather than in value: the escape chain is the emitted
shortcut (`%and11.i.i = carry & ~backslash` where the mask unit writes
`(carry & ~backslash) & 1`), and the in-string word is taken from the register
carry rather than the carry slot.  Each identity below is a `BitVec` equation
between the body's word and the mask unit's; together they say the two units
compute one word, so the entry word's specification (`entryMask64`) and the
escape list's inputs are the body's own.

The shortcut's identity is the only one that needs a fact about a value rather
than the shape of a term: `%and.i.i` is the conjunction of two one-bit words, so
it is `0` or `1`, and `carry & ~backslash` keeps exactly the lanes
`(carry & ~backslash) & 1` keeps.
-/
import LeanLLVM.Refinement.JsonS1BlocksBody

namespace LeanLLVM.Refinement.JsonS1BlocksSteps

open LeanLLVM
open LeanLLVM.Refinement.QuoteDerive
open LeanLLVM.Refinement.Pclmul (clmul)
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonS1MasksSteps
open LeanLLVM.Refinement.JsonScanSpec

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ### The carry word is a one-bit word -/

/-- The conjunction of two one-bit words is their conjunction as booleans. -/
theorem oneLane_and (a b : Bool) : oneLane 64 a &&& oneLane 64 b = oneLane 64 (a && b) := by
  cases a <;> cases b <;> rfl

/-- `bv` at a one-bit word is that word. -/
theorem bv_oneLane (b : Bool) : bv (oneLane 64 b) = oneLane 64 b := by
  cases b <;> rfl

/-- **The carry conjunction is `open & ppar` in lane zero.**  The mask unit's
`%and.i.i` is `ppar & open`, and both are one-bit words, so the conjunction is
the one-bit word `open & ppar`. -/
theorem escAnd00W_oneLane (k : Ctx) : escAnd00W k = oneLane 64 (k.opened && k.ppar) := by
  rw [escAnd00W, pparW, openW, oneLane_and, bv_oneLane, Bool.and_comm]

/-- A one-bit word is zero or one. -/
theorem oneLane_eq_zero_or_one (b : Bool) : oneLane 64 b = 0 ∨ oneLane 64 b = 1 := by
  cases b <;> simp [oneLane]

/-- `oneW` is the literal one. -/
theorem oneW_self : oneW = (1 : BitVec 64) := rfl

/-! ### The escape chain -/

/-- **The emitted shortcut's boundary term is the mask unit's.**  The body ANDs the
carry conjunction with the complement of the backslash word; the mask unit first
cuts the complement to lane zero and then ANDs the carry.  The two agree because
the carry conjunction is `0` or `1`: masking with it keeps lane zero and nothing
else, whichever side the `& 1` sits on. -/
theorem blkAnd11W_eq_escAnd11W (k : Ctx) : blkAnd11W k = escAnd11W k := by
  rw [blkAnd11W, escAnd11W, escAnd10W, escAnd00W_oneLane, bv_eq, bv_eq, bv_eq,
    oneW_self]
  rcases oneLane_eq_zero_or_one (k.opened && k.ppar) with h | h
  · rw [h]
    simp
  · rw [h, BitVec.and_comm (1 : BitVec 64) (escNotBsW k), BitVec.and_assoc,
      BitVec.and_self]

/-- The escape join is the mask unit's. -/
theorem blkOr62W_eq_escOr62W (k : Ctx) : blkOr62W k = escOr62W k := by
  simp only [blkOr62W, escOr62W, bv_eq, blkAnd11W_eq_escAnd11W]

/-- **The escape word is `s1f_escaped`'s.**  `%or12.i.i` is the emitted shortcut's
word, and the join identity makes it the mask unit's `escapedWord`. -/
theorem blkEscapedW_eq_escapedWord (k : Ctx) : blkEscapedW k = escapedWord k := by
  simp only [blkEscapedW, escapedWord, bv_eq, blkOr62W_eq_escOr62W]

/-- `%not.i`: the escape word's complement, in the mask unit's spelling. -/
theorem blkNotEscW_eq_notEscW (k : Ctx) : blkNotEscW k = notEscW k := by
  simp only [blkNotEscW, notEscW, bv_eq, blkEscapedW_eq_escapedWord]

/-- `%and.i`: the unescaped quote word is the mask unit's. -/
theorem blkAndQuoteW_eq_andQuoteW (k : Ctx) : blkAndQuoteW k = andQuoteW k := by
  simp only [blkAndQuoteW, andQuoteW, bv_eq, blkNotEscW_eq_notEscW]

/-- `%vecinit1.i.i.i`'s lanes are the mask unit's. -/
theorem blkVecInitLanes_eq_vecInitLanes (k : Ctx) :
    blkVecInitLanes k = vecInitLanes k := by
  simp only [blkVecInitLanes, vecInitLanes, blkAndQuoteW_eq_andQuoteW]

/-- `%29`'s lanes are the mask unit's. -/
theorem blkPclmulLanes_eq_pclmulLanes (k : Ctx) :
    blkPclmulLanes k = pclmulLanes k := by
  simp only [blkPclmulLanes, pclmulLanes, blkAndQuoteW_eq_andQuoteW]

/-- `%vecext.i.i.i` is the mask unit's carry-less product. -/
theorem blkVecextW_eq_vecextW (k : Ctx) : blkVecextW k = vecextW k := by
  simp only [blkVecextW, vecextW, blkAndQuoteW_eq_andQuoteW]

/-! ### The in-string word -/

/-- `%xor.i`'s word: the carry-less product against the incoming in-string word. -/
def blkInStringW (k : Ctx) : BitVec 64 := bv (blkVecextW k ^^^ seedW k)

/-- `%shr.i`'s word: the in-string word's sign, the next block's carry. -/
def blkImSignW (k : Ctx) : BitVec 64 := bv (BitVec.sshiftRight (blkInStringW k) 63)

/-- **The in-string word is the mask unit's.**  The body takes the carry from the
register chain instead of the carry slot; the two words differ only in where the
incoming word was read, and `seedW` is that word at this unit's carry. -/
theorem blkInStringW_eq_inStringWord (k : Ctx) : blkInStringW k = inStringWord k := by
  rw [blkInStringW, inStringWord, blkVecextW_eq_vecextW]

/-- The outgoing in-string sign is the mask unit's. -/
theorem blkImSignW_eq_imSignW (k : Ctx) : blkImSignW k = imSignW k := by
  rw [blkImSignW, imSignW, blkInStringW_eq_inStringWord]

/-! ### The entry chain's words -/

/-- The low half's complement cell: `%not.i46.i`. -/
def not46W (k : Ctx) : BitVec 32 :=
  BitVec.ofNat 32 (complW (BitVec.ofNat 32 (lanesToNat (cmpWordLanes k)))).toNat

/-- The high half's complement cell: `%not.i49.i`. -/
def not49W (k : Ctx) : BitVec 32 :=
  BitVec.ofNat 32 (complW (BitVec.ofNat 32 (lanesToNat (cmpWordLanesHi k)))).toNat

theorem not46W_eq (k : Ctx) : not46W k = delimLoW k := by
  rw [not46W, delimLoW, ofNat32_toNat']

theorem not49W_eq (k : Ctx) : not49W k = delimHiW k := by
  rw [not49W, delimHiW, ofNat32_toNat']

/-- **`%or19.i` is the delimiter word.**  The register chain zero-extends each
half's complement and joins them; read at those cells, the join is `or5W`, the
word the entry composition and the escape chain both name. -/
theorem or19W_eq_or5W (k : Ctx) :
    bv (bv (bv (shlUpW (zext64W (not49W k)))) ||| bv (zext64W (not46W k))) = or5W k := by
  rw [or5W, not46W_eq, not49W_eq]
  simp only [bv32, ofNat32_toNat']

end LeanLLVM.Refinement.JsonS1BlocksSteps
