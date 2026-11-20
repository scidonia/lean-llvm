/-
The fast mask pass's composition, against the specification's masks.

The contracted block unit's loop body computes the entry word from **three** of
the classifier's words rather than four: the unescaped quote, the delimiter
word, the in-string word, and the *neither* word — the lanes that are neither a
structural byte nor a whitespace byte.  The scalar word it does not compute is

  `S = neither & ~quote & ~in_string`,

which is the same complement `specScalar64` is: `neither` is `~(delim | space)`,
so `S` is `~(quote | delim | space | in_string)`.  This module states that
identity (`scalar_eq_neither`) and the composition that consumes it
(`entry_eq_compose`), plus the clamp the peeled final block applies
(`entry_clamp`).  The six per-mask identities, the escape arithmetic and the
in-string word are the mask unit's (`JsonS1MasksSteps`); this module only joins
them at the word level.

The instruction trace over the emitted body — the per-block `denoteCode`
composition, the loop induction and the escape-list calls — is not stated here.
-/
import LeanLLVM.Refinement.JsonS1MasksSteps
import LeanLLVM.Refinement.JsonEntSpec

namespace LeanLLVM.Refinement.JsonS1BlocksSteps

open LeanLLVM
open LeanLLVM.Refinement.JsonScanSpec

/-! ### The reduction to two masks -/

/-- The neither word's lanes are the complement of the delimiter and whitespace
masks: a byte's table entry is zero exactly when it carries neither the
structural bits nor the whitespace bits.  This is the boolean fact the fast
pass turns on, and it is what lets the composition drop the whitespace word. -/
theorem scalar_eq_neither (q d s im : BitVec 64) :
    (~~~ (d ||| s)) &&& ~~~ q &&& ~~~ im = ~~~ (q ||| d ||| s ||| im) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_and, BitVec.getLsbD_and,
    BitLanes.getLsbD_not_of_lt _ hk, BitLanes.getLsbD_not_of_lt _ hk,
    BitLanes.getLsbD_not_of_lt _ hk,
    BitLanes.getLsbD_not_of_lt _ hk,
    BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_or,
    BitVec.getLsbD_or]
  cases hq : q.getLsbD k <;> cases hd : d.getLsbD k <;>
    cases hs : s.getLsbD k <;> cases hi : im.getLsbD k <;> rfl

/-- The scalar word in the fast body's spelling is the specification's: with
`neither = ~(delimiter | whitespace)` substituted, the body's
`neither & ~quote & ~in_string` is `specScalar64`. -/
theorem specScalar64_eq_neither (lo hi : LeanLLVM.JSON.Block32) (st : ClassState) :
    (~~~ (specDelimiter64 lo hi st ||| specSpace64 lo hi st)) &&&
        ~~~ specQuote64 lo hi st &&& ~~~ specInString64 lo hi st
      = specScalar64 lo hi st := by
  rw [scalar_eq_neither, specScalar64]
  congr 1
  ac_rfl

/-- The composition, at the specification's words: the body's
`quote | (delim & ~im) | (S & ~((S << 1) | prevS))` is `entryMask64`.  The
first two terms are `structuralOnly64`, the third is `scalarStarts64` at
`specScalar64`, and `entryMask64` is their join. -/
theorem entry_eq_compose (lo hi : LeanLLVM.JSON.Block32) (st : ClassState) (prevS : Bool) :
    (specQuote64 lo hi st |||
      (specDelimiter64 lo hi st &&& ~~~ specInString64 lo hi st) |||
      (specScalar64 lo hi st &&&
        ~~~ ((specScalar64 lo hi st <<< 1) ||| (if prevS then 1 else 0))))
      = entryMask64 lo hi st prevS := by
  unfold entryMask64 structuralOnly64 scalarStarts64
  rfl

/-- **The peel's clamp.**  The final partial block masks its word with the all-ones
shift the body computes, and that word is `limMask` at the block's remaining
bytes. -/
theorem entry_clamp (w : BitVec 64) (lim : Nat) (h : lim < 2 ^ 64) :
    w &&& clampWord lim = w &&& limMask lim := by
  rw [clampWord_eq_limMask lim h]

theorem entry_clamp_eq (lo hi : LeanLLVM.JSON.Block32) (st : ClassState) (prevS : Bool) (lim : Nat)
    (h : lim < 2 ^ 64) :
    entryMask64 lo hi st prevS &&& clampWord lim =
      entryMask64 lo hi st prevS &&& limMask lim :=
  entry_clamp _ lim h

end LeanLLVM.Refinement.JsonS1BlocksSteps

/-! ### Axiom footprints

The reduction and the composition are boolean and definitional; none of them
reads a choice principle. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksSteps.scalar_eq_neither
#print axioms LeanLLVM.Refinement.JsonS1BlocksSteps.specScalar64_eq_neither
#print axioms LeanLLVM.Refinement.JsonS1BlocksSteps.entry_eq_compose
#print axioms LeanLLVM.Refinement.JsonS1BlocksSteps.entry_clamp
