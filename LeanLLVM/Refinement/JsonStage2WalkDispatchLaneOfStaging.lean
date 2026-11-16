/-
# The entry lane's arithmetic, shared by the producers

Two facts the advanced arms' producers read off the input rather than off the invariant,
stated once because more than one arm builds the same terms:

* `contLane_gt` — the next entry's lane word is above this entry's index.  The bundle
  fields spell it as `evalICmp .ugt (%cond350.i) (%idxprom.i) = 1`; `%idxprom.i` is
  `entryPos G C.k` (`WalkInv.idx_reg`), so the inequality is between two document
  positions and it is what puts the byte before the entry's end at an index above zero.
* `slt_one_of_toInt_le` — the `= 1` twin of `hlast_slt_zero_of_toInt_le`: a byte below
  `58` in the signed order is below `91`, which is how the plain-value class's `h91`
  follows from its `h58`.
-/
import LeanLLVM.Refinement.JsonStage2WalkHcontFactsOfStaging

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- **The lane's word is above the entry's index, as a document inequality.**  `%idxprom.i`
is `entryPos G C.k` and the two words are sixty-four bits wide, so the test's `1` is the
`Nat` order of the two positions. -/
theorem contLane_gt {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {v : BitVec 32}
    (hk : C.k + 1 < G.nep)
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat)
      (BitVec.ofNat 64 (entryPos G C.k)) = 1) :
    entryPos G C.k < v.toNat := by
  have hk1 : C.k < G.nep := by omega
  have he := entryPos_lt G hk1
  have h2 := G.maxDoc
  simp only [stage2MaxDocument] at h2
  have he64 : entryPos G C.k < 2 ^ 64 := by omega
  have hv64 : v.toNat < 2 ^ 64 := by have := v.isLt; omega
  have h := (evalICmp_ugt_one_iff_toNat (BitVec.ofNat 64 v.toNat)
    (BitVec.ofNat 64 (entryPos G C.k))).1 hugt
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64,
    Nat.mod_eq_of_lt hv64] at h

/-- **A signed comparison set at a smaller literal is set at every larger one.**  The bit
is `x.slt a`, so `a.toInt ≤ b.toInt` carries it to `b`. -/
theorem slt_one_of_toInt_le {w : Nat} {x a b : BitVec w}
    (hab : a.toInt ≤ b.toInt) (h : evalICmp .slt x a = 1) : evalICmp .slt x b = 1 := by
  have hlt : x.toInt < a.toInt := by
    by_contra hc
    have h0 : evalICmp .slt x a = 0 := by simp [evalICmp, BitVec.slt_eq_decide, hc]
    rw [h] at h0
    exact absurd h0 (by decide)
  have hltb : x.toInt < b.toInt := lt_of_lt_of_le hlt hab
  simp [evalICmp, BitVec.slt_eq_decide, hltb]

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.contLane_gt
#print axioms LeanLLVM.Refinement.WalkScope.slt_one_of_toInt_le

end WalkScope
end LeanLLVM.Refinement
