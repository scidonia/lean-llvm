/-
`num_fast_el1`'s counters at the merge block `if.end230`.

The conversion's two counters are read at `if.end230`: `%sub231` is `exp10 -
fdig` and `%add232` is `fdig + idig`, which are the model's `numEff` and
`digitCount` (`LeanLLVM.Refinement.numEff`, `LeanLLVM.StrtodRefine.digitCount`;
`numEff` is `eff` off the accumulator's saturation gates,
`JsonStage2Body.numEff_eq_eff_of_specRange`).  The digit
runs that fill `idig`, `fdig` and `exp10` are `land.lhs.true41` (the integer
run), `land.lhs.true119` (the fraction run) and `land.lhs.true195` (the
exponent run); each is a `BoundLoop` of the shape `JsonStage2NumFastScan` fixed
for the integer run.

**What is proved here.**  The merge block's arithmetic, at the body's own
instruction list — `%sub231` is the register difference and `%add232` the sum —
and the two counters at the model: with the carried registers the counts and the
accumulator (`exp10 = expVal d`, `fdig` the fraction's digit count, `idig` the
integer part's), the pair is `(@numEff d, @digitCount d)`, the values the
contract's gates read.

**What is not.**  That the three runs' registers carry those counts is the
`BoundLoop` arms.  For the integer run they are parameters of
`JsonStage2NumFastScan.numFastScanBoundLoop`; the fraction run at
`land.lhs.true119` and the exponent run at `land.lhs.true195` have the same
shape, and their arms are open for a reason that is partly mechanical: the two
runs' blocks are pinned (`numFastBody.findBlock` resolves them, and the whole
body literal carries their text), but `JsonStage2HelperIRNumFast` exposes named
instruction lists only for the fourteen blocks the straight-line proofs read,
and neither run's four blocks is among them.  An arm is a `runFuel` prefix over
four blocks, so stating it needs those blocks' instruction lists as literals —
either a regeneration of `capture-stage2-helpers.sh --emit-pins` output for the
six blocks, or a hand transcription, which is what the pinning module exists to
avoid.  The counters are therefore proved *at the merge*, not at the three runs.
-/
import LeanLLVM.Refinement.JsonStage2NumFastCalls
import LeanLLVM.Refinement.JsonStage2Body

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.JSON
open LeanLLVM.StrtodRefine

/-- The merge block's two arithmetic instructions, as the body's own text has
them: `%sub231 = %exp10.4731 - %fdig.4719727` and
`%add232 = %fdig.4719727 + %idig.4709716730`. -/
def numFastIfEnd230Arith : List Instr :=
  [Instr.binop "%sub231" (BinOp.sub) 64
     (Operand.reg "%exp10.4731") (Operand.reg "%fdig.4719727"),
   Instr.binop "%add232" (BinOp.add) 64
     (Operand.reg "%fdig.4719727") (Operand.reg "%idig.4709716730")]

/-- The merge block's arithmetic, at the carried counters: the difference and
the sum, in the registers the model's `eff` and `nd` are read from. -/
theorem numFast_ifEnd230_arith (calls : Calls) (env : Env) (s : State)
    {exp10 fdig idig : BitVec 64}
    (he : lookupName env "%exp10.4731" = some (.int 64 exp10))
    (hf : lookupName env "%fdig.4719727" = some (.int 64 fdig))
    (hi : lookupName env "%idig.4709716730" = some (.int 64 idig)) :
    denoteCode calls numFastIfEnd230Arith (stateAt env s) =
      some (stateAt
        (("%add232", .int 64 (fdig + idig)) ::
         ("%sub231", .int 64 (exp10 - fdig)) :: env) s) := by
  unfold numFastIfEnd230Arith
  rw [denoteCode_sub_reg _ _ _ _ _ _ he hf,
    denoteCode_add_reg _ _ _ _ _ _
      (lookupName_cons_tail (k := "%sub231") (v := .int 64 (exp10 - fdig)) (by decide) hf)
      (lookupName_cons_tail (k := "%sub231") (v := .int 64 (exp10 - fdig)) (by decide) hi),
    denoteCode_nil]

/-- **The counters at the model.**  When the carried registers are the lexeme's
counts — `idig` its integer digits, `fdig` its fraction's, `exp10` its exponent's
value at the emitted accumulator — the merge block's two words are
`(@digitCount d, @numEff d)`: the add's unsigned reading is the digit count and
the subtract's signed pattern is `eff`. -/
theorem numFast_ifEnd230_counts {d : Decimal} {exp10 fdig idig : BitVec 64}
    (hE : exp10 = BitVec.ofInt 64 (expVal d))
    (hF : fdig = BitVec.ofNat 64 (fracDigits d))
    (hI : idig = BitVec.ofNat 64 (intDigits d)) :
    fdig + idig = BitVec.ofNat 64 (digitCount d) ∧
      exp10 - fdig = BitVec.ofInt 64 (numEff d) := by
  subst hE
  subst hF
  subst hI
  constructor
  · rw [digitCount]
    bv_omega
  · rw [numEff]
    bv_omega

/-- The digits' sum, as the count the gates read: `idig + fdig` is `nd`.  This is
the `Nat` reading of the add, at the same hypotheses. -/
theorem numFast_ifEnd230_add_nat {d : Decimal} {idig fdig : BitVec 64}
    (hI : idig = BitVec.ofNat 64 (intDigits d)) (hF : fdig = BitVec.ofNat 64 (fracDigits d))
    (hbound : intDigits d + fracDigits d < 2 ^ 64) :
    (fdig + idig).toNat = digitCount d := by
  subst hI
  subst hF
  rw [digitCount, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  omega

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.numFast_ifEnd230_arith' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_ifEnd230_arith

/-- info: 'LeanLLVM.Refinement.numFast_ifEnd230_counts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_ifEnd230_counts

/-- info: 'LeanLLVM.Refinement.numFast_ifEnd230_add_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_ifEnd230_add_nat

end LeanLLVM.Refinement
