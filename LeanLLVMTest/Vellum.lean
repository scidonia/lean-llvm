import LeanLLVM

open LeanLLVM.Vellum

-- The local obligation: the candidate refines the baseline.
example : commaContract ⊢ byteLoop ⊑ swar := byteLoop_refines_swar

-- Correctness transfers along refinement.
example : Correct commaContract byteLoop := byteLoop_correct

-- Contextual replacement preserves a two-call caller.
example (x : BitVec 64) :
    twoCallContext.run byteLoop x = twoCallContext.run swar x :=
  twoCallContext_preserved x

-- The same statement at the C ABI type.
example (x : UInt64) : seamCandidate x = seamBaseline x := seam_refines x

-- Concrete values, including the borrow counterexample lane.
#guard spec 0x2D2C = 0x80
#guard byteLoop 0x2D2C = 0x80
#guard swar 0x2D2C = 0x80
#guard swar 0x2C2C2C2C2C2C2C2C = 0x8080808080808080

-- The two 64-bit identities are proved by `bv_decide`, whose SAT step emits a
-- native bit-blast axiom per theorem.  The pins name that trust boundary; it
-- is not a kernel reduction.  Replacing it with a kernel-checked certificate
-- is tracked as follow-up work.

/--
info: 'LeanLLVM.Vellum.byteLoop_refines_swar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 byteLoop_eq_spec._native.bv_decide.ax_1_5,
 swar_eq_spec._native.bv_decide.ax_1_5]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.byteLoop_refines_swar

/--
info: 'LeanLLVM.Vellum.twoCallContext_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 byteLoop_eq_spec._native.bv_decide.ax_1_5,
 swar_eq_spec._native.bv_decide.ax_1_5]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.twoCallContext_preserved

-- The probe's `Baseline.lean` body is definitionally the proved function.
def probeBaselineBody (x : UInt64) : UInt64 :=
  let m := x ^^^ 0x2C2C2C2C2C2C2C2C
  ~~~(((m &&& 0x7F7F7F7F7F7F7F7F) + 0x7F7F7F7F7F7F7F7F) ||| m) &&& 0x8080808080808080

example : probeBaselineBody = seamBaseline := by
  funext x
  rfl
