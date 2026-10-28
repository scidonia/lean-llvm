/-
The first certified pure seam.

`swar` is the exact no-borrow comma mask compiled into the baseline object;
`byteLoop` is the byte loop compiled into the candidate object.  Both are
proved equal to the lane-wise specification `spec`, so

  commaContract ⊢ byteLoop ⊑ swar

holds, and `Correct` transfers from the baseline to the candidate.
-/
import Std.Tactic.BVDecide
import LeanLLVM.Vellum.Refinement

namespace LeanLLVM.Vellum

/-- The lane-wise specification: bit `8*i + 7` is set iff byte `i` of the
comma-XOR word is zero. -/
def spec (x : BitVec 64) : BitVec 64 :=
  let m := x ^^^ 0x2C2C2C2C2C2C2C2C
  (if ((m >>> 0) &&& 0xFF) = 0 then 0x0000000000000080 else 0) |||
  (if ((m >>> 8) &&& 0xFF) = 0 then 0x0000000000008000 else 0) |||
  (if ((m >>> 16) &&& 0xFF) = 0 then 0x0000000000800000 else 0) |||
  (if ((m >>> 24) &&& 0xFF) = 0 then 0x0000000080000000 else 0) |||
  (if ((m >>> 32) &&& 0xFF) = 0 then 0x0000008000000000 else 0) |||
  (if ((m >>> 40) &&& 0xFF) = 0 then 0x0000800000000000 else 0) |||
  (if ((m >>> 48) &&& 0xFF) = 0 then 0x0080000000000000 else 0) |||
  (if ((m >>> 56) &&& 0xFF) = 0 then 0x8000000000000000 else 0)

/-- The baseline body: the exact no-borrow packed mask. -/
def swar (x : BitVec 64) : BitVec 64 :=
  let m := x ^^^ 0x2C2C2C2C2C2C2C2C
  ~~~(((m &&& 0x7F7F7F7F7F7F7F7F) + 0x7F7F7F7F7F7F7F7F) ||| m) &&& 0x8080808080808080

/-- The candidate body: a fold over the eight lanes. -/
def byteLoop (x : BitVec 64) : BitVec 64 :=
  let m := x ^^^ 0x2C2C2C2C2C2C2C2C
  ([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).foldl
    (fun acc i =>
      let shift := 8 * i
      let b := (m >>> shift) &&& 0xFF
      if b = 0 then acc ||| (0x80 <<< shift) else acc)
    0

/-- The packed formula meets the lane specification. -/
theorem swar_eq_spec (x : BitVec 64) : swar x = spec x := by
  unfold swar spec
  bv_decide

/-- The byte loop meets the same specification. -/
theorem byteLoop_eq_spec (x : BitVec 64) : byteLoop x = spec x := by
  unfold byteLoop spec
  simp only [List.foldl_cons, List.foldl_nil]
  bv_decide

/-- The boundary contract for the comma mask.  Every input is admitted; the
postcondition is the lane specification. -/
def commaContract : Contract where
  pre := fun _ => True
  post := fun x y => y = spec x

/-- The certified local obligation: the candidate refines the baseline. -/
theorem byteLoop_refines_swar : commaContract ⊢ byteLoop ⊑ swar := by
  intro x _
  rw [byteLoop_eq_spec, swar_eq_spec]

/-- The baseline meets the contract. -/
theorem swar_correct : Correct commaContract swar := by
  intro x _
  exact swar_eq_spec x

/-- Correctness transfers to the candidate by refinement. -/
theorem byteLoop_correct : Correct commaContract byteLoop :=
  Correct.of_refines byteLoop_refines_swar swar_correct

/-! ### Contextual replacement -/

/-- A caller that adds the results of two seam calls. -/
def twoCallContext : Context where
  args := fun x => [x, x ^^^ 1]
  pre := fun _ => True

theorem twoCallContext_admissible : twoCallContext.admissible commaContract := by
  intro _ _ _ _
  trivial

/-- Replacing the baseline by the candidate preserves the caller's result. -/
theorem twoCallContext_preserved (x : BitVec 64) :
    twoCallContext.run byteLoop x = twoCallContext.run swar x :=
  Context.refines byteLoop_refines_swar twoCallContext_admissible x trivial

/-! ### The `UInt64` seam

The probe's exported functions are `UInt64`; this is the same statement at the
type the C ABI uses.  The object-level connection remains the differential
certificate in `probes/install/`. -/

def seamBaseline (x : UInt64) : UInt64 :=
  UInt64.ofBitVec (swar x.toBitVec)

def seamCandidate (x : UInt64) : UInt64 :=
  UInt64.ofBitVec (byteLoop x.toBitVec)

theorem seam_refines (x : UInt64) : seamCandidate x = seamBaseline x := by
  unfold seamCandidate seamBaseline
  rw [byteLoop_eq_spec, swar_eq_spec]

end LeanLLVM.Vellum
