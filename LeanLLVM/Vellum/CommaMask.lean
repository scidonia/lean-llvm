/-
The first certified pure seam: definitions.

`swar` is the exact no-borrow comma mask compiled into the baseline object;
`byteLoop` is the byte loop compiled into the candidate object.  The proofs
that both meet the lane-wise specification, and hence that

  commaContract ⊢ byteLoop ⊑ swar

are in `CommaMaskKernel.lean`, which uses a kernel-checked byte-lane argument
rather than `bv_decide`.
-/
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

/-- The boundary contract for the comma mask.  Every input is admitted; the
postcondition is the lane specification. -/
def commaContract : Contract where
  pre := fun _ => True
  post := fun x y => y = spec x

/-! ### Contextual replacement -/

/-- A caller that adds the results of two seam calls. -/
def twoCallContext : Context where
  args := fun x => [x, x ^^^ 1]
  pre := fun _ => True

theorem twoCallContext_admissible : twoCallContext.admissible commaContract := by
  intro _ _ _ _
  trivial

end LeanLLVM.Vellum
