/-
`od_gap_recover` at its call boundary: the entry chain, and the arithmetic lemmas
its run proof reads.

`JsonStage2HelperIROdGapSteps` pins the body's blocks and proves the instruction
and terminator steps at its widths.  This module begins the run those steps
compose, and it states no contract: `gap_entry_denote` is the entry block's eight
instructions at the staged cursor, leaving the environment the `cond.true` and
`cond.false` branches read.  Nothing here reaches `cond.end`, `while.end`,
`cleanup82`, either loop, or `stage2GapRecoverRule`, so the body's relation to the
model is still the seam `docs/contract.md` records.
-/
import LeanLLVM.Refinement.JsonStage2HelperIROdGapSteps

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval

/-- `(8#64).signExtend 64).toNat` is eight: the entry's `%n` field. -/
theorem gap_se8 : ((0x0000000000000008#64).signExtend 64).toNat = 8 := by decide
/-- `(16#64).signExtend 64).toNat` is sixteen: the cursor's `ix` field. -/
theorem gap_se16 : ((0x0000000000000010#64).signExtend 64).toNat = 16 := by decide
/-- `(24#64).signExtend 64).toNat` is twenty-four: the cursor's `nix` field. -/
theorem gap_se24 : ((0x0000000000000018#64).signExtend 64).toNat = 24 := by decide
/-- `(32#64).signExtend 64).toNat` is thirty-two: the cursor's `k` field. -/
theorem gap_se32 : ((0x0000000000000020#64).signExtend 64).toNat = 32 := by decide

/-- An index word's `Nat` reading, at the `i64` the `zext` produces. -/
theorem gap_word64 {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `signExtend` at full width is the identity on the `Nat` reading. -/
theorem gap_signExtend_ofNat (c : Nat) (hc : c < 2 ^ 64) :
    ((BitVec.ofNat 64 c).signExtend 64).toNat = c := by
  rw [BitVec.toNat_signExtend]
  have hset : (BitVec.setWidth 64 (BitVec.ofNat 64 c)).toNat = c := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
      Nat.mod_eq_of_lt hc]
  rw [hset]
  split <;> omega

/-- An unsigned comparison with itself is false. -/
theorem gap_ult_self (x : BitVec 64) : evalICmp .ult x x = 0#1 := by
  unfold evalICmp
  have hf : BitVec.ult x x = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact Nat.lt_irrefl _ ((BitVec.ult_iff_toNat_lt).1 h)
  rw [hf]
  rfl

/-- An equality comparison with itself is true. -/
theorem gap_eq_self (x : BitVec 64) : evalICmp .eq x x = 1#1 := by
  simp [evalICmp]

/-! ### The entry block -/

/-- The four argument cells the entry leaves, plus the two allocated slots. -/
def gapEntryEnv (env : Env) (next c b k nix : Nat) : Env :=
  ("%cmp", .int 1 (evalICmp .ult (BitVec.ofNat 64 k) (BitVec.ofNat 64 nix))) ::
  ("%2", .int 64 (BitVec.ofNat 64 nix)) ::
  ("%nix", .ptr (c + 24)) ::
  ("%1", .int 64 (BitVec.ofNat 64 k)) ::
  ("%k", .ptr (c + 32)) ::
  ("%0", .ptr b) ::
  ("%ei", .ptr (next + (Ty.double).sizeBytes)) ::
  ("%d", .ptr next) :: env

/-- The entry block's eight instructions, from the staged cursor. -/
theorem gap_entry_denote {calls : Calls} {env : Env} {s : State} {c b k nix : Nat}
    (hc : lookupName env "%c" = some (.ptr c))
    (hb : readBytes s.mem c 8 = some (natToBytes b 8)) (hb64 : b < 2 ^ 64)
    (hk : readBytes s.mem (c + 32) 8 = some (natToBytes k 8)) (hk64 : k < 2 ^ 64)
    (hnix : readBytes s.mem (c + 24) 8 = some (natToBytes nix 8)) (hnix64 : nix < 2 ^ 64) :
    denoteCode calls odGapRecoverEntryInstrs (stateAt env s) =
      some (stateAt (gapEntryEnv env s.next c b k nix)
        { s with next := s.next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes }) := by
  rw [odGapRecoverEntryInstrs]
  refine Eq.trans (gap_denote_alloca calls env s "%d" Ty.double 0 _) ?_
  refine Eq.trans (gap_denote_alloca calls (("%d", .ptr s.next) :: env)
    { s with next := s.next + (Ty.double).sizeBytes } "%ei" (Ty.int 64) 0 _) ?_
  refine Eq.trans (gap_denote_loadPtr calls
    (("%ei", .ptr (s.next + (Ty.double).sizeBytes)) :: ("%d", .ptr s.next) :: env)
    { s with next := s.next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes }
    "%0" "%c" (by block_lk) hb hb64 _) ?_
  refine Eq.trans (gap_denote_gep8_imm calls
    (("%0", .ptr b) :: ("%ei", .ptr (s.next + (Ty.double).sizeBytes)) ::
      ("%d", .ptr s.next) :: env)
    { s with next := s.next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes }
    "%k" "%c" (0x0000000000000020#64) (by block_lk) (by decide) _) ?_
  rw [gap_se32]
  refine Eq.trans (denoteCode_load64 calls
    (("%k", .ptr (c + 32)) :: ("%0", .ptr b) ::
      ("%ei", .ptr (s.next + (Ty.double).sizeBytes)) :: ("%d", .ptr s.next) :: env)
    { s with next := s.next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes }
    "%1" "%k" (by block_lk) (by rw [gap_word64 hk64]; exact hk) _) ?_
  refine Eq.trans (gap_denote_gep8_imm calls
    (("%1", .int 64 (BitVec.ofNat 64 k)) :: ("%k", .ptr (c + 32)) :: ("%0", .ptr b) ::
      ("%ei", .ptr (s.next + (Ty.double).sizeBytes)) :: ("%d", .ptr s.next) :: env)
    { s with next := s.next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes }
    "%nix" "%c" (0x0000000000000018#64) (by block_lk) (by decide) _) ?_
  rw [gap_se24]
  refine Eq.trans (denoteCode_load64 calls
    (("%nix", .ptr (c + 24)) :: ("%1", .int 64 (BitVec.ofNat 64 k)) ::
      ("%k", .ptr (c + 32)) :: ("%0", .ptr b) ::
      ("%ei", .ptr (s.next + (Ty.double).sizeBytes)) :: ("%d", .ptr s.next) :: env)
    { s with next := s.next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes }
    "%2" "%nix" (by block_lk) (by rw [gap_word64 hnix64]; exact hnix) _) ?_
  refine Eq.trans (gap_denote_icmp_ult_reg calls
    (("%2", .int 64 (BitVec.ofNat 64 nix)) :: ("%nix", .ptr (c + 24)) ::
      ("%1", .int 64 (BitVec.ofNat 64 k)) :: ("%k", .ptr (c + 32)) :: ("%0", .ptr b) ::
      ("%ei", .ptr (s.next + (Ty.double).sizeBytes)) :: ("%d", .ptr s.next) :: env)
    { s with next := s.next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes }
    "%cmp" "%1" "%2" (by block_lk) (by block_lk) _) ?_
  rfl


/-! ### The entry run's axiom footprint -/

#print axioms gap_entry_denote

end LeanLLVM.Refinement
