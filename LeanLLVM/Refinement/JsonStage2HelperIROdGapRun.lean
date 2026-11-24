/-
`od_gap_recover` at its call boundary: the entry chain, and the arithmetic lemmas
its run proof reads.

`JsonStage2HelperIROdGapSteps` pins the body's blocks and proves the instruction
and terminator steps at its widths.  This module begins the run those steps
compose, and it states no contract: it proves the `denoteCode` of the entry block,
of `cond.true` and `cond.false`, of `cond.end` from each of them, and of
`while.end` entered from `cond.end` — the path the body takes when the token's
position is already `ip`.  The control steps those blocks compose into, the
`runFuel` completion, `cleanup82`, the two loops, and the model's
`stage2GapRecoverRule` are not in this module, so the body's relation to the model
is still the seam `docs/contract.md` records.
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

/-- An index word's `Nat` reading, at the `i32` the `load` produces. -/
theorem gap_word32' {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k).toNat = k := by
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


/-! ### `cond.true`, `cond.false`, and the `ip` they compute -/

/-- `cond.true`: the index word at `ix + 4k`, zero-extended to `i64`. -/
theorem gap_condTrue_denote {calls : Calls} {env : Env} {s : State}
    {c k ix idx : Nat}
    (hc : lookupName env "%c" = some (.ptr c))
    (h1 : lookupName env "%1" = some (.int 64 (BitVec.ofNat 64 k)))
    (hix : readBytes s.mem (c + 16) 8 = some (natToBytes ix 8)) (hix64 : ix < 2 ^ 64)
    (hk64 : k < 2 ^ 64) (hk63 : k < 2 ^ 63)
    (hidx : readBytes s.mem (ix + k * 4) 4 = some (natToBytes idx 4))
    (hidx32 : idx < 2 ^ 32) :
    denoteCode calls odGapRecoverCondTrueInstrs (stateAt env s) =
      some (stateAt
        (("%conv", .int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 idx).toNat)) ::
          ("%4", .int 32 (BitVec.ofNat 32 idx)) ::
          ("%arrayidx", .ptr (ix + k * 4)) ::
          ("%3", .ptr ix) :: ("%ix", .ptr (c + 16)) :: env) s) := by
  rw [odGapRecoverCondTrueInstrs]
  refine Eq.trans (gap_denote_gep8_imm calls env s "%ix" "%c"
    (0x0000000000000010#64) hc (by decide) _) ?_
  rw [gap_se16]
  refine Eq.trans (gap_denote_loadPtr calls (("%ix", .ptr (c + 16)) :: env) s
    "%3" "%ix" (by block_lk) hix hix64 _) ?_
  refine Eq.trans (gap_denote_gep32 calls
    (("%3", .ptr ix) :: ("%ix", .ptr (c + 16)) :: env) s
    "%arrayidx" "%3" "%1" (by block_lk) h1
    (by rw [gap_signExtend_ofNat k hk64]; omega) _) ?_
  rw [gap_signExtend_ofNat k hk64]
  refine Eq.trans (gap_denote_load32 calls
    (("%arrayidx", .ptr (ix + k * 4)) :: ("%3", .ptr ix) ::
      ("%ix", .ptr (c + 16)) :: env) s
    "%4" "%arrayidx" (by block_lk) (by rw [gap_word32' hidx32]; exact hidx) _) ?_
  refine Eq.trans (denoteCode_zext calls
    (("%4", .int 32 (BitVec.ofNat 32 idx)) :: ("%arrayidx", .ptr (ix + k * 4)) ::
      ("%3", .ptr ix) :: ("%ix", .ptr (c + 16)) :: env) s
    "%conv" "%4" 32 64 (by block_lk) []) ?_
  rfl

/-- `cond.false`: the document's length word. -/
theorem gap_condFalse_denote {calls : Calls} {env : Env} {s : State}
    {c n : Nat}
    (hc : lookupName env "%c" = some (.ptr c))
    (hn : readBytes s.mem (c + 8) 8 = some (natToBytes n 8)) (hn64 : n < 2 ^ 64) :
    denoteCode calls odGapRecoverCondFalseInstrs (stateAt env s) =
      some (stateAt (("%5", .int 64 (BitVec.ofNat 64 n)) ::
          ("%n", .ptr (c + 8)) :: env) s) := by
  rw [odGapRecoverCondFalseInstrs]
  refine Eq.trans (gap_denote_gep8_imm calls env s "%n" "%c"
    (0x0000000000000008#64) hc (by decide) _) ?_
  rw [gap_se8]
  refine Eq.trans (denoteCode_load64 calls (("%n", .ptr (c + 8)) :: env) s
    "%5" "%n" (by block_lk) (by rw [gap_word64 hn64]; exact hn) _) ?_
  rfl

/-- `cond.end` entered from `cond.true`: the `phi` selects the index word, and the
position test is `p0 < ip`. -/
theorem gap_condEnd_fromTrue_denote {calls : Calls} {env : Env} {s : State}
    {p0 idx : Nat}
    (hpre : s.pre = some "cond.true")
    (ht : lookupName env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 p0)))
    (hconv : lookupName env "%conv" = some (.int 64 (BitVec.ofNat 64 idx)))
    (hidx : idx < 2 ^ 64) :
    denoteCode calls odGapRecoverCondEndInstrs (stateAt env s) =
      some (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 p0)
            (BitVec.ofNat 64 idx))) ::
          ("%cond", .int 64 (BitVec.ofNat 64 idx)) :: env) s) := by
  rw [odGapRecoverCondEndInstrs]
  have hinc : phiIncoming "cond.true"
      [("cond.true", Operand.reg "%conv"), ("cond.false", Operand.reg "%5")] =
        some (Operand.reg "%conv") := by decide
  have hop : evalOperand (stateAt env s) (Operand.reg "%conv") =
      some (.int 64 (BitVec.ofNat 64 idx)) := by
    simp only [evalOperand, stateAt]
    rw [hconv]
  refine Eq.trans (denoteCode_phi calls env s "%cond" (Ty.int 64)
    [("cond.true", Operand.reg "%conv"), ("cond.false", Operand.reg "%5")]
    (p := "cond.true") (op := Operand.reg "%conv") (v := .int 64 (BitVec.ofNat 64 idx))
    hpre hinc hop [    Instr.icmp "%cmp310" (IPred.ult) 64 (Operand.reg "%t.0.val") (Operand.reg "%cond")] (by decide)) ?_
  refine Eq.trans (gap_denote_icmp_ult_reg calls
    (("%cond", .int 64 (BitVec.ofNat 64 idx)) :: env) s
    "%cmp310" "%t.0.val" "%cond" (by block_lk) (by block_lk) _) ?_
  rfl

/-- `cond.end` entered from `cond.false`: the `phi` selects the length word. -/
theorem gap_condEnd_fromFalse_denote {calls : Calls} {env : Env} {s : State}
    {p0 n : Nat}
    (hpre : s.pre = some "cond.false")
    (ht : lookupName env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 p0)))
    (h5 : lookupName env "%5" = some (.int 64 (BitVec.ofNat 64 n)))
    (hn : n < 2 ^ 64) :
    denoteCode calls odGapRecoverCondEndInstrs (stateAt env s) =
      some (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 p0)
            (BitVec.ofNat 64 n))) ::
          ("%cond", .int 64 (BitVec.ofNat 64 n)) :: env) s) := by
  rw [odGapRecoverCondEndInstrs]
  have hinc : phiIncoming "cond.false"
      [("cond.true", Operand.reg "%conv"), ("cond.false", Operand.reg "%5")] =
        some (Operand.reg "%5") := by decide
  have hop : evalOperand (stateAt env s) (Operand.reg "%5") =
      some (.int 64 (BitVec.ofNat 64 n)) := by
    simp only [evalOperand, stateAt]
    rw [h5]
  refine Eq.trans (denoteCode_phi calls env s "%cond" (Ty.int 64)
    [("cond.true", Operand.reg "%conv"), ("cond.false", Operand.reg "%5")]
    (p := "cond.false") (op := Operand.reg "%5") (v := .int 64 (BitVec.ofNat 64 n))
    hpre hinc hop [    Instr.icmp "%cmp310" (IPred.ult) 64 (Operand.reg "%t.0.val") (Operand.reg "%cond")] (by decide)) ?_
  refine Eq.trans (gap_denote_icmp_ult_reg calls
    (("%cond", .int 64 (BitVec.ofNat 64 n)) :: env) s
    "%cmp310" "%t.0.val" "%cond" (by block_lk) (by block_lk) _) ?_
  rfl

/-- `while.end` entered from `cond.end`: the token itself is the scan's end, so the
`phi` carries `%t.0.val`, and the equality test is `ip = ip`. -/
theorem gap_whileEnd_fromCondEnd_denote {calls : Calls} {env : Env} {s : State}
    {ip : Nat}
    (hpre : s.pre = some "cond.end")
    (ht : lookupName env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hcond : lookupName env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hip64 : ip < 2 ^ 64) :
    denoteCode calls odGapRecoverWhileEndInstrs (stateAt env s) =
      some (stateAt (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 ip)
            (BitVec.ofNat 64 ip))) ::
          ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 ip)) :: env) s) := by
  rw [odGapRecoverWhileEndInstrs]
  have hinc : phiIncoming "cond.end"
      [("cond.end", Operand.reg "%t.0.val"), ("LeafBlock", Operand.reg "%ee.011"),
       ("LeafBlock1", Operand.reg "%ee.011"), ("LeafBlock3", Operand.reg "%ee.011")] =
        some (Operand.reg "%t.0.val") := by decide
  have hop : evalOperand (stateAt env s) (Operand.reg "%t.0.val") =
      some (.int 64 (BitVec.ofNat 64 ip)) := by
    simp only [evalOperand, stateAt]
    rw [ht]
  refine Eq.trans (denoteCode_phi calls env s "%ee.0.lcssa" (Ty.int 64)
    [("cond.end", Operand.reg "%t.0.val"), ("LeafBlock", Operand.reg "%ee.011"),
     ("LeafBlock1", Operand.reg "%ee.011"), ("LeafBlock3", Operand.reg "%ee.011")]
    (p := "cond.end") (op := Operand.reg "%t.0.val")
    (v := .int 64 (BitVec.ofNat 64 ip)) hpre hinc hop
    [Instr.icmp "%cmp6" (IPred.eq) 64 (Operand.reg "%ee.0.lcssa") (Operand.reg "%cond")]
    (by decide)) ?_
  refine Eq.trans (gap_denote_icmp_eq_reg calls
    (("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 ip)) :: env) s
    "%cmp6" "%ee.0.lcssa" "%cond" (by block_lk) (by block_lk) _) ?_
  rfl

/-! ### Axiom footprints -/

#print axioms gap_entry_denote
#print axioms gap_condTrue_denote
#print axioms gap_condFalse_denote
#print axioms gap_condEnd_fromTrue_denote
#print axioms gap_condEnd_fromFalse_denote
#print axioms gap_whileEnd_fromCondEnd_denote

end LeanLLVM.Refinement
