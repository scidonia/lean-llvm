/-
`od_gap_recover` at its call boundary: the entry chain, the token-at-`ip` case,
the first scan's routing and head, and the arithmetic lemmas its run reads.

`JsonStage2HelperIROdGapSteps` pins the body's blocks and proves the instruction
and terminator steps at its widths.  This module begins the run those steps
compose, and it states no contract: it proves the `denoteCode` and the control
`step` of the entry block, of `cond.true` and `cond.false`, of `cond.end` from
each of them, of `while.end` entered from `cond.end`, and of `cleanup82` — the
path the body takes when the token's position is already `ip` — together with the
rule's no-write value at that position and the two word readings the model's
fields use.  The `p = ip` case of the `runFuel` completion is proved (`gap_run_atIp`, with
`gap_rule_atIp`'s `.unchanged` value), and it states the model's post at that one
staging — not a contract over the whole function.  The first scan's vocabulary is
here as far as its head: the routing the switch takes at every byte
(`gapRoute`), and `land.rhs`'s two steps, entered from `cond.end` and from
`while.body`.  The scan's remaining blocks, its `BoundLoop` instance and its run,
the four refusal arms and the other no-write case (the scan advancing to `ip`) are
not in this module, so the body's relation to the model is still the seam
`docs/contract.md` records.
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

/-- An unsigned comparison is true exactly when the left word is smaller. -/
theorem gap_ult_one {k nix : Nat} (hk : k < 2 ^ 64) (hn : nix < 2 ^ 64) (h : k < nix) :
    evalICmp .ult (BitVec.ofNat 64 k) (BitVec.ofNat 64 nix) = 1#1 := by
  unfold evalICmp
  have ht : BitVec.ult (BitVec.ofNat 64 k) (BitVec.ofNat 64 nix) = true := by
    rw [BitVec.ult_iff_toNat_lt, gap_word64 hk, gap_word64 hn]
    exact h
  rw [ht]
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
        (("%conv", .int 64 (BitVec.ofNat 64 idx)) ::
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
  rw [gap_word32' hidx32]
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



/-! ### The first scan's routing

The emitted switch tests one byte with three comparisons; the block it selects
decides whether the scan stops (`while.end`) or advances (`while.body`).  The
facts are enumerated over the 256 bytes the load can produce: `gapRouteProp`
states, per byte, which of the three leaves the switch selects and whether that
leaf stops the scan. -/

/-- The eight-bit word a loaded byte produces. -/
def gapByte (byte : UInt8) : BitVec 8 := BitVec.ofNat 8 byte.toNat

/-- `add i8 %6, -9`: the switch's `'\\t'`/`'\\n'` test folds the subtraction in. -/
def gapOff (x : BitVec 8) : BitVec 8 := x + BitVec.ofInt 8 (-9)

/-- The scan-stopping routes: each leaf selects `while.end`. -/
def gapWsRoute (x : BitVec 8) : Prop :=
  (evalICmp .slt x (BitVec.ofNat 8 13) = 1#1 ∧
      evalICmp .ule (gapOff x) (BitVec.ofNat 8 1) = 1#1) ∨
  (evalICmp .slt x (BitVec.ofNat 8 13) = 0#1 ∧
      evalICmp .slt x (BitVec.ofNat 8 32) = 1#1 ∧
      evalICmp .eq x (BitVec.ofNat 8 13) = 1#1) ∨
  (evalICmp .slt x (BitVec.ofNat 8 13) = 0#1 ∧
      evalICmp .slt x (BitVec.ofNat 8 32) = 0#1 ∧
      evalICmp .eq x (BitVec.ofNat 8 32) = 1#1)

/-- The advancing routes: each leaf selects `while.body`. -/
def gapNonWsRoute (x : BitVec 8) : Prop :=
  (evalICmp .slt x (BitVec.ofNat 8 13) = 1#1 ∧
      evalICmp .ule (gapOff x) (BitVec.ofNat 8 1) = 0#1) ∨
  (evalICmp .slt x (BitVec.ofNat 8 13) = 0#1 ∧
      evalICmp .slt x (BitVec.ofNat 8 32) = 1#1 ∧
      evalICmp .eq x (BitVec.ofNat 8 13) = 0#1) ∨
  (evalICmp .slt x (BitVec.ofNat 8 13) = 0#1 ∧
      evalICmp .slt x (BitVec.ofNat 8 32) = 0#1 ∧
      evalICmp .eq x (BitVec.ofNat 8 32) = 0#1)

/-- The routing, as a computation: the branch the switch takes for a byte. -/
def gapRouteOK (byte : UInt8) : Bool :=
  let x := gapByte byte
  let b1 := evalICmp .slt x (BitVec.ofNat 8 13)
  let b2 := evalICmp .ule (gapOff x) (BitVec.ofNat 8 1)
  let b3 := evalICmp .slt x (BitVec.ofNat 8 32)
  let b4 := evalICmp .eq x (BitVec.ofNat 8 13)
  let b5 := evalICmp .eq x (BitVec.ofNat 8 32)
  if gapIsWs byte then
    (b1 == 1#1 && b2 == 1#1) || (b1 == 0#1 && b3 == 1#1 && b4 == 1#1) ||
      (b1 == 0#1 && b3 == 0#1 && b5 == 1#1)
  else
    (b1 == 1#1 && b2 == 0#1) || (b1 == 0#1 && b3 == 1#1 && b4 == 0#1) ||
      (b1 == 0#1 && b3 == 0#1 && b5 == 0#1)

/-- The routing, per byte: a whitespace byte stops the scan, any other advances it. -/
def gapRouteProp (byte : UInt8) : Prop :=
  (gapIsWs byte = true → gapWsRoute (gapByte byte)) ∧
  (gapIsWs byte = false → gapNonWsRoute (gapByte byte))

/-- The computation and the rule agree at every byte. -/
theorem gapRouteOK_eq (byte : UInt8) : gapRouteOK byte = true ↔ gapRouteProp byte := by
  unfold gapRouteOK gapRouteProp gapWsRoute gapNonWsRoute gapByte gapOff
  cases gapIsWs byte <;> simp [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, and_assoc, or_assoc]

/-- The enumeration: the routing holds at every byte. -/
theorem gapRoute_pin :
    (List.range 256).all (fun a => gapRouteOK (UInt8.ofNat a)) = true := by
  decide

/-- Every loaded byte routes as the switch says. -/
theorem gapRoute (byte : UInt8) : gapRouteProp byte := by
  have hall := List.all_eq_true.mp gapRoute_pin
  have h := hall byte.toNat (List.mem_range.mpr byte.toNat_lt)
  have hb : UInt8.ofNat byte.toNat = byte := by simp
  rw [hb] at h
  exact (gapRouteOK_eq byte).1 h

/-- A whitespace byte takes a leaf that stops the scan. -/
theorem gapRoute_ws {byte : UInt8} (h : gapIsWs byte = true) : gapWsRoute (gapByte byte) :=
  (gapRoute byte).1 h

/-- Any other byte takes a leaf that advances the scan. -/
theorem gapRoute_nonWs {byte : UInt8} (h : gapIsWs byte = false) :
    gapNonWsRoute (gapByte byte) :=
  (gapRoute byte).2 h

/-! ### The scan's block steps -/

/-- The state `land.rhs` leaves: the counter cell, its address, and the byte. -/
def gapLandRhsEnv (env : Env) (b c : Nat) (byte : UInt8) : Env :=
  ("%6", .int 8 (gapByte byte)) ::
  ("%arrayidx5", .ptr (b + c)) ::
  ("%ee.011", .int 64 (BitVec.ofNat 64 c)) :: env

/-- `land.rhs` entered from `cond.end`: the counter is the token's position. -/
theorem gap_step_landRhs_condEnd {calls : Calls} {env : Env} {s : State}
    {b c : Nat} {byte : UInt8}
    (hpc : s.pc = "land.rhs") (hpre : s.pre = some "cond.end")
    (hb : lookupName env "%0" = some (.ptr b))
    (ht : lookupName env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 c)))
    (hld : readBytes s.mem (b + c) 1 = some (natToBytes (gapByte byte).toNat 1))
    (hc63 : c < 2 ^ 63) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt (gapLandRhsEnv env b c byte)
        { s with pc := "NodeBlock5", pre := some "land.rhs" }) := by
  have hpc' : (stateAt env s).pc = "land.rhs" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"land.rhs", odGapRecoverLandRhsInstrs,
        Term.br "NodeBlock5"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_land_rhs
  have hinc : phiIncoming "cond.end"
      [("while.body", Operand.reg "%inc"), ("cond.end", Operand.reg "%t.0.val")] =
        some (Operand.reg "%t.0.val") := by decide
  have hop : evalOperand (stateAt env s) (Operand.reg "%t.0.val") =
      some (.int 64 (BitVec.ofNat 64 c)) := by
    simp only [evalOperand, stateAt]
    rw [ht]
  have hgp : ((BitVec.ofNat 64 c).signExtend 64).toNat < 2 ^ 63 := by
    rw [gap_signExtend_ofNat c (by omega)]
    omega
  have hden : denoteCode calls odGapRecoverLandRhsInstrs (stateAt env s) =
      some (stateAt (gapLandRhsEnv env b c byte) s) := by
    rw [odGapRecoverLandRhsInstrs]
    refine Eq.trans (denoteCode_phi calls env s "%ee.011" (Ty.int 64)
      [("while.body", Operand.reg "%inc"), ("cond.end", Operand.reg "%t.0.val")]
      (p := "cond.end") (op := Operand.reg "%t.0.val")
      (v := .int 64 (BitVec.ofNat 64 c)) hpre hinc hop
      [Instr.gep "%arrayidx5" (Ty.int 8) (Operand.reg "%0") (Operand.reg "%ee.011"),
       Instr.load "%6" (Ty.int 8) (Operand.reg "%arrayidx5")] (by decide)) ?_
    refine Eq.trans (denoteCode_gep8_reg calls
      (("%ee.011", .int 64 (BitVec.ofNat 64 c)) :: env) s
      "%arrayidx5" "%0" "%ee.011" (by block_lk) (by block_lk) hgp
      [Instr.load "%6" (Ty.int 8) (Operand.reg "%arrayidx5")]) ?_
    rw [gap_signExtend_ofNat c (by omega)]
    refine Eq.trans (gap_denote_load8 calls
      (("%arrayidx5", .ptr (b + c)) :: ("%ee.011", .int 64 (BitVec.ofNat 64 c)) :: env) s
      "%6" "%arrayidx5" (by block_lk) hld []) ?_
    rfl
  have hterm : execTerm (stateAt (gapLandRhsEnv env b c byte) s) (Term.br "NodeBlock5") =
      .jump (stateAt (gapLandRhsEnv env b c byte)
        { s with pc := "NodeBlock5", pre := some "land.rhs" }) := by
    rw [gap_execTerm_br]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `land.rhs` entered from `while.body`: the counter is the incremented one. -/
theorem gap_step_landRhs_whileBody {calls : Calls} {env : Env} {s : State}
    {b c : Nat} {byte : UInt8}
    (hpc : s.pc = "land.rhs") (hpre : s.pre = some "while.body")
    (hb : lookupName env "%0" = some (.ptr b))
    (hinc : lookupName env "%inc" = some (.int 64 (BitVec.ofNat 64 c)))
    (hld : readBytes s.mem (b + c) 1 = some (natToBytes (gapByte byte).toNat 1))
    (hc63 : c < 2 ^ 63) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt (gapLandRhsEnv env b c byte)
        { s with pc := "NodeBlock5", pre := some "land.rhs" }) := by
  have hpc' : (stateAt env s).pc = "land.rhs" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"land.rhs", odGapRecoverLandRhsInstrs,
        Term.br "NodeBlock5"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_land_rhs
  have hinc' : phiIncoming "while.body"
      [("while.body", Operand.reg "%inc"), ("cond.end", Operand.reg "%t.0.val")] =
        some (Operand.reg "%inc") := by decide
  have hop : evalOperand (stateAt env s) (Operand.reg "%inc") =
      some (.int 64 (BitVec.ofNat 64 c)) := by
    simp only [evalOperand, stateAt]
    rw [hinc]
  have hgp : ((BitVec.ofNat 64 c).signExtend 64).toNat < 2 ^ 63 := by
    rw [gap_signExtend_ofNat c (by omega)]
    omega
  have hden : denoteCode calls odGapRecoverLandRhsInstrs (stateAt env s) =
      some (stateAt (gapLandRhsEnv env b c byte) s) := by
    rw [odGapRecoverLandRhsInstrs]
    refine Eq.trans (denoteCode_phi calls env s "%ee.011" (Ty.int 64)
      [("while.body", Operand.reg "%inc"), ("cond.end", Operand.reg "%t.0.val")]
      (p := "while.body") (op := Operand.reg "%inc")
      (v := .int 64 (BitVec.ofNat 64 c)) hpre hinc' hop
      [Instr.gep "%arrayidx5" (Ty.int 8) (Operand.reg "%0") (Operand.reg "%ee.011"),
       Instr.load "%6" (Ty.int 8) (Operand.reg "%arrayidx5")] (by decide)) ?_
    refine Eq.trans (denoteCode_gep8_reg calls
      (("%ee.011", .int 64 (BitVec.ofNat 64 c)) :: env) s
      "%arrayidx5" "%0" "%ee.011" (by block_lk) (by block_lk) hgp
      [Instr.load "%6" (Ty.int 8) (Operand.reg "%arrayidx5")]) ?_
    rw [gap_signExtend_ofNat c (by omega)]
    refine Eq.trans (gap_denote_load8 calls
      (("%arrayidx5", .ptr (b + c)) :: ("%ee.011", .int 64 (BitVec.ofNat 64 c)) :: env) s
      "%6" "%arrayidx5" (by block_lk) hld []) ?_
    rfl
  have hterm : execTerm (stateAt (gapLandRhsEnv env b c byte) s) (Term.br "NodeBlock5") =
      .jump (stateAt (gapLandRhsEnv env b c byte)
        { s with pc := "NodeBlock5", pre := some "land.rhs" }) := by
    rw [gap_execTerm_br]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-! ### Axiom footprints -/

#print axioms gap_entry_denote
#print axioms gap_condTrue_denote
#print axioms gap_condFalse_denote
#print axioms gap_condEnd_fromTrue_denote
#print axioms gap_condEnd_fromFalse_denote
#print axioms gap_whileEnd_fromCondEnd_denote


/-! ### The control steps of the entry chain

Each is one `step`: the block is found by name, its instructions denote to the
state the block's own lemma names, and its terminator is executed.  The state the
terminator leaves carries `pre := some s.pc`, so the block's hypothesis rewrites
`s.pc` in the conclusion, and a conditional terminator's branch bit is the value
the block computed. -/

/-- The entry block's step. -/
theorem gap_step_entry {calls : Calls} {env : Env} {s : State} {c b k nix : Nat}
    (hpc : s.pc = "entry")
    (hc : lookupName env "%c" = some (.ptr c))
    (hb : readBytes s.mem c 8 = some (natToBytes b 8)) (hb64 : b < 2 ^ 64)
    (hk : readBytes s.mem (c + 32) 8 = some (natToBytes k 8)) (hk64 : k < 2 ^ 64)
    (hnix : readBytes s.mem (c + 24) 8 = some (natToBytes nix 8)) (hnix64 : nix < 2 ^ 64) :
    step calls odGapRecoverBody (stateAt env s) =
      (if evalICmp .ult (BitVec.ofNat 64 k) (BitVec.ofNat 64 nix) = 1#1
       then .jump (stateAt (gapEntryEnv env s.next c b k nix)
              { s with next := s.next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes,
                       pc := "cond.true", pre := some "entry" })
       else .jump (stateAt (gapEntryEnv env s.next c b k nix)
              { s with next := s.next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes,
                       pc := "cond.false", pre := some "entry" })) := by
  have hpc' : (stateAt env s).pc = "entry" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"entry", odGapRecoverEntryInstrs,
        Term.condbr (Operand.reg "%cmp") "cond.true" "cond.false"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_entry
  have hden := gap_entry_denote (calls := calls) (env := env) (s := s)
    hc hb hb64 hk hk64 hnix hnix64
  by_cases hbit : evalICmp .ult (BitVec.ofNat 64 k) (BitVec.ofNat 64 nix) = 1#1
  · have hterm : execTerm
        (stateAt (gapEntryEnv env s.next c b k nix)
          { s with next := s.next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes })
        (Term.condbr (Operand.reg "%cmp") "cond.true" "cond.false") =
      .jump (stateAt (gapEntryEnv env s.next c b k nix)
        { s with next := s.next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes,
                 pc := "cond.true", pre := some "entry" }) := by
      rw [gap_execTerm_condbr_one
        (by simp only [evalOperand, stateAt, gapEntryEnv, lookupName_cons_self, hbit]; rfl)]
      simp only [stateAt, hpc]
    simp only [step, hfind, hden, hterm, if_pos hbit]
  · have hz : evalICmp .ult (BitVec.ofNat 64 k) (BitVec.ofNat 64 nix) = 0#1 := by
      rcases bitVec1_eq_zero_or_one
        (evalICmp .ult (BitVec.ofNat 64 k) (BitVec.ofNat 64 nix)) with h | h
      · exact h
      · exact absurd h hbit
    have hterm : execTerm
        (stateAt (gapEntryEnv env s.next c b k nix)
          { s with next := s.next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes })
        (Term.condbr (Operand.reg "%cmp") "cond.true" "cond.false") =
      .jump (stateAt (gapEntryEnv env s.next c b k nix)
        { s with next := s.next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes,
                 pc := "cond.false", pre := some "entry" }) := by
      rw [gap_execTerm_condbr_zero
        (by simp only [evalOperand, stateAt, gapEntryEnv, lookupName_cons_self, hz]; rfl)]
      simp only [stateAt, hpc]
    simp only [step, hfind, hden, hterm, if_neg hbit]

/-- `cond.true`'s step. -/
theorem gap_step_condTrue {calls : Calls} {env : Env} {s : State}
    {c k ix idx : Nat}
    (hpc : s.pc = "cond.true") (hpre : s.pre = some "entry")
    (hc : lookupName env "%c" = some (.ptr c))
    (h1 : lookupName env "%1" = some (.int 64 (BitVec.ofNat 64 k)))
    (hix : readBytes s.mem (c + 16) 8 = some (natToBytes ix 8)) (hix64 : ix < 2 ^ 64)
    (hk64 : k < 2 ^ 64) (hk63 : k < 2 ^ 63)
    (hidx : readBytes s.mem (ix + k * 4) 4 = some (natToBytes idx 4))
    (hidx32 : idx < 2 ^ 32) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%conv", .int 64 (BitVec.ofNat 64 idx)) ::
          ("%4", .int 32 (BitVec.ofNat 32 idx)) ::
          ("%arrayidx", .ptr (ix + k * 4)) ::
          ("%3", .ptr ix) :: ("%ix", .ptr (c + 16)) :: env)
        { s with pc := "cond.end", pre := some "cond.true" }) := by
  have hpc' : (stateAt env s).pc = "cond.true" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"cond.true", odGapRecoverCondTrueInstrs, Term.br "cond.end"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_cond_true
  have hden := gap_condTrue_denote (calls := calls) (env := env) (s := s)
    hc h1 hix hix64 hk64 hk63 hidx hidx32
  have hterm : execTerm
      (stateAt
        (("%conv", .int 64 (BitVec.ofNat 64 idx)) ::
          ("%4", .int 32 (BitVec.ofNat 32 idx)) ::
          ("%arrayidx", .ptr (ix + k * 4)) ::
          ("%3", .ptr ix) :: ("%ix", .ptr (c + 16)) :: env) s)
      (Term.br "cond.end") =
    .jump (stateAt
      (("%conv", .int 64 (BitVec.ofNat 64 idx)) ::
        ("%4", .int 32 (BitVec.ofNat 32 idx)) ::
        ("%arrayidx", .ptr (ix + k * 4)) ::
        ("%3", .ptr ix) :: ("%ix", .ptr (c + 16)) :: env)
      { s with pc := "cond.end", pre := some "cond.true" }) := by
    rw [gap_execTerm_br]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm, gap_word32' hidx32]

/-- `cond.false`'s step. -/
theorem gap_step_condFalse {calls : Calls} {env : Env} {s : State} {c n : Nat}
    (hpc : s.pc = "cond.false") (hpre : s.pre = some "entry")
    (hc : lookupName env "%c" = some (.ptr c))
    (hn : readBytes s.mem (c + 8) 8 = some (natToBytes n 8)) (hn64 : n < 2 ^ 64) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt (("%5", .int 64 (BitVec.ofNat 64 n)) ::
          ("%n", .ptr (c + 8)) :: env)
        { s with pc := "cond.end", pre := some "cond.false" }) := by
  have hpc' : (stateAt env s).pc = "cond.false" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"cond.false", odGapRecoverCondFalseInstrs, Term.br "cond.end"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_cond_false
  have hden := gap_condFalse_denote (calls := calls) (env := env) (s := s) hc hn hn64
  have hterm : execTerm
      (stateAt (("%5", .int 64 (BitVec.ofNat 64 n)) :: ("%n", .ptr (c + 8)) :: env) s)
      (Term.br "cond.end") =
    .jump (stateAt (("%5", .int 64 (BitVec.ofNat 64 n)) :: ("%n", .ptr (c + 8)) :: env)
      { s with pc := "cond.end", pre := some "cond.false" }) := by
    rw [gap_execTerm_br]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `cond.end` from `cond.true`'s step. -/
theorem gap_step_condEnd_fromTrue {calls : Calls} {env : Env} {s : State} {p0 idx : Nat}
    (hpc : s.pc = "cond.end") (hpre : s.pre = some "cond.true")
    (ht : lookupName env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 p0)))
    (hconv : lookupName env "%conv" = some (.int 64 (BitVec.ofNat 64 idx)))
    (hidx : idx < 2 ^ 64) :
    step calls odGapRecoverBody (stateAt env s) =
      (if evalICmp .ult (BitVec.ofNat 64 p0) (BitVec.ofNat 64 idx) = 1#1
       then .jump (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 p0)
              (BitVec.ofNat 64 idx))) ::
            ("%cond", .int 64 (BitVec.ofNat 64 idx)) :: env)
              { s with pc := "land.rhs", pre := some "cond.end" })
       else .jump (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 p0)
              (BitVec.ofNat 64 idx))) ::
            ("%cond", .int 64 (BitVec.ofNat 64 idx)) :: env)
              { s with pc := "while.end", pre := some "cond.end" })) := by
  have hpc' : (stateAt env s).pc = "cond.end" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"cond.end", odGapRecoverCondEndInstrs,
        Term.condbr (Operand.reg "%cmp310") "land.rhs" "while.end"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_cond_end
  have hden := gap_condEnd_fromTrue_denote (calls := calls) (env := env) (s := s)
    hpre ht hconv hidx
  by_cases hbit : evalICmp .ult (BitVec.ofNat 64 p0) (BitVec.ofNat 64 idx) = 1#1
  · have hterm : execTerm
        (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 p0)
            (BitVec.ofNat 64 idx))) ::
          ("%cond", .int 64 (BitVec.ofNat 64 idx)) :: env) s)
        (Term.condbr (Operand.reg "%cmp310") "land.rhs" "while.end") =
      .jump (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 p0)
            (BitVec.ofNat 64 idx))) ::
          ("%cond", .int 64 (BitVec.ofNat 64 idx)) :: env)
        { s with pc := "land.rhs", pre := some "cond.end" }) := by
      rw [gap_execTerm_condbr_one
        (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
      simp only [stateAt, hpc]
    simp only [step, hfind, hden, hterm, if_pos hbit]
  · have hz : evalICmp .ult (BitVec.ofNat 64 p0) (BitVec.ofNat 64 idx) = 0#1 := by
      rcases bitVec1_eq_zero_or_one
        (evalICmp .ult (BitVec.ofNat 64 p0) (BitVec.ofNat 64 idx)) with h | h
      · exact h
      · exact absurd h hbit
    have hterm : execTerm
        (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 p0)
            (BitVec.ofNat 64 idx))) ::
          ("%cond", .int 64 (BitVec.ofNat 64 idx)) :: env) s)
        (Term.condbr (Operand.reg "%cmp310") "land.rhs" "while.end") =
      .jump (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 p0)
            (BitVec.ofNat 64 idx))) ::
          ("%cond", .int 64 (BitVec.ofNat 64 idx)) :: env)
        { s with pc := "while.end", pre := some "cond.end" }) := by
      rw [gap_execTerm_condbr_zero
        (by simp only [evalOperand, stateAt, lookupName_cons_self, hz]; rfl)]
      simp only [stateAt, hpc]
    simp only [step, hfind, hden, hterm, if_neg hbit]

/-- `cond.end` from `cond.false`'s step. -/
theorem gap_step_condEnd_fromFalse {calls : Calls} {env : Env} {s : State} {p0 n : Nat}
    (hpc : s.pc = "cond.end") (hpre : s.pre = some "cond.false")
    (ht : lookupName env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 p0)))
    (h5 : lookupName env "%5" = some (.int 64 (BitVec.ofNat 64 n)))
    (hn : n < 2 ^ 64) :
    step calls odGapRecoverBody (stateAt env s) =
      (if evalICmp .ult (BitVec.ofNat 64 p0) (BitVec.ofNat 64 n) = 1#1
       then .jump (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 p0)
              (BitVec.ofNat 64 n))) ::
            ("%cond", .int 64 (BitVec.ofNat 64 n)) :: env)
              { s with pc := "land.rhs", pre := some "cond.end" })
       else .jump (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 p0)
              (BitVec.ofNat 64 n))) ::
            ("%cond", .int 64 (BitVec.ofNat 64 n)) :: env)
              { s with pc := "while.end", pre := some "cond.end" })) := by
  have hpc' : (stateAt env s).pc = "cond.end" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"cond.end", odGapRecoverCondEndInstrs,
        Term.condbr (Operand.reg "%cmp310") "land.rhs" "while.end"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_cond_end
  have hden := gap_condEnd_fromFalse_denote (calls := calls) (env := env) (s := s)
    hpre ht h5 hn
  by_cases hbit : evalICmp .ult (BitVec.ofNat 64 p0) (BitVec.ofNat 64 n) = 1#1
  · have hterm : execTerm
        (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 p0)
            (BitVec.ofNat 64 n))) ::
          ("%cond", .int 64 (BitVec.ofNat 64 n)) :: env) s)
        (Term.condbr (Operand.reg "%cmp310") "land.rhs" "while.end") =
      .jump (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 p0)
            (BitVec.ofNat 64 n))) ::
          ("%cond", .int 64 (BitVec.ofNat 64 n)) :: env)
        { s with pc := "land.rhs", pre := some "cond.end" }) := by
      rw [gap_execTerm_condbr_one
        (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
      simp only [stateAt, hpc]
    simp only [step, hfind, hden, hterm, if_pos hbit]
  · have hz : evalICmp .ult (BitVec.ofNat 64 p0) (BitVec.ofNat 64 n) = 0#1 := by
      rcases bitVec1_eq_zero_or_one
        (evalICmp .ult (BitVec.ofNat 64 p0) (BitVec.ofNat 64 n)) with h | h
      · exact h
      · exact absurd h hbit
    have hterm : execTerm
        (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 p0)
            (BitVec.ofNat 64 n))) ::
          ("%cond", .int 64 (BitVec.ofNat 64 n)) :: env) s)
        (Term.condbr (Operand.reg "%cmp310") "land.rhs" "while.end") =
      .jump (stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 p0)
            (BitVec.ofNat 64 n))) ::
          ("%cond", .int 64 (BitVec.ofNat 64 n)) :: env)
        { s with pc := "while.end", pre := some "cond.end" }) := by
      rw [gap_execTerm_condbr_zero
        (by simp only [evalOperand, stateAt, lookupName_cons_self, hz]; rfl)]
      simp only [stateAt, hpc]
    simp only [step, hfind, hden, hterm, if_neg hbit]

/-- `while.end` from `cond.end`'s step. -/
theorem gap_step_whileEnd_fromCondEnd {calls : Calls} {env : Env} {s : State} {ip : Nat}
    (hpc : s.pc = "while.end") (hpre : s.pre = some "cond.end")
    (ht : lookupName env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hcond : lookupName env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hip64 : ip < 2 ^ 64) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 ip)
            (BitVec.ofNat 64 ip))) ::
          ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 ip)) :: env)
        { s with pc := "cleanup82", pre := some "while.end" }) := by
  have hpc' : (stateAt env s).pc = "while.end" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"while.end", odGapRecoverWhileEndInstrs,
        Term.condbr (Operand.reg "%cmp6") "cleanup82" "if.end"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_while_end
  have hden := gap_whileEnd_fromCondEnd_denote (calls := calls) (env := env) (s := s)
    hpre ht hcond hip64
  have hbit : evalICmp .eq (BitVec.ofNat 64 ip) (BitVec.ofNat 64 ip) = 1#1 :=
    gap_eq_self _
  have hterm : execTerm
      (stateAt (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 ip)
          (BitVec.ofNat 64 ip))) ::
        ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 ip)) :: env) s)
      (Term.condbr (Operand.reg "%cmp6") "cleanup82" "if.end") =
    .jump (stateAt (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 ip)
          (BitVec.ofNat 64 ip))) ::
        ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 ip)) :: env)
      { s with pc := "cleanup82", pre := some "while.end" }) := by
    rw [gap_execTerm_condbr_one
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `cleanup82`'s step: the body returns `void`. -/
theorem gap_step_cleanup82 {calls : Calls} {env : Env} {s : State}
    (hpc : s.pc = "cleanup82") :
    step calls odGapRecoverBody (stateAt env s) = .ret none (stateAt env s) := by
  have hpc' : (stateAt env s).pc = "cleanup82" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"cleanup82", odGapRecoverCleanup82Instrs, Term.ret Ty.void none⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_cleanup82
  have hterm : execTerm (stateAt env s) (Term.ret Ty.void none) =
      .ret none (stateAt env s) := gap_execTerm_retVoid _
  simp only [step, hfind, odGapRecoverCleanup82Instrs, denoteCode_nil, hterm]


/-! ### The model, at `p = ip`

`gapRecoverWrite bytes ip ip` is no write — the scan's start is its end — and the
`p = ip` run leaves the caller's memory unchanged, which is the model's
`.unchanged` effect. -/

/-- The rule's write is `none` when the token starts at `ip`. -/
theorem gap_recoverWrite_self (bytes : List UInt8) (ip : Nat) :
    gapRecoverWrite bytes ip ip = GapWrite.none := by
  simp [gapRecoverWrite, gapEe, gapNonWsRun]

/-- A sixty-four-bit word read is the model's `Nat`. -/
theorem gap_readWord {mem : Mem} {a n : Nat}
    (h : readBytes mem a 8 = some (natToBytes n 8)) (hn : n < 2 ^ 64) :
    stage2ReadWord mem a 8 = some n := by
  simp only [stage2ReadWord, h, Option.map, natToBytes_toNat,
    show (256 : Nat) ^ 8 = 2 ^ 64 from by decide, Nat.mod_eq_of_lt hn]

/-- A thirty-two-bit word read is the model's `Nat`. -/
theorem gap_readWord4 {mem : Mem} {a n : Nat}
    (h : readBytes mem a 4 = some (natToBytes n 4)) (hn : n < 2 ^ 32) :
    stage2ReadWord mem a 4 = some n := by
  simp only [stage2ReadWord, h, Option.map, natToBytes_toNat,
    show (256 : Nat) ^ 4 = 2 ^ 32 from by decide, Nat.mod_eq_of_lt hn]

/-- The model's rule at `p = ip`: no write, given the cursor's six words, the
index word (or the length when the cursor has no index) and the document window. -/
theorem gap_rule_atIp {mem : Mem} {c ip b n ix nix k e : Nat} {bytes : List UInt8}
    (hb : stage2ReadWord mem c 8 = some b)
    (hn : stage2ReadWord mem (c + 8) 8 = some n)
    (hix : stage2ReadWord mem (c + 16) 8 = some ix)
    (hnix : stage2ReadWord mem (c + 24) 8 = some nix)
    (hk : stage2ReadWord mem (c + 32) 8 = some k)
    (he : stage2ReadWord mem (c + 1112) 8 = some e)
    (hidx : ∀ (_ : k < nix), stage2ReadWord mem (ix + 4 * k) 4 = some ip)
    (hnip : nix ≤ k → ip = n)
    (hbytes : readBytes mem b ip = some bytes) :
    stage2GapRecoverRule mem c ip = some .unchanged := by
  unfold stage2GapRecoverRule
  simp only [odGapCurN, odGapCurIx, odGapCurNix, odGapCurK, odGapCurE]
  simp only [hb, hn, hix, hnix, hk, he]
  by_cases hklt : k < nix
  · simp only [if_pos hklt, hidx hklt, hbytes, gap_recoverWrite_self]
  · simp only [if_neg hklt, ← hnip (by omega), hbytes, gap_recoverWrite_self]

/-! ### The `p = ip` run -/

/-- **The `p = ip` arm, at the call boundary.**  The token's position is already
`ip` (the cursor's index word is `ip` and `k < nix`), so the body takes
`cond.true`'s branch, `cond.end`'s position test is false, `while.end`'s equality
test is true, `cleanup82` returns `void`, and the caller's memory is unchanged.
The model's rule answers `.unchanged` at the same staging, so the outcome
satisfies `Stage2GapRecoverPost`. -/
theorem gap_run_atIp {nf : Calls} {mem : Mem} {next c ip b n ix nix k e lt lf ln : Nat}
    {bytes : List UInt8}
    (hb : readBytes mem c 8 = some (natToBytes b 8)) (hb64 : b < 2 ^ 64)
    (hn : readBytes mem (c + 8) 8 = some (natToBytes n 8)) (hn64 : n < 2 ^ 64)
    (hnip : n = ip)
    (hix : readBytes mem (c + 16) 8 = some (natToBytes ix 8)) (hix64 : ix < 2 ^ 64)
    (hnix : readBytes mem (c + 24) 8 = some (natToBytes nix 8)) (hnix64 : nix < 2 ^ 64)
    (hk : readBytes mem (c + 32) 8 = some (natToBytes k 8)) (hk64 : k < 2 ^ 64)
    (hk63 : k < 2 ^ 63)
    (he : readBytes mem (c + 1112) 8 = some (natToBytes e 8)) (he64 : e < 2 ^ 64)
    (hidx : readBytes mem (ix + 4 * k) 4 = some (natToBytes ip 4)) (hip32 : ip < 2 ^ 32)
    (hklt : k < nix)
    (hbytes : readBytes mem b ip = some bytes) :
    ∃ (o : CallOutcome),
      o = { ret := voidRet, mem := mem, next := next } ∧
      runFuel (JsonStage2IR.stage2Calls nf) 5 odGapRecoverBody
        (stagedState odGapRecoverBody
          [.ptr c, .int 64 (BitVec.ofNat 64 ip), .ptr lt, .ptr lf, .ptr ln] mem next) =
        some (.ret none mem) ∧
      Stage2GapRecoverPost mem next c ip o := by
  have wb := gap_readWord hb hb64
  have wn := gap_readWord hn hn64
  have wix := gap_readWord hix hix64
  have wnix := gap_readWord hnix hnix64
  have wk := gap_readWord hk hk64
  have we := gap_readWord he he64
  have widx : ∀ (_ : k < nix), stage2ReadWord mem (ix + 4 * k) 4 = some ip := by
    intro _
    exact gap_readWord4 hidx hip32
  have hrule := gap_rule_atIp (mem := mem) (c := c) (ip := ip) (b := b) (n := n)
    (ix := ix) (nix := nix) (k := k) (e := e) (bytes := bytes)
    wb wn wix wnix wk we widx (by intro _; exact hnip.symm) hbytes
  refine ⟨{ ret := voidRet, mem := mem, next := next }, rfl, ?_, ?_⟩
  · -- the run
    change runFuel (JsonStage2IR.stage2Calls nf) 5 odGapRecoverBody
      { env := [("%c", .ptr c),
                ("%t.0.val", .int 64 (BitVec.ofNat 64 ip)),
                ("%littrue", .ptr lt), ("%litfalse", .ptr lf), ("%litnull", .ptr ln)],
        mem := mem, next := next, pc := "entry", pre := none }
      = some (.ret none mem)
    let s0 : State :=
      { env := [("%c", .ptr c),
                ("%t.0.val", .int 64 (BitVec.ofNat 64 ip)),
                ("%littrue", .ptr lt), ("%litfalse", .ptr lf), ("%litnull", .ptr ln)],
        mem := mem, next := next, pc := "entry", pre := none }
    let env1 : Env := gapEntryEnv s0.env s0.next c b k nix
    let s1 : State := stateAt env1 { s0 with next := s0.next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes, pc := "cond.true", pre := some "entry" }
    let env2 : Env :=
      ("%conv", .int 64 (BitVec.ofNat 64 ip)) ::
      ("%4", .int 32 (BitVec.ofNat 32 ip)) ::
      ("%arrayidx", .ptr (ix + k * 4)) ::
      ("%3", .ptr ix) :: ("%ix", .ptr (c + 16)) :: env1
    let s2 : State := stateAt env2 { s1 with pc := "cond.end", pre := some "cond.true" }
    let env3 : Env :=
      ("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 ip) (BitVec.ofNat 64 ip))) ::
      ("%cond", .int 64 (BitVec.ofNat 64 ip)) :: env2
    let s3 : State := stateAt env3 { s2 with pc := "while.end", pre := some "cond.end" }
    let env4 : Env :=
      ("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 ip) (BitVec.ofNat 64 ip))) ::
      ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 ip)) :: env3
    let s4 : State := stateAt env4 { s3 with pc := "cleanup82", pre := some "while.end" }
    have hpc0 : s0.pc = "entry" := rfl
    have hc0 : lookupName s0.env "%c" = some (.ptr c) := by
      simp only [s0]
      block_lk
    have ht0 : lookupName s0.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 ip)) := by
      simp only [s0]
      block_lk
    have hult1 : evalICmp .ult (BitVec.ofNat 64 k) (BitVec.ofNat 64 nix) = 1#1 :=
      gap_ult_one hk64 hnix64 hklt
    have hult0 : evalICmp .ult (BitVec.ofNat 64 ip) (BitVec.ofNat 64 ip) = 0#1 :=
      gap_ult_self _
    have heq1 : evalICmp .eq (BitVec.ofNat 64 ip) (BitVec.ofNat 64 ip) = 1#1 :=
      gap_eq_self _
    have h1 : step (JsonStage2IR.stage2Calls nf) odGapRecoverBody s0 = .jump s1 := by
      have hh := gap_step_entry (calls := JsonStage2IR.stage2Calls nf) (env := s0.env)
        (s := s0) hpc0 hc0 hb hb64 hk hk64 hnix hnix64
      rw [hult1, if_pos rfl] at hh
      have hst : stateAt s0.env s0 = s0 := rfl
      simpa only [hst, s1, env1] using hh
    have hc1 : lookupName env1 "%c" = some (.ptr c) := by
      simp only [env1, gapEntryEnv]
      block_lk
    have h1cell : lookupName env1 "%1" = some (.int 64 (BitVec.ofNat 64 k)) := by
      simp only [env1, gapEntryEnv]
      block_lk
    have h2 : step (JsonStage2IR.stage2Calls nf) odGapRecoverBody s1 = .jump s2 := by
      have hh := gap_step_condTrue (calls := JsonStage2IR.stage2Calls nf) (env := env1)
        (s := s1) (c := c) (k := k) (ix := ix) (idx := ip)
        rfl rfl hc1 h1cell hix hix64 hk64 hk63
        (by rw [Nat.mul_comm k 4]; exact hidx) hip32
      have hst : stateAt env1 s1 = s1 := rfl
      simpa only [hst, s2, env2] using hh
    have hconv : lookupName env2 "%conv" = some (.int 64 (BitVec.ofNat 64 ip)) := by
      simp only [env2, lookupName_cons_self]
    have h3 : step (JsonStage2IR.stage2Calls nf) odGapRecoverBody s2 = .jump s3 := by
      have hh := gap_step_condEnd_fromTrue (calls := JsonStage2IR.stage2Calls nf)
        (env := env2) (s := s2) (p0 := ip) (idx := ip)
        rfl rfl ht0 hconv (by omega)
      rw [hult0, if_neg (by decide)] at hh
      have hst : stateAt env2 s2 = s2 := rfl
      simpa only [hst, s3, env3, hult0] using hh
    have hcond : lookupName env3 "%cond" = some (.int 64 (BitVec.ofNat 64 ip)) := by
      simp only [env3]
      block_lk
    have h4 : step (JsonStage2IR.stage2Calls nf) odGapRecoverBody s3 = .jump s4 := by
      have hh := gap_step_whileEnd_fromCondEnd (calls := JsonStage2IR.stage2Calls nf)
        (env := env3) (s := s3) (ip := ip) rfl rfl ht0 hcond (by omega)
      have hst : stateAt env3 s3 = s3 := rfl
      simpa only [hst, s4, env4] using hh
    have h5 : step (JsonStage2IR.stage2Calls nf) odGapRecoverBody s4
        = .ret none (stateAt env4 s4) :=
      gap_step_cleanup82 (calls := JsonStage2IR.stage2Calls nf) (env := env4) (s := s4) rfl
    rw [show (5 : Nat) = 1 + 4 from rfl, runFuel_jump_prefix h1 4]
    rw [show (4 : Nat) = 1 + 3 from rfl, runFuel_jump_prefix h2 3]
    rw [show (3 : Nat) = 1 + 2 from rfl, runFuel_jump_prefix h3 2]
    rw [show (2 : Nat) = 1 + 1 from rfl, runFuel_jump_prefix h4 1]
    simp only [runFuel, h5]
    rfl
  · -- the post
    refine ⟨rfl, rfl, ?_⟩
    exact ⟨.unchanged, hrule, rfl⟩

/-! ### Axiom footprints -/

#print axioms gap_step_entry
#print axioms gap_step_condTrue
#print axioms gap_step_condFalse
#print axioms gap_step_condEnd_fromTrue
#print axioms gap_step_condEnd_fromFalse
#print axioms gap_step_whileEnd_fromCondEnd
#print axioms gap_step_cleanup82
#print axioms gap_recoverWrite_self
#print axioms gap_readWord
#print axioms gap_readWord4
#print axioms gap_rule_atIp
#print axioms gap_run_atIp
#print axioms gapRoute_pin
#print axioms gapRoute
#print axioms gapRoute_ws
#print axioms gapRoute_nonWs
#print axioms gap_step_landRhs_condEnd
#print axioms gap_step_landRhs_whileBody

end LeanLLVM.Refinement
