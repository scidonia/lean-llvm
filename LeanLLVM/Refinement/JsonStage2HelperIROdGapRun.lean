/-
`od_gap_recover` at its call boundary: the entry chain, the token-at-`ip` case,
the first scan's routing, blocks and run, and the arithmetic lemmas its run
reads.

`JsonStage2HelperIROdGapSteps` pins the body's blocks and proves the instruction
and terminator steps at its widths.  This module begins the run those steps
compose, and it states no contract: it proves the `denoteCode` and the control
`step` of the entry block, of `cond.true` and `cond.false`, of `cond.end` from
each of them, of `while.end` entered from `cond.end`, and of `cleanup82` — the
path the body takes when the token's position is already `ip` — together with the
rule's no-write value at that position and the two word readings the model's
fields use.  The `p = ip` case of the `runFuel` completion is proved (`gap_run_atIp`, with
`gap_rule_atIp`'s `.unchanged` value), and it states the model's post at that one
staging — not a contract over the whole function.

The first scan is proved as a run: the routing the switch takes at every byte
(`gapRoute`), `land.rhs`'s two steps, the scan's three `runFuel` prefixes — the
whitespace exit to `while.end` (`gap_scan_exit_ws`), the `ip` exit to `cleanup82`
(`gap_scan_exit_ip`) and the advance back to the head (`gap_scan_step_loop`, over
`gap_scan_toWhileBody`) — the invariant they preserve (`gapScanInv`: the carried
counter, the stable cells, the no-whitespace prefix and the budget `ip ≤ c + r`),
the `BoundLoop` instance built from them (`gapScanLoop`, `cost = 5`) with its
`run` and `run_from` (`gapScanLoop_run`, `gapScanLoop_run_from`), and the two
exits' continuations: `while.end`'s `%cmp6` false into `if.end` with
`%ee.0.lcssa` the first whitespace (`gap_scan_whileEnd_continue`), and
`cleanup82`'s `void` return with the model writing nothing
(`gap_scan_cleanup82_continue`).

The literal loop that follows `if.end`, the four refusal arms and the model's
post beyond the scan's exit are not in this module, so the body's relation to the
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

/-- `NodeBlock5`: `%6 < 13` selects LeafBlock. -/
theorem gap_step_NodeBlock5_toLeaf {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "NodeBlock5") (hpre : s.pre = some "land.rhs")
    (h6 : lookupName env "%6" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .slt (gapByte byte) (BitVec.ofNat 8 13) = 1#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%Pivot6", .int 1 (evalICmp .slt (gapByte byte) (BitVec.ofNat 8 13))) :: env)
        { s with pc := "LeafBlock", pre := some "NodeBlock5" }) := by
  have hpc' : (stateAt env s).pc = "NodeBlock5" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"NodeBlock5", odGapRecoverNodeBlock5Instrs,
        Term.condbr (Operand.reg "%Pivot6") "LeafBlock" "NodeBlock"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_NodeBlock5
  have hden : denoteCode calls odGapRecoverNodeBlock5Instrs (stateAt env s) =
      some (stateAt (("%Pivot6", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 13))) :: env) s) := by
    rw [odGapRecoverNodeBlock5Instrs]
    refine Eq.trans (gap_denote_icmp_slt_imm calls env s "%Pivot6" "%6" (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%Pivot6", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 13))) :: env) s)
      (Term.condbr (Operand.reg "%Pivot6") "LeafBlock" "NodeBlock") =
    .jump (stateAt (("%Pivot6", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 13))) :: env)
      { s with pc := "LeafBlock", pre := some "NodeBlock5" }) := by
    rw [gap_execTerm_condbr_one
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `NodeBlock5`: `%6 < 13` selects NodeBlock. -/
theorem gap_step_NodeBlock5_toNode {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "NodeBlock5") (hpre : s.pre = some "land.rhs")
    (h6 : lookupName env "%6" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .slt (gapByte byte) (BitVec.ofNat 8 13) = 0#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%Pivot6", .int 1 (evalICmp .slt (gapByte byte) (BitVec.ofNat 8 13))) :: env)
        { s with pc := "NodeBlock", pre := some "NodeBlock5" }) := by
  have hpc' : (stateAt env s).pc = "NodeBlock5" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"NodeBlock5", odGapRecoverNodeBlock5Instrs,
        Term.condbr (Operand.reg "%Pivot6") "LeafBlock" "NodeBlock"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_NodeBlock5
  have hden : denoteCode calls odGapRecoverNodeBlock5Instrs (stateAt env s) =
      some (stateAt (("%Pivot6", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 13))) :: env) s) := by
    rw [odGapRecoverNodeBlock5Instrs]
    refine Eq.trans (gap_denote_icmp_slt_imm calls env s "%Pivot6" "%6" (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%Pivot6", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 13))) :: env) s)
      (Term.condbr (Operand.reg "%Pivot6") "LeafBlock" "NodeBlock") =
    .jump (stateAt (("%Pivot6", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 13))) :: env)
      { s with pc := "NodeBlock", pre := some "NodeBlock5" }) := by
    rw [gap_execTerm_condbr_zero
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `NodeBlock`: `%6 < 32` selects LeafBlock1. -/
theorem gap_step_NodeBlock_toLeaf1 {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "NodeBlock") (hpre : s.pre = some "NodeBlock5")
    (h6 : lookupName env "%6" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .slt (gapByte byte) (BitVec.ofNat 8 32) = 1#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%Pivot", .int 1 (evalICmp .slt (gapByte byte) (BitVec.ofNat 8 32))) :: env)
        { s with pc := "LeafBlock1", pre := some "NodeBlock" }) := by
  have hpc' : (stateAt env s).pc = "NodeBlock" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"NodeBlock", odGapRecoverNodeBlockInstrs,
        Term.condbr (Operand.reg "%Pivot") "LeafBlock1" "LeafBlock3"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_NodeBlock
  have hden : denoteCode calls odGapRecoverNodeBlockInstrs (stateAt env s) =
      some (stateAt (("%Pivot", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 32))) :: env) s) := by
    rw [odGapRecoverNodeBlockInstrs]
    refine Eq.trans (gap_denote_icmp_slt_imm calls env s "%Pivot" "%6" (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%Pivot", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 32))) :: env) s)
      (Term.condbr (Operand.reg "%Pivot") "LeafBlock1" "LeafBlock3") =
    .jump (stateAt (("%Pivot", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 32))) :: env)
      { s with pc := "LeafBlock1", pre := some "NodeBlock" }) := by
    rw [gap_execTerm_condbr_one
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `NodeBlock`: `%6 < 32` selects LeafBlock3. -/
theorem gap_step_NodeBlock_toLeaf3 {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "NodeBlock") (hpre : s.pre = some "NodeBlock5")
    (h6 : lookupName env "%6" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .slt (gapByte byte) (BitVec.ofNat 8 32) = 0#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%Pivot", .int 1 (evalICmp .slt (gapByte byte) (BitVec.ofNat 8 32))) :: env)
        { s with pc := "LeafBlock3", pre := some "NodeBlock" }) := by
  have hpc' : (stateAt env s).pc = "NodeBlock" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"NodeBlock", odGapRecoverNodeBlockInstrs,
        Term.condbr (Operand.reg "%Pivot") "LeafBlock1" "LeafBlock3"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_NodeBlock
  have hden : denoteCode calls odGapRecoverNodeBlockInstrs (stateAt env s) =
      some (stateAt (("%Pivot", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 32))) :: env) s) := by
    rw [odGapRecoverNodeBlockInstrs]
    refine Eq.trans (gap_denote_icmp_slt_imm calls env s "%Pivot" "%6" (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%Pivot", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 32))) :: env) s)
      (Term.condbr (Operand.reg "%Pivot") "LeafBlock1" "LeafBlock3") =
    .jump (stateAt (("%Pivot", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 32))) :: env)
      { s with pc := "LeafBlock3", pre := some "NodeBlock" }) := by
    rw [gap_execTerm_condbr_zero
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `LeafBlock3`: `%6 == 32` selects while.end. -/
theorem gap_step_LeafBlock3_toWhileEnd {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "LeafBlock3") (hpre : s.pre = some "NodeBlock")
    (h6 : lookupName env "%6" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .eq (gapByte byte) (BitVec.ofNat 8 32) = 1#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf4", .int 1 (evalICmp .eq (gapByte byte) (BitVec.ofNat 8 32))) :: env)
        { s with pc := "while.end", pre := some "LeafBlock3" }) := by
  have hpc' : (stateAt env s).pc = "LeafBlock3" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"LeafBlock3", odGapRecoverLeafBlock3Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf4") "while.end" "while.body"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_LeafBlock3
  have hden : denoteCode calls odGapRecoverLeafBlock3Instrs (stateAt env s) =
      some (stateAt (("%SwitchLeaf4", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 32))) :: env) s) := by
    rw [odGapRecoverLeafBlock3Instrs]
    refine Eq.trans (gap_denote_icmp_eq_imm calls env s "%SwitchLeaf4" "%6" (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%SwitchLeaf4", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 32))) :: env) s)
      (Term.condbr (Operand.reg "%SwitchLeaf4") "while.end" "while.body") =
    .jump (stateAt (("%SwitchLeaf4", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 32))) :: env)
      { s with pc := "while.end", pre := some "LeafBlock3" }) := by
    rw [gap_execTerm_condbr_one
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `LeafBlock3`: `%6 == 32` selects while.body. -/
theorem gap_step_LeafBlock3_toWhileBody {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "LeafBlock3") (hpre : s.pre = some "NodeBlock")
    (h6 : lookupName env "%6" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .eq (gapByte byte) (BitVec.ofNat 8 32) = 0#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf4", .int 1 (evalICmp .eq (gapByte byte) (BitVec.ofNat 8 32))) :: env)
        { s with pc := "while.body", pre := some "LeafBlock3" }) := by
  have hpc' : (stateAt env s).pc = "LeafBlock3" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"LeafBlock3", odGapRecoverLeafBlock3Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf4") "while.end" "while.body"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_LeafBlock3
  have hden : denoteCode calls odGapRecoverLeafBlock3Instrs (stateAt env s) =
      some (stateAt (("%SwitchLeaf4", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 32))) :: env) s) := by
    rw [odGapRecoverLeafBlock3Instrs]
    refine Eq.trans (gap_denote_icmp_eq_imm calls env s "%SwitchLeaf4" "%6" (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%SwitchLeaf4", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 32))) :: env) s)
      (Term.condbr (Operand.reg "%SwitchLeaf4") "while.end" "while.body") =
    .jump (stateAt (("%SwitchLeaf4", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 32))) :: env)
      { s with pc := "while.body", pre := some "LeafBlock3" }) := by
    rw [gap_execTerm_condbr_zero
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `LeafBlock1`: `%6 == 13` selects while.end. -/
theorem gap_step_LeafBlock1_toWhileEnd {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "LeafBlock1") (hpre : s.pre = some "NodeBlock")
    (h6 : lookupName env "%6" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .eq (gapByte byte) (BitVec.ofNat 8 13) = 1#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf2", .int 1 (evalICmp .eq (gapByte byte) (BitVec.ofNat 8 13))) :: env)
        { s with pc := "while.end", pre := some "LeafBlock1" }) := by
  have hpc' : (stateAt env s).pc = "LeafBlock1" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"LeafBlock1", odGapRecoverLeafBlock1Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf2") "while.end" "while.body"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_LeafBlock1
  have hden : denoteCode calls odGapRecoverLeafBlock1Instrs (stateAt env s) =
      some (stateAt (("%SwitchLeaf2", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 13))) :: env) s) := by
    rw [odGapRecoverLeafBlock1Instrs]
    refine Eq.trans (gap_denote_icmp_eq_imm calls env s "%SwitchLeaf2" "%6" (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%SwitchLeaf2", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 13))) :: env) s)
      (Term.condbr (Operand.reg "%SwitchLeaf2") "while.end" "while.body") =
    .jump (stateAt (("%SwitchLeaf2", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 13))) :: env)
      { s with pc := "while.end", pre := some "LeafBlock1" }) := by
    rw [gap_execTerm_condbr_one
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `LeafBlock1`: `%6 == 13` selects while.body. -/
theorem gap_step_LeafBlock1_toWhileBody {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "LeafBlock1") (hpre : s.pre = some "NodeBlock")
    (h6 : lookupName env "%6" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .eq (gapByte byte) (BitVec.ofNat 8 13) = 0#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf2", .int 1 (evalICmp .eq (gapByte byte) (BitVec.ofNat 8 13))) :: env)
        { s with pc := "while.body", pre := some "LeafBlock1" }) := by
  have hpc' : (stateAt env s).pc = "LeafBlock1" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"LeafBlock1", odGapRecoverLeafBlock1Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf2") "while.end" "while.body"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_LeafBlock1
  have hden : denoteCode calls odGapRecoverLeafBlock1Instrs (stateAt env s) =
      some (stateAt (("%SwitchLeaf2", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 13))) :: env) s) := by
    rw [odGapRecoverLeafBlock1Instrs]
    refine Eq.trans (gap_denote_icmp_eq_imm calls env s "%SwitchLeaf2" "%6" (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%SwitchLeaf2", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 13))) :: env) s)
      (Term.condbr (Operand.reg "%SwitchLeaf2") "while.end" "while.body") =
    .jump (stateAt (("%SwitchLeaf2", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 13))) :: env)
      { s with pc := "while.body", pre := some "LeafBlock1" }) := by
    rw [gap_execTerm_condbr_zero
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `LeafBlock`: `%6 - 9 <= 1` selects while.end. -/
theorem gap_step_LeafBlock_toWhileEnd {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "LeafBlock") (hpre : s.pre = some "NodeBlock5")
    (h6 : lookupName env "%6" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .ule (gapOff (gapByte byte)) (BitVec.ofNat 8 1) = 1#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf", .int 1 (evalICmp .ule (gapOff (gapByte byte))
          (BitVec.ofNat 8 1))) :: ("%.off", .int 8 (gapOff (gapByte byte))) :: env)
        { s with pc := "while.end", pre := some "LeafBlock" }) := by
  have hpc' : (stateAt env s).pc = "LeafBlock" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"LeafBlock", odGapRecoverLeafBlockInstrs,
        Term.condbr (Operand.reg "%SwitchLeaf") "while.end" "while.body"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_LeafBlock
  have hden : denoteCode calls odGapRecoverLeafBlockInstrs (stateAt env s) =
      some (stateAt (("%SwitchLeaf", .int 1 (evalICmp .ule (gapOff (gapByte byte))
        (BitVec.ofNat 8 1))) :: ("%.off", .int 8 (gapOff (gapByte byte))) :: env) s) := by
    rw [odGapRecoverLeafBlockInstrs]
    refine Eq.trans (gap_denote_add_imm calls env s "%.off" "%6" (by block_lk) _) ?_
    refine Eq.trans (gap_denote_icmp_ule_imm calls
      (("%.off", .int 8 (gapOff (gapByte byte))) :: env) s
      "%SwitchLeaf" "%.off" (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%SwitchLeaf", .int 1 (evalICmp .ule (gapOff (gapByte byte))
        (BitVec.ofNat 8 1))) :: ("%.off", .int 8 (gapOff (gapByte byte))) :: env) s)
      (Term.condbr (Operand.reg "%SwitchLeaf") "while.end" "while.body") =
    .jump (stateAt (("%SwitchLeaf", .int 1 (evalICmp .ule (gapOff (gapByte byte))
        (BitVec.ofNat 8 1))) :: ("%.off", .int 8 (gapOff (gapByte byte))) :: env)
      { s with pc := "while.end", pre := some "LeafBlock" }) := by
    rw [gap_execTerm_condbr_one
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `LeafBlock`: `%6 - 9 <= 1` selects while.body. -/
theorem gap_step_LeafBlock_toWhileBody {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "LeafBlock") (hpre : s.pre = some "NodeBlock5")
    (h6 : lookupName env "%6" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .ule (gapOff (gapByte byte)) (BitVec.ofNat 8 1) = 0#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf", .int 1 (evalICmp .ule (gapOff (gapByte byte))
          (BitVec.ofNat 8 1))) :: ("%.off", .int 8 (gapOff (gapByte byte))) :: env)
        { s with pc := "while.body", pre := some "LeafBlock" }) := by
  have hpc' : (stateAt env s).pc = "LeafBlock" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"LeafBlock", odGapRecoverLeafBlockInstrs,
        Term.condbr (Operand.reg "%SwitchLeaf") "while.end" "while.body"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_LeafBlock
  have hden : denoteCode calls odGapRecoverLeafBlockInstrs (stateAt env s) =
      some (stateAt (("%SwitchLeaf", .int 1 (evalICmp .ule (gapOff (gapByte byte))
        (BitVec.ofNat 8 1))) :: ("%.off", .int 8 (gapOff (gapByte byte))) :: env) s) := by
    rw [odGapRecoverLeafBlockInstrs]
    refine Eq.trans (gap_denote_add_imm calls env s "%.off" "%6" (by block_lk) _) ?_
    refine Eq.trans (gap_denote_icmp_ule_imm calls
      (("%.off", .int 8 (gapOff (gapByte byte))) :: env) s
      "%SwitchLeaf" "%.off" (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%SwitchLeaf", .int 1 (evalICmp .ule (gapOff (gapByte byte))
        (BitVec.ofNat 8 1))) :: ("%.off", .int 8 (gapOff (gapByte byte))) :: env) s)
      (Term.condbr (Operand.reg "%SwitchLeaf") "while.end" "while.body") =
    .jump (stateAt (("%SwitchLeaf", .int 1 (evalICmp .ule (gapOff (gapByte byte))
        (BitVec.ofNat 8 1))) :: ("%.off", .int 8 (gapOff (gapByte byte))) :: env)
      { s with pc := "while.body", pre := some "LeafBlock" }) := by
    rw [gap_execTerm_condbr_zero
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `while.body`: `%inc == %cond` selects cleanup82. -/
theorem gap_step_whileBody_toCleanup {calls : Calls} {env : Env} {s : State}
    {c ip : Nat}
    (hpc : s.pc = "while.body")
    (hinc : lookupName env "%ee.011" = some (.int 64 (BitVec.ofNat 64 c)))
    (hcond : lookupName env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hbit : evalICmp .eq (BitVec.ofNat 64 c + 1) (BitVec.ofNat 64 ip) = 1#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
            (BitVec.ofNat 64 ip))) ::
          ("%inc", .int 64 (BitVec.ofNat 64 c + 1)) :: env)
        { s with pc := "cleanup82", pre := some "while.body" }) := by
  have hpc' : (stateAt env s).pc = "while.body" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"while.body", odGapRecoverWhileBodyInstrs,
        Term.condbr (Operand.reg "%exitcond.not") "cleanup82" "land.rhs"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_while_body
  have hden : denoteCode calls odGapRecoverWhileBodyInstrs (stateAt env s) =
      some (stateAt (("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
        (BitVec.ofNat 64 ip))) :: ("%inc", .int 64 (BitVec.ofNat 64 c + 1)) :: env) s) := by
    rw [odGapRecoverWhileBodyInstrs]
    refine Eq.trans (gap_denote_add_imm calls env s "%inc" "%ee.011" (by block_lk) _) ?_
    refine Eq.trans (gap_denote_icmp_eq_reg calls
      (("%inc", .int 64 (BitVec.ofNat 64 c + 1)) :: env) s
      "%exitcond.not" "%inc" "%cond" (by block_lk) (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
        (BitVec.ofNat 64 ip))) :: ("%inc", .int 64 (BitVec.ofNat 64 c + 1)) :: env) s)
      (Term.condbr (Operand.reg "%exitcond.not") "cleanup82" "land.rhs") =
    .jump (stateAt (("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
        (BitVec.ofNat 64 ip))) :: ("%inc", .int 64 (BitVec.ofNat 64 c + 1)) :: env)
      { s with pc := "cleanup82", pre := some "while.body" }) := by
    rw [gap_execTerm_condbr_one
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `while.body`: `%inc == %cond` selects land.rhs. -/
theorem gap_step_whileBody_toLandRhs {calls : Calls} {env : Env} {s : State}
    {c ip : Nat}
    (hpc : s.pc = "while.body")
    (hinc : lookupName env "%ee.011" = some (.int 64 (BitVec.ofNat 64 c)))
    (hcond : lookupName env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hbit : evalICmp .eq (BitVec.ofNat 64 c + 1) (BitVec.ofNat 64 ip) = 0#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
            (BitVec.ofNat 64 ip))) ::
          ("%inc", .int 64 (BitVec.ofNat 64 c + 1)) :: env)
        { s with pc := "land.rhs", pre := some "while.body" }) := by
  have hpc' : (stateAt env s).pc = "while.body" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"while.body", odGapRecoverWhileBodyInstrs,
        Term.condbr (Operand.reg "%exitcond.not") "cleanup82" "land.rhs"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_while_body
  have hden : denoteCode calls odGapRecoverWhileBodyInstrs (stateAt env s) =
      some (stateAt (("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
        (BitVec.ofNat 64 ip))) :: ("%inc", .int 64 (BitVec.ofNat 64 c + 1)) :: env) s) := by
    rw [odGapRecoverWhileBodyInstrs]
    refine Eq.trans (gap_denote_add_imm calls env s "%inc" "%ee.011" (by block_lk) _) ?_
    refine Eq.trans (gap_denote_icmp_eq_reg calls
      (("%inc", .int 64 (BitVec.ofNat 64 c + 1)) :: env) s
      "%exitcond.not" "%inc" "%cond" (by block_lk) (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
        (BitVec.ofNat 64 ip))) :: ("%inc", .int 64 (BitVec.ofNat 64 c + 1)) :: env) s)
      (Term.condbr (Operand.reg "%exitcond.not") "cleanup82" "land.rhs") =
    .jump (stateAt (("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
        (BitVec.ofNat 64 ip))) :: ("%inc", .int 64 (BitVec.ofNat 64 c + 1)) :: env)
      { s with pc := "land.rhs", pre := some "while.body" }) := by
    rw [gap_execTerm_condbr_zero
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `while.end` from a leaf: the `phi` carries the counter, and `%cmp6` is false
while the counter is below `ip`, so the scan leaves for `if.end`. -/
theorem gap_step_whileEnd_fromLeaf {calls : Calls} {env : Env} {s : State}
    {c ip : Nat} {p : String}
    (hpc : s.pc = "while.end") (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("cond.end", Operand.reg "%t.0.val"), ("LeafBlock", Operand.reg "%ee.011"),
       ("LeafBlock1", Operand.reg "%ee.011"), ("LeafBlock3", Operand.reg "%ee.011")] =
        some (Operand.reg "%ee.011"))
    (h6 : lookupName env "%ee.011" = some (.int 64 (BitVec.ofNat 64 c)))
    (hcond : lookupName env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hbit : evalICmp .eq (BitVec.ofNat 64 c) (BitVec.ofNat 64 ip) = 0#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 c) (BitVec.ofNat 64 ip))) ::
          ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 c)) :: env)
        { s with pc := "if.end", pre := some "while.end" }) := by
  have hpc' : (stateAt env s).pc = "while.end" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"while.end", odGapRecoverWhileEndInstrs,
        Term.condbr (Operand.reg "%cmp6") "cleanup82" "if.end"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_while_end
  have hop : evalOperand (stateAt env s) (Operand.reg "%ee.011") =
      some (.int 64 (BitVec.ofNat 64 c)) := by
    simp only [evalOperand, stateAt]
    rw [h6]
  have hden : denoteCode calls odGapRecoverWhileEndInstrs (stateAt env s) =
      some (stateAt (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 c)
        (BitVec.ofNat 64 ip))) :: ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 c)) :: env) s) := by
    rw [odGapRecoverWhileEndInstrs]
    refine Eq.trans (denoteCode_phi calls env s "%ee.0.lcssa" (Ty.int 64)
      [("cond.end", Operand.reg "%t.0.val"), ("LeafBlock", Operand.reg "%ee.011"),
       ("LeafBlock1", Operand.reg "%ee.011"), ("LeafBlock3", Operand.reg "%ee.011")]
      (p := p) (op := Operand.reg "%ee.011") (v := .int 64 (BitVec.ofNat 64 c))
      hpre hinc hop
      [Instr.icmp "%cmp6" (IPred.eq) 64 (Operand.reg "%ee.0.lcssa") (Operand.reg "%cond")]
      (by decide)) ?_
    refine Eq.trans (gap_denote_icmp_eq_reg calls
      (("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 c)) :: env) s
      "%cmp6" "%ee.0.lcssa" "%cond" (by block_lk) (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 c)
        (BitVec.ofNat 64 ip))) :: ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 c)) :: env) s)
      (Term.condbr (Operand.reg "%cmp6") "cleanup82" "if.end") =
    .jump (stateAt (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 c)
        (BitVec.ofNat 64 ip))) :: ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 c)) :: env)
      { s with pc := "if.end", pre := some "while.end" }) := by
    rw [gap_execTerm_condbr_zero
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `while.end` from `cond.end`: the same equality test at the token's position. -/
theorem gap_step_whileEnd_fromCondEnd_scan {calls : Calls} {env : Env} {s : State}
    {c ip : Nat}
    (hpc : s.pc = "while.end") (hpre : s.pre = some "cond.end")
    (ht : lookupName env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 c)))
    (hcond : lookupName env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hbit : evalICmp .eq (BitVec.ofNat 64 c) (BitVec.ofNat 64 ip) = 0#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 c) (BitVec.ofNat 64 ip))) ::
          ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 c)) :: env)
        { s with pc := "if.end", pre := some "while.end" }) := by
  have hpc' : (stateAt env s).pc = "while.end" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"while.end", odGapRecoverWhileEndInstrs,
        Term.condbr (Operand.reg "%cmp6") "cleanup82" "if.end"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_while_end
  have hop : evalOperand (stateAt env s) (Operand.reg "%t.0.val") =
      some (.int 64 (BitVec.ofNat 64 c)) := by
    simp only [evalOperand, stateAt]
    rw [ht]
  have hinc : phiIncoming "cond.end"
      [("cond.end", Operand.reg "%t.0.val"), ("LeafBlock", Operand.reg "%ee.011"),
       ("LeafBlock1", Operand.reg "%ee.011"), ("LeafBlock3", Operand.reg "%ee.011")] =
        some (Operand.reg "%t.0.val") := by decide
  have hden : denoteCode calls odGapRecoverWhileEndInstrs (stateAt env s) =
      some (stateAt (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 c)
        (BitVec.ofNat 64 ip))) :: ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 c)) :: env) s) := by
    rw [odGapRecoverWhileEndInstrs]
    refine Eq.trans (denoteCode_phi calls env s "%ee.0.lcssa" (Ty.int 64)
      [("cond.end", Operand.reg "%t.0.val"), ("LeafBlock", Operand.reg "%ee.011"),
       ("LeafBlock1", Operand.reg "%ee.011"), ("LeafBlock3", Operand.reg "%ee.011")]
      (p := "cond.end") (op := Operand.reg "%t.0.val")
      (v := .int 64 (BitVec.ofNat 64 c)) hpre hinc hop
      [Instr.icmp "%cmp6" (IPred.eq) 64 (Operand.reg "%ee.0.lcssa") (Operand.reg "%cond")]
      (by decide)) ?_
    refine Eq.trans (gap_denote_icmp_eq_reg calls
      (("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 c)) :: env) s
      "%cmp6" "%ee.0.lcssa" "%cond" (by block_lk) (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 c)
        (BitVec.ofNat 64 ip))) :: ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 c)) :: env) s)
      (Term.condbr (Operand.reg "%cmp6") "cleanup82" "if.end") =
    .jump (stateAt (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 c)
        (BitVec.ofNat 64 ip))) :: ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 c)) :: env)
      { s with pc := "if.end", pre := some "while.end" }) := by
    rw [gap_execTerm_condbr_zero
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]



/-! ### The scan's advance prefix

From the loop head over a byte that is not whitespace, the body takes one of the
switch's three advancing leaves and re-enters `land.rhs` with the counter
incremented.  The routes are stated separately: the caller selects one from
`gapRoute_nonWs`. -/

/-- `icmp eq` is false at unequal words. -/
theorem gap_eq_zero {w : Nat} {x y : BitVec w} (h : x ≠ y) :
    evalICmp .eq x y = 0#1 := by
  simp [evalICmp, h]

/-- `icmp eq` is true at equal words. -/
theorem gap_eq_one {x y : BitVec 64} (h : x = y) :
    evalICmp .eq x y = 1#1 := by
  subst h
  exact gap_eq_self x

/-- Two `Nat` words below `2 ^ 64` that differ give unequal `i64` values. -/
theorem gap_ofNat_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    (BitVec.ofNat 64 a) ≠ (BitVec.ofNat 64 b) := by
  intro he
  apply h
  have := congrArg BitVec.toNat he
  simpa only [gap_word64 ha, gap_word64 hb] using this

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
#print axioms gap_step_NodeBlock5_toLeaf
#print axioms gap_step_NodeBlock5_toNode
#print axioms gap_step_NodeBlock_toLeaf1
#print axioms gap_step_NodeBlock_toLeaf3
#print axioms gap_step_LeafBlock3_toWhileEnd
#print axioms gap_step_LeafBlock3_toWhileBody
#print axioms gap_step_LeafBlock1_toWhileEnd
#print axioms gap_step_LeafBlock1_toWhileBody
#print axioms gap_step_LeafBlock_toWhileEnd
#print axioms gap_step_LeafBlock_toWhileBody
#print axioms gap_step_whileBody_toCleanup
#print axioms gap_step_whileBody_toLandRhs
#print axioms gap_step_whileEnd_fromLeaf
#print axioms gap_step_whileEnd_fromCondEnd_scan
#print axioms gap_eq_zero
#print axioms gap_eq_one
#print axioms gap_ofNat_ne

/-! ### The scan's byte reads

The scan's head reads one byte at a time, while the document is read as a range
(`readBytes mem b ip`).  `gapBytesAt` states the range's bytes one at a time, and
`gap_readOne` turns one of them into the one-byte `readBytes` the head's load
consumes. -/

/-- The document's bytes, as the per-byte reads a byte-walking body performs. -/
def gapBytesAt (mem : Mem) (bytes : List UInt8) (b ip : Nat) : Prop :=
  ∀ i, i < ip → readByte mem (b + i) = some (bytes.getD i 0)

/-- A range's read is the byte-by-byte one. -/
theorem gapBytesAt_of_readBytes {mem : Mem} {bytes : List UInt8} {b ip : Nat}
    (h : readBytes mem b ip = some bytes) : gapBytesAt mem bytes b ip := by
  intro i hi
  exact readByte_of_readBytes h hi

/-- The byte a one-byte load reads, as the loaded byte's encoding. -/
theorem gap_natToBytes_gapByte (byte : UInt8) :
    natToBytes (gapByte byte).toNat 1 = [byte] := by
  simp only [gapByte, natToBytes, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt byte.toNat_lt, Nat.mod_eq_of_lt byte.toNat_lt, UInt8.ofNat_toNat]

/-- The one-byte read the head's load consumes, supplied by the range's read. -/
theorem gap_readOne {mem : Mem} {bytes : List UInt8} {b ip c : Nat} {byte : UInt8}
    (h : gapBytesAt mem bytes b ip) (hc : c < ip) (hbyte : bytes.getD c 0 = byte) :
    readBytes mem (b + c) 1 = some (natToBytes (gapByte byte).toNat 1) := by
  rw [JsonEntrySteps.readBytes_one, h c hc, hbyte, gap_natToBytes_gapByte]
  rfl

/-! ### The model's prefix arithmetic

The position the scan stops at is the model's `gapEe`: the count of
non-whitespace bytes from the token's start.  The invariant carries that count as
a prefix fact — the first `c - p` bytes from `p` are non-whitespace — and these
lemmas turn it into the model's value at each of the scan's two exits. -/

/-- A dropped list's byte at an offset. -/
theorem gap_getD_drop_add (bs : List UInt8) (a i : Nat) :
    (bs.drop a).getD i 0 = bs.getD (a + i) 0 := by
  induction bs generalizing a i with
  | nil => cases a <;> cases i <;> rfl
  | cons b bs ih => cases a with
    | zero => simp
    | succ a =>
      rw [List.drop_succ_cons, ih, show a + 1 + i = a + i + 1 from by omega]
      simp [List.getD]

/-- A dropped list's first byte. -/
theorem gap_getD_drop (bs : List UInt8) (k : Nat) :
    (bs.drop k).getD 0 0 = bs.getD k 0 := by
  rw [gap_getD_drop_add, Nat.add_zero]

/-- The run from a non-whitespace prefix appends. -/
theorem gapNonWsRun_add {k m : Nat} {bs : List UInt8}
    (h : gapNonWsRun k bs = k) :
    gapNonWsRun (k + m) bs = k + gapNonWsRun m (bs.drop k) := by
  induction k generalizing bs with
  | zero => simp
  | succ k ih =>
    cases bs with
    | nil => simp [gapNonWsRun] at h
    | cons b bs =>
      simp only [gapNonWsRun] at h
      split at h
      · omega
      · rename_i hws
        have hk : gapNonWsRun k bs = k := by omega
        rw [show k + 1 + m = k + m + 1 from by omega]
        simp only [gapNonWsRun, hws, Bool.false_eq_true, ite_false, List.drop_succ_cons]
        rw [ih hk]
        omega

/-- A run that starts on a whitespace byte is zero. -/
theorem gapNonWsRun_zero_of_ws {m : Nat} {bs : List UInt8} (hm : 0 < m)
    (hws : gapIsWs (bs.getD 0 0) = true) : gapNonWsRun m bs = 0 := by
  cases m with
  | zero => omega
  | succ m =>
    cases bs with
    | nil => simp [gapIsWs] at hws
    | cons b bs =>
      have hb : gapIsWs b = true := hws
      simp [gapNonWsRun, hb]

/-- A run continues one byte past a non-whitespace prefix. -/
theorem gapNonWsRun_succ {k : Nat} {bs : List UInt8}
    (h : gapNonWsRun k bs = k) (hk : k < bs.length)
    (hws : gapIsWs (bs.getD k 0) = false) :
    gapNonWsRun (k + 1) bs = k + 1 := by
  rw [gapNonWsRun_add h]
  have hone : gapNonWsRun 1 (bs.drop k) = 1 := by
    have hne : bs.drop k ≠ [] := by
      intro hnil
      have h0 : (bs.drop k).length = 0 := by rw [hnil]; rfl
      rw [List.length_drop] at h0
      omega
    cases hd : bs.drop k with
    | nil => exact absurd hd hne
    | cons b rest =>
      have hb : gapIsWs b = false := by
        have hh := hws
        rw [← gap_getD_drop bs k] at hh
        rw [show (bs.drop k).getD 0 0 = (b :: rest).getD 0 0 from by rw [hd]] at hh
        simpa using hh
      simp [gapNonWsRun, hb]
  rw [hone]

/-- A drop of a drop. -/
theorem gap_drop_drop (bs : List UInt8) (a b : Nat) :
    (bs.drop a).drop b = bs.drop (a + b) := List.drop_drop ..

/-- **The scan's whitespace exit.**  With the first `c - p` bytes non-whitespace
and the byte at `c` a whitespace, the model's first loop has stopped at `c`. -/
theorem gapEe_of_prefix_ws {bytes : List UInt8} {ip p c : Nat}
    (hpc : p ≤ c) (hlt : c < ip)
    (hpre : gapNonWsRun (c - p) (bytes.drop p) = c - p)
    (hws : gapIsWs (bytes.getD c 0) = true) :
    gapEe bytes ip p = c := by
  unfold gapEe
  have hadd := gapNonWsRun_add (m := ip - c) hpre
  rw [show c - p + (ip - c) = ip - p from by omega] at hadd
  rw [hadd, gap_drop_drop, show p + (c - p) = c from by omega,
    gapNonWsRun_zero_of_ws (m := ip - c) (by omega)
      (by rw [gap_getD_drop]; exact hws)]
  omega

/-- **The scan's `ip` exit.**  With the first `c - p` bytes non-whitespace, the
byte at `c` not a whitespace, and `c + 1 = ip`, the model's first loop has run
the whole window: its stop is `ip`. -/
theorem gapEe_of_prefix_all {bytes : List UInt8} {ip p c : Nat}
    (hblen : bytes.length = ip) (hpc : p ≤ c) (hnext : c + 1 = ip)
    (hpre : gapNonWsRun (c - p) (bytes.drop p) = c - p)
    (hnws : gapIsWs (bytes.getD c 0) = false) :
    gapEe bytes ip p = ip := by
  unfold gapEe
  have hone : gapNonWsRun 1 (bytes.drop c) = 1 :=
    gapNonWsRun_succ (k := 0) rfl (by rw [List.length_drop, hblen]; omega)
      (by rw [gap_getD_drop]; exact hnws)
  have hadd := gapNonWsRun_add (m := ip - c) hpre
  rw [show c - p + (ip - c) = ip - p from by omega] at hadd
  rw [hadd, gap_drop_drop, show p + (c - p) = c from by omega,
    show ip - c = 1 from by omega, hone]
  omega

/-- `ofNat 64 c + 1` is the successor's word. -/
theorem gap_ofNat64_add_one {c : Nat} (hc : c + 1 < 2 ^ 64) :
    BitVec.ofNat 64 c + 1 = BitVec.ofNat 64 (c + 1) := by
  have hc' : c < 2 ^ 64 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hc',
    Nat.mod_eq_of_lt hc]

/-! ### The scan's invariant

The head `land.rhs` carries the counter `c` in the cell its `phi` selects: the
token's position on the first visit (`%t.0.val`, from `cond.end`) and the
incremented counter on every later one (`%inc`, from `while.body`), so the
predecessor picks which cell the counter lives in.  The budget `ip ≤ c + r` is
what `BoundLoop` consumes as its measure, and `gapNonWsRun`'s prefix fact is the
model's: every byte from the token's start to `c` is non-whitespace. -/

/-- The counter the head's `phi` carries, by predecessor. -/
def gapScanCarried (s : State) (c : Nat) : Prop :=
  (s.pre = some "cond.end" ∧
    lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 c))) ∨
  (s.pre = some "while.body" ∧
    lookupName s.env "%inc" = some (.int 64 (BitVec.ofNat 64 c)))

/-- The scan's invariant at `land.rhs`: the head's own block, the caller's memory,
the two cells a step reads besides the counter (`%0` the document's base and
`%cond` the window's end), the carried counter, the window's arithmetic —
`p ≤ c < ip < 2 ^ 63`, the last because the head's `gep i8` signs the counter —
the budget `ip ≤ c + r`, and the model's no-whitespace prefix. -/
def gapScanInv (bytes : List UInt8) (ip b p : Nat) (mem : Mem)
    (r : Nat) (s : State) (c : Nat) : Prop :=
  s.pc = "land.rhs" ∧ s.mem = mem ∧
  lookupName s.env "%0" = some (.ptr b) ∧
  lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)) ∧
  lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 p)) ∧
  gapScanCarried s c ∧
  p ≤ c ∧ c < ip ∧ ip < 2 ^ 63 ∧ ip ≤ c + r ∧
  gapNonWsRun (c - p) (bytes.drop p) = c - p

/-- The head's exit test: the byte at the counter is a whitespace, or the counter
is the window's last position. -/
def gapScanAtBound (bytes : List UInt8) (ip : Nat) (_s : State) (c : Nat) : Bool :=
  gapIsWs (bytes.getD c 0) || decide (c + 1 = ip)

/-- The scan's exit word: at `while.end` the counter is the model's `ee` — the
first whitespace — and at `cleanup82` the model's `ee` is `ip`.  The cells the
exit's continuation reads are here, and so is the predecessor, because the
`while.end` `phi` selects by it. -/
def gapScanExit (bytes : List UInt8) (b ip p : Nat) (mem : Mem) (e : State) : Prop :=
  (∃ (leaf : String) (c : Nat),
      e.pc = "while.end" ∧ e.pre = some leaf ∧ e.mem = mem ∧
      phiIncoming leaf
          [("cond.end", Operand.reg "%t.0.val"), ("LeafBlock", Operand.reg "%ee.011"),
           ("LeafBlock1", Operand.reg "%ee.011"),
           ("LeafBlock3", Operand.reg "%ee.011")] = some (Operand.reg "%ee.011") ∧
      lookupName e.env "%ee.011" = some (.int 64 (BitVec.ofNat 64 c)) ∧
      lookupName e.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)) ∧
      lookupName e.env "%0" = some (.ptr b) ∧
      lookupName e.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 p)) ∧
      gapEe bytes ip p = c ∧ c < ip)
  ∨ (e.pc = "cleanup82" ∧ e.mem = mem ∧ gapEe bytes ip p = ip)

/-- The invariant at the head's first visit: the token's start is the counter,
and the budget is the whole bound. -/
theorem gapScanInv_seed {bytes : List UInt8} {ip b p : Nat} {mem : Mem} {s : State}
    (hp : p < ip) (hiplt : ip < 2 ^ 63)
    (hpc : s.pc = "land.rhs") (hpre : s.pre = some "cond.end") (hmem : s.mem = mem)
    (hb : lookupName s.env "%0" = some (.ptr b))
    (ht : lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 p)))
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip))) :
    gapScanInv bytes ip b p mem ip s p :=
  ⟨hpc, hmem, hb, hcond, ht, Or.inl ⟨hpre, ht⟩, le_rfl, hp, hiplt, by omega,
    by simp [gapNonWsRun]⟩

/-! ### The scan's three prefixes

Each is the `∃ j ≤ cost` shape `BoundLoop`'s arms consume: at an exit the state
leaves with `gapScanExit`, and on the advance the invariant holds one counter
further with one unit of the budget spent.  `cost = 5` is the longest of the
three, the advance and the `ip` exit. -/

/-- **The scan's whitespace exit.**  From the head over a whitespace byte, three
control steps (`'\t'`/`'\n'`) or four (`'\r'`/`' '`) reach `while.end`, the counter
being the model's `ee`. -/
theorem gap_scan_exit_ws {calls : Calls} {bytes : List UInt8} {ip b p r c : Nat}
    {mem : Mem} {s : State}
    (hbytes : gapBytesAt mem bytes b ip)
    (hinv : gapScanInv bytes ip b p mem r s c)
    (hws : gapIsWs (bytes.getD c 0) = true) :
    ∃ (e : State) (j : Nat), j ≤ 4 ∧ (e.pc = "while.end" ∨ e.pc = "cleanup82") ∧
      gapScanExit bytes b ip p mem e ∧
      ∀ k, runFuel calls (j + k) odGapRecoverBody s =
        runFuel calls k odGapRecoverBody e := by
  obtain ⟨hpc, hmem, hb, hcond, _htv, hcarried, hple, hclt, hiplt, _hbud, hpre⟩ := hinv
  have hc63 : c < 2 ^ 63 := by omega
  have hbytes' : gapBytesAt s.mem bytes b ip := by rw [hmem]; exact hbytes
  have hread : readBytes s.mem (b + c) 1
      = some (natToBytes (gapByte (bytes.getD c 0)).toNat 1) :=
    gap_readOne hbytes' hclt rfl
  have hee : gapEe bytes ip p = c := gapEe_of_prefix_ws hple hclt hpre hws
  let s1 : State := stateAt (gapLandRhsEnv s.env b c (bytes.getD c 0))
    { s with pc := "NodeBlock5", pre := some "land.rhs" }
  have h1 : step calls odGapRecoverBody s = .jump s1 := by
    rcases hcarried with ⟨hpre0, ht⟩ | ⟨hpre0, hinc⟩
    · have hh := gap_step_landRhs_condEnd (calls := calls) (env := s.env) (s := s)
        (b := b) (c := c) (byte := bytes.getD c 0) hpc hpre0 hb ht hread hc63
      have hst : stateAt s.env s = s := rfl
      simpa only [hst, s1] using hh
    · have hh := gap_step_landRhs_whileBody (calls := calls) (env := s.env) (s := s)
        (b := b) (c := c) (byte := bytes.getD c 0) hpc hpre0 hb hinc hread hc63
      have hst : stateAt s.env s = s := rfl
      simpa only [hst, s1] using hh
  have hs1 : lookupName s1.env "%6" = some (.int 8 (gapByte (bytes.getD c 0))) := by
    simp only [s1, stateAt, gapLandRhsEnv]
    block_lk
  have hroute := gapRoute_ws hws
  rcases hroute with ⟨hb1, hb2⟩ | ⟨hb1, hb3, hb4⟩ | ⟨hb1, hb3, hb5⟩
  · -- `\t`/`\n`: `NodeBlock5` → `LeafBlock` → `while.end`
    let s2 : State := stateAt
      (("%Pivot6", .int 1 (evalICmp .slt (gapByte (bytes.getD c 0))
        (BitVec.ofNat 8 13))) :: s1.env)
      { s1 with pc := "LeafBlock", pre := some "NodeBlock5" }
    have h2 : step calls odGapRecoverBody s1 = .jump s2 := by
      have hh := gap_step_NodeBlock5_toLeaf (calls := calls) (env := s1.env) (s := s1)
        (byte := bytes.getD c 0) rfl rfl hs1 hb1
      have hst : stateAt s1.env s1 = s1 := rfl
      simpa only [hst, s2] using hh
    have hs2 : lookupName s2.env "%6" = some (.int 8 (gapByte (bytes.getD c 0))) := by
      simp only [s2, stateAt]
      block_lk
    let s3 : State := stateAt
      (("%SwitchLeaf", .int 1 (evalICmp .ule (gapOff (gapByte (bytes.getD c 0)))
          (BitVec.ofNat 8 1))) ::
        ("%.off", .int 8 (gapOff (gapByte (bytes.getD c 0)))) :: s2.env)
      { s2 with pc := "while.end", pre := some "LeafBlock" }
    have h3 : step calls odGapRecoverBody s2 = .jump s3 := by
      have hh := gap_step_LeafBlock_toWhileEnd (calls := calls) (env := s2.env) (s := s2)
        (byte := bytes.getD c 0) rfl rfl hs2 hb2
      have hst : stateAt s2.env s2 = s2 := rfl
      simpa only [hst, s3] using hh
    refine ⟨s3, 3, by omega, Or.inl rfl, ?_, ?_⟩
    · refine Or.inl ⟨"LeafBlock", c, rfl, rfl, ?_, by decide, ?_, ?_, ?_, ?_, hee, hclt⟩
      · simp only [s3, stateAt]; exact hmem
      · simp only [s3, s2, s1, stateAt, gapLandRhsEnv]
        block_lk
      · simp only [s3, s2, s1, stateAt, gapLandRhsEnv]
        block_lk
      · simp only [s3, s2, s1, stateAt, gapLandRhsEnv]
        block_lk
      · simp only [s3, s2, s1, stateAt, gapLandRhsEnv]
        block_lk
    · intro k
      rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
        runFuel_jump_prefix h1 (1 + (1 + k)),
        runFuel_jump_prefix h2 (1 + k), runFuel_jump_prefix h3 k]
  · -- `\r`: `NodeBlock5` → `NodeBlock` → `LeafBlock1` → `while.end`
    let s2 : State := stateAt
      (("%Pivot6", .int 1 (evalICmp .slt (gapByte (bytes.getD c 0))
        (BitVec.ofNat 8 13))) :: s1.env)
      { s1 with pc := "NodeBlock", pre := some "NodeBlock5" }
    have h2 : step calls odGapRecoverBody s1 = .jump s2 := by
      have hh := gap_step_NodeBlock5_toNode (calls := calls) (env := s1.env) (s := s1)
        (byte := bytes.getD c 0) rfl rfl hs1 hb1
      have hst : stateAt s1.env s1 = s1 := rfl
      simpa only [hst, s2] using hh
    have hs2 : lookupName s2.env "%6" = some (.int 8 (gapByte (bytes.getD c 0))) := by
      simp only [s2, stateAt]
      block_lk
    let s3 : State := stateAt
      (("%Pivot", .int 1 (evalICmp .slt (gapByte (bytes.getD c 0))
        (BitVec.ofNat 8 32))) :: s2.env)
      { s2 with pc := "LeafBlock1", pre := some "NodeBlock" }
    have h3 : step calls odGapRecoverBody s2 = .jump s3 := by
      have hh := gap_step_NodeBlock_toLeaf1 (calls := calls) (env := s2.env) (s := s2)
        (byte := bytes.getD c 0) rfl rfl hs2 hb3
      have hst : stateAt s2.env s2 = s2 := rfl
      simpa only [hst, s3] using hh
    have hs3 : lookupName s3.env "%6" = some (.int 8 (gapByte (bytes.getD c 0))) := by
      simp only [s3, stateAt]
      block_lk
    let s4 : State := stateAt
      (("%SwitchLeaf2", .int 1 (evalICmp .eq (gapByte (bytes.getD c 0))
        (BitVec.ofNat 8 13))) :: s3.env)
      { s3 with pc := "while.end", pre := some "LeafBlock1" }
    have h4 : step calls odGapRecoverBody s3 = .jump s4 := by
      have hh := gap_step_LeafBlock1_toWhileEnd (calls := calls) (env := s3.env) (s := s3)
        (byte := bytes.getD c 0) rfl rfl hs3 hb4
      have hst : stateAt s3.env s3 = s3 := rfl
      simpa only [hst, s4] using hh
    refine ⟨s4, 4, by omega, Or.inl rfl, ?_, ?_⟩
    · refine Or.inl ⟨"LeafBlock1", c, rfl, rfl, ?_, by decide, ?_, ?_, ?_, ?_, hee, hclt⟩
      · simp only [s4, stateAt]; exact hmem
      · simp only [s4, s3, s2, s1, stateAt, gapLandRhsEnv]
        block_lk
      · simp only [s4, s3, s2, s1, stateAt, gapLandRhsEnv]
        block_lk
      · simp only [s4, s3, s2, s1, stateAt, gapLandRhsEnv]
        block_lk
      · simp only [s4, s3, s2, s1, stateAt, gapLandRhsEnv]
        block_lk
    · intro k
      rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
        runFuel_jump_prefix h1 (1 + (1 + (1 + k))),
        runFuel_jump_prefix h2 (1 + (1 + k)),
        runFuel_jump_prefix h3 (1 + k), runFuel_jump_prefix h4 k]
  · -- `\ `: `NodeBlock5` → `NodeBlock` → `LeafBlock3` → `while.end`
    let s2 : State := stateAt
      (("%Pivot6", .int 1 (evalICmp .slt (gapByte (bytes.getD c 0))
        (BitVec.ofNat 8 13))) :: s1.env)
      { s1 with pc := "NodeBlock", pre := some "NodeBlock5" }
    have h2 : step calls odGapRecoverBody s1 = .jump s2 := by
      have hh := gap_step_NodeBlock5_toNode (calls := calls) (env := s1.env) (s := s1)
        (byte := bytes.getD c 0) rfl rfl hs1 hb1
      have hst : stateAt s1.env s1 = s1 := rfl
      simpa only [hst, s2] using hh
    have hs2 : lookupName s2.env "%6" = some (.int 8 (gapByte (bytes.getD c 0))) := by
      simp only [s2, stateAt]
      block_lk
    let s3 : State := stateAt
      (("%Pivot", .int 1 (evalICmp .slt (gapByte (bytes.getD c 0))
        (BitVec.ofNat 8 32))) :: s2.env)
      { s2 with pc := "LeafBlock3", pre := some "NodeBlock" }
    have h3 : step calls odGapRecoverBody s2 = .jump s3 := by
      have hh := gap_step_NodeBlock_toLeaf3 (calls := calls) (env := s2.env) (s := s2)
        (byte := bytes.getD c 0) rfl rfl hs2 hb3
      have hst : stateAt s2.env s2 = s2 := rfl
      simpa only [hst, s3] using hh
    have hs3 : lookupName s3.env "%6" = some (.int 8 (gapByte (bytes.getD c 0))) := by
      simp only [s3, stateAt]
      block_lk
    let s4 : State := stateAt
      (("%SwitchLeaf4", .int 1 (evalICmp .eq (gapByte (bytes.getD c 0))
        (BitVec.ofNat 8 32))) :: s3.env)
      { s3 with pc := "while.end", pre := some "LeafBlock3" }
    have h4 : step calls odGapRecoverBody s3 = .jump s4 := by
      have hh := gap_step_LeafBlock3_toWhileEnd (calls := calls) (env := s3.env) (s := s3)
        (byte := bytes.getD c 0) rfl rfl hs3 hb5
      have hst : stateAt s3.env s3 = s3 := rfl
      simpa only [hst, s4] using hh
    refine ⟨s4, 4, by omega, Or.inl rfl, ?_, ?_⟩
    · refine Or.inl ⟨"LeafBlock3", c, rfl, rfl, ?_, by decide, ?_, ?_, ?_, ?_, hee, hclt⟩
      · simp only [s4, stateAt]; exact hmem
      · simp only [s4, s3, s2, s1, stateAt, gapLandRhsEnv]
        block_lk
      · simp only [s4, s3, s2, s1, stateAt, gapLandRhsEnv]
        block_lk
      · simp only [s4, s3, s2, s1, stateAt, gapLandRhsEnv]
        block_lk
      · simp only [s4, s3, s2, s1, stateAt, gapLandRhsEnv]
        block_lk
    · intro k
      rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
        runFuel_jump_prefix h1 (1 + (1 + (1 + k))),
        runFuel_jump_prefix h2 (1 + (1 + k)),
        runFuel_jump_prefix h3 (1 + k), runFuel_jump_prefix h4 k]

/-- **The scan's advance head.**  From the head over a non-whitespace byte, three
control steps (`'\t'`/`'\n'`) or four (`'\r'`/`' '`) — the switch's three
advancing routes — reach `while.body`, and the cells its own step reads are still
bound. -/
theorem gap_scan_toWhileBody {calls : Calls} {bytes : List UInt8} {ip b p r c : Nat}
    {mem : Mem} {s : State}
    (hbytes : gapBytesAt mem bytes b ip)
    (hinv : gapScanInv bytes ip b p mem r s c)
    (hnws : gapIsWs (bytes.getD c 0) = false) :
    ∃ (e : State) (j : Nat), j ≤ 4 ∧ e.pc = "while.body" ∧ e.mem = mem ∧
      lookupName e.env "%ee.011" = some (.int 64 (BitVec.ofNat 64 c)) ∧
      lookupName e.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)) ∧
      lookupName e.env "%0" = some (.ptr b) ∧
      lookupName e.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 p)) ∧
      ∀ k, runFuel calls (j + k) odGapRecoverBody s =
        runFuel calls k odGapRecoverBody e := by
  obtain ⟨hpc, hmem, hb, hcond, _h0v, hcarried, _hple, hclt, hiplt, _hbud, _hpre⟩ := hinv
  have hc63 : c < 2 ^ 63 := by omega
  have hbytes' : gapBytesAt s.mem bytes b ip := by rw [hmem]; exact hbytes
  have hread : readBytes s.mem (b + c) 1
      = some (natToBytes (gapByte (bytes.getD c 0)).toNat 1) :=
    gap_readOne hbytes' hclt rfl
  let s1 : State := stateAt (gapLandRhsEnv s.env b c (bytes.getD c 0))
    { s with pc := "NodeBlock5", pre := some "land.rhs" }
  have h1 : step calls odGapRecoverBody s = .jump s1 := by
    rcases hcarried with ⟨hpre0, ht⟩ | ⟨hpre0, hinc⟩
    · have hh := gap_step_landRhs_condEnd (calls := calls) (env := s.env) (s := s)
        (b := b) (c := c) (byte := bytes.getD c 0) hpc hpre0 hb ht hread hc63
      have hst : stateAt s.env s = s := rfl
      simpa only [hst, s1] using hh
    · have hh := gap_step_landRhs_whileBody (calls := calls) (env := s.env) (s := s)
        (b := b) (c := c) (byte := bytes.getD c 0) hpc hpre0 hb hinc hread hc63
      have hst : stateAt s.env s = s := rfl
      simpa only [hst, s1] using hh
  have hs1 : lookupName s1.env "%6" = some (.int 8 (gapByte (bytes.getD c 0))) := by
    simp only [s1, stateAt, gapLandRhsEnv]
    block_lk
  have hroute := gapRoute_nonWs hnws
  rcases hroute with ⟨hb1, hb2⟩ | ⟨hb1, hb3, hb4⟩ | ⟨hb1, hb3, hb5⟩
  · -- `\t`/`\n`: `LeafBlock` advances
    let s2 : State := stateAt
      (("%Pivot6", .int 1 (evalICmp .slt (gapByte (bytes.getD c 0))
        (BitVec.ofNat 8 13))) :: s1.env)
      { s1 with pc := "LeafBlock", pre := some "NodeBlock5" }
    have h2 : step calls odGapRecoverBody s1 = .jump s2 := by
      have hh := gap_step_NodeBlock5_toLeaf (calls := calls) (env := s1.env) (s := s1)
        (byte := bytes.getD c 0) rfl rfl hs1 hb1
      have hst : stateAt s1.env s1 = s1 := rfl
      simpa only [hst, s2] using hh
    have hs2 : lookupName s2.env "%6" = some (.int 8 (gapByte (bytes.getD c 0))) := by
      simp only [s2, stateAt]
      block_lk
    let s3 : State := stateAt
      (("%SwitchLeaf", .int 1 (evalICmp .ule (gapOff (gapByte (bytes.getD c 0)))
          (BitVec.ofNat 8 1))) ::
        ("%.off", .int 8 (gapOff (gapByte (bytes.getD c 0)))) :: s2.env)
      { s2 with pc := "while.body", pre := some "LeafBlock" }
    have h3 : step calls odGapRecoverBody s2 = .jump s3 := by
      have hh := gap_step_LeafBlock_toWhileBody (calls := calls) (env := s2.env) (s := s2)
        (byte := bytes.getD c 0) rfl rfl hs2 hb2
      have hst : stateAt s2.env s2 = s2 := rfl
      simpa only [hst, s3] using hh
    refine ⟨s3, 3, by omega, rfl, hmem, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [s3, s2, s1, stateAt, gapLandRhsEnv]
      block_lk
    · simp only [s3, s2, s1, stateAt, gapLandRhsEnv]
      block_lk
    · simp only [s3, s2, s1, stateAt, gapLandRhsEnv]
      block_lk
    · simp only [s3, s2, s1, stateAt, gapLandRhsEnv]
      block_lk
    · intro k
      rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
        runFuel_jump_prefix h1 (1 + (1 + k)),
        runFuel_jump_prefix h2 (1 + k), runFuel_jump_prefix h3 k]
  · -- `\r`: `LeafBlock1` advances
    let s2 : State := stateAt
      (("%Pivot6", .int 1 (evalICmp .slt (gapByte (bytes.getD c 0))
        (BitVec.ofNat 8 13))) :: s1.env)
      { s1 with pc := "NodeBlock", pre := some "NodeBlock5" }
    have h2 : step calls odGapRecoverBody s1 = .jump s2 := by
      have hh := gap_step_NodeBlock5_toNode (calls := calls) (env := s1.env) (s := s1)
        (byte := bytes.getD c 0) rfl rfl hs1 hb1
      have hst : stateAt s1.env s1 = s1 := rfl
      simpa only [hst, s2] using hh
    have hs2 : lookupName s2.env "%6" = some (.int 8 (gapByte (bytes.getD c 0))) := by
      simp only [s2, stateAt]
      block_lk
    let s3 : State := stateAt
      (("%Pivot", .int 1 (evalICmp .slt (gapByte (bytes.getD c 0))
        (BitVec.ofNat 8 32))) :: s2.env)
      { s2 with pc := "LeafBlock1", pre := some "NodeBlock" }
    have h3 : step calls odGapRecoverBody s2 = .jump s3 := by
      have hh := gap_step_NodeBlock_toLeaf1 (calls := calls) (env := s2.env) (s := s2)
        (byte := bytes.getD c 0) rfl rfl hs2 hb3
      have hst : stateAt s2.env s2 = s2 := rfl
      simpa only [hst, s3] using hh
    have hs3 : lookupName s3.env "%6" = some (.int 8 (gapByte (bytes.getD c 0))) := by
      simp only [s3, stateAt]
      block_lk
    let s4 : State := stateAt
      (("%SwitchLeaf2", .int 1 (evalICmp .eq (gapByte (bytes.getD c 0))
        (BitVec.ofNat 8 13))) :: s3.env)
      { s3 with pc := "while.body", pre := some "LeafBlock1" }
    have h4 : step calls odGapRecoverBody s3 = .jump s4 := by
      have hh := gap_step_LeafBlock1_toWhileBody (calls := calls) (env := s3.env) (s := s3)
        (byte := bytes.getD c 0) rfl rfl hs3 hb4
      have hst : stateAt s3.env s3 = s3 := rfl
      simpa only [hst, s4] using hh
    refine ⟨s4, 4, by omega, rfl, hmem, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [s4, s3, s2, s1, stateAt, gapLandRhsEnv]
      block_lk
    · simp only [s4, s3, s2, s1, stateAt, gapLandRhsEnv]
      block_lk
    · simp only [s4, s3, s2, s1, stateAt, gapLandRhsEnv]
      block_lk
    · simp only [s4, s3, s2, s1, stateAt, gapLandRhsEnv]
      block_lk
    · intro k
      rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
        runFuel_jump_prefix h1 (1 + (1 + (1 + k))),
        runFuel_jump_prefix h2 (1 + (1 + k)),
        runFuel_jump_prefix h3 (1 + k), runFuel_jump_prefix h4 k]
  · -- `\ `: `LeafBlock3` advances
    let s2 : State := stateAt
      (("%Pivot6", .int 1 (evalICmp .slt (gapByte (bytes.getD c 0))
        (BitVec.ofNat 8 13))) :: s1.env)
      { s1 with pc := "NodeBlock", pre := some "NodeBlock5" }
    have h2 : step calls odGapRecoverBody s1 = .jump s2 := by
      have hh := gap_step_NodeBlock5_toNode (calls := calls) (env := s1.env) (s := s1)
        (byte := bytes.getD c 0) rfl rfl hs1 hb1
      have hst : stateAt s1.env s1 = s1 := rfl
      simpa only [hst, s2] using hh
    have hs2 : lookupName s2.env "%6" = some (.int 8 (gapByte (bytes.getD c 0))) := by
      simp only [s2, stateAt]
      block_lk
    let s3 : State := stateAt
      (("%Pivot", .int 1 (evalICmp .slt (gapByte (bytes.getD c 0))
        (BitVec.ofNat 8 32))) :: s2.env)
      { s2 with pc := "LeafBlock3", pre := some "NodeBlock" }
    have h3 : step calls odGapRecoverBody s2 = .jump s3 := by
      have hh := gap_step_NodeBlock_toLeaf3 (calls := calls) (env := s2.env) (s := s2)
        (byte := bytes.getD c 0) rfl rfl hs2 hb3
      have hst : stateAt s2.env s2 = s2 := rfl
      simpa only [hst, s3] using hh
    have hs3 : lookupName s3.env "%6" = some (.int 8 (gapByte (bytes.getD c 0))) := by
      simp only [s3, stateAt]
      block_lk
    let s4 : State := stateAt
      (("%SwitchLeaf4", .int 1 (evalICmp .eq (gapByte (bytes.getD c 0))
        (BitVec.ofNat 8 32))) :: s3.env)
      { s3 with pc := "while.body", pre := some "LeafBlock3" }
    have h4 : step calls odGapRecoverBody s3 = .jump s4 := by
      have hh := gap_step_LeafBlock3_toWhileBody (calls := calls) (env := s3.env) (s := s3)
        (byte := bytes.getD c 0) rfl rfl hs3 hb5
      have hst : stateAt s3.env s3 = s3 := rfl
      simpa only [hst, s4] using hh
    refine ⟨s4, 4, by omega, rfl, hmem, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [s4, s3, s2, s1, stateAt, gapLandRhsEnv]
      block_lk
    · simp only [s4, s3, s2, s1, stateAt, gapLandRhsEnv]
      block_lk
    · simp only [s4, s3, s2, s1, stateAt, gapLandRhsEnv]
      block_lk
    · simp only [s4, s3, s2, s1, stateAt, gapLandRhsEnv]
      block_lk
    · intro k
      rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
        runFuel_jump_prefix h1 (1 + (1 + (1 + k))),
        runFuel_jump_prefix h2 (1 + (1 + k)),
        runFuel_jump_prefix h3 (1 + k), runFuel_jump_prefix h4 k]

/-- `while.body`'s exit bit at the window's end: the increment is `ip`. -/
theorem gap_scan_atIp_bit {c ip : Nat} (hip64 : ip < 2 ^ 64) (hnext : c + 1 = ip) :
    evalICmp .eq (BitVec.ofNat 64 c + 1) (BitVec.ofNat 64 ip) = 1#1 := by
  rw [gap_ofNat64_add_one (by omega), hnext]
  exact gap_eq_self _

/-- `while.body`'s exit bit off the window's end. -/
theorem gap_scan_offIp_bit {c ip : Nat} (hclt : c < ip) (hip64 : ip < 2 ^ 64)
    (hnext : c + 1 ≠ ip) :
    evalICmp .eq (BitVec.ofNat 64 c + 1) (BitVec.ofNat 64 ip) = 0#1 := by
  rw [gap_ofNat64_add_one (by omega)]
  exact gap_eq_zero (gap_ofNat_ne (by omega) hip64 hnext)

/-- **The scan's `ip` exit.**  From the head over a non-whitespace byte whose
successor is the window's end, five control steps reach `cleanup82`, and the
model's first loop has run the whole window. -/
theorem gap_scan_exit_ip {calls : Calls} {bytes : List UInt8} {ip b p r c : Nat}
    {mem : Mem} {s : State}
    (hbytes : gapBytesAt mem bytes b ip) (hblen : bytes.length = ip)
    (hinv : gapScanInv bytes ip b p mem r s c)
    (hnws : gapIsWs (bytes.getD c 0) = false) (hnext : c + 1 = ip) :
    ∃ (e : State) (j : Nat), j ≤ 5 ∧ (e.pc = "while.end" ∨ e.pc = "cleanup82") ∧
      gapScanExit bytes b ip p mem e ∧
      ∀ k, runFuel calls (j + k) odGapRecoverBody s =
        runFuel calls k odGapRecoverBody e := by
  obtain ⟨e1, j1, hj1, hpc1, hmem1, h6cell, hcond1, _h0cell, _htcell, hrun1⟩ :=
    gap_scan_toWhileBody (calls := calls) hbytes hinv hnws
  obtain ⟨hpc, hmem, hb, hcond, _htv, hcarried, hple, hclt, hiplt, _hbud, hpre⟩ := hinv
  have hip64 : ip < 2 ^ 64 := by omega
  have hee : gapEe bytes ip p = ip := gapEe_of_prefix_all hblen hple hnext hpre hnws
  have hbit : evalICmp .eq (BitVec.ofNat 64 c + 1) (BitVec.ofNat 64 ip) = 1#1 :=
    gap_scan_atIp_bit hip64 hnext
  let sE : State := stateAt
    (("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
        (BitVec.ofNat 64 ip))) ::
      ("%inc", .int 64 (BitVec.ofNat 64 c + 1)) :: e1.env)
    { e1 with pc := "cleanup82", pre := some "while.body" }
  have hstep : step calls odGapRecoverBody e1 = .jump sE := by
    have hh := gap_step_whileBody_toCleanup (calls := calls) (env := e1.env) (s := e1)
      (c := c) (ip := ip) hpc1 h6cell hcond1 hbit
    have hst : stateAt e1.env e1 = e1 := rfl
    simpa only [hst, sE] using hh
  refine ⟨sE, j1 + 1, by omega, Or.inr rfl, Or.inr ⟨rfl, ?_, hee⟩, ?_⟩
  · simpa only [sE, stateAt] using hmem1
  intro k
  rw [show j1 + 1 + k = j1 + (1 + k) from by omega, hrun1 (1 + k),
    runFuel_jump_prefix hstep k]

/-- **The scan's advance.**  From the head over a non-whitespace byte whose
successor is still inside the window, five control steps re-enter `land.rhs` with
the counter advanced and the invariant at one unit of budget less. -/
theorem gap_scan_step_loop {calls : Calls} {bytes : List UInt8} {ip b p r c : Nat}
    {mem : Mem} {s : State}
    (hbytes : gapBytesAt mem bytes b ip) (hblen : bytes.length = ip)
    (hinv : gapScanInv bytes ip b p mem (r + 1) s c)
    (hnws : gapIsWs (bytes.getD c 0) = false) (hnext : c + 1 ≠ ip) :
    ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 5 ∧ e.pc = "land.rhs" ∧ c < c' ∧
      gapScanInv bytes ip b p mem r e c' ∧
      ∀ k, runFuel calls (j + k) odGapRecoverBody s =
        runFuel calls k odGapRecoverBody e := by
  obtain ⟨e1, j1, hj1, hpc1, hmem1, h6cell, hcond1, h0cell, htcell1, hrun1⟩ :=
    gap_scan_toWhileBody (calls := calls) hbytes hinv hnws
  obtain ⟨hpc, hmem, hb, hcond, _htv, hcarried, hple, hclt, hiplt, hbud, hpre⟩ := hinv
  have hip64 : ip < 2 ^ 64 := by omega
  have hkp : c - p < (bytes.drop p).length := by
    rw [List.length_drop, hblen]; omega
  have hbit : evalICmp .eq (BitVec.ofNat 64 c + 1) (BitVec.ofNat 64 ip) = 0#1 :=
    gap_scan_offIp_bit hclt hip64 hnext
  let sE : State := stateAt
    (("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
        (BitVec.ofNat 64 ip))) ::
      ("%inc", .int 64 (BitVec.ofNat 64 c + 1)) :: e1.env)
    { e1 with pc := "land.rhs", pre := some "while.body" }
  have hstep : step calls odGapRecoverBody e1 = .jump sE := by
    have hh := gap_step_whileBody_toLandRhs (calls := calls) (env := e1.env) (s := e1)
      (c := c) (ip := ip) hpc1 h6cell hcond1 hbit
    have hst : stateAt e1.env e1 = e1 := rfl
    simpa only [hst, sE] using hh
  have hseed : gapNonWsRun (c + 1 - p) (bytes.drop p) = c + 1 - p := by
    rw [show c + 1 - p = (c - p) + 1 from by omega,
      gapNonWsRun_succ hpre hkp
        (by rw [gap_getD_drop_add, show p + (c - p) = c from by omega]; exact hnws)]
  refine ⟨sE, c + 1, j1 + 1, by omega, rfl, by omega, ?_, ?_⟩
  · refine ⟨rfl, hmem1, ?_, ?_, ?_, Or.inr ⟨rfl, ?_⟩, by omega, by omega, hiplt,
      by omega, hseed⟩
    · simp only [sE, stateAt]
      block_lk
    · simp only [sE, stateAt]
      block_lk
    · simp only [sE, stateAt]
      block_lk
    · simp only [sE, stateAt]
      rw [gap_ofNat64_add_one (c := c) (by omega)]
      block_lk
  · intro k
    rw [show j1 + 1 + k = j1 + (1 + k) from by omega, hrun1 (1 + k),
      runFuel_jump_prefix hstep k]

/-! ### The loop instance

The instance's bound is `ip` itself, its measure the budget `ip ≤ c + r`, and its
per-iteration control-step bound the longest of the three prefixes: the advance
and the `ip` exit at five, the whitespace exit at four.  The exits are
`while.end` and `cleanup82`, because the scan leaves by the switch on a
whitespace and by `while.body`'s test at the window's end. -/

/-- The scan's exits: `while.end` on a whitespace, `cleanup82` at the window's
end. -/
def gapScanExitBlock (e : State) : Prop := e.pc = "while.end" ∨ e.pc = "cleanup82"

/-- **The scan as a `BoundLoop`.**  The budget's zero edge is empty: the invariant
asks for `c < ip` and for `ip ≤ c`, so no head state carries zero budget, and the
induction's base case cannot fire.  The exits are the loop's two tests — the
switch on a whitespace and `while.body`'s equality with `ip` — and the bound `ip`
is what `run` turns into `(ip + 1) * 5`. -/
def gapScanLoop (calls : Calls) (bytes : List UInt8) (ip b p : Nat) (mem : Mem)
    (hbytes : gapBytesAt mem bytes b ip) (hblen : bytes.length = ip) :
    BoundLoop calls odGapRecoverBody where
  head := "land.rhs"
  exitBlock := "while.end"
  N := ip
  cost := 5
  Inv := gapScanInv bytes ip b p mem
  atBound := gapScanAtBound bytes ip
  Exit := gapScanExitBlock
  ExitWord := gapScanExit bytes b ip p mem
  step_exit := by
    intro r s c hinv hat
    unfold gapScanAtBound at hat
    by_cases hws : gapIsWs (bytes.getD c 0) = true
    · obtain ⟨e, j, hj, hexit, hword, hrun⟩ := gap_scan_exit_ws hbytes hinv hws
      exact ⟨e, j, by omega, hexit, hword, hrun⟩
    · have hfalse : gapIsWs (bytes.getD c 0) = false := by
        cases h : gapIsWs (bytes.getD c 0) with
        | false => rfl
        | true => exact absurd h hws
      have hid : decide (c + 1 = ip) = true := by
        rcases Bool.or_eq_true_iff.mp hat with h | h
        · exact absurd h hws
        · exact h
      exact gap_scan_exit_ip hbytes hblen hinv hfalse (of_decide_eq_true hid)
  step_loop := by
    intro r s c hinv hat
    unfold gapScanAtBound at hat
    rcases Bool.or_eq_false_iff.mp hat with ⟨hws, hid⟩
    exact gap_scan_step_loop hbytes hblen hinv hws (of_decide_eq_false hid)
  exit_at_zero := by
    intro s c hinv
    obtain ⟨_, _, _, _, _, _, _, hclt, _, hbud, _⟩ := hinv
    exact absurd hbud (by omega)
  budget := by
    intro r s c hinv
    obtain ⟨_, _, _, _, _, _, hple, _, _, hbud, _⟩ := hinv
    exact ⟨by omega, hbud⟩

/-- **The scan's run from its head.**  From `land.rhs` with `r` iterations of
budget, the scan reaches one of its exits within `(r + 1) * 5` control steps. -/
theorem gapScanLoop_run_from {calls : Calls} {bytes : List UInt8} {ip b p : Nat}
    {mem : Mem} (hbytes : gapBytesAt mem bytes b ip) (hblen : bytes.length = ip)
    (r : Nat) (s : State) (c : Nat) (h : gapScanInv bytes ip b p mem r s c) :
    ∃ (e : State) (j : Nat), j ≤ (r + 1) * 5 ∧ gapScanExitBlock e ∧
      gapScanExit bytes b ip p mem e ∧
      ∀ k, runFuel calls (j + k) odGapRecoverBody s =
        runFuel calls k odGapRecoverBody e :=
  (gapScanLoop calls bytes ip b p mem hbytes hblen).run_from r s c h

/-- **The scan's run.**  At the whole bound as its budget, the scan of the
document `[0, ip)` from the token's start reaches one of its exits within
`(ip + 1) * 5` control steps, and the run continues identically from there. -/
theorem gapScanLoop_run {calls : Calls} {bytes : List UInt8} {ip b p : Nat} {mem : Mem}
    (hbytes : gapBytesAt mem bytes b ip) (hblen : bytes.length = ip)
    (s : State) (c : Nat) (h : gapScanInv bytes ip b p mem ip s c) (k : Nat) :
    ∃ (e : State) (j : Nat), j ≤ (ip + 1) * 5 ∧ gapScanExitBlock e ∧
      gapScanExit bytes b ip p mem e ∧
      runFuel calls (j + k) odGapRecoverBody s = runFuel calls k odGapRecoverBody e :=
  (gapScanLoop calls bytes ip b p mem hbytes hblen).run s c h k

/-! ### The scan's exits, continued

The scan leaves at `while.end` on a whitespace and at `cleanup82` at the window's
end.  At `while.end` the `phi` carries the counter and `%cmp6` is the equality
with `ip`, which is false because the counter is below it; the scan continues to
`if.end` with `%ee.0.lcssa` the first whitespace.  At `cleanup82` the body returns
`void`, and the model's first loop has run the window, so its rule writes
nothing. -/

/-- The rule writes nothing when the model's first loop has run the window. -/
theorem gap_recoverWrite_none_of_ee {bytes : List UInt8} {ip p : Nat}
    (h : gapEe bytes ip p = ip) : gapRecoverWrite bytes ip p = GapWrite.none := by
  simp [gapRecoverWrite, h]

/-- **The scan's `while.end` continuation.**  With the counter the `phi` carries
below `ip`, `%cmp6` is false and the scan leaves for `if.end` carrying the first
whitespace. -/
theorem gap_scan_whileEnd_step {calls : Calls} {ip c : Nat}
    {e : State} {leaf : String}
    (hpc : e.pc = "while.end") (hpre : e.pre = some leaf)
    (hinc : phiIncoming leaf
        [("cond.end", Operand.reg "%t.0.val"), ("LeafBlock", Operand.reg "%ee.011"),
         ("LeafBlock1", Operand.reg "%ee.011"),
         ("LeafBlock3", Operand.reg "%ee.011")] = some (Operand.reg "%ee.011"))
    (h6 : lookupName e.env "%ee.011" = some (.int 64 (BitVec.ofNat 64 c)))
    (hcond : lookupName e.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hlt : c < ip) (hip64 : ip < 2 ^ 64) :
    step calls odGapRecoverBody e =
      .jump (stateAt
        (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 c) (BitVec.ofNat 64 ip))) ::
          ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 c)) :: e.env)
        { e with pc := "if.end", pre := some "while.end" }) := by
  have hbit : evalICmp .eq (BitVec.ofNat 64 c) (BitVec.ofNat 64 ip) = 0#1 :=
    gap_eq_zero (gap_ofNat_ne (by omega) hip64 (by omega))
  have hh := gap_step_whileEnd_fromLeaf (calls := calls) (env := e.env) (s := e)
    (c := c) (ip := ip) (p := leaf) hpc hpre hinc h6 hcond hbit
  have hst : stateAt e.env e = e := rfl
  simpa only [hst] using hh

/-- **At the scan's whitespace exit.**  The exit word's first arm is the basis of
the continuation: the counter is the model's `ee`, and the scan leaves
`while.end` for `if.end`. -/
theorem gap_scan_whileEnd_continue {calls : Calls} {bytes : List UInt8} {ip b p : Nat}
    {mem : Mem} {e : State} (hpc : e.pc = "while.end") (hexit : gapScanExit bytes b ip p mem e)
    (hip64 : ip < 2 ^ 64) :
    ∃ (leaf : String) (c : Nat), e.pre = some leaf ∧ gapEe bytes ip p = c ∧ c < ip ∧
      step calls odGapRecoverBody e =
        .jump (stateAt
          (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 c) (BitVec.ofNat 64 ip))) ::
            ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 c)) :: e.env)
          { e with pc := "if.end", pre := some "while.end" }) := by
  rcases hexit with ⟨leaf, c, hpc', hpre, _hmem, hinc, h6, hcond, _h0, _ht, hee, hlt⟩
      | ⟨hpc', _⟩
  · refine ⟨leaf, c, hpre, hee, hlt, ?_⟩
    exact gap_scan_whileEnd_step hpc hpre hinc h6 hcond hlt hip64
  · rw [hpc] at hpc'
    exact absurd hpc' (by decide)

/-- **At the scan's `ip` exit.**  `cleanup82` returns `void`, and the model's
rule writes nothing. -/
theorem gap_scan_cleanup82_exit {calls : Calls} {bytes : List UInt8} {ip p : Nat}
    {e : State} (hpc : e.pc = "cleanup82") (hee : gapEe bytes ip p = ip) :
    step calls odGapRecoverBody e = .ret none e ∧ gapRecoverWrite bytes ip p = GapWrite.none := by
  refine ⟨?_, gap_recoverWrite_none_of_ee hee⟩
  have hh := gap_step_cleanup82 (calls := calls) (env := e.env) (s := e) hpc
  have hst : stateAt e.env e = e := rfl
  simpa only [hst] using hh

/-- **At the scan's `ip` exit, from the exit word.** -/
theorem gap_scan_cleanup82_continue {calls : Calls} {bytes : List UInt8} {ip b p : Nat}
    {mem : Mem} {e : State} (hpc : e.pc = "cleanup82") (hexit : gapScanExit bytes b ip p mem e) :
    step calls odGapRecoverBody e = .ret none e ∧
      gapRecoverWrite bytes ip p = GapWrite.none := by
  rcases hexit with ⟨leaf, c, hpc', _⟩ | ⟨_, _hmem, hee⟩
  · rw [hpc] at hpc'
    exact absurd hpc' (by decide)
  · exact gap_scan_cleanup82_exit hpc hee

/-! ### Axiom footprints -/

#print axioms gapBytesAt_of_readBytes
#print axioms gap_natToBytes_gapByte
#print axioms gap_readOne
#print axioms gap_getD_drop_add
#print axioms gap_getD_drop
#print axioms gapNonWsRun_add
#print axioms gapNonWsRun_zero_of_ws
#print axioms gapNonWsRun_succ
#print axioms gap_drop_drop
#print axioms gapEe_of_prefix_ws
#print axioms gapEe_of_prefix_all
#print axioms gap_ofNat64_add_one
#print axioms gapScanInv_seed
#print axioms gap_scan_exit_ws
#print axioms gap_scan_toWhileBody
#print axioms gap_scan_atIp_bit
#print axioms gap_scan_offIp_bit
#print axioms gap_scan_exit_ip
#print axioms gap_scan_step_loop
#print axioms gapScanExitBlock
#print axioms gapScanLoop
#print axioms gapScanLoop_run_from
#print axioms gapScanLoop_run
#print axioms gap_recoverWrite_none_of_ee
#print axioms gap_scan_whileEnd_step
#print axioms gap_scan_whileEnd_continue
#print axioms gap_scan_cleanup82_exit
#print axioms gap_scan_cleanup82_continue

end LeanLLVM.Refinement
