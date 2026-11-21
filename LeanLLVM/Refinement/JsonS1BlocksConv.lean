/-
The gate word's ride-through: the entry's `%conv` from the block to the exits.

`entry` computes `%conv` from the arm alone: `%0 = trunc arm`, `%1 = %0 >>> 2`,
`%conv = %1 &&& 1`, so the cell is the arm's bit 2 (`JsonS1BlocksRefine.entryGate`).
No block of the ASCII phase and no block of the fused loop rebinds that cell, so
the value the entry wrote is the value at every latch, at every loop head, and at
`for.end101`.  `JsonS1BlocksPrefix` already proves the per-builder reads (its
`EntryCells` bundle), and `JsonS1BlocksPeelStaging` records that the peel's
silent arm takes `conv = 0` as a premise because nothing ties that running cell
back to `entryGate arm`.  This module is that tie.

## What is proved

* **The gate arithmetic.**  `entryGate arm = 0` exactly when the arm's bit 2 is
  clear (`arm &&& 4 = 0`), and `entryGate arm` is the arm's bit 2 as a 32-bit
  word (`entryGate_toNat`).  `entryGate_ne_zero_iff` is the other arm's side.
* **The ride-through.**  `GateWord env arm` is `lookupName env "%conv" =
  some (.int 32 (entryGate arm))`.  It holds at `entryEnv`, is preserved by every
  phase builder (`lrPhEnv`, `forIncEnv`, `forBodyOut`, `ifEndEnv`, `asciiHandoffEnv`,
  `ifThen38Out`, `ifEnd50Out`, `fb54PageEnv`, `forBody54LrPhEnv`, `fb54Env9`,
  and the segment builders `fbEnv1`–`fbEnv7`, `iftEnv1`–`iftEnv9`,
  `handoffIfThenEnv`, `handoffIfEndEnv`, `handoffThen38Env`, `handoffOut`,
  `ifEnd147Env`, `ifEnd153ThreadEnv`, `ifEnd153Env`, `ifEnd170Env`, `ifThenOut`)
  and every fused-loop builder (`fusedE3`, `ifThen90Out`, `fusedDfaEnv`,
  `ifEnd93Env`, `fusedE9`, `ifThen96Out`, `fusedE96`, `fusedDfaLatchEnv`,
  `fusedDfaEscapedLatchEnv`, `ifEnd98Env`, and the segment builders
  `ift90Env1`–`ift90Env6`, `fb54Env1`–`fb54Env8`), and is therefore the gate word
  at the exits: `peelEntryEnv` (the phase's `for.end101` arm), `forEnd101Out` /
  `forEnd101OutOf` (the fused loop's), and the short arm's `shortJoinEnv`.
* **The derived premise.**  On the arm's bit-2-clear decision the gate word is
  zero at each exit (`conv_eq_zero_at_phase_exit`,
  `conv_eq_zero_at_fusedExit`, `conv_eq_zero_at_shortJoin`).  `%or.cond190` and
  `%or.cond191` are then the peel's selects at a zero gate
  (`cond190_eq_one_of_gate`, `cond191_eq_one_of_gate`), and the compositions'
  `hsilent` hypotheses follow with `conv`'s value supplied by the run rather than
  assumed (`hsilent_fusedExit_of_gate`, `hsilent_asciiExit_of_gate`,
  `hsilent_shortPeel_of_gate`).

## Which arm decision supplies `conv = 0`

The gate word is the arm's bit 2.  The loop's *escape* decision reads the arm's
bit 1 (`%and18`/`%and94 = arm &&& 2` followed by `%tobool.not`/`%tobool95.not`),
and the loop's own *silent* decision is `%tobool87 = (%conv = 0)` at
`for.body54.lr.ph`; the peel's silent merge then tests `%or.cond191`, whose left
factor is `%tobool139 = (%conv = 0)` again.  Those are two different bits of the
arm: bit 1 decides the loop's calling/skip arm, bit 2 is the gate word that
decides whether the peel accepts the block at all.  So the escape gate does not
supply `conv = 0` (`escape_bit_zero_not_gate_word`), and the decision that does
is the arm's bit-2-clear: `arm &&& 4 = 0`, i.e. `entryGate arm = 0`
(`gate_off_of_arm_bit_two_zero`), which is exactly the `%tobool87`/`%tobool139`
gate-off (`tobool87_eq_one_of_gate`, `tobool139_eq_one_of_gate`).  The
compositions therefore take the arm's bit-2 decision and derive the gate word's
zero; they do not assume the gate word.

## What remains

The bit-2 decision itself is the caller's arm, not a consequence of the document
or of the escape gate.  `hsilent_*_of_gate` still take the peel's other premises
Unchanged: the block's high-bit probe (`hprobe`), the carried byte (`hprev`), and,
for the staging family, the document window and the peel's two reads.  The
fused loop's page identities (`JsonS1BlocksLoopRun`'s `PageModel`) and the
composed frame are outside this module, as they were before it.
-/
import LeanLLVM.Refinement.JsonS1BlocksPeelStaging
import LeanLLVM.Refinement.JsonS1BlocksShort
import LeanLLVM.Refinement.JsonS1BlocksPrefix

namespace LeanLLVM.Refinement.JsonS1BlocksConv

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksEntry
open LeanLLVM.Refinement.JsonS1BlocksExit
open LeanLLVM.Refinement.JsonS1BlocksStaging
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonS1BlocksRefines
open LeanLLVM.Refinement.JsonS1BlocksPrefix
open LeanLLVM.Refinement.JsonS1BlocksShort
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksPeelStaging
open LeanLLVM.Refinement.JsonScanSpec

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The gate arithmetic

`%conv` is `(%0 >>> 2) &&& 1` over `%0 = trunc arm`; the truncation keeps the
arm's low thirty-two bits, and the shift and mask read bit 2.  The lemmas below
express that twice: as the bit test the branch reads, and as the `Nat` value the
exit's `conv` is.
-/

/-- The truncated arm's `Nat` value. -/
theorem entryTrunc_toNat (arm : BitVec 64) :
    (entryTrunc arm).toNat = arm.toNat % 2 ^ 32 := by
  unfold entryTrunc
  rw [BitVec.toNat_ofNat, Nat.mod_mod]

/-- **The gate word is the arm's bit 2.** -/
theorem entryGate_toNat (arm : BitVec 64) :
    (entryGate arm).toNat = (arm.toNat / 4) % 2 := by
  unfold entryGate
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, entryTrunc_toNat]
  rw [show BitVec.toNat (1 : BitVec 32) = 1 from rfl]
  rw [Nat.and_one_is_mod]
  show ((arm.toNat % 2 ^ 32) >>> 2) % 2 = arm.toNat / 4 % 2
  rw [Nat.shiftRight_eq_div_pow, show 2 ^ 32 = 4 * 2 ^ 30 from by decide]
  rw [Nat.mod_mul_right_div_self]
  rw [Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 30 from by decide)]

/-- The `Nat` mask `&&& 4` is bit 2. -/
theorem nat_and_four_testBit_zero (a : Nat) :
    a &&& 4 = 0 ↔ a.testBit 2 = false := by
  constructor
  · intro h
    have h4 : (4 : Nat) = 2 ^ 2 := by decide
    rw [h4] at h
    have := congrArg (fun n => n.testBit 2) h
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit] at this
    simpa using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.zero_testBit, Nat.testBit_and]
    by_cases hj : j = 2
    · subst hj
      rw [h, show (4 : Nat).testBit 2 = true from by decide]
      rfl
    · have h4 : (4 : Nat).testBit j = false := by
        rw [show (4 : Nat) = 2 ^ 2 from by decide, Nat.testBit_two_pow,
          decide_eq_false_iff_not]
        omega
      rw [h4, Bool.and_false]

/-- The second bit, as `Nat`'s `testBit` reads it. -/
theorem nat_testBit_two_eq_mod (a : Nat) :
    a.testBit 2 = (a / 4 % 2 == 1) := by
  have h1 : a.testBit 2 = (a / 4).testBit 0 := by
    have h := Nat.testBit_shiftRight (i := 2) (j := 0) a
    rw [Nat.shiftRight_eq_div_pow] at h
    simpa using h.symm
  rw [h1, Nat.testBit_zero]
  rfl

/-- `a &&& 4 = 0` is `a`'s bit 2 being clear. -/
theorem nat_and_four_eq_zero_iff (a : Nat) :
    a &&& 4 = 0 ↔ a / 4 % 2 = 0 := by
  rw [nat_and_four_testBit_zero, nat_testBit_two_eq_mod]
  show decide (a / 4 % 2 = 1) = false ↔ a / 4 % 2 = 0
  rw [decide_eq_false_iff_not]
  omega

/-- **The gate word is zero exactly at the arm's bit-2-clear.** -/
theorem entryGate_eq_zero_iff (arm : BitVec 64) :
    entryGate arm = 0 ↔ arm &&& 4 = 0 := by
  have hto : (arm &&& 4).toNat = arm.toNat &&& 4 := BitVec.toNat_and _ _
  constructor
  · intro h
    have h1 : (entryGate arm).toNat = 0 := by rw [h]; rfl
    rw [entryGate_toNat] at h1
    apply BitVec.eq_of_toNat_eq
    show arm.toNat &&& 4 = 0
    rw [nat_and_four_eq_zero_iff]
    exact h1
  · intro h
    have h1 : (arm &&& 4).toNat = 0 := by rw [h]; rfl
    rw [hto] at h1
    apply BitVec.eq_of_toNat_eq
    rw [entryGate_toNat]
    exact (nat_and_four_eq_zero_iff arm.toNat).mp h1

/-- The gate's off state, from the arm's bit-2 decision. -/
theorem entryGate_eq_zero_of_and_four (arm : BitVec 64) (h : arm &&& 4 = 0) :
    entryGate arm = 0 :=
  (entryGate_eq_zero_iff arm).mpr h

/-- The gate's on state, from the arm's bit-2 decision. -/
theorem entryGate_ne_zero_iff (arm : BitVec 64) :
    entryGate arm ≠ 0 ↔ arm &&& 4 ≠ 0 := by
  constructor
  · intro h hz
    exact h ((entryGate_eq_zero_iff arm).mpr hz)
  · intro h hz
    exact h ((entryGate_eq_zero_iff arm).mp hz)

/-- The entry's own comparison of the arm's bit 2 with zero, as a one-bit word. -/
theorem entryGate_eq_zero_of_cmp (arm : BitVec 64)
    (h : evalICmp .eq (arm &&& 4) 0 = 1) : entryGate arm = 0 :=
  entryGate_eq_zero_of_and_four arm ((evalICmp_eq_one_iff (arm &&& 4) 0).mp h)

/-- **The escape gate does not supply the gate word.**  The loop's escape
decision reads the arm's bit 1; the gate word reads bit 2, and an arm can have
bit 1 clear with bit 2 set. -/
theorem escape_bit_zero_not_gate_word :
    ¬ (∀ arm : BitVec 64, arm &&& 2 = 0 → arm &&& 4 = 0) := by
  intro h
  have h4 : ((4 : BitVec 64) &&& 2) = 0 := by decide
  have hz := h 4 h4
  exact absurd hz (by decide)

/-- The two arm decisions are independent in the other direction too. -/
theorem gate_word_zero_not_escape_bit :
    ¬ (∀ arm : BitVec 64, arm &&& 4 = 0 → arm &&& 2 = 0) := by
  intro h
  have h2 : ((2 : BitVec 64) &&& 4) = 0 := by decide
  have hz := h 2 h2
  exact absurd hz (by decide)

/-! ### The gate word as a predicate

`GateWord env arm` is the environment's cell at the value the entry wrote.  It
is a property of the running environment alone, so the builders' preservation
lemmas compose, and the exits read the same value. -/

/-- The environment's `%conv` is the entry's `entryGate arm`. -/
def GateWord (env : Env) (arm : BitVec 64) : Prop :=
  lookupName env "%conv" = some (.int 32 (entryGate arm))

/-- The entry's own environment satisfies it. -/
theorem gateWord_entryEnv (env : Env) (n arm : BitVec 64) :
    GateWord (LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv env n arm) arm :=
  lookupName_entryEnv_conv env n arm

/-! ### The phase's builders -/

theorem gateWord_lrPhEnv (env : Env) (arm : BitVec 64) (h : GateWord env arm) :
    GateWord (lrPhEnv env arm) arm := by
  unfold GateWord at *
  rw [lookupName_lrPhEnv_conv]
  exact h

theorem gateWord_forIncEnv (env : Env) (i shr : BitVec 64) (arm : BitVec 64)
    (h : GateWord env arm) :
    GateWord (forIncEnv env i shr) arm := by
  unfold GateWord at *
  rw [lookupName_forIncEnv_conv]
  exact h

theorem gateWord_forBodyOut (env : Env) (v : ForBodyValues) (arm : BitVec 64)
    (h : GateWord env arm) :
    GateWord (forBodyOut env v) arm := by
  unfold GateWord at *
  rw [lookupName_forBodyOut_conv]
  exact h

theorem gateWord_ifEndEnv (env : Env) (a2 a3 : List (BitVec 64)) (arm : BitVec 64)
    (h : GateWord env arm) :
    GateWord (ifEndEnv env a2 a3) arm := by
  unfold GateWord at *
  rw [lookupName_ifEndEnv_conv]
  exact h

/-- The phase's seed: the preheader's first pass. -/
theorem gateWord_asciiSeedEnv (env : Env) (arm : BitVec 64) (v : ForBodyValues)
    (h : GateWord env arm) :
    GateWord (ifEndEnv (forBodyOut (lrPhEnv env arm) v) v.w2 v.w3) arm := by
  unfold GateWord at *
  rw [lookupName_asciiSeedEnv_conv]
  exact h

/-- The hand-off's environment: the latch, the body and the class test. -/
theorem lookupName_asciiHandoffEnv_conv (env : Env) (c : AsciiCarry)
    (v : ForBodyValues) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (asciiHandoffEnv env c v) "%conv" = some (.int 32 conv) := by
  unfold asciiHandoffEnv
  rw [lookupName_ifEndEnv_conv, lookupName_forBodyOut_conv, lookupName_forIncEnv_conv]
  exact h

theorem gateWord_asciiHandoffEnv (env : Env) (c : AsciiCarry) (v : ForBodyValues)
    (arm : BitVec 64) (h : GateWord env arm) :
    GateWord (asciiHandoffEnv env c v) arm := by
  unfold GateWord at *
  exact lookupName_asciiHandoffEnv_conv env c v h

theorem gateWord_ifThen38Out (env : Env) (v : IfThen38Values) (arm : BitVec 64)
    (h : GateWord env arm) :
    GateWord (ifThen38Out env v) arm := by
  unfold GateWord at *
  rw [lookupName_ifThen38Out_conv]
  exact h

/-- The hand-off's join, at the entry edge. -/
theorem lookupName_ifEnd50EntryOut_conv (env : Env) (shr : BitVec 64)
    {conv : BitVec 32} (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (ifEnd50EntryOut env shr) "%conv" = some (.int 32 conv) := by
  simp only [ifEnd50EntryOut, cells]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]
  exact h

theorem gateWord_ifEnd50EntryOut (env : Env) (shr : BitVec 64) (arm : BitVec 64)
    (h : GateWord env arm) :
    GateWord (ifEnd50EntryOut env shr) arm := by
  unfold GateWord at *
  exact lookupName_ifEnd50EntryOut_conv env shr h

/-- The hand-off's join, at `if.then38`. -/
theorem lookupName_ifEnd50Out_conv (env : Env) (shr17 st0 st9 st15 : BitVec 64)
    (oii or284 : List (BitVec 64)) (inc49 shr : BitVec 64) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (ifEnd50Out env shr17 st0 st9 st15 oii or284 inc49 shr) "%conv"
      = some (.int 32 conv) :=
  lookupName_ifEnd50Out_of env shr17 st0 st9 st15 oii or284 inc49 shr h
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem gateWord_ifEnd50Out (env : Env) (shr17 st0 st9 st15 : BitVec 64)
    (oii or284 : List (BitVec 64)) (inc49 shr : BitVec 64) (arm : BitVec 64)
    (h : GateWord env arm) :
    GateWord (ifEnd50Out env shr17 st0 st9 st15 oii or284 inc49 shr) arm := by
  unfold GateWord at *
  exact lookupName_ifEnd50Out_conv env shr17 st0 st9 st15 oii or284 inc49 shr h

/-- The page's entry environment: the join over the hand-off's. -/
theorem gateWord_fb54PageEnv (env : Env) (c : AsciiCarry) (v : ForBodyValues)
    (v38 : IfThen38Values) (arm : BitVec 64) (h : GateWord env arm) :
    GateWord (fb54PageEnv env c v v38) arm := by
  unfold GateWord at *
  exact lookupName_fb54PageEnv_conv env c v v38 h

/-- The fused loop's preheader. -/
theorem gateWord_forBody54LrPhEnv (env : Env) (arm : BitVec 64)
    (conv : BitVec 32) (h : GateWord env arm) :
    GateWord (forBody54LrPhEnv env arm conv) arm := by
  unfold GateWord at *
  exact lookupName_forBody54LrPhEnv_conv' env arm conv h

/-- The fused loop's body: its nine segments. -/
theorem gateWord_fb54Env9 (env : Env) (v : ForBody54Values) (gate : BitVec 1)
    (arm : BitVec 64) (h : GateWord env arm) :
    GateWord (fb54Env9 env v gate) arm := by
  unfold GateWord at *
  exact lookupName_fb54Env9_conv env v gate h

/-! ### The fused loop's builders -/

theorem gateWord_fusedE3 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (arm : BitVec 64) (h : GateWord env arm) :
    GateWord (fusedE3 env c gate bs73 bs74) arm :=
  gateWord_fb54Env9 env (fusedValues c bs73 bs74) gate arm h

theorem gateWord_ifThen90Out (env : Env) (v : IfThen90Values) (arm : BitVec 64)
    (h : GateWord env arm) :
    GateWord (ifThen90Out env v) arm := by
  unfold GateWord at *
  exact lookupName_ifThen90Out_conv env v h

theorem gateWord_fusedDfaEnv (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) (arm : BitVec 64)
    (h : GateWord env arm) :
    GateWord (fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) arm :=
  gateWord_ifThen90Out _ (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59) arm
    (gateWord_fusedE3 env c gate bs73 bs74 arm h)

theorem gateWord_ifEnd93Env (env : Env) (u8k : List (BitVec 64)) (arm : BitVec 64)
    (h : GateWord env arm) :
    GateWord (ifEnd93Env env u8k) arm := by
  unfold GateWord at *
  exact lookupName_ifEnd93Env_conv env u8k h

theorem gateWord_fusedE9 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (arm : BitVec 64) (h : GateWord env arm) :
    GateWord (fusedE9 env c gate bs73 bs74) arm :=
  gateWord_ifEnd93Env _ c.u8k arm (gateWord_fusedE3 env c gate bs73 bs74 arm h)

theorem gateWord_ifThen96Out (env : Env) (a2 a3 : List (BitVec 64)) (arm : BitVec 64)
    (h : GateWord env arm) :
    GateWord (ifThen96Out env a2 a3) arm := by
  unfold GateWord at *
  exact lookupName_ifThen96Out_conv env a2 a3 h

theorem gateWord_fusedE96 (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 : List UInt8) (arm : BitVec 64) (h : GateWord env arm) :
    GateWord (fusedE96 env c gate bs73 bs74) arm :=
  gateWord_ifThen96Out _ (fusedValues c bs73 bs74).w73 (fusedValues c bs73 bs74).w74
    arm (gateWord_fusedE9 env c gate bs73 bs74 arm h)

theorem gateWord_fusedDfaLatchEnv (env : Env) (c : FusedCarry) (gate : BitVec 1)
    (bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) (arm : BitVec 64)
    (h : GateWord env arm) :
    GateWord (fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      arm :=
  gateWord_ifEnd93Env _
    (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281 arm
    (gateWord_fusedDfaEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 arm h)

theorem gateWord_fusedDfaEscapedLatchEnv (env : Env) (c : FusedCarry)
    (gate : BitVec 1) (bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8)
    (arm : BitVec 64) (h : GateWord env arm) :
    GateWord
      (fusedDfaEscapedLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59)
      arm :=
  gateWord_ifThen96Out _ (fusedValues c bs73 bs74).w73 (fusedValues c bs73 bs74).w74
    arm (gateWord_fusedDfaLatchEnv env c gate bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59
      arm h)

theorem gateWord_ifEnd98Env (env : Env) (i shr : BitVec 64) (arm : BitVec 64)
    (h : GateWord env arm) :
    GateWord (ifEnd98Env env i shr) arm := by
  unfold GateWord at *
  exact lookupName_ifEnd98Env_conv env i shr h

/-! ### The exits

The phase's peel entry is `forIncEnv` then `for.end101`'s output; the fused
loop's is the same block's output over the loop's registers; the short arm's is
the join's output directly.  Each reads `%conv` from the environment beneath its
own cells, so each carries the gate word the entry wrote. -/

/-- `%conv` through `for.end101`'s generic output. -/
theorem lookupName_forEnd101OutOf_conv (env : Env) (prevS : BitVec 64)
    (ascii u8k : List (BitVec 64)) (prevAscii : BitVec 32)
    (st0 st9 st15 andv : BitVec 64) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (forEnd101OutOf env prevS ascii u8k prevAscii st0 st9 st15 andv)
        "%conv" = some (.int 32 conv) :=
  lookupName_forEnd101OutOf_of env prevS ascii u8k prevAscii st0 st9 st15 andv h
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- `%conv` through the ASCII exit's `for.end101` output. -/
theorem lookupName_forEnd101Out_conv (env : Env) (c : AsciiCarry) (andv : BitVec 64)
    {conv : BitVec 32} (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (forEnd101Out env c andv) "%conv" = some (.int 32 conv) := by
  rw [forEnd101Out_eq]
  exact lookupName_forEnd101OutOf_conv env c.prevS (List.replicate 4 0)
    (List.replicate 4 0) (1 : BitVec 32) c.st0 c.st9 c.st15 andv h

theorem gateWord_forEnd101OutOf (env : Env) (prevS : BitVec 64)
    (ascii u8k : List (BitVec 64)) (prevAscii : BitVec 32)
    (st0 st9 st15 andv : BitVec 64) (arm : BitVec 64) (h : GateWord env arm) :
    GateWord (forEnd101OutOf env prevS ascii u8k prevAscii st0 st9 st15 andv) arm := by
  unfold GateWord at *
  exact lookupName_forEnd101OutOf_conv env prevS ascii u8k prevAscii st0 st9 st15 andv h

theorem gateWord_forEnd101Out (env : Env) (c : AsciiCarry) (andv : BitVec 64)
    (arm : BitVec 64) (h : GateWord env arm) :
    GateWord (forEnd101Out env c andv) arm := by
  unfold GateWord at *
  exact lookupName_forEnd101Out_conv env c andv h

/-- The phase's peel entry: the latch and the block over the running
environment. -/
theorem gateWord_peelEntryEnv (env : Env) (c : AsciiCarry) (andv : BitVec 64)
    (arm : BitVec 64) (h : GateWord env arm) :
    GateWord (peelEntryEnv env c andv) arm := by
  unfold GateWord at *
  exact lookupName_peelEntryEnv_conv env c andv h

/-- The short arm's entry environment. -/
theorem gateWord_shortEntryEnv (env : Env) (n arm : BitVec 64) :
    GateWord (shortEntryEnv env n arm) arm :=
  gateWord_entryEnv env n arm

/-- The short arm's join: `%conv` is the entry's own cell, unchanged. -/
theorem gateWord_shortJoinEnv (env : Env) (n arm : BitVec 64) :
    GateWord (shortJoinEnv env n arm) arm :=
  lookupName_shortJoinEnv_conv env n arm

/-! ### The derived zero at the exits

On the arm's bit-2-clear, each exit's environment stores zero in `%conv`.  These
are the values the peel's `ifThen103Values` arguments take when `conv` is not an
assumption but the run's own cell. -/

/-- `%conv = 0` at the phase's peel entry, from the arm's bit-2 decision. -/
theorem conv_eq_zero_at_phase_exit (env : Env) (c : AsciiCarry) (andv : BitVec 64)
    (arm : BitVec 64) (h : GateWord env arm) (h4 : arm &&& 4 = 0) :
    lookupName (peelEntryEnv env c andv) "%conv" = some (.int 32 0) := by
  have hw := gateWord_peelEntryEnv env c andv arm h
  unfold GateWord at hw
  rw [entryGate_eq_zero_of_and_four arm h4] at hw
  exact hw

/-- `%conv = 0` at the fused loop's exit, from the arm's bit-2 decision. -/
theorem conv_eq_zero_at_fusedExit (env : Env) (c : FusedCarry) (andv : BitVec 64)
    (arm : BitVec 64) (h : GateWord env arm) (h4 : arm &&& 4 = 0) :
    lookupName (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii
      c.st0 c.st9 c.st15 andv) "%conv" = some (.int 32 0) := by
  have hw := gateWord_forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii
    c.st0 c.st9 c.st15 andv arm h
  unfold GateWord at hw
  rw [entryGate_eq_zero_of_and_four arm h4] at hw
  exact hw

/-- `%conv = 0` at the short arm's join, from the arm's bit-2 decision. -/
theorem conv_eq_zero_at_shortJoin (env : Env) (n arm : BitVec 64)
    (h4 : arm &&& 4 = 0) :
    lookupName (shortJoinEnv env n arm) "%conv" = some (.int 32 0) := by
  have hw := gateWord_shortJoinEnv env n arm
  unfold GateWord at hw
  rw [entryGate_eq_zero_of_and_four arm h4] at hw
  exact hw

/-! ### The select words and the silent arm's gate

`if.then103` stores the block's word, then tests `%tobool139 = (%conv = 0)` and
`%tobool141 = (%138 ≠ 0)`, selecting `%or.cond190`; `%or.cond191` adds
`%tobool143 = (%prev_ascii ≠ 0)`.  With `conv` at the arm's bit 2 and the bit
clear, `%tobool139` is set and the first select is the probe, so `%or.cond190`
and `%or.cond191` are the probe and the carried byte's conjunction.

The loop's own silent decision is `%tobool87 = (%conv = 0)` at
`for.body54.lr.ph`; it is the same gate word, and the arm's bit-2-clear sets it.
-/

/-- `%tobool139`'s comparison, at the gate word. -/
theorem tobool139_eq_one_of_gate (arm : BitVec 64) (h4 : arm &&& 4 = 0) :
    evalICmp .eq (entryGate arm) (0 : BitVec 32) = 1 := by
  rw [entryGate_eq_zero_of_and_four arm h4]
  decide

/-- The loop preheader's silent-arm gate, at the gate word. -/
theorem tobool87_eq_one_of_gate (env : Env) (arm : BitVec 64)
    (h4 : arm &&& 4 = 0) :
    lookupName (forBody54LrPhEnv env arm (entryGate arm)) "%tobool87"
      = some (.int 1 1) := by
  rw [lookupName_forBody54LrPhEnv_tobool87]
  congr 1
  rw [tobool139_eq_one_of_gate arm h4]

/-- **`%or.cond190` at the gate word.**  The arm's bit-2 decision sets the
gate's zero test, so the inner select is the block's high-bit probe. -/
theorem cond190_eq_one_of_gate (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat) (arm : BitVec 64)
    (prevAscii : BitVec 32) (h4 : arm &&& 4 = 0)
    (hprobe : (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      (entryGate arm) prevAscii).ptz138 ≠ 0) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      (entryGate arm) prevAscii).cond190 = 1 :=
  (ifThen103Values_cond190_eq_one_iff n b bs136 bs137 ascii st0 st9 st15 prevS
    andv shr ent (entryGate arm) prevAscii).mpr
    ⟨entryGate_eq_zero_of_and_four arm h4, hprobe⟩

/-- **`%or.cond191` at the gate word.**  The peel's silent-merge test is the
probe's and the carried byte's conjunction once the gate is zero. -/
theorem cond191_eq_one_of_gate (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat) (arm : BitVec 64)
    (prevAscii : BitVec 32) (h4 : arm &&& 4 = 0)
    (hprobe : (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      (entryGate arm) prevAscii).ptz138 ≠ 0) (hprev : prevAscii ≠ 0) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      (entryGate arm) prevAscii).cond191 = 1 :=
  (ifThen103Values_cond191_eq_one_iff n b bs136 bs137 ascii st0 st9 st15 prevS
    andv shr ent (entryGate arm) prevAscii).mpr
    ⟨entryGate_eq_zero_of_and_four arm h4, hprobe, hprev⟩

/-! ### The compositions' `hsilent`, with the gate derived

`JsonS1BlocksPeelStaging`'s `hsilent_*` take `conv = 0`.  At `conv`'s actual
value, the entry's gate word, the arm's bit-2-clear supplies it, so the
compositions take the arm decision and derive what they previously assumed. -/

/-- **`hsilent` at the fused loop's exit, gate derived.** -/
theorem hsilent_fusedExit_of_gate (env : Env) (c : FusedCarry) (n andv : BitVec 64)
    (bs136 bs137 : List UInt8) (arm : BitVec 64) {bs : List UInt8} {k : Nat}
    (hk : k < blocksOf bs.length) (hshr : c.shr.toNat = k)
    (h136 : bs136 = (docBlock bs k).take 32)
    (h137 : bs137 = (docBlock bs k).drop 32)
    (h4 : arm &&& 4 = 0)
    (hprobe : ∀ x ∈ blockHalfOr bs k, x.toNat < 0x80)
    (hprev : c.prevAscii ≠ 0) :
    ∀ (v : IfThen103Values),
      v = fusedPeelValues env c n andv bs136 bs137 (entryGate arm) →
      lookupName (ifThen103Out (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii
        c.st0 c.st9 c.st15 andv) v) "%or.cond191" = some (.int 1 1) :=
  hsilent_fusedExit env c n andv bs136 bs137 (entryGate arm) hk hshr h136 h137
    (entryGate_eq_zero_of_and_four arm h4) hprobe hprev

/-- **`hsilent` at the ASCII phase's exit, gate derived.** -/
theorem hsilent_asciiExit_of_gate (env : Env) (c : AsciiCarry) (n andv : BitVec 64)
    (bs136 bs137 : List UInt8) (arm : BitVec 64) {bs : List UInt8} {k : Nat}
    (hk : k < blocksOf bs.length) (hshr : c.shr.toNat = k)
    (h136 : bs136 = (docBlock bs k).take 32)
    (h137 : bs137 = (docBlock bs k).drop 32)
    (h4 : arm &&& 4 = 0)
    (hprobe : ∀ x ∈ blockHalfOr bs k, x.toNat < 0x80) :
    ∀ (v : IfThen103Values),
      v = ifThen103Values n c.b bs136 bs137 (List.replicate 4 0)
        c.st0 c.st9 c.st15 c.prevS andv c.shr c.ent (entryGate arm) 1 →
      lookupName (ifThen103Out (peelEntryEnv env c andv) v) "%or.cond191"
        = some (.int 1 1) :=
  hsilent_asciiExit env c n andv bs136 bs137 (entryGate arm) hk hshr h136 h137
    (entryGate_eq_zero_of_and_four arm h4) hprobe

/-- **`hsilent` at the short document's join, gate derived.** -/
theorem hsilent_shortPeel_of_gate (env : Env) (n arm : BitVec 64) (b ent : Nat)
    (bs136 bs137 : List UInt8) {bs : List UInt8} {k : Nat}
    (hk : k < blocksOf bs.length) (hshr : (n >>> 6).toNat = k)
    (h136 : bs136 = (docBlock bs k).take 32)
    (h137 : bs137 = (docBlock bs k).drop 32)
    (h4 : arm &&& 4 = 0)
    (hprobe : ∀ x ∈ blockHalfOr bs k, x.toNat < 0x80) :
    ∀ (v : IfThen103Values), v = ifThen103Values n b bs136 bs137
        (List.replicate 4 0) 0 0 0 0 (n &&& 63) (n >>> 6) ent (entryGate arm) 1 →
      lookupName (ifThen103Out env v) "%or.cond191" = some (.int 1 1) :=
  hsilent_shortPeel env n arm b ent bs136 bs137 hk hshr h136 h137
    (entryGate_eq_zero_of_and_four arm h4) hprobe

/-! ### The remaining environment builders

The blocks split their runs at segment boundaries, and each segment's builder is
a `cells` list of the words that segment wrote.  None of them binds `%conv`, so
the gate word passes through each one: the ASCII body's `fbEnv1`–`fbEnv7`, the
class test's `iftEnv1`–`iftEnv9`, the DFA arm's `ift90Env1`–`ift90Env6`, the
fused body's `fb54Env1`–`fb54Env8`, the hand-off's four, and the peeled tail's
merge and escape builders.  The lemmas below state the value-level fact for each;
the block-level composites above are their `entryGate`-instantiated wrappers
(`forBodyOut = fbEnv7`, `ifThen38Out = iftEnv9`, `ifThen90Out = ift90Env6`).
-/

theorem lookupName_fbEnv1_conv (env : Env) (v : ForBodyValues) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (fbEnv1 env v) "%conv" = some (.int 32 conv) := by
  simp only [fbEnv1, cells]
  exact h

theorem lookupName_fbEnv2_conv (env : Env) (v : ForBodyValues) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (fbEnv2 env v) "%conv" = some (.int 32 conv) := by
  simp only [fbEnv2, cells]
  exact lookupName_fbEnv1_conv env v h

theorem lookupName_fbEnv3_conv (env : Env) (v : ForBodyValues) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (fbEnv3 env v) "%conv" = some (.int 32 conv) := by
  simp only [fbEnv3, cells]
  exact lookupName_fbEnv2_conv env v h

theorem lookupName_fbEnv4_conv (env : Env) (v : ForBodyValues) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (fbEnv4 env v) "%conv" = some (.int 32 conv) := by
  simp only [fbEnv4, cells]
  exact lookupName_fbEnv3_conv env v h

theorem lookupName_fbEnv5_conv (env : Env) (v : ForBodyValues) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (fbEnv5 env v) "%conv" = some (.int 32 conv) := by
  simp only [fbEnv5, cells]
  exact lookupName_fbEnv4_conv env v h

theorem lookupName_fbEnv6_conv (env : Env) (v : ForBodyValues) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (fbEnv6 env v) "%conv" = some (.int 32 conv) := by
  simp only [fbEnv6, cells]
  exact lookupName_fbEnv5_conv env v h

theorem lookupName_fbEnv7_conv (env : Env) (v : ForBodyValues) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (fbEnv7 env v) "%conv" = some (.int 32 conv) := by
  simp only [fbEnv7, cells]
  exact lookupName_fbEnv6_conv env v h

theorem lookupName_iftEnv1_conv (env : Env) (v : IfThen38Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (iftEnv1 env v) "%conv" = some (.int 32 conv) := by
  simp only [iftEnv1, cells]
  exact h

theorem lookupName_iftEnv2_conv (env : Env) (v : IfThen38Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (iftEnv2 env v) "%conv" = some (.int 32 conv) := by
  simp only [iftEnv2, cells]
  exact lookupName_iftEnv1_conv env v h

theorem lookupName_iftEnv3_conv (env : Env) (v : IfThen38Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (iftEnv3 env v) "%conv" = some (.int 32 conv) := by
  simp only [iftEnv3, cells]
  exact lookupName_iftEnv2_conv env v h

theorem lookupName_iftEnv4_conv (env : Env) (v : IfThen38Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (iftEnv4 env v) "%conv" = some (.int 32 conv) := by
  simp only [iftEnv4, cells]
  exact lookupName_iftEnv3_conv env v h

theorem lookupName_iftEnv5_conv (env : Env) (v : IfThen38Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (iftEnv5 env v) "%conv" = some (.int 32 conv) := by
  simp only [iftEnv5, cells]
  exact lookupName_iftEnv4_conv env v h

theorem lookupName_iftEnv6_conv (env : Env) (v : IfThen38Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (iftEnv6 env v) "%conv" = some (.int 32 conv) := by
  simp only [iftEnv6, cells]
  exact lookupName_iftEnv5_conv env v h

theorem lookupName_iftEnv7_conv (env : Env) (v : IfThen38Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (iftEnv7 env v) "%conv" = some (.int 32 conv) := by
  simp only [iftEnv7, cells]
  exact lookupName_iftEnv6_conv env v h

theorem lookupName_iftEnv8_conv (env : Env) (v : IfThen38Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (iftEnv8 env v) "%conv" = some (.int 32 conv) := by
  simp only [iftEnv8, cells]
  exact lookupName_iftEnv7_conv env v h

theorem lookupName_iftEnv9_conv (env : Env) (v : IfThen38Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (iftEnv9 env v) "%conv" = some (.int 32 conv) := by
  simp only [iftEnv9, cells]
  exact lookupName_iftEnv8_conv env v h

theorem lookupName_ift90Env1_conv (env : Env) (v : IfThen90Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (ift90Env1 env v) "%conv" = some (.int 32 conv) := by
  simp only [ift90Env1, cells]
  exact h

theorem lookupName_ift90Env2_conv (env : Env) (v : IfThen90Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (ift90Env2 env v) "%conv" = some (.int 32 conv) := by
  simp only [ift90Env2, cells]
  exact lookupName_ift90Env1_conv env v h

theorem lookupName_ift90Env3_conv (env : Env) (v : IfThen90Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (ift90Env3 env v) "%conv" = some (.int 32 conv) := by
  simp only [ift90Env3, cells]
  exact lookupName_ift90Env2_conv env v h

theorem lookupName_ift90Env4_conv (env : Env) (v : IfThen90Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (ift90Env4 env v) "%conv" = some (.int 32 conv) := by
  simp only [ift90Env4, cells]
  exact lookupName_ift90Env3_conv env v h

theorem lookupName_ift90Env5_conv (env : Env) (v : IfThen90Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (ift90Env5 env v) "%conv" = some (.int 32 conv) := by
  simp only [ift90Env5, cells]
  exact lookupName_ift90Env4_conv env v h

theorem lookupName_ift90Env6_conv (env : Env) (v : IfThen90Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (ift90Env6 env v) "%conv" = some (.int 32 conv) := by
  simp only [ift90Env6, cells]
  exact lookupName_ift90Env5_conv env v h

theorem lookupName_fb54Env1_conv (env : Env) (v : ForBody54Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (fb54Env1 env v) "%conv" = some (.int 32 conv) := by
  simp only [fb54Env1, cells]
  exact h

theorem lookupName_fb54Env2_conv (env : Env) (v : ForBody54Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (fb54Env2 env v) "%conv" = some (.int 32 conv) := by
  simp only [fb54Env2, cells]
  exact lookupName_fb54Env1_conv env v h

theorem lookupName_fb54Env3_conv (env : Env) (v : ForBody54Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (fb54Env3 env v) "%conv" = some (.int 32 conv) := by
  simp only [fb54Env3, cells]
  exact lookupName_fb54Env2_conv env v h

theorem lookupName_fb54Env4_conv (env : Env) (v : ForBody54Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (fb54Env4 env v) "%conv" = some (.int 32 conv) := by
  simp only [fb54Env4, cells]
  exact lookupName_fb54Env3_conv env v h

theorem lookupName_fb54Env5_conv (env : Env) (v : ForBody54Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (fb54Env5 env v) "%conv" = some (.int 32 conv) := by
  simp only [fb54Env5, cells]
  exact lookupName_fb54Env4_conv env v h

theorem lookupName_fb54Env6_conv (env : Env) (v : ForBody54Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (fb54Env6 env v) "%conv" = some (.int 32 conv) := by
  simp only [fb54Env6, cells]
  exact lookupName_fb54Env5_conv env v h

theorem lookupName_fb54Env7_conv (env : Env) (v : ForBody54Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (fb54Env7 env v) "%conv" = some (.int 32 conv) := by
  simp only [fb54Env7, cells]
  exact lookupName_fb54Env6_conv env v h

theorem lookupName_fb54Env8_conv (env : Env) (v : ForBody54Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (fb54Env8 env v) "%conv" = some (.int 32 conv) := by
  simp only [fb54Env8, cells]
  exact lookupName_fb54Env7_conv env v h

/-- The escape call's output over the body's. -/
theorem lookupName_ifThenOut_conv (env : Env) (a2 a3 : List (BitVec 64))
    {conv : BitVec 32} (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (ifThenOut env a2 a3) "%conv" = some (.int 32 conv) := by
  simp only [ifThenOut, cells]
  exact h

/-- The hand-off's escape arm. -/
theorem lookupName_handoffIfThenEnv_conv (env : Env) (v : ForBodyValues)
    {conv : BitVec 32} (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (handoffIfThenEnv env v) "%conv" = some (.int 32 conv) := by
  unfold handoffIfThenEnv
  exact lookupName_ifThenOut_conv _ v.w2 v.w3
    (by rw [lookupName_forBodyOut_conv]; exact h)

/-- The hand-off's class test. -/
theorem lookupName_handoffIfEndEnv_conv (env : Env) (v : ForBodyValues)
    {conv : BitVec 32} (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (handoffIfEndEnv env v) "%conv" = some (.int 32 conv) := by
  unfold handoffIfEndEnv
  rw [lookupName_ifEndEnv_conv]
  exact lookupName_handoffIfThenEnv_conv env v h

/-- The hand-off's `if.then38`. -/
theorem lookupName_handoffThen38Env_conv (env : Env) (v : ForBodyValues)
    (v38 : IfThen38Values) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (handoffThen38Env env v v38) "%conv" = some (.int 32 conv) := by
  unfold handoffThen38Env
  rw [lookupName_ifThen38Out_conv]
  exact lookupName_handoffIfEndEnv_conv env v h

/-- The hand-off's join. -/
theorem lookupName_handoffOut_conv (env : Env) (v : ForBodyValues)
    (v38 : IfThen38Values) (shr : BitVec 64) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (handoffOut env v v38 shr) "%conv" = some (.int 32 conv) := by
  unfold handoffOut
  exact lookupName_ifEnd50Out_conv _ v.shr17 v.shrII v.conv13II v.shrI v38.or291
    v38.or284 v38.inc49 shr (lookupName_handoffThen38Env_conv env v v38 h)

/-- The peel's merge entry. -/
theorem lookupName_ifEnd147Env_conv (env : Env) (arm : BitVec 64)
    (u8k : List (BitVec 64)) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (ifEnd147Env env arm u8k) "%conv" = some (.int 32 conv) := by
  simp only [ifEnd147Env, cells]
  exact h

/-- The tail's first aligned block. -/
theorem lookupName_ifEnd153ThreadEnv_conv (env : Env) (u8k : List (BitVec 64))
    {conv : BitVec 32} (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (ifEnd153ThreadEnv env u8k) "%conv" = some (.int 32 conv) := by
  simp only [ifEnd153ThreadEnv, cells]
  exact h

/-- The tail's aligned arm. -/
theorem lookupName_ifEnd153Env_conv (env : Env) (n : BitVec 64)
    (u8k : List (BitVec 64)) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (ifEnd153Env env n u8k) "%conv" = some (.int 32 conv) := by
  simp only [ifEnd153Env, cells]
  exact h

/-- The tail's merge. -/
theorem lookupName_ifEnd170Env_conv (env : Env) (ascii : List (BitVec 64))
    (err : BitVec 1) {conv : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (ifEnd170Env env ascii err) "%conv" = some (.int 32 conv) := by
  simp only [ifEnd170Env, cells]
  exact h

/-- The first page's preheader environment. -/
theorem lookupName_entryPageEnv_conv (env : Env) (c : AsciiCarry)
    (v : ForBodyValues) (v38 : IfThen38Values) (arm : BitVec 64)
    (conv : BitVec 32) {conv' : BitVec 32}
    (h : lookupName env "%conv" = some (.int 32 conv')) :
    lookupName (LeanLLVM.Refinement.JsonS1BlocksEntry.entryEnv env c v v38 arm conv)
        "%conv" = some (.int 32 conv') := by
  unfold LeanLLVM.Refinement.JsonS1BlocksEntry.entryEnv
  exact lookupName_forBody54LrPhEnv_conv' _ arm conv
    (lookupName_fb54PageEnv_conv env c v v38 h)

/-! ### Axiom footprints -/

#print axioms entryTrunc_toNat
#print axioms entryGate_toNat
#print axioms nat_and_four_testBit_zero
#print axioms nat_testBit_two_eq_mod
#print axioms nat_and_four_eq_zero_iff
#print axioms entryGate_eq_zero_iff
#print axioms entryGate_ne_zero_iff
#print axioms escape_bit_zero_not_gate_word
#print axioms gate_word_zero_not_escape_bit
#print axioms gateWord_entryEnv
#print axioms gateWord_lrPhEnv
#print axioms gateWord_forIncEnv
#print axioms gateWord_forBodyOut
#print axioms gateWord_ifEndEnv
#print axioms gateWord_asciiSeedEnv
#print axioms gateWord_asciiHandoffEnv
#print axioms gateWord_ifThen38Out
#print axioms gateWord_ifEnd50EntryOut
#print axioms gateWord_ifEnd50Out
#print axioms gateWord_fb54PageEnv
#print axioms gateWord_forBody54LrPhEnv
#print axioms gateWord_fb54Env9
#print axioms gateWord_fusedE3
#print axioms gateWord_ifThen90Out
#print axioms gateWord_fusedDfaEnv
#print axioms gateWord_ifEnd93Env
#print axioms gateWord_fusedE9
#print axioms gateWord_ifThen96Out
#print axioms gateWord_fusedE96
#print axioms gateWord_fusedDfaLatchEnv
#print axioms gateWord_fusedDfaEscapedLatchEnv
#print axioms gateWord_ifEnd98Env
#print axioms gateWord_forEnd101OutOf
#print axioms gateWord_forEnd101Out
#print axioms gateWord_peelEntryEnv
#print axioms gateWord_shortEntryEnv
#print axioms gateWord_shortJoinEnv
#print axioms conv_eq_zero_at_phase_exit
#print axioms conv_eq_zero_at_fusedExit
#print axioms conv_eq_zero_at_shortJoin
#print axioms tobool139_eq_one_of_gate
#print axioms tobool87_eq_one_of_gate
#print axioms cond190_eq_one_of_gate
#print axioms cond191_eq_one_of_gate
#print axioms hsilent_fusedExit_of_gate
#print axioms hsilent_asciiExit_of_gate
#print axioms hsilent_shortPeel_of_gate
#print axioms lookupName_fbEnv1_conv
#print axioms lookupName_fbEnv7_conv
#print axioms lookupName_iftEnv1_conv
#print axioms lookupName_iftEnv9_conv
#print axioms lookupName_ift90Env1_conv
#print axioms lookupName_ift90Env6_conv
#print axioms lookupName_fb54Env1_conv
#print axioms lookupName_fb54Env8_conv
#print axioms lookupName_ifThenOut_conv
#print axioms lookupName_handoffIfThenEnv_conv
#print axioms lookupName_handoffIfEndEnv_conv
#print axioms lookupName_handoffThen38Env_conv
#print axioms lookupName_handoffOut_conv
#print axioms lookupName_ifEnd147Env_conv
#print axioms lookupName_ifEnd153ThreadEnv_conv
#print axioms lookupName_ifEnd153Env_conv
#print axioms lookupName_ifEnd170Env_conv
#print axioms lookupName_entryPageEnv_conv

end LeanLLVM.Refinement.JsonS1BlocksConv
