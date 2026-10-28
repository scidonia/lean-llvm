/-
The comma mask as a memory-backed loop.

`probes/install/ir/loop.ll` is the control-flow-different counterpart of the
unrolled candidate: the counter and accumulator live in memory, the lane test
and bit are computed from the counter, and `select` folds the accumulator.
This module

1. parses and pins the loop;
2. defines the lane prefix the invariant tracks;
3. proves the loop's entry reaches `cond` with the empty prefix;
4. (next) proves one iteration preserves the invariant, and chains it.

The final theorem is functional correctness of the loop: it returns the
lane-wise specification.  It is proved by induction over the counter, not by
unrolling eight copies of the body, and it is where the memory round trip and
the write-below framing are exercised by a real program.
-/
import LeanLLVM.Parser
import LeanLLVM.Semantics
import LeanLLVM.Memory
import LeanLLVM.Vellum.CommaMaskIR

namespace LeanLLVM.Vellum.CommaMaskLoop

open LeanLLVM
open LeanLLVM.Vellum.CommaMaskIR

/-! ### The fixture -/

def loopSrc : String := include_str "../../probes/install/ir/loop.ll"

def firstFunction (src : String) : Option Function :=
  match parseModule src with
  | .ok m => m.functions.head?
  | .error _ => none

/-- The entry block of the loop. -/
def entryInstrs : List Instr := [
  .binop "%m" .xor 64 (.reg "%arg") (lit 3182967604875373612),
  .alloca "%acc" (.int 64) 8,
  .alloca "%i" (.int 64) 8,
  .store (.int 64) (.imm (.int 64 0)) (.reg "%acc"),
  .store (.int 64) (.imm (.int 64 0)) (.reg "%i")]

def condInstrs : List Instr := [
  .load "%i1" (.int 64) (.reg "%i"),
  .icmp "%c" .ult 64 (.reg "%i1") (.imm (.int 64 8))]

def bodyInstrs : List Instr := [
  .binop "%sh" .mul 64 (.reg "%i1") (.imm (.int 64 8)),
  .binop "%b" .lshr 64 (.reg "%m") (.reg "%sh"),
  .binop "%b2" .and 64 (.reg "%b") (.imm (.int 64 255)),
  .icmp "%z" .eq 64 (.reg "%b2") (.imm (.int 64 0)),
  .load "%a0" (.int 64) (.reg "%acc"),
  .binop "%bit" .shl 64 (.imm (.int 64 128)) (.reg "%sh"),
  .binop "%a1" .or 64 (.reg "%a0") (.reg "%bit"),
  .select "%a2" (.int 64) (.reg "%z") (.reg "%a1") (.reg "%a0"),
  .store (.int 64) (.reg "%a2") (.reg "%acc"),
  .binop "%i2" .add 64 (.reg "%i1") (.imm (.int 64 1)),
  .store (.int 64) (.reg "%i2") (.reg "%i")]

def doneInstrs : List Instr := [
  .load "%r" (.int 64) (.reg "%acc")]

/-- The condition block. -/
def condBody : Block :=
  { name := "cond", instrs := condInstrs, term := .condbr (.reg "%c") "body" "done" }

/-- `probes/install/ir/loop.ll`, as an AST. -/
def loopFunction : Function :=
  { name := "leanllvm_comma_mask8_loop", retTy := .int 64, params := [("%arg", .int 64)],
    blocks := [
      { name := "entry", instrs := entryInstrs, term := .br "cond" },
      condBody,
      { name := "body", instrs := bodyInstrs, term := .br "cond" },
      { name := "done", instrs := doneInstrs, term := .ret (.int 64) (some (.reg "%r")) }] }

#guard decide (firstFunction loopSrc = some loopFunction)

/-! ### The lane prefix -/

/-- The fold over the first `k` lanes. -/
def maskPrefix (m : BitVec 64) (k : Nat) : BitVec 64 :=
  (List.range k).foldl
    (fun acc t => acc ||| (if isZeroByte m t then (0x80 : BitVec 64) <<< (8 * t) else 0)) 0

theorem maskPrefix_zero (m : BitVec 64) : maskPrefix m 0 = 0 := rfl

theorem maskPrefix_succ (m : BitVec 64) (k : Nat) :
    maskPrefix m (k + 1) =
      maskPrefix m k |||
        (if isZeroByte m k then (0x80 : BitVec 64) <<< (8 * k) else 0) := by
  simp only [maskPrefix, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- At eight lanes the prefix is the kernel's fold, hence the specification. -/
theorem maskPrefix_eight (m : BitVec 64) : maskPrefix m 8 = maskFold m := by
  simp only [maskPrefix, maskFold,
    show ([0, 1, 2, 3, 4, 5, 6, 7] : List Nat) = List.range 8 from by decide]

/-! ### The loop invariant -/

/-- The loop's state facts: the accumulator is the lane prefix and the counter
is `k`, with the two pointers at the addresses `alloca` assigns. -/
structure LoopFacts (s : State) (m acc : BitVec 64) (k : Nat) : Prop where
  mReg : lookupName s.env "%m" = some (.int 64 m)
  accPtr : lookupName s.env "%acc" = some (.ptr 1)
  iPtr : lookupName s.env "%i" = some (.ptr 9)
  accLoad : loadValue s.mem (.int 64) 1 = some (.int 64 acc)
  iLoad : loadValue s.mem (.int 64) 9 = some (.int 64 (BitVec.ofNat 64 k))

/-- At the loop condition with the facts holding. -/
def LoopInv (s : State) (m acc : BitVec 64) (k : Nat) : Prop :=
  s.pc = "cond" ∧ LoopFacts s m acc k

/-- A 64-bit load of a register operand. -/
theorem eval_load_64 (calls : Calls) (s : State) (d : String) (p : Operand)
    (addr : Nat) (v : BitVec 64)
    (hp : evalOperand s p = some (.ptr addr))
    (hv : loadValue s.mem (.int 64) addr = some (.int 64 v)) :
    evalInstr calls s (.load d (.int 64) p) = some (s.bind d (.int 64 v)) := by
  simp only [evalInstr, hp, hv]

/-- A 64-bit store. -/
theorem eval_store_64 (calls : Calls) (s : State) (v p : Operand)
    (val : BitVec 64) (addr : Nat)
    (hv : evalOperand s v = some (.int 64 val))
    (hp : evalOperand s p = some (.ptr addr)) :
    evalInstr calls s (.store (.int 64) v p) = storeValue s (.int 64) (.int 64 val) addr := by
  simp only [evalInstr, hv, hp]

/-- The state the entry block reaches at `cond`. -/
def entryState (x : BitVec 64) : State :=
  { env := [("%i", .ptr 9), ("%acc", .ptr 1), ("%m", .int 64 (x ^^^ 0x2C2C2C2C2C2C2C2C)),
            ("%arg", .int 64 x)],
    mem := writeBytes (writeBytes [] 1 (natToBytes 0 8)) 9 (natToBytes 0 8),
    next := 17, pc := "cond" }

theorem entry_run (x : BitVec 64) :
    step noCalls loopFunction (initState loopFunction [.int 64 x]) =
      .jump (entryState x) := by
  simp [step, loopFunction, Function.findBlock, findBlockList, denoteCode, entryInstrs,
    initState, Function.entry?, List.head?, Option.getD, List.map, List.zip, List.zipWith,
    evalInstr, evalOperand, Const.toValue, State.bind, entryState, execTerm,
    lookupName, Value.intToNat, evalBinopNat, evalBinop, c, lit, Ty.sizeBytes, storeValue]

theorem ofNat_toNat_self {w : Nat} (x : BitVec w) : BitVec.ofNat w x.toNat = x := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem ofNat_mul (a b : BitVec 64) :
    BitVec.ofNat 64 (a.toNat * b.toNat % 18446744073709551616) = a * b := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_ofNat, BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))

theorem ofNat_ushiftRight (a : BitVec 64) (n : Nat) :
    BitVec.ofNat 64 (a.toNat >>> n) = a >>> n := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) a.isLt)

theorem ofNat_shiftLeft (a : BitVec 64) (n : Nat) :
    BitVec.ofNat 64 (a.toNat <<< n % 18446744073709551616) = a <<< n := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))

theorem entry_inv (x : BitVec 64) :
    LoopInv (entryState x) (x ^^^ c 3182967604875373612) 0 0 := by
  refine ⟨rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [entryState, lookupName, c]
  · simp [entryState, lookupName]
  · simp [entryState]
  · -- accumulator load: the counter write at 9 is below 1 + 8
    have h9 : loadValue (writeBytes (writeBytes [] 1 (natToBytes 0 8)) 9 (natToBytes 0 8))
        (.int 64) 1 = loadValue (writeBytes [] 1 (natToBytes 0 8)) (.int 64) 1 :=
      loadValue_writeBytes_below (writeBytes [] 1 (natToBytes 0 8)) (natToBytes 0 8)
        64 1 9 (by decide)
    have h1 := (loadValue_storeValue_64 { env := [], mem := [], next := 1, pc := "entry" }
      (0 : BitVec 64) 1).2
    simp only [entryState, h9]
    simpa using h1
  · -- counter load
    have h := (loadValue_storeValue_64
      { env := [], mem := writeBytes [] 1 (natToBytes 0 8), next := 9, pc := "entry" }
      (0 : BitVec 64) 9).2
    simp only [entryState]
    simpa using h

/-! ### Instruction evaluators

The loop uses instructions the comma-mask bridge does not: a 64-bit load and
store, `mul` by an immediate, `lshr` by a register, `shl` by a register and
`icmp ult` against an immediate.  Each is stated with the register environment
and memory left abstract, so the block proofs below can rewrite one step at a
time.
-/

theorem evalInstr_mul_imm (calls : Calls) (s : State) (d r : String) (b : BitVec 64) :
    evalInstr calls s (.binop d .mul 64 (.reg r) (.imm (.int 64 b))) =
      (match lookupName s.env r with
       | some (.int 64 a) => some (s.bind d (.int 64 (a * b)))
       | _ => none) := by
  simp only [evalInstr, evalOperand, Const.toValue]
  cases lookupName s.env r with
  | none => simp
  | some v =>
    cases v with
    | int w a =>
      by_cases hw : w = 64
      · subst hw
        simp [Value.intToNat, evalBinopNat, evalBinop, ofNat_mul]
      · simp [Value.intToNat, hw]
    | ptr a => simp [Value.intToNat]

theorem evalInstr_lshr_reg (calls : Calls) (s : State) (d r₁ r₂ : String) :
    evalInstr calls s (.binop d .lshr 64 (.reg r₁) (.reg r₂)) =
      (match lookupName s.env r₁, lookupName s.env r₂ with
       | some (.int 64 a), some (.int 64 b) => some (s.bind d (.int 64 (a >>> b.toNat)))
       | _, _ => none) := by
  simp only [evalInstr, evalOperand]
  cases lookupName s.env r₁ with
  | none => simp
  | some v₁ =>
    cases lookupName s.env r₂ with
    | none => simp
    | some v₂ =>
      cases v₁ with
      | int w a =>
        cases v₂ with
        | int w' b =>
          by_cases hw : w = 64
          · by_cases hw' : w' = 64
            · subst hw; subst hw'
              simp [Value.intToNat, evalBinopNat, evalBinop, ofNat_ushiftRight]
            · simp [Value.intToNat, hw']
          · simp [Value.intToNat, hw]
        | ptr b => simp [Value.intToNat]
      | ptr a => simp [Value.intToNat]

theorem evalInstr_shl_imm_reg (calls : Calls) (s : State) (d r : String) (a : BitVec 64) :
    evalInstr calls s (.binop d .shl 64 (.imm (.int 64 a)) (.reg r)) =
      (match lookupName s.env r with
       | some (.int 64 b) => some (s.bind d (.int 64 (a <<< b.toNat)))
       | _ => none) := by
  simp only [evalInstr, evalOperand, Const.toValue]
  cases lookupName s.env r with
  | none => simp
  | some v =>
    cases v with
    | int w b =>
      by_cases hw : w = 64
      · subst hw
        simp [Value.intToNat, evalBinopNat, evalBinop, ofNat_shiftLeft]
      · simp [Value.intToNat, hw]
    | ptr a => simp [Value.intToNat]

theorem c_eight : c 8 = (BitVec.ofNat 64 8 : BitVec 64) := by decide
theorem c_zero : c 0 = (0 : BitVec 64) := by decide
theorem c_255 : c 255 = (0xFF : BitVec 64) := by decide
theorem c_128 : c 128 = (0x80 : BitVec 64) := by decide
theorem c_one : c 1 = (1 : BitVec 64) := by decide

/-- `acc ||| (if p then bit else 0)` read as a select. -/
theorem or_ite (acc bit : BitVec 64) (p : Prop) [Decidable p] :
    acc ||| (if p then bit else 0) = if p then acc ||| bit else acc := by
  by_cases h : p <;> simp [h]

/-- The lane shift `k * 8` as a `BitVec`. -/
theorem ofNat_mul_eight (k : Nat) (hk : k < 8) :
    BitVec.ofNat 64 k * c 8 = BitVec.ofNat 64 (8 * k) := by
  rw [c_eight]
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem ofNat_eight_mul_toNat (k : Nat) (hk : k < 8) :
    (BitVec.ofNat 64 (8 * k)).toNat = 8 * k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- The counter increment. -/
theorem ofNat_add_one (k : Nat) (hk : k < 8) :
    BitVec.ofNat 64 k + c 1 = BitVec.ofNat 64 (k + 1) := by
  rw [c_one]
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h1 : BitVec.toNat (1 : BitVec 64) = 1 := by decide
  rw [h1]
  rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64)]

theorem ofBool_ult (k : Nat) (hk : k < 8) :
    BitVec.ofBool ((BitVec.ofNat 64 k).ult (8 : BitVec 64)) = 1 := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    BitVec.ult_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by decide : 8 < 2 ^ 64)]
  simp [BitVec.ofBool]
  omega

theorem evalInstr_icmp_ult_imm (calls : Calls) (s : State) (d r : String) (b : BitVec 64) :
    evalInstr calls s (.icmp d .ult 64 (.reg r) (.imm (.int 64 b))) =
      (match lookupName s.env r with
       | some (.int 64 a) => some (s.bind d (.int 1 (BitVec.ofBool (a.ult b))))
       | _ => none) := by
  simp only [evalInstr, evalOperand, Const.toValue]
  cases lookupName s.env r with
  | none => simp
  | some v =>
    cases v with
    | int w a =>
      by_cases hw : w = 64
      · subst hw
        simp [Value.intToNat, evalICmpNat, evalICmp]
      · simp [Value.intToNat, hw]
    | ptr a => simp [Value.intToNat]

theorem lookup_bind_self (s : State) (d : String) (v : Value) :
    lookupName (s.bind d v).env d = some v := by
  simp [State.bind]

/-- One trip through the condition block: the counter is loaded and the branch
to `body` is taken. -/
theorem cond_step (s : State) (m acc : BitVec 64) (k : Nat) (hk : k < 8)
    (hinv : LoopInv s m acc k) :
    ∃ s', step noCalls loopFunction s = .jump s' ∧
      s'.pc = "body" ∧ LoopFacts s' m acc k ∧
      lookupName s'.env "%i1" = some (.int 64 (BitVec.ofNat 64 k)) := by
  obtain ⟨hpc, hf⟩ := hinv
  let s1 : State := s.bind "%i1" (.int 64 (BitVec.ofNat 64 k))
  let s2 : State :=
    s1.bind "%c" (.int 1 (BitVec.ofBool ((BitVec.ofNat 64 k).ult (8 : BitVec 64))))
  let s3 : State := { s2 with pc := "body" }
  have hli1 : lookupName s1.env "%i1" = some (.int 64 (BitVec.ofNat 64 k)) :=
    lookup_bind_self s "%i1" _
  have hlc : lookupName s2.env "%c" =
      some (.int 1 (BitVec.ofBool ((BitVec.ofNat 64 k).ult (8 : BitVec 64)))) :=
    lookup_bind_self s1 "%c" _
  have e1 : evalInstr noCalls s (.load "%i1" (.int 64) (.reg "%i")) = some s1 := by
    have h := eval_load_64 noCalls s "%i1" (.reg "%i") 9 (BitVec.ofNat 64 k)
      hf.iPtr hf.iLoad
    simpa [s1] using h
  have e2 : evalInstr noCalls s1 (.icmp "%c" .ult 64 (.reg "%i1") (.imm (.int 64 (8 : BitVec 64)))) =
      some s2 := by
    have h := evalInstr_icmp_ult_imm noCalls s1 "%c" "%i1" (8 : BitVec 64)
    simp only [hli1] at h
    simpa [s2] using h
  refine ⟨s3, ?_, rfl, ?_, ?_⟩
  · have hfind : loopFunction.findBlock s.pc = some condBody := by
      simp [loopFunction, Function.findBlock, findBlockList, hpc, condBody, condInstrs]
    simp only [step, hfind, condBody, condInstrs, denoteCode]
    rw [e1]
    simp only []
    rw [e2]
    simp only [execTerm, evalOperand, hlc, ofBool_ult k hk, s3]
    simp
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [s3, s2, s1, State.bind, lookupName, hf.mReg]
    · simp [s3, s2, s1, State.bind, lookupName, hf.accPtr]
    · simp [s3, s2, s1, State.bind, lookupName, hf.iPtr]
    · simp [s3, s2, s1, State.bind, hf.accLoad]
    · simp [s3, s2, s1, State.bind, hf.iLoad]
  · simp [s3, s2, s1, State.bind, lookupName]

end LeanLLVM.Vellum.CommaMaskLoop
