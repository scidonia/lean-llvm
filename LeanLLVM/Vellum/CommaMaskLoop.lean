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

/-- The exit block. -/
def doneBlock : Block :=
  { name := "done", instrs := doneInstrs, term := .ret (.int 64) (some (.reg "%r")) }

/-- The body block. -/
def bodyBlock : Block :=
  { name := "body", instrs := bodyInstrs, term := .br "cond" }

/-- The condition block. -/
def condBody : Block :=
  { name := "cond", instrs := condInstrs, term := .condbr (.reg "%c") "body" "done" }

/-- `probes/install/ir/loop.ll`, as an AST. -/
def loopFunction : Function :=
  { name := "leanllvm_comma_mask8_loop", retTy := .int 64, params := [("%arg", .int 64)],
    blocks := [
      { name := "entry", instrs := entryInstrs, term := .br "cond" },
      condBody,
      bodyBlock,
      doneBlock] }

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
theorem eight_lit : (8 : BitVec 64) = BitVec.ofNat 64 8 := rfl
theorem one_lit : (1 : BitVec 64) = c 1 := by decide
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

theorem body_lane_shift (k : Nat) (hk : k < 8) :
    (BitVec.ofNat 64 k * c 8).toNat = 8 * k := by
  rw [ofNat_mul_eight k hk, ofNat_eight_mul_toNat k hk]

theorem ofNat_mul_eight_lit (k : Nat) (hk : k < 8) :
    BitVec.ofNat 64 k * (8 : BitVec 64) = BitVec.ofNat 64 (8 * k) := by
  rw [show (8 : BitVec 64) = c 8 from c_eight.symm, ofNat_mul_eight k hk]

theorem ofNat_add_one_lit (k : Nat) (hk : k < 8) :
    BitVec.ofNat 64 k + (1 : BitVec 64) = BitVec.ofNat 64 (k + 1) := by
  rw [show (1 : BitVec 64) = c 1 from one_lit, ofNat_add_one k hk]

/-- One trip through the body block: the lane is folded into the accumulator,
the two stores run, and the loop returns to `cond` with the next prefix. -/
theorem body_step (s : State) (m acc : BitVec 64) (k : Nat) (hk : k < 8)
    (hacc : acc = maskPrefix m k) (hpc : s.pc = "body") (hf : LoopFacts s m acc k)
    (hi1 : lookupName s.env "%i1" = some (.int 64 (BitVec.ofNat 64 k))) :
    ∃ s', step noCalls loopFunction s = .jump s' ∧ s'.pc = "cond" ∧
      LoopFacts s' m (maskPrefix m (k + 1)) (k + 1) := by
  let shv : BitVec 64 := BitVec.ofNat 64 k * (8 : BitVec 64)
  let bv : BitVec 64 := m >>> shv.toNat
  let b2v : BitVec 64 := bv &&& (255 : BitVec 64)
  let zv : BitVec 1 := BitVec.ofBool (b2v = (0 : BitVec 64))
  let bitv : BitVec 64 := (128 : BitVec 64) <<< shv.toNat
  let a1v : BitVec 64 := acc ||| bitv
  let a2v : BitVec 64 := if zv = 1 then a1v else acc
  let s1 : State := s.bind "%sh" (.int 64 shv)
  let s2 : State := s1.bind "%b" (.int 64 bv)
  let s3 : State := s2.bind "%b2" (.int 64 b2v)
  let s4 : State := s3.bind "%z" (.int 1 zv)
  let s5 : State := s4.bind "%a0" (.int 64 acc)
  let s6 : State := s5.bind "%bit" (.int 64 bitv)
  let s7 : State := s6.bind "%a1" (.int 64 a1v)
  let s8 : State := s7.bind "%a2" (.int 64 a2v)
  -- the two stores
  have hstore1 : storeValue s8 (.int 64) (.int 64 a2v) 1 =
      some { s8 with mem := writeBytes s8.mem 1 (natToBytes a2v.toNat 8) } :=
    (loadValue_storeValue_64 s8 a2v 1).1
  let s9 : State := { s8 with mem := writeBytes s8.mem 1 (natToBytes a2v.toNat 8) }
  let i2v : BitVec 64 := BitVec.ofNat 64 k + (1 : BitVec 64)
  let s10 : State := s9.bind "%i2" (.int 64 i2v)
  have hstore2 : storeValue s10 (.int 64) (.int 64 i2v) 9 =
      some { s10 with mem := writeBytes s10.mem 9 (natToBytes i2v.toNat 8) } :=
    (loadValue_storeValue_64 s10 i2v 9).1
  let s11 : State := { s10 with mem := writeBytes s10.mem 9 (natToBytes i2v.toNat 8) }
  let s12 : State := { s11 with pc := "cond" }
  -- one instruction at a time
  have e1 : evalInstr noCalls s (.binop "%sh" .mul 64 (.reg "%i1") (.imm (.int 64 8))) = some s1 := by
    have h := evalInstr_mul_imm noCalls s "%sh" "%i1" (8 : BitVec 64)
    simp only [hi1] at h
    simpa [s1, shv] using h
  have hl1 : lookupName s1.env "%m" = some (.int 64 m) := by
    simp [s1, State.bind, lookupName, hf.mReg]
  have hl2 : lookupName s1.env "%sh" = some (.int 64 shv) := by
    simp [s1, State.bind, shv]
  have e2 : evalInstr noCalls s1 (.binop "%b" .lshr 64 (.reg "%m") (.reg "%sh")) = some s2 := by
    have h := evalInstr_lshr_reg noCalls s1 "%b" "%m" "%sh"
    simp only [hl1, hl2] at h
    simpa [s2, bv] using h
  have hl3 : lookupName s2.env "%b" = some (.int 64 bv) := by
    simp [s2, State.bind, bv]
  have e3 : evalInstr noCalls s2 (.binop "%b2" .and 64 (.reg "%b") (.imm (.int 64 255))) = some s3 := by
    have h := evalInstr_and_imm noCalls s2 "%b2" "%b" (255 : BitVec 64)
    simp only [hl3] at h
    simpa [s3, b2v] using h
  have hl4 : lookupName s3.env "%b2" = some (.int 64 b2v) := by
    simp [s3, State.bind, b2v]
  have e4 : evalInstr noCalls s3 (.icmp "%z" .eq 64 (.reg "%b2") (.imm (.int 64 0))) = some s4 := by
    have h := evalInstr_icmp_eq_imm noCalls s3 "%z" "%b2" (0 : BitVec 64)
    simp only [hl4] at h
    simpa [s4, zv] using h
  have hl_acc : lookupName s4.env "%acc" = some (.ptr 1) := by
    simp [s4, s3, s2, s1, State.bind, lookupName, hf.accPtr]
  have e5 : evalInstr noCalls s4 (.load "%a0" (.int 64) (.reg "%acc")) = some s5 := by
    have h := eval_load_64 noCalls s4 "%a0" (.reg "%acc") 1 acc hl_acc (by simpa [s4, s3, s2, s1, State.bind] using hf.accLoad)
    simpa [s5] using h
  have hl_sh2 : lookupName s5.env "%sh" = some (.int 64 shv) := by
    simp [s5, s4, s3, s2, s1, State.bind, lookupName, shv]
  have e6 : evalInstr noCalls s5 (.binop "%bit" .shl 64 (.imm (.int 64 128)) (.reg "%sh")) = some s6 := by
    have h := evalInstr_shl_imm_reg noCalls s5 "%bit" "%sh" (128 : BitVec 64)
    simp only [hl_sh2] at h
    simpa [s6, bitv] using h
  have hl_a0 : lookupName s6.env "%a0" = some (.int 64 acc) := by
    simp [s6, s5, s4, s3, s2, s1, State.bind, lookupName]
  have hl_bit : lookupName s6.env "%bit" = some (.int 64 bitv) := by
    simp [s6, State.bind, bitv]
  have e7 : evalInstr noCalls s6 (.binop "%a1" .or 64 (.reg "%a0") (.reg "%bit")) = some s7 := by
    have h := evalInstr_or_reg noCalls s6 "%a1" "%a0" "%bit"
    simp only [hl_a0, hl_bit] at h
    simpa [s7, a1v] using h
  have hl_z : lookupName s7.env "%z" = some (.int 1 zv) := by
    simp [s7, s6, s5, s4, State.bind, lookupName, zv]
  have hl_a1 : lookupName s7.env "%a1" = some (.int 64 a1v) := by
    simp [s7, State.bind, a1v]
  have hl_a0b : lookupName s7.env "%a0" = some (.int 64 acc) := by
    simp [s7, s6, s5, s4, s3, s2, s1, State.bind, lookupName]
  have e8 : evalInstr noCalls s7 (.select "%a2" (.int 64) (.reg "%z") (.reg "%a1") (.reg "%a0")) = some s8 := by
    have h := evalInstr_select_reg noCalls s7 "%a2" "%z" "%a1" "%a0"
    simp only [hl_z, hl_a1, hl_a0b] at h
    simp only [ite_int] at h
    simpa [s8, a2v] using h
  have hl_a2 : lookupName s8.env "%a2" = some (.int 64 a2v) := by
    simp [s8, State.bind, a2v]
  have hl_acc8 : lookupName s8.env "%acc" = some (.ptr 1) := by
    simp [s8, s7, s6, s5, s4, s3, s2, s1, State.bind, lookupName, hf.accPtr]
  have e9 : evalInstr noCalls s8 (.store (.int 64) (.reg "%a2") (.reg "%acc")) = some s9 := by
    have h := eval_store_64 noCalls s8 (.reg "%a2") (.reg "%acc") a2v 1 hl_a2 hl_acc8
    rw [h, hstore1]
  have hl_i1_9 : lookupName s9.env "%i1" = some (.int 64 (BitVec.ofNat 64 k)) := by
    simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.bind, lookupName, hi1]
  have e10 : evalInstr noCalls s9 (.binop "%i2" .add 64 (.reg "%i1") (.imm (.int 64 1))) = some s10 := by
    have h := evalInstr_add_imm noCalls s9 "%i2" "%i1" (1 : BitVec 64)
    simp only [hl_i1_9] at h
    simpa [s10, i2v] using h
  have hl_i2 : lookupName s10.env "%i2" = some (.int 64 i2v) := by
    simp [s10, State.bind, i2v]
  have hl_i10 : lookupName s10.env "%i" = some (.ptr 9) := by
    simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.bind, lookupName, hf.iPtr]
  have e11 : evalInstr noCalls s10 (.store (.int 64) (.reg "%i2") (.reg "%i")) = some s11 := by
    have h := eval_store_64 noCalls s10 (.reg "%i2") (.reg "%i") i2v 9 hl_i2 hl_i10
    rw [h, hstore2]
  refine ⟨s12, ?_, rfl, ?_⟩
  · have hfind : loopFunction.findBlock s.pc = some bodyBlock := by
      simp [loopFunction, Function.findBlock, findBlockList, hpc, bodyBlock, bodyInstrs,
        condBody]
    simp only [step, hfind, bodyBlock, bodyInstrs, denoteCode, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
    simp [execTerm, s12, s11]
  · have hsh : shv.toNat = 8 * k := by
      simp only [shv]
      rw [ofNat_mul_eight_lit k hk, ofNat_eight_mul_toNat k hk]
    have hbit : bitv = (0x80 : BitVec 64) <<< (8 * k) := by
      simp only [bitv, hsh]
    have hz : (zv = 1) ↔ isZeroByte m k := by
      simp only [zv, ofBool_eq_one]
      simp only [b2v, bv, hsh, isZeroByte]
    have ha2 : a2v = maskPrefix m (k + 1) := by
      simp only [a2v, a1v, hacc]
      rw [maskPrefix_succ]
      by_cases hp : isZeroByte m k
      · rw [ite_eq_left (hz.mpr hp), ite_eq_left hp, hbit]
      · rw [ite_eq_right (fun h => hp (hz.mp h)), ite_eq_right hp]
        simp
    have hi2 : i2v = BitVec.ofNat 64 (k + 1) := by
      simp only [i2v]
      rw [ofNat_add_one_lit k hk]
    have hbelow : loadValue
        (writeBytes (writeBytes s.mem 1 (natToBytes a2v.toNat 8)) 9 (natToBytes i2v.toNat 8))
        (.int 64) 1 =
        loadValue (writeBytes s.mem 1 (natToBytes a2v.toNat 8)) (.int 64) 1 :=
      loadValue_writeBytes_below (writeBytes s.mem 1 (natToBytes a2v.toNat 8))
        (natToBytes i2v.toNat 8) 64 1 9 (by decide)
    have hrt1 : loadValue (writeBytes s.mem 1 (natToBytes a2v.toNat 8)) (.int 64) 1 =
        some (.int 64 a2v) :=
      (loadValue_storeValue_64 s a2v 1).2
    have hrt2 : loadValue
        (writeBytes (writeBytes s.mem 1 (natToBytes a2v.toNat 8)) 9 (natToBytes i2v.toNat 8))
        (.int 64) 9 = some (.int 64 i2v) :=
      (loadValue_storeValue_64
        { s with mem := writeBytes s.mem 1 (natToBytes a2v.toNat 8) } i2v 9).2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.bind, lookupName, hf.mReg]
    · simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.bind, lookupName, hf.accPtr]
    · simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.bind, lookupName, hf.iPtr]
    · simp only [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.bind]
      rw [hbelow, hrt1, ha2]
    · simp only [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.bind]
      rw [hrt2, hi2]

theorem ofBool_ult_eight :
    BitVec.ofBool ((BitVec.ofNat 64 8).ult (8 : BitVec 64)) = 0 := by decide

/-- The condition block at counter eight: the branch to `done` is taken. -/
theorem cond_done_step (s : State) (m acc : BitVec 64)
    (hinv : LoopInv s m acc 8) :
    ∃ s', step noCalls loopFunction s = .jump s' ∧ s'.pc = "done" ∧
      LoopFacts s' m acc 8 := by
  obtain ⟨hpc, hf⟩ := hinv
  let s1 : State := s.bind "%i1" (.int 64 (BitVec.ofNat 64 8))
  let s2 : State :=
    s1.bind "%c" (.int 1 (BitVec.ofBool ((BitVec.ofNat 64 8).ult (8 : BitVec 64))))
  let s3 : State := { s2 with pc := "done" }
  have hli1 : lookupName s1.env "%i1" = some (.int 64 (BitVec.ofNat 64 8)) :=
    lookup_bind_self s "%i1" _
  have hlc : lookupName s2.env "%c" =
      some (.int 1 (BitVec.ofBool ((BitVec.ofNat 64 8).ult (8 : BitVec 64)))) :=
    lookup_bind_self s1 "%c" _
  have e1 : evalInstr noCalls s (.load "%i1" (.int 64) (.reg "%i")) = some s1 := by
    have h := eval_load_64 noCalls s "%i1" (.reg "%i") 9 (BitVec.ofNat 64 8) hf.iPtr hf.iLoad
    simpa [s1] using h
  have e2 : evalInstr noCalls s1 (.icmp "%c" .ult 64 (.reg "%i1") (.imm (.int 64 8))) = some s2 := by
    have h := evalInstr_icmp_ult_imm noCalls s1 "%c" "%i1" (8 : BitVec 64)
    simp only [hli1] at h
    simpa [s2] using h
  refine ⟨s3, ?_, rfl, ?_⟩
  · have hfind : loopFunction.findBlock s.pc = some condBody := by
      simp [loopFunction, Function.findBlock, findBlockList, hpc, condBody, condInstrs]
    simp only [step, hfind, condBody, condInstrs, denoteCode]
    rw [e1]
    simp only []
    rw [e2]
    simp only [execTerm, evalOperand, hlc, ofBool_ult_eight, s3]
    simp
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [s3, s2, s1, State.bind, lookupName, hf.mReg]
    · simp [s3, s2, s1, State.bind, lookupName, hf.accPtr]
    · simp [s3, s2, s1, State.bind, lookupName, hf.iPtr]
    · simp [s3, s2, s1, State.bind, hf.accLoad]
    · simp [s3, s2, s1, State.bind, hf.iLoad]

/-- The exit block: load the accumulator and return it. -/
theorem done_step (s : State) (m acc : BitVec 64)
    (hpc : s.pc = "done") (hf : LoopFacts s m acc 8) :
    ∃ s', step noCalls loopFunction s = .ret (some (.int 64 acc)) s' := by
  let s1 : State := s.bind "%r" (.int 64 acc)
  have hl_acc : lookupName s.env "%acc" = some (.ptr 1) := hf.accPtr
  have e1 : evalInstr noCalls s (.load "%r" (.int 64) (.reg "%acc")) = some s1 := by
    have h := eval_load_64 noCalls s "%r" (.reg "%acc") 1 acc hl_acc hf.accLoad
    simpa [s1] using h
  have hl_r : lookupName s1.env "%r" = some (.int 64 acc) := by
    simp [s1, State.bind]
  have hfind : loopFunction.findBlock s.pc = some doneBlock := by
    simp [loopFunction, Function.findBlock, findBlockList, hpc, doneBlock, doneInstrs,
      bodyBlock, condBody]
  refine ⟨s1, ?_⟩
  simp only [step, hfind, doneBlock, doneInstrs, denoteCode]
  rw [e1]
  simp only [execTerm, evalOperand, hl_r]

/-- Runs that have returned keep their result under more fuel. -/
theorem runFuel_ret_succ {f : Function} {s : State} {v : Option Value} {mem : Mem} :
    ∀ {n : Nat}, runFuel noCalls n f s = some (.ret v mem) →
      runFuel noCalls (n + 1) f s = some (.ret v mem)
  | 0, h => by
      simp only [runFuel] at h
      cases h
  | n + 1, h => by
      cases hs : step noCalls f s with
      | ub =>
          simp only [runFuel, hs] at h
          cases h
      | ret v' s' =>
          simp only [runFuel, hs] at h ⊢
          exact h
      | jump s' =>
          simp only [runFuel, hs] at h ⊢
          exact runFuel_ret_succ h

/-- The loop condition: from the invariant at `k`, `k ≤ 8`, the run returns the
full prefix.  The induction is on `8 - k`, i.e. on the counter, not on unrolled
copies of the body. -/
theorem cond_run_aux : ∀ (n : Nat) (s : State) (m acc : BitVec 64) (k : Nat),
    k ≤ 8 → 8 - k = n → acc = maskPrefix m k → LoopInv s m acc k →
    ∃ mem, runFuel noCalls (2 * n + 2) loopFunction s =
      some (.ret (some (.int 64 (maskPrefix m 8))) mem)
  | 0, s, m, acc, k, hk, hn, hacc, hinv => by
      have hk8 : k = 8 := by omega
      subst hk8
      obtain ⟨s1, h1, hp1, hf1⟩ := cond_done_step s m acc hinv
      obtain ⟨s2, h2⟩ := done_step s1 m acc hp1 hf1
      refine ⟨s2.mem, ?_⟩
      simp only [runFuel, h1, h2]
      rw [hacc]
  | n + 1, s, m, acc, k, hk, hn, hacc, hinv => by
      have hk8 : k < 8 := by omega
      obtain ⟨s1, h1, hp1, hf1, hi1⟩ := cond_step s m acc k hk8 hinv
      obtain ⟨s2, h2, hp2, hf2⟩ := body_step s1 m acc k hk8 hacc hp1 hf1 hi1
      obtain ⟨mem, hrun⟩ := cond_run_aux n s2 m (maskPrefix m (k + 1)) (k + 1)
        (by omega) (by omega) rfl ⟨hp2, hf2⟩
      refine ⟨mem, ?_⟩
      simp only [runFuel, h1, h2]
      rw [show 2 * (n + 1) = 2 * n + 2 from by omega, hrun]

/-- The loop returns the lane-wise specification. -/
theorem loop_returns_spec (x : BitVec 64) :
    ∃ mem, run noCalls loopFunction [.int 64 x] =
      some (.ret (some (.int 64 (spec x))) mem) := by
  have hstep : step noCalls loopFunction (initState loopFunction [.int 64 x]) =
      .jump (entryState x) := entry_run x
  obtain ⟨mem, hrun⟩ := cond_run_aux 8 (entryState x)
    (x ^^^ c 3182967604875373612) 0 0 (by decide) (by decide) (maskPrefix_zero _).symm
    (entry_inv x)
  refine ⟨mem, ?_⟩
  simp only [run]
  have hfuel : runFuel noCalls 10000 loopFunction (initState loopFunction [.int 64 x]) =
      runFuel noCalls 9999 loopFunction (entryState x) := by
    rw [runFuel, hstep]
  rw [hfuel]
  -- 9999 = 18 + 9981: returned at 18, remains under more fuel
  have h18 : runFuel noCalls 18 loopFunction (entryState x) =
      some (.ret (some (.int 64 (maskPrefix (x ^^^ c 3182967604875373612) 8))) mem) := by
    simpa using hrun
  have hmono : ∀ d, runFuel noCalls (18 + d) loopFunction (entryState x) =
      some (.ret (some (.int 64 (maskPrefix (x ^^^ c 3182967604875373612) 8))) mem) := by
    intro d
    induction d with
    | zero => simpa using h18
    | succ d ih =>
        rw [Nat.add_succ]
        exact runFuel_ret_succ ih
  rw [show 9999 = 18 + 9981 from by decide, hmono]
  -- the value is the specification
  rw [maskPrefix_eight, c_comma, ← spec_eq_maskFold]

end LeanLLVM.Vellum.CommaMaskLoop
