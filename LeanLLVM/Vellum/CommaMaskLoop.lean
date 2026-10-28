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

/-- `probes/install/ir/loop.ll`, as an AST. -/
def loopFunction : Function :=
  { name := "leanllvm_comma_mask8_loop", retTy := .int 64, params := [("%arg", .int 64)],
    blocks := [
      { name := "entry", instrs := entryInstrs, term := .br "cond" },
      { name := "cond", instrs := condInstrs,
        term := .condbr (.reg "%c") "body" "done" },
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

/-- The accumulator is the lane prefix and the counter is `k`; the two pointers
are the addresses `alloca` assigns, and the block is `cond`. -/
def LoopInv (s : State) (m acc : BitVec 64) (k : Nat) : Prop :=
  s.pc = "cond" ∧
  lookupName s.env "%m" = some (.int 64 m) ∧
  lookupName s.env "%acc" = some (.ptr 1) ∧
  lookupName s.env "%i" = some (.ptr 9) ∧
  loadValue s.mem (.int 64) 1 = some (.int 64 acc) ∧
  loadValue s.mem (.int 64) 9 = some (.int 64 (BitVec.ofNat 64 k))

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

theorem entry_inv (x : BitVec 64) :
    LoopInv (entryState x) (x ^^^ c 3182967604875373612) 0 0 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
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

end LeanLLVM.Vellum.CommaMaskLoop
