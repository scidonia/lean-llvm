/-
The block unit's refinement: the composition.

The body is the phase-split v2 shape: an ASCII-first loop that runs the
classifier's entry composition on each all-ASCII block, a hand-off that runs the
fused DFA on the first non-ASCII block, the fused UTF-8-gated loop, the peeled
tail, and the return word.

This module holds the trace skeleton: the chain steps the body's blocks use,
stated at the unit's own call environment, and the block runs in the order the
body composes them.  Each block run is one `denoteCode` equation at the block's
own instruction list; the tactic closes it, so the register values are the
block's own computation rather than a re-derivation.

The unit's environment binds the mask unit's two table intrinsics, the probe's
zero test, the DFA's saturating subtract, and — for a call that reaches the
escape list — the caller's own selection; a block that makes no call is
independent of the selection (`evalInstr_calls_irrelevance`).
-/
import LeanLLVM.Refinement.JsonS1BlocksBlocks
import LeanLLVM.Refinement.JsonS1BlocksReuse
import LeanLLVM.Refinement.BlockEvalVector
import LeanLLVM.Refinement.JsonUtf8IR
import LeanLLVM.Refinement.JsonUtf8Steps
import LeanLLVM.Refinement.JsonEscapeListContract
import LeanLLVM.Refinement.JsonEscapeIR
import LeanLLVM.Refinement.LoopFuel

namespace LeanLLVM.Refinement.JsonS1BlocksRefine

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BlockEvalVector
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonUtf8IR (reg)
open LeanLLVM.Refinement.BitLanes (ptestz)

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### Chain steps at an arbitrary integer width

`BlockEval`'s integer steps are stated at `i64`.  The body's prologue — the
arm truncation and the gate bit — is `i32`, so the same steps are needed at
`w`.  Each is the `i64` lemma's proof with the width generalized; the value is
the operation read at its own width. -/

theorem denoteCode_and_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w} (ha : lookupName env a = some (.int w x))
    (is : List Instr) :
    denoteCode calls (.binop d .and w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x &&& c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (show evalInstr calls (stateAt env s) (.binop d .and w (.reg a) (.imm (.int w c))) =
        some (stateAt ((d, .int w (x &&& c)) :: env) s) from by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
        using evalInstr_binop (op := .and) (r := (x &&& c).toNat)
          (ha := BlockEval.evalOperand_reg_of env s a (.int w x) ha)
          (hb := BlockEval.evalOperand_lit_of _ w c)
          (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat]))]

theorem denoteCode_or_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w} (ha : lookupName env a = some (.int w x))
    (is : List Instr) :
    denoteCode calls (.binop d .or w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x ||| c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (show evalInstr calls (stateAt env s) (.binop d .or w (.reg a) (.imm (.int w c))) =
        some (stateAt ((d, .int w (x ||| c)) :: env) s) from by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
        using evalInstr_binop (op := .or) (r := (x ||| c).toNat)
          (ha := BlockEval.evalOperand_reg_of env s a (.int w x) ha)
          (hb := BlockEval.evalOperand_lit_of _ w c)
          (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat]))]

theorem denoteCode_xor_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w} (ha : lookupName env a = some (.int w x))
    (is : List Instr) :
    denoteCode calls (.binop d .xor w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x ^^^ c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (show evalInstr calls (stateAt env s) (.binop d .xor w (.reg a) (.imm (.int w c))) =
        some (stateAt ((d, .int w (x ^^^ c)) :: env) s) from by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
        using evalInstr_binop (op := .xor) (r := (x ^^^ c).toNat)
          (ha := BlockEval.evalOperand_reg_of env s a (.int w x) ha)
          (hb := BlockEval.evalOperand_lit_of _ w c)
          (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat]))]

theorem denoteCode_add_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w} (ha : lookupName env a = some (.int w x))
    (is : List Instr) :
    denoteCode calls (.binop d .add w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x + c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (show evalInstr calls (stateAt env s) (.binop d .add w (.reg a) (.imm (.int w c))) =
        some (stateAt ((d, .int w (x + c)) :: env) s) from by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
        using evalInstr_binop (op := .add) (r := (x + c).toNat)
          (ha := BlockEval.evalOperand_reg_of env s a (.int w x) ha)
          (hb := BlockEval.evalOperand_lit_of _ w c)
          (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat]))]

theorem denoteCode_lshr_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w} (ha : lookupName env a = some (.int w x))
    (is : List Instr) :
    denoteCode calls (.binop d .lshr w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x >>> c.toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (show evalInstr calls (stateAt env s) (.binop d .lshr w (.reg a) (.imm (.int w c))) =
        some (stateAt ((d, .int w (x >>> c.toNat)) :: env) s) from by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
        using evalInstr_binop (op := .lshr) (r := (x >>> c.toNat).toNat)
          (ha := BlockEval.evalOperand_reg_of env s a (.int w x) ha)
          (hb := BlockEval.evalOperand_lit_of _ w c)
          (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat]))]

theorem denoteCode_icmp_ult_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w} (ha : lookupName env a = some (.int w x))
    (is : List Instr) :
    denoteCode calls (.icmp d .ult w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .ult x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (show evalInstr calls (stateAt env s) (.icmp d .ult w (.reg a) (.imm (.int w c))) =
        some (stateAt ((d, .int 1 (evalICmp .ult x c)) :: env) s) from by
      simpa only [stateAt, State.bind]
        using evalInstr_icmp (ha := BlockEval.evalOperand_reg_of env s a (.int w x) ha)
          (hb := BlockEval.evalOperand_lit_of _ w c))]

theorem denoteCode_icmp_eq_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w} (ha : lookupName env a = some (.int w x))
    (is : List Instr) :
    denoteCode calls (.icmp d .eq w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .eq x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (show evalInstr calls (stateAt env s) (.icmp d .eq w (.reg a) (.imm (.int w c))) =
        some (stateAt ((d, .int 1 (evalICmp .eq x c)) :: env) s) from by
      simpa only [stateAt, State.bind]
        using evalInstr_icmp (ha := BlockEval.evalOperand_reg_of env s a (.int w x) ha)
          (hb := BlockEval.evalOperand_lit_of _ w c))]

theorem denoteCode_or_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (w : Nat) {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y))
    (is : List Instr) :
    denoteCode calls (.binop d .or w (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x ||| y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (show evalInstr calls (stateAt env s) (.binop d .or w (.reg a) (.reg b)) =
        some (stateAt ((d, .int w (x ||| y)) :: env) s) from by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
        using evalInstr_binop (op := .or) (r := (x ||| y).toNat)
          (ha := BlockEval.evalOperand_reg_of env s a (.int w x) ha)
          (hb := BlockEval.evalOperand_reg_of env s b (.int w y) hb)
          (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat]))]

theorem denoteCode_icmp_ne_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w} (ha : lookupName env a = some (.int w x))
    (is : List Instr) :
    denoteCode calls (.icmp d .ne w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .ne x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (show evalInstr calls (stateAt env s) (.icmp d .ne w (.reg a) (.imm (.int w c))) =
        some (stateAt ((d, .int 1 (evalICmp .ne x c)) :: env) s) from by
      simpa only [stateAt, State.bind]
        using evalInstr_icmp (ha := BlockEval.evalOperand_reg_of env s a (.int w x) ha)
          (hb := BlockEval.evalOperand_lit_of _ w c))]

theorem denoteCode_icmp_ugt_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w} (ha : lookupName env a = some (.int w x))
    (is : List Instr) :
    denoteCode calls (.icmp d .ugt w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .ugt x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (show evalInstr calls (stateAt env s) (.icmp d .ugt w (.reg a) (.imm (.int w c))) =
        some (stateAt ((d, .int 1 (evalICmp .ugt x c)) :: env) s) from by
      simpa only [stateAt, State.bind]
        using evalInstr_icmp (ha := BlockEval.evalOperand_reg_of env s a (.int w x) ha)
          (hb := BlockEval.evalOperand_lit_of _ w c))]

/-- A one-byte load: `load i8`, whose value is the byte read. -/
theorem denoteCode_load8 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {b : UInt8} (hp : lookupName env p = some (.ptr a))
    (hr : readBytes s.mem a 1 = some [b]) (is : List Instr) :
    denoteCode calls (.load d (.int 8) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 8 (BitVec.ofNat 8 b.toNat)) :: env) s) := by
  have hstep : evalInstr calls (stateAt env s) (.load d (.int 8) (.reg p)) =
      some (stateAt ((d, .int 8 (BitVec.ofNat 8 b.toNat)) :: env) s) := by
    rw [evalInstr_load (hp := BlockEval.evalOperand_reg_of env s p (.ptr a) hp)
      (hv := by
        show loadValue s.mem (.int 8) a = some (.int 8 (BitVec.ofNat 8 b.toNat))
        simp only [loadValue]
        rw [show (8 + 7) / 8 = 1 from rfl, hr]
        simp [bytesToNat])]
    simp only [stateAt, State.bind]
  rw [denoteCode_cons_of _ _ _ _ _ hstep]

/-- A `select` whose two values are constants and whose condition is a register:
the `i64` the return composes from the error bit. -/
theorem denoteCode_select_bit_imm_imm (calls : Calls) (env : Env) (s : State)
    (d c : String) {bb : BitVec 1} {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 bb)) (is : List Instr) :
    denoteCode calls
        (.select d (.int 64) (.reg c) (.imm (.int 64 x)) (.imm (.int 64 y)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (if bb = 1 then x else y)) :: env) s) := by
  have hstep : evalInstr calls (stateAt env s)
      (.select d (.int 64) (.reg c) (.imm (.int 64 x)) (.imm (.int 64 y))) =
      some (stateAt ((d, .int 64 (if bb = 1 then x else y)) :: env) s) := by
    rcases bitVec1_eq_zero_or_one bb with h | h
    · subst h
      rw [evalInstr_select_false
        (hc := BlockEval.evalOperand_reg_of env s c (.int 1 (0 : BitVec 1)) hc)
        (ha := BlockEval.evalOperand_lit_of _ 64 x)
        (hb := BlockEval.evalOperand_lit_of _ 64 y)]
      simp [stateAt, State.bind]
    · subst h
      rw [evalInstr_select_true
        (hc := BlockEval.evalOperand_reg_of env s c (.int 1 (1 : BitVec 1)) hc)
        (ha := BlockEval.evalOperand_lit_of _ 64 x)
        (hb := BlockEval.evalOperand_lit_of _ 64 y)]
      simp [stateAt, State.bind]
  rw [denoteCode_cons_of _ _ _ _ _ hstep]

/-! ### The two-argument intrinsic call, at the unit's environment

The probe is `i32 (<4 x i64>, <4 x i64>)`, the table lookup is `<32 x i8>` at
both argument types, and the saturating subtract is `<32 x i8>`: one step covers
all three, with the result and argument types named. -/

theorem denoteCode_call2t (calls : Calls) (env : Env) (s : State) (d callee : String)
    (dTy aTy1 aTy2 : Ty) (o1 o2 : Operand) {v1 v2 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (hc : calls callee [v1, v2] s.mem s.next = some r) (is : List Instr) :
    denoteCode calls (.call d dTy callee [(aTy1, o1), (aTy2, o2)] :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, r.ret) :: env)
        { s with mem := r.mem, next := r.next }) := by
  have hstep : evalInstr calls (stateAt env s)
      (.call d dTy callee [(aTy1, o1), (aTy2, o2)]) =
      some (stateAt ((d, r.ret) :: env) { s with mem := r.mem, next := r.next }) := by
    have ha : evalOperands (stateAt env s) [(aTy1, o1), (aTy2, o2)]
        = some [v1, v2] := by
      simp [evalOperands, h1, h2]
    rw [evalInstr_call (s := stateAt env s) ha hc]
    simp only [stateAt]
  rw [denoteCode_cons_of _ _ _ _ _ hstep]

/-- The probe, at the unit's environment: the zero test of two `<4 x i64>`
operands, as `ptestz` reads their packed words. -/
theorem denoteCode_ptestz_b (env : Env) (s : State) (dst : String)
    (o1 o2 : Operand) {a b : List (BitVec 64)}
    (h1 : evalOperand (stateAt env s) o1 = some (.vec 4 64 a))
    (h2 : evalOperand (stateAt env s) o2 = some (.vec 4 64 b)) (is : List Instr) :
    denoteCode s1BlocksCalls
        (.call dst (.int 32) "llvm.x86.avx.ptestz.256"
          [(.vec 4 (.int 64), o1), (.vec 4 (.int 64), o2)] :: is) (stateAt env s) =
      denoteCode s1BlocksCalls is
        (stateAt ((dst, .int 32 (ptestz (BitVec.ofNat 256 (packLanes a))
          (BitVec.ofNat 256 (packLanes b)))) :: env) s) := by
  have hstep : evalInstr s1BlocksCalls (stateAt env s)
      (.call dst (.int 32) "llvm.x86.avx.ptestz.256"
        [(.vec 4 (.int 64), o1), (.vec 4 (.int 64), o2)]) =
      some (stateAt ((dst, .int 32 (ptestz (BitVec.ofNat 256 (packLanes a))
        (BitVec.ofNat 256 (packLanes b)))) :: env) s) := by
    have ha : evalOperands (stateAt env s)
        [(.vec 4 (.int 64), o1), (.vec 4 (.int 64), o2)] =
        some [.vec 4 64 a, .vec 4 64 b] := by
      simp [evalOperands, h1, h2]
    rw [evalInstr_call (s := stateAt env s) ha
      (s1BlocksCalls_ptestz a b s.mem s.next)]
    simp only [stateAt]
  rw [denoteCode_cons_of _ _ _ _ _ hstep]

/-! ### The block tactic

`block_step_v` covers the vector and `i64` shapes; the width-generic steps are
appended for the prologue's `i32` arithmetic. -/

macro "block_step_b" : tactic => `(tactic|
  (first
   | block_step_v
   | rw [denoteCode_and_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_or_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_xor_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_add_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_lshr_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_icmp_ult_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_icmp_eq_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_or_reg_w _ _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_icmp_ne_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_icmp_ugt_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_load8 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_select_bit_imm_imm _ _ _ _ _ ?_ _]
   | rw [denoteCode_ptestz_b _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_call2t _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ _]))

macro "block_eval_b" : tactic => `(tactic|
  (repeat block_step_b
   block_close_v))

/-! ### `entry` -/

/-- The arm's low word, as `trunc i64` binds it. -/
def entryTrunc (arm : BitVec 64) : BitVec 32 :=
  BitVec.ofNat 32 (arm.toNat % 2 ^ 32)

/-- The gate bit: `(%arm >> 2) & 1`, the arm's bit 2. -/
def entryGate (arm : BitVec 64) : BitVec 32 :=
  (entryTrunc arm >>> 2) &&& 1

/-- `entry`'s environment: the block's six cells applied to the incoming one. -/
def entryEnv (env : Env) (n arm : BitVec 64) : Env :=
  cells [("%cmp2506.not", .int 1 (evalICmp .ult n 64)),
         ("%conv", .int 32 (entryGate arm)),
         ("%1", .int 32 (entryTrunc arm >>> 2)),
         ("%0", .int 32 (entryTrunc arm)),
         ("%and", .int 64 (n &&& 63)),
         ("%shr", .int 64 (n >>> 6))] env

theorem entry_denote (env : Env) (s : State) (n arm : BitVec 64)
    (hn : lookupName env "%n" = some (.int 64 n))
    (harm : lookupName env "%arm" = some (.int 64 arm)) :
    denoteCode s1BlocksCalls entryInstrs (stateAt env s) =
      some (stateAt (entryEnv env n arm) s) := by
  unfold entryInstrs entryEnv
  block_eval_b

/-! ### One control step, and the branches

A block's `denoteCode` run and its terminator compose into one `step`; the
branch lemmas read the condition at the state the run leaves. -/

theorem step_at {calls : Calls} {f : Function} {s s' : State} {b : Block}
    (hfind : f.findBlock s.pc = some b)
    (hbody : denoteCode calls b.instrs s = some s') :
    step calls f s = execTerm s' b.term := by
  simp only [step, hfind, hbody]

theorem execTerm_br (s : State) (t : String) :
    execTerm s (.br t) = .jump { s with pc := t, pre := some s.pc } := rfl

theorem execTerm_condbr_true {s : State} {c : Operand} {bit : BitVec 1}
    {t f : String} (h : evalOperand s c = some (.int 1 bit)) (hb : bit = 1) :
    execTerm s (.condbr c t f) = .jump { s with pc := t, pre := some s.pc } := by
  simp [execTerm, h, hb]

theorem execTerm_condbr_false {s : State} {c : Operand} {bit : BitVec 1}
    {t f : String} (h : evalOperand s c = some (.int 1 bit)) (hb : bit = 0) :
    execTerm s (.condbr c t f) = .jump { s with pc := f, pre := some s.pc } := by
  simp [execTerm, h, hb]

/-- The entry's terminator branches to `if.end50` on a short document and to the
ASCII loop otherwise. -/
theorem entry_step_short (env : Env) (s : State) (n arm : BitVec 64)
    (hpc : s.pc = "entry")
    (hn : lookupName env "%n" = some (.int 64 n))
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hbit : evalICmp .ult n 64 = 1) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (entryEnv env n arm)
        { s with pc := "if.end50", pre := some "entry" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some entryBlock := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_entry
  rw [step_at hfind (entry_denote env s n arm hn harm)]
  rw [show entryBlock.term = entryTerm from rfl]
  simp only [entryTerm]
  rw [execTerm_condbr_true
    (BlockEval.evalOperand_reg_of _ _ _ _ (by
      simp [entryEnv, cells])) hbit]
  simp only [stateAt, hpc]

theorem entry_step_blocks (env : Env) (s : State) (n arm : BitVec 64)
    (hpc : s.pc = "entry")
    (hn : lookupName env "%n" = some (.int 64 n))
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hbit : evalICmp .ult n 64 = 0) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (entryEnv env n arm)
        { s with pc := "for.body.lr.ph", pre := some "entry" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some entryBlock := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_entry
  rw [step_at hfind (entry_denote env s n arm hn harm)]
  rw [show entryBlock.term = entryTerm from rfl]
  simp only [entryTerm]
  rw [execTerm_condbr_false
    (BlockEval.evalOperand_reg_of _ _ _ _ (by
      simp [entryEnv, cells])) hbit]
  simp only [stateAt, hpc]

/-! ### `for.body.lr.ph` -/

/-- The escape gate: `%tobool.not` is `(arm & 2) = 0`. -/
def lrPhEnv (env : Env) (arm : BitVec 64) : Env :=
  cells [("%tobool.not", .int 1 (evalICmp .eq (arm &&& 2) 0)),
         ("%and18", .int 64 (arm &&& 2))] env

theorem for_body_lr_ph_denote (env : Env) (s : State) (arm : BitVec 64)
    (harm : lookupName env "%arm" = some (.int 64 arm)) :
    denoteCode s1BlocksCalls for_body_lr_phInstrs (stateAt env s) =
      some (stateAt (lrPhEnv env arm) s) := by
  unfold for_body_lr_phInstrs lrPhEnv
  block_eval_b

theorem for_body_lr_ph_step (env : Env) (s : State) (arm : BitVec 64)
    (hpc : s.pc = "for.body.lr.ph")
    (harm : lookupName env "%arm" = some (.int 64 arm)) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (lrPhEnv env arm)
        { s with pc := "for.body", pre := some "for.body.lr.ph" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some for_body_lr_phBlock := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_for_body_lr_ph
  rw [step_at hfind (for_body_lr_ph_denote env s arm harm)]
  rw [show for_body_lr_phBlock.term = for_body_lr_phTerm from rfl]
  simp only [for_body_lr_phTerm, execTerm]
  simp only [stateAt, hpc]

/-! ### `for.inc` -/

/-- The latch's successor: the incremented index and the loop's exit test. -/
def forIncEnv (env : Env) (i shr : BitVec 64) : Env :=
  cells [("%exitcond.not", .int 1 (evalICmp .eq (i + 1) shr)),
         ("%inc", .int 64 (i + 1))] env

theorem for_inc_denote (env : Env) (s : State) (i shr : BitVec 64)
    (hi : lookupName env "%i.0510" = some (.int 64 i))
    (hshr : lookupName env "%shr" = some (.int 64 shr)) :
    denoteCode s1BlocksCalls for_incInstrs (stateAt env s) =
      some (stateAt (forIncEnv env i shr) s) := by
  unfold for_incInstrs forIncEnv
  block_eval_b

theorem for_inc_step_exit (env : Env) (s : State) (i shr : BitVec 64)
    (hpc : s.pc = "for.inc")
    (hi : lookupName env "%i.0510" = some (.int 64 i))
    (hshr : lookupName env "%shr" = some (.int 64 shr))
    (hbit : evalICmp .eq (i + 1) shr = 1) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (forIncEnv env i shr)
        { s with pc := "for.end101", pre := some "for.inc" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some for_incBlock := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_for_inc
  rw [step_at hfind (for_inc_denote env s i shr hi hshr)]
  rw [show for_incBlock.term = for_incTerm from rfl]
  simp only [for_incTerm]
  rw [execTerm_condbr_true
    (BlockEval.evalOperand_reg_of _ _ _ _ (by simp [forIncEnv, cells])) hbit]
  simp only [stateAt, hpc]

theorem for_inc_step_loop (env : Env) (s : State) (i shr : BitVec 64)
    (hpc : s.pc = "for.inc")
    (hi : lookupName env "%i.0510" = some (.int 64 i))
    (hshr : lookupName env "%shr" = some (.int 64 shr))
    (hbit : evalICmp .eq (i + 1) shr = 0) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (forIncEnv env i shr)
        { s with pc := "for.body", pre := some "for.inc" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some for_incBlock := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_for_inc
  rw [step_at hfind (for_inc_denote env s i shr hi hshr)]
  rw [show for_incBlock.term = for_incTerm from rfl]
  simp only [for_incTerm]
  rw [execTerm_condbr_false
    (BlockEval.evalOperand_reg_of _ _ _ _ (by simp [forIncEnv, cells])) hbit]
  simp only [stateAt, hpc]

/-! ### `if.end93` — the fused loop's accumulator merge

`%u8k.2` is the accumulator after the DFA arm (or the incoming one when the arm
is skipped), and the terminator is the escape gate. -/

def ifEnd93Env (env : Env) (u8k : List (BitVec 64)) : Env :=
  cells [("%u8k.2", .vec 4 64 u8k)] env

theorem if_end93_denote (env : Env) (s : State) (p : String) (op : Operand)
    (u8k : List (BitVec 64))
    (hpre : s.pre = some p)
    (hinc : phiIncoming p [("for.body54", .reg "%u8k.1521"),
      ("if.then90", .reg "%or.i281")] = some op)
    (hop : evalOperand (stateAt env s) op = some (.vec 4 64 u8k)) :
    denoteCode s1BlocksCalls if_end93Instrs (stateAt env s) =
      some (stateAt (ifEnd93Env env u8k) s) := by
  unfold if_end93Instrs ifEnd93Env
  block_eval_b

theorem if_end93_step_skip (env : Env) (s : State) (p : String) (op : Operand)
    (u8k : List (BitVec 64)) (b : BitVec 1)
    (hpc : s.pc = "if.end93")
    (hpre : s.pre = some p)
    (hinc : phiIncoming p [("for.body54", .reg "%u8k.1521"),
      ("if.then90", .reg "%or.i281")] = some op)
    (hop : evalOperand (stateAt env s) op = some (.vec 4 64 u8k))
    (hg : lookupName env "%tobool95.not" = some (.int 1 b))
    (hbit : b = 1) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd93Env env u8k)
        { s with pc := "if.end98", pre := some "if.end93" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_end93Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_end93
  rw [step_at hfind (if_end93_denote env s p op u8k hpre hinc hop)]
  rw [show if_end93Block.term = if_end93Term from rfl]
  simp only [if_end93Term]
  rw [execTerm_condbr_true
    (BlockEval.evalOperand_reg_of _ _ _ _ (by
      rw [ifEnd93Env]
      show lookupName (("%u8k.2", .vec 4 64 u8k) :: env) "%tobool95.not"
        = some (.int 1 b)
      exact (lookupName_cons_ne _ _ (by decide)).trans hg)) hbit]
  simp only [stateAt, hpc]

theorem if_end93_step_escape (env : Env) (s : State) (p : String) (op : Operand)
    (u8k : List (BitVec 64)) (b : BitVec 1)
    (hpc : s.pc = "if.end93")
    (hpre : s.pre = some p)
    (hinc : phiIncoming p [("for.body54", .reg "%u8k.1521"),
      ("if.then90", .reg "%or.i281")] = some op)
    (hop : evalOperand (stateAt env s) op = some (.vec 4 64 u8k))
    (hg : lookupName env "%tobool95.not" = some (.int 1 b))
    (hbit : b = 0) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd93Env env u8k)
        { s with pc := "if.then96", pre := some "if.end93" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_end93Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_end93
  rw [step_at hfind (if_end93_denote env s p op u8k hpre hinc hop)]
  rw [show if_end93Block.term = if_end93Term from rfl]
  simp only [if_end93Term]
  rw [execTerm_condbr_false
    (BlockEval.evalOperand_reg_of _ _ _ _ (by
      rw [ifEnd93Env]
      show lookupName (("%u8k.2", .vec 4 64 u8k) :: env) "%tobool95.not"
        = some (.int 1 b)
      exact (lookupName_cons_ne _ _ (by decide)).trans hg)) hbit]
  simp only [stateAt, hpc]

/-! ### `if.end98` — the fused loop's latch -/

def ifEnd98Env (env : Env) (i shr : BitVec 64) : Env :=
  cells [("%exitcond537.not", .int 1 (evalICmp .eq (i + 1) shr)),
         ("%inc100", .int 64 (i + 1))] env

theorem if_end98_denote (env : Env) (s : State) (i shr : BitVec 64)
    (hi : lookupName env "%i.2523" = some (.int 64 i))
    (hshr : lookupName env "%shr" = some (.int 64 shr)) :
    denoteCode s1BlocksCalls if_end98Instrs (stateAt env s) =
      some (stateAt (ifEnd98Env env i shr) s) := by
  unfold if_end98Instrs ifEnd98Env
  block_eval_b

theorem if_end98_step_exit (env : Env) (s : State) (i shr : BitVec 64)
    (hpc : s.pc = "if.end98")
    (hi : lookupName env "%i.2523" = some (.int 64 i))
    (hshr : lookupName env "%shr" = some (.int 64 shr))
    (hbit : evalICmp .eq (i + 1) shr = 1) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd98Env env i shr)
        { s with pc := "for.end101", pre := some "if.end98" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_end98Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_end98
  rw [step_at hfind (if_end98_denote env s i shr hi hshr)]
  rw [show if_end98Block.term = if_end98Term from rfl]
  simp only [if_end98Term]
  rw [execTerm_condbr_true
    (BlockEval.evalOperand_reg_of _ _ _ _ (by simp [ifEnd98Env, cells])) hbit]
  simp only [stateAt, hpc]

theorem if_end98_step_loop (env : Env) (s : State) (i shr : BitVec 64)
    (hpc : s.pc = "if.end98")
    (hi : lookupName env "%i.2523" = some (.int 64 i))
    (hshr : lookupName env "%shr" = some (.int 64 shr))
    (hbit : evalICmp .eq (i + 1) shr = 0) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd98Env env i shr)
        { s with pc := "for.body54", pre := some "if.end98" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_end98Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_end98
  rw [step_at hfind (if_end98_denote env s i shr hi hshr)]
  rw [show if_end98Block.term = if_end98Term from rfl]
  simp only [if_end98Term]
  rw [execTerm_condbr_false
    (BlockEval.evalOperand_reg_of _ _ _ _ (by simp [ifEnd98Env, cells])) hbit]
  simp only [stateAt, hpc]

/-! ### `if.end147` — the peeled tail's accumulator merge -/

def ifEnd147Env (env : Env) (arm : BitVec 64) (u8k : List (BitVec 64)) : Env :=
  cells [("%tobool149.not", .int 1 (evalICmp .eq (arm &&& 2) 0)),
         ("%and148", .int 64 (arm &&& 2)),
         ("%u8k.3", .vec 4 64 u8k)] env

theorem if_end147_denote (env : Env) (s : State) (p : String) (op : Operand)
    (arm : BitVec 64) (u8k : List (BitVec 64))
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hpre : s.pre = some p)
    (hinc : phiIncoming p [("if.then103", .reg "%u8k.1.lcssa"),
      ("if.then144", .reg "%or.i")] = some op)
    (hop : evalOperand (stateAt env s) op = some (.vec 4 64 u8k)) :
    denoteCode s1BlocksCalls if_end147Instrs (stateAt env s) =
      some (stateAt (ifEnd147Env env arm u8k) s) := by
  unfold if_end147Instrs ifEnd147Env
  block_eval_b

theorem if_end147_step_thread (env : Env) (s : State) (p : String) (op : Operand)
    (arm : BitVec 64) (u8k : List (BitVec 64))
    (hpc : s.pc = "if.end147")
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hpre : s.pre = some p)
    (hinc : phiIncoming p [("if.then103", .reg "%u8k.1.lcssa"),
      ("if.then144", .reg "%or.i")] = some op)
    (hop : evalOperand (stateAt env s) op = some (.vec 4 64 u8k))
    (hbit : evalICmp .eq (arm &&& 2) 0 = 1) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd147Env env arm u8k)
        { s with pc := "if.end153.thread", pre := some "if.end147" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_end147Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_end147
  rw [step_at hfind (if_end147_denote env s p op arm u8k harm hpre hinc hop)]
  rw [show if_end147Block.term = if_end147Term from rfl]
  simp only [if_end147Term]
  rw [execTerm_condbr_true
    (BlockEval.evalOperand_reg_of _ _ _ _ (by
      rw [ifEnd147Env]; simp [cells])) hbit]
  simp only [stateAt, hpc]

theorem if_end147_step_escape (env : Env) (s : State) (p : String) (op : Operand)
    (arm : BitVec 64) (u8k : List (BitVec 64))
    (hpc : s.pc = "if.end147")
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hpre : s.pre = some p)
    (hinc : phiIncoming p [("if.then103", .reg "%u8k.1.lcssa"),
      ("if.then144", .reg "%or.i")] = some op)
    (hop : evalOperand (stateAt env s) op = some (.vec 4 64 u8k))
    (hbit : evalICmp .eq (arm &&& 2) 0 = 0) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd147Env env arm u8k)
        { s with pc := "if.then150", pre := some "if.end147" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_end147Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_end147
  rw [step_at hfind (if_end147_denote env s p op arm u8k harm hpre hinc hop)]
  rw [show if_end147Block.term = if_end147Term from rfl]
  simp only [if_end147Term]
  rw [execTerm_condbr_false
    (BlockEval.evalOperand_reg_of _ _ _ _ (by
      rw [ifEnd147Env]; simp [cells])) hbit]
  simp only [stateAt, hpc]

/-! ### The verdict blocks

Both read the accumulator's zero test and the document's last-byte check; the
probe is `ptestz` of the accumulator against itself. -/

/-- The accumulator's zero test: `ptestz u8k u8k`. -/
def ptestzU8k (u8k : List (BitVec 64)) : BitVec 32 :=
  ptestz (BitVec.ofNat 256 (packLanes u8k)) (BitVec.ofNat 256 (packLanes u8k))

def ifEnd153ThreadEnv (env : Env) (u8k : List (BitVec 64)) : Env :=
  cells [("%cmp155495", .int 1 (evalICmp .eq (ptestzU8k u8k) 0)),
         ("%199", .int 32 (ptestzU8k u8k))] env

theorem if_end153_thread_denote (env : Env) (s : State) (u8k : List (BitVec 64))
    (hu : lookupName env "%u8k.3" = some (.vec 4 64 u8k)) :
    denoteCode s1BlocksCalls if_end153_threadInstrs (stateAt env s) =
      some (stateAt (ifEnd153ThreadEnv env u8k) s) := by
  unfold if_end153_threadInstrs ifEnd153ThreadEnv
  block_eval_b

theorem if_end153_thread_step (env : Env) (s : State) (u8k : List (BitVec 64))
    (hpc : s.pc = "if.end153.thread")
    (hu : lookupName env "%u8k.3" = some (.vec 4 64 u8k)) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd153ThreadEnv env u8k)
        { s with pc := "if.end170", pre := some "if.end153.thread" }) := by
  have hfind :
      s1BlocksFunction.findBlock (stateAt env s).pc = some if_end153_threadBlock := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_end153_thread
  rw [step_at hfind (if_end153_thread_denote env s u8k hu)]
  rw [show if_end153_threadBlock.term = if_end153_threadTerm from rfl]
  simp only [if_end153_threadTerm, execTerm]
  simp only [stateAt, hpc]

def ifEnd153Env (env : Env) (n : BitVec 64) (u8k : List (BitVec 64)) : Env :=
  cells [("%cmp158.not.not", .int 1 (evalICmp .eq n 0)),
         ("%cmp155", .int 1 (evalICmp .eq (ptestzU8k u8k) 0)),
         ("%200", .int 32 (ptestzU8k u8k))] env

theorem if_end153_denote (env : Env) (s : State) (n : BitVec 64)
    (u8k : List (BitVec 64))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hu : lookupName env "%u8k.1.lcssa" = some (.vec 4 64 u8k)) :
    denoteCode s1BlocksCalls if_end153Instrs (stateAt env s) =
      some (stateAt (ifEnd153Env env n u8k) s) := by
  unfold if_end153Instrs ifEnd153Env
  block_eval_b

theorem if_end153_step_nothing (env : Env) (s : State) (n : BitVec 64)
    (u8k : List (BitVec 64))
    (hpc : s.pc = "if.end153")
    (hn : lookupName env "%n" = some (.int 64 n))
    (hu : lookupName env "%u8k.1.lcssa" = some (.vec 4 64 u8k))
    (hbit : evalICmp .eq n 0 = 1) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd153Env env n u8k)
        { s with pc := "if.end170", pre := some "if.end153" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_end153Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_end153
  rw [step_at hfind (if_end153_denote env s n u8k hn hu)]
  rw [show if_end153Block.term = if_end153Term from rfl]
  simp only [if_end153Term]
  rw [execTerm_condbr_true
    (BlockEval.evalOperand_reg_of _ _ _ _ (by
      rw [ifEnd153Env]; simp [cells])) hbit]
  simp only [stateAt, hpc]

theorem if_end153_step_tail (env : Env) (s : State) (n : BitVec 64)
    (u8k : List (BitVec 64))
    (hpc : s.pc = "if.end153")
    (hn : lookupName env "%n" = some (.int 64 n))
    (hu : lookupName env "%u8k.1.lcssa" = some (.vec 4 64 u8k))
    (hbit : evalICmp .eq n 0 = 0) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd153Env env n u8k)
        { s with pc := "if.then164", pre := some "if.end153" }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_end153Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_end153
  rw [step_at hfind (if_end153_denote env s n u8k hn hu)]
  rw [show if_end153Block.term = if_end153Term from rfl]
  simp only [if_end153Term]
  rw [execTerm_condbr_false
    (BlockEval.evalOperand_reg_of _ _ _ _ (by
      rw [ifEnd153Env]; simp [cells])) hbit]
  simp only [stateAt, hpc]

/-! ### `if.end170` — the return word

The two phis select the ASCII word and the error bit; the probe tests the ASCII
word against the high-bit mask, the error bit becomes `2`, and the return is
their join. -/

/-- The probe's mask lanes: the high bit of every byte. -/
def highMaskLanes : List (BitVec 64) :=
  List.replicate 4 (0x8080808080808080#64)

/-- The verdict: `ptestz` of the ASCII word against the high-bit mask. -/
def asciiProbe (ascii : List (BitVec 64)) : BitVec 32 :=
  ptestz (BitVec.ofNat 256 (packLanes ascii))
    (BitVec.ofNat 256 (packLanes highMaskLanes))

/-- The two-bit return word: the ASCII bit and the UTF-8 error bit. -/
def verdictWord (ascii : List (BitVec 64)) (err : BitVec 1) : BitVec 64 :=
  (if err = 1 then (2 : BitVec 64) else 0) |||
    BitVec.ofNat 64 (evalICmp .ne (asciiProbe ascii) (0 : BitVec 32)).toNat

def ifEnd170Env (env : Env) (ascii : List (BitVec 64)) (err : BitVec 1) : Env :=
  cells [("%or176", .int 64 (verdictWord ascii err)),
         ("%shl175", .int 64 (if err = 1 then (2 : BitVec 64) else 0)),
         ("%conv174", .int 64
           (BitVec.ofNat 64 (evalICmp .ne (asciiProbe ascii) (0 : BitVec 32)).toNat)),
         ("%cmp172", .int 1 (evalICmp .ne (asciiProbe ascii) (0 : BitVec 32))),
         ("%205", .int 32 (asciiProbe ascii)),
         ("%err.0.in", .int 1 err),
         ("%ascii.2499", .vec 4 64 ascii)] env

theorem if_end170_denote (env : Env) (s : State) (p : String)
    (op1 op2 : Operand) (ascii : List (BitVec 64)) (err : BitVec 1)
    (hpre : s.pre = some p)
    (hinc1 : phiIncoming p [("if.then164", .reg "%ascii.1.lcssa"),
      ("if.end153", .reg "%ascii.1.lcssa"),
      ("if.end153.thread", .reg "%or.i279")] = some op1)
    (hop1 : evalOperand (stateAt env s) op1 = some (.vec 4 64 ascii))
    (hinc2 : phiIncoming p [("if.then164", .reg "%or169500"),
      ("if.end153", .reg "%cmp155"),
      ("if.end153.thread", .reg "%cmp155495")] = some op2)
    (hop2 : evalOperand (stateAt env s) op2 = some (.int 1 err)) :
    denoteCode s1BlocksCalls if_end170Instrs (stateAt env s) =
      some (stateAt (ifEnd170Env env ascii err) s) := by
  unfold if_end170Instrs ifEnd170Env
  block_eval_b

theorem execTerm_ret_int64 {s : State} {v : Operand} {x : Value}
    (h : evalOperand s v = some x) :
    execTerm s (.ret (.int 64) (some v)) = .ret (some x) s := by
  simp [execTerm, h]

theorem if_end170_step (env : Env) (s : State) (p : String)
    (op1 op2 : Operand) (ascii : List (BitVec 64)) (err : BitVec 1)
    (hpc : s.pc = "if.end170")
    (hpre : s.pre = some p)
    (hinc1 : phiIncoming p [("if.then164", .reg "%ascii.1.lcssa"),
      ("if.end153", .reg "%ascii.1.lcssa"),
      ("if.end153.thread", .reg "%or.i279")] = some op1)
    (hop1 : evalOperand (stateAt env s) op1 = some (.vec 4 64 ascii))
    (hinc2 : phiIncoming p [("if.then164", .reg "%or169500"),
      ("if.end153", .reg "%cmp155"),
      ("if.end153.thread", .reg "%cmp155495")] = some op2)
    (hop2 : evalOperand (stateAt env s) op2 = some (.int 1 err)) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .ret (some (.int 64 (verdictWord ascii err)))
        (stateAt (ifEnd170Env env ascii err) s) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_end170Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_end170
  rw [step_at hfind (if_end170_denote env s p op1 op2 ascii err hpre hinc1 hop1 hinc2 hop2)]
  rw [show if_end170Block.term = if_end170Term from rfl]
  simp only [if_end170Term]
  rw [execTerm_ret_int64 (v := .reg "%or176") (x := .int 64 (verdictWord ascii err))
    (BlockEval.evalOperand_reg_of _ _ _ _ (by simp [ifEnd170Env, cells]))]

/-! ### Axiom footprints

The block runs and the branch lemmas compute from the block's own literal lists;
none of them reads a choice principle.  The call steps are the unit's four
intrinsic arms. -/

#print axioms denoteCode_ptestz_b
#print axioms denoteCode_load8
#print axioms denoteCode_select_bit_imm_imm
#print axioms entry_denote
#print axioms entry_step_short
#print axioms for_body_lr_ph_denote
#print axioms for_inc_step_exit
#print axioms if_end93_denote
#print axioms if_end98_step_loop
#print axioms if_end147_step_thread
#print axioms if_end153_thread_denote
#print axioms if_end153_denote
#print axioms if_end170_denote
#print axioms if_end170_step

end LeanLLVM.Refinement.JsonS1BlocksRefine
