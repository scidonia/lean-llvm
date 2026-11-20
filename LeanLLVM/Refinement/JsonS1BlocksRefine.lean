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
import LeanLLVM.Refinement.JsonEntrySteps
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

/-! ### The vector intrinsics, at the unit's call environment

`BlockEvalVector` states the table lookup and the carry-less product at the mask
unit's `s1Calls`, because that is where the mask unit's body runs.  The block
unit's environment binds the same two arms, so a block run needs the same two
steps at `s1BlocksCalls`; the arms are `s1BlocksCalls_pshufb` and
`s1BlocksCalls_pclmulqdq` in `JsonS1BlocksReuse`. -/

/-- `pshuf.b` at the block unit's environment: the thirty-two-lane lookup at the
table the parsed emission spells.  The emission carries the table as the literal
lane list (`Const.vector`), not as the integer list the authored fixtures use, so
the step takes the vector's lanes and the fact that there are thirty-two of
them. -/
theorem step_pshufb_b (env : Env) (s : State) (r dst : String)
    (tab ctl : List (BitVec 8)) (htab : tab.length = 32)
    (h : evalOperand (stateAt env s) (.reg r) = some (.vec 32 8 ctl)) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.call dst v32i8 "llvm.x86.avx2.pshuf.b"
          [(v32i8, .imm (.vector 8 tab)), (v32i8, .reg r)]) =
      some (stateAt ((dst, .vec 32 8 (pshufbLanes tab ctl)) :: env) s) := by
  have hreg : lookupName env r = some (.vec 32 8 ctl) := by
    simp only [evalOperand, stateAt] at h
    split at h
    · cases h
    · exact h
  have ha : evalOperands (stateAt env s)
      [(v32i8, .imm (.vector 8 tab)), (v32i8, .reg r)]
      = some [.vec 32 8 tab, .vec 32 8 ctl] := by
    rw [evalOperands_cons (v := .vec 32 8 tab) (vs := [.vec 32 8 ctl])
      (by simp [evalOperand, stateAt, Const.toValue, htab])
      (evalOperands_cons (by simp only [evalOperand, stateAt, hreg]) rfl)]
  rw [evalInstr_call (s := stateAt env s) ha
    (s1BlocksCalls_pshufb tab ctl s.mem s.next)]
  rfl

/-- `pclmulqdq` at immediate zero, at the block unit's environment: lane zero is
the carry-less product, lane one zero.  The emission spells both the multiplier
and the selector as literals. -/
theorem step_pclmul_b (env : Env) (s : State) (r dst : String) {a0 a1 : BitVec 64}
    (h : evalOperand (stateAt env s) (.reg r) = some (.vec 2 64 [a0, a1])) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.call dst (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
          [(.vec 2 (.int 64), .reg r),
           (.vec 2 (.int 64), .imm (.vector 64 [BitVec.allOnes 64, 0])),
           (.int 8, .imm (.int 8 0))]) =
      some (stateAt ((dst, .vec 2 64 [Pclmul.clmul a0 (BitVec.allOnes 64), 0]) :: env) s) := by
  have hreg : lookupName env r = some (.vec 2 64 [a0, a1]) := by
    simp only [evalOperand, stateAt] at h
    split at h
    · cases h
    · exact h
  have ha : evalOperands (stateAt env s)
      [(.vec 2 (.int 64), .reg r),
       (.vec 2 (.int 64), .imm (.vector 64 [BitVec.allOnes 64, 0])),
       (.int 8, .imm (.int 8 0))] =
      some [.vec 2 64 [a0, a1], .vec 2 64 [BitVec.allOnes 64, 0], .int 8 0] := by
    rw [evalOperands_cons (v := .vec 2 64 [a0, a1])
      (vs := [.vec 2 64 [BitVec.allOnes 64, 0], .int 8 0])
      (by simp only [evalOperand, stateAt, hreg])
      (evalOperands_cons (v := .vec 2 64 [BitVec.allOnes 64, 0])
        (vs := [.int 8 0])
        (by simp [evalOperand, stateAt, Const.toValue]) rfl)]
  rw [evalInstr_call (s := stateAt env s) ha
    (s1BlocksCalls_pclmulqdq a0 a1 (BitVec.allOnes 64) 0 s.mem s.next)]
  rfl

/-- The table lookup, as a chain step at the block unit's environment. -/
theorem denoteCode_pshufb_b (env : Env) (s : State) (r dst : String)
    (tab ctl : List (BitVec 8)) (htab : tab.length = 32)
    (h : evalOperand (stateAt env s) (.reg r) = some (.vec 32 8 ctl))
    (is : List Instr) :
    denoteCode s1BlocksCalls
        (.call dst v32i8 "llvm.x86.avx2.pshuf.b"
          [(v32i8, .imm (.vector 8 tab)), (v32i8, .reg r)] :: is) (stateAt env s) =
      denoteCode s1BlocksCalls is
        (stateAt ((dst, .vec 32 8 (pshufbLanes tab ctl)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_pshufb_b env s r dst tab ctl htab h)]

/-- The carry-less product, as a chain step at the block unit's environment. -/
theorem denoteCode_pclmul_b (env : Env) (s : State) (r dst : String) {a0 a1 : BitVec 64}
    (h : evalOperand (stateAt env s) (.reg r) = some (.vec 2 64 [a0, a1]))
    (is : List Instr) :
    denoteCode s1BlocksCalls
        (.call dst (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
          [(.vec 2 (.int 64), .reg r),
           (.vec 2 (.int 64), .imm (.vector 64 [BitVec.allOnes 64, 0])),
           (.int 8, .imm (.int 8 0))] :: is) (stateAt env s) =
      denoteCode s1BlocksCalls is
        (stateAt ((dst, .vec 2 64 [Pclmul.clmul a0 (BitVec.allOnes 64), 0]) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_pclmul_b env s r dst h)]

/-! ### The remaining shapes the ASCII phase and the hand-off use

The prologue's arithmetic shift, a `<32 x i8>` load (the lane width the generic
vector load excludes), the saturating subtract, the `i64`-element register
`getelementptr` the entry store indexes through, and the three backward `i8`
offsets the hand-off's shifted windows read. -/

/-- An arithmetic shift by an immediate. -/
theorem denoteCode_ashr_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w} (ha : lookupName env a = some (.int w x))
    (is : List Instr) :
    denoteCode calls (.binop d .ashr w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (BitVec.sshiftRight x c.toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (show evalInstr calls (stateAt env s) (.binop d .ashr w (.reg a) (.imm (.int w c))) =
        some (stateAt ((d, .int w (BitVec.sshiftRight x c.toNat)) :: env) s) from by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
        using evalInstr_binop (op := .ashr) (r := (BitVec.sshiftRight x c.toNat).toNat)
          (ha := BlockEval.evalOperand_reg_of env s a (.int w x) ha)
          (hb := BlockEval.evalOperand_lit_of _ w c)
          (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat]))]

/-- `%d = load <32 x i8>, ptr %p`: `loadValue`'s byte-lane arm maps the thirty-two
bytes one for one. -/
theorem step_load32_8 (calls : Calls) (env : Env) (s : State) (d p : String) (a : Nat)
    (bs : List UInt8) (hp : lookupName env p = some (.ptr a))
    (hr : readBytes s.mem a 32 = some bs) :
    evalInstr calls (stateAt env s) (.load d v32i8 (.reg p)) =
      some (stateAt ((d, .vec 32 8 (bs.map fun b => BitVec.ofNat 8 b.toNat)) :: env) s) := by
  have hv : loadValue (stateAt env s).mem v32i8 a =
      some (.vec 32 8 (bs.map fun b => BitVec.ofNat 8 b.toNat)) := by
    simp only [stateAt, loadValue]
    rw [hr]
  rw [evalInstr_load (v := .vec 32 8 (bs.map fun b => BitVec.ofNat 8 b.toNat))
    (hp := BlockEval.evalOperand_reg_of env s p (.ptr a) hp) hv]
  rfl

/-- The byte-lane load, as a chain step. -/
theorem denoteCode_load32_8 (calls : Calls) (env : Env) (s : State) (d p : String) (a : Nat)
    (bs : List UInt8) (hp : lookupName env p = some (.ptr a))
    (hr : readBytes s.mem a 32 = some bs) (is : List Instr) :
    denoteCode calls (.load d v32i8 (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .vec 32 8 (bs.map fun b => BitVec.ofNat 8 b.toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_load32_8 calls env s d p a bs hp hr)]

/-- The saturating subtract, as a chain step at the unit's environment. -/
theorem denoteCode_usubSat_b (env : Env) (s : State) (dst : String)
    (o1 o2 : Operand) {a b : List (BitVec 8)}
    (h1 : evalOperand (stateAt env s) o1 = some (.vec 32 8 a))
    (h2 : evalOperand (stateAt env s) o2 = some (.vec 32 8 b)) (is : List Instr) :
    denoteCode s1BlocksCalls
        (.call dst v32i8 "llvm.usub.sat.v32i8"
          [(v32i8, o1), (v32i8, o2)] :: is) (stateAt env s) =
      denoteCode s1BlocksCalls is
        (stateAt ((dst, .vec 32 8 (List.zipWith BitLanes.subsSat a b)) :: env) s) := by
  have hstep : evalInstr s1BlocksCalls (stateAt env s)
      (.call dst v32i8 "llvm.usub.sat.v32i8" [(v32i8, o1), (v32i8, o2)]) =
      some (stateAt ((dst, .vec 32 8 (List.zipWith BitLanes.subsSat a b)) :: env) s) := by
    have ha : evalOperands (stateAt env s) [(v32i8, o1), (v32i8, o2)] =
        some [.vec 32 8 a, .vec 32 8 b] := by
      simp [evalOperands, h1, h2]
    rw [evalInstr_call (s := stateAt env s) ha
      (s1BlocksCalls_usubSat a b s.mem s.next)]
    simp only [stateAt]
  rw [denoteCode_cons_of _ _ _ _ _ hstep]

/-- `%d = getelementptr <elem>, ptr %base, i64 %off`, at an index below `2 ^ 63`. -/
theorem step_gep_reg_elem (calls : Calls) (env : Env) (s : State) (d base off : String)
    (elem : Ty) {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d elem (.reg base) (.reg off)) =
      some (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat * elem.sizeBytes)) :: env) s) := by
  rw [evalInstr_gep (hb := BlockEval.evalOperand_reg_of env s base (.ptr a) hb)
    (ho := BlockEval.evalOperand_reg_of env s off (.int 64 idx) ho) (hpos := hpos)]
  simp only [stateAt, State.bind]

/-- The `i64`-element register `getelementptr`, as a chain step. -/
theorem denoteCode_gep_reg_elem (calls : Calls) (env : Env) (s : State) (d base off : String)
    (elem : Ty) {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d elem (.reg base) (.reg off) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat * elem.sizeBytes)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_gep_reg_elem calls env s d base off elem hb ho hpos)]

/-- A backward `i8` offset: the sign-extended index is at or above `2 ^ 63` and
its magnitude does not exceed the base. -/
theorem step_gep8_imm_back (calls : Calls) (env : Env) (s : State) (d base : String)
    (c : BitVec 64) {a : Nat}
    (hb : lookupName env base = some (.ptr a))
    (hneg : ¬ (c.signExtend 64).toNat < 2 ^ 63)
    (hk : (2 ^ 64 - (c.signExtend 64).toNat) ≤ a) :
    evalInstr calls (stateAt env s) (.gep d (.int 8) (.reg base) (.imm (.int 64 c))) =
      some (stateAt ((d, .ptr (a - (2 ^ 64 - (c.signExtend 64).toNat))) :: env) s) := by
  have h1 : (8 + 7) / 8 = 1 := by decide
  rw [evalInstr_gep_back (elemTy := .int 8)
    (hb := BlockEval.evalOperand_reg_of env s base (.ptr a) hb)
    (ho := BlockEval.evalOperand_lit_of _ 64 c) hneg (by simpa [Ty.sizeBytes] using hk)]
  simp only [stateAt, State.bind, Ty.sizeBytes, h1, Nat.mul_one]

/-- The backward `getelementptr i8` chain step, at the `-1` the hand-off reads. -/
theorem denoteCode_gep8_imm_m1 (calls : Calls) (env : Env) (s : State) (d base : String)
    {a : Nat} (hb : lookupName env base = some (.ptr a)) (hk : 1 ≤ a) (is : List Instr) :
    denoteCode calls
        (.gep d (.int 8) (.reg base) (.imm (.int 64 0xffffffffffffffff#64)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a - 1)) :: env) s) := by
  have hneg : ¬ ((0xffffffffffffffff#64).signExtend 64).toNat < 2 ^ 63 := by decide
  have hk' : (2 ^ 64 - ((0xffffffffffffffff#64).signExtend 64).toNat) ≤ a := by simpa using hk
  rw [denoteCode_cons_of _ _ _ _ _
    (by simpa using step_gep8_imm_back calls env s d base 0xffffffffffffffff#64 hb hneg hk')]

/-- The backward `getelementptr i8` chain step, at the `-2` the hand-off reads. -/
theorem denoteCode_gep8_imm_m2 (calls : Calls) (env : Env) (s : State) (d base : String)
    {a : Nat} (hb : lookupName env base = some (.ptr a)) (hk : 2 ≤ a) (is : List Instr) :
    denoteCode calls
        (.gep d (.int 8) (.reg base) (.imm (.int 64 0xfffffffffffffffe#64)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a - 2)) :: env) s) := by
  have hneg : ¬ ((0xfffffffffffffffe#64).signExtend 64).toNat < 2 ^ 63 := by decide
  have hk' : (2 ^ 64 - ((0xfffffffffffffffe#64).signExtend 64).toNat) ≤ a := by simpa using hk
  rw [denoteCode_cons_of _ _ _ _ _
    (by simpa using step_gep8_imm_back calls env s d base 0xfffffffffffffffe#64 hb hneg hk')]

/-- The backward `getelementptr i8` chain step, at the `-3` the hand-off reads. -/
theorem denoteCode_gep8_imm_m3 (calls : Calls) (env : Env) (s : State) (d base : String)
    {a : Nat} (hb : lookupName env base = some (.ptr a)) (hk : 3 ≤ a) (is : List Instr) :
    denoteCode calls
        (.gep d (.int 8) (.reg base) (.imm (.int 64 0xfffffffffffffffd#64)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a - 3)) :: env) s) := by
  have hneg : ¬ ((0xfffffffffffffffd#64).signExtend 64).toNat < 2 ^ 63 := by decide
  have hk' : (2 ^ 64 - ((0xfffffffffffffffd#64).signExtend 64).toNat) ≤ a := by simpa using hk
  rw [denoteCode_cons_of _ _ _ _ _
    (by simpa using step_gep8_imm_back calls env s d base 0xfffffffffffffffd#64 hb hneg hk')]

/-! ### The lane-wise sum, in the two shapes a splat operand produces

`binopLanes` is a `mapM` over a `zip`, so a splat operand's value is stuck on a
symbolic lane list.  These two lemmas are the lane-wise operations' values: the
`zipWith` of two lists, or the map of the first against a constant. -/

/-- Two lists' lane-wise operation, when the operation always answers. -/
theorem binopLanes_zipWith {w : Nat} (op : BinOp) (f : BitVec w → BitVec w → BitVec w)
    (hg : ∀ x y, evalBinop op x y = some (f x y)) (l1 l2 : List (BitVec w))
    (h : l1.length = l2.length) :
    binopLanes op l1 l2 = some (List.zipWith f l1 l2) :=
  JsonUtf8Steps.zip_mapM_binop op f hg l1 l2 h

/-- A lane-wise operation against a splatted constant. -/
theorem binopLanes_replicate {w : Nat} (op : BinOp) (f : BitVec w → BitVec w → BitVec w)
    (hg : ∀ x y, evalBinop op x y = some (f x y)) (l : List (BitVec w)) (n : Nat)
    (hn : l.length = n) (c : BitVec w) :
    binopLanes op l (List.replicate n c) = some (l.map fun x => f x c) := by
  subst hn
  exact zipReplicate_mapM l c (fun x y => evalBinop op x y) (fun x => f x c)
    (fun x => hg x c)


/-- `mapM` depends only on the values its function takes on the list. -/
theorem mapM_congr_mem {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} {l : List α}
    {f g : α → m β} (h : ∀ a ∈ l, f a = g a) : l.mapM f = l.mapM g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.mapM_cons, List.mapM_cons, h a (by simp),
        ih (fun b hb => h b (by simp [hb]))]

/-- A mask that copies `n` lanes from each of two `n`-lane operands: the join is
the concatenation.  The index arithmetic of the copy is what the `0 … 2n - 1`
masks state, and the range is the emission's spelling of that list. -/
theorem mapM_range_split {w : Nat} {l1 l2 : List (BitVec w)} (n : Nat)
    (h1 : l1.length = n) (h2 : l2.length = n) :
    (List.range (2 * n)).mapM (fun k => if k < n then l1[k]? else l2[k - n]?) =
      some (l1 ++ l2) := by
  classical
  let f : Nat → BitVec w := fun k => if k < n then l1.getD k 0 else l2.getD (k - n) 0
  have hf : ∀ k ∈ List.range (2 * n), (if k < n then l1[k]? else l2[k - n]?) = some (f k) := by
    intro k hk
    have hk2 : k < 2 * n := List.mem_range.mp hk
    by_cases h : k < n
    · rw [ite_eq_left h]
      rw [show f k = l1.getD k 0 from by simp only [f, ite_eq_left h]]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    · rw [ite_eq_right h]
      rw [show f k = l2.getD (k - n) 0 from by simp only [f, ite_eq_right h]]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [mapM_congr_mem hf,
    show (fun a => some (f a)) = (fun a => pure (f a)) from rfl, List.mapM_pure]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_append, h1, h2]
    omega
  · intro k hk1 hk2
    have hk2' : k < 2 * n := by simpa using hk1
    simp only [List.getElem_map, List.getElem_range]
    by_cases h : k < n
    · rw [show f k = l1.getD k 0 from by simp only [f, ite_eq_left h]]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact (List.getElem_append_left (by omega)).symm
    · rw [show f k = l2.getD (k - n) 0 from by simp only [f, ite_eq_right h]]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [List.getElem_append_right (as := l1) (bs := l2) (i := k) (by omega)]
      congr 1
      omega

/-- The mask `[0 … 63]` at two thirty-two-lane operands: the byte join of the two
vectors, which is what the fused loop's `u8k` word is read off. -/
theorem mapM_pick32 {w : Nat} {l1 l2 : List (BitVec w)} (h1 : l1.length = 32)
    (h2 : l2.length = 32) :
    ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
      24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
      46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63] : List Nat).mapM
      (fun k => if k < 32 then l1[k]? else l2[k - 32]?) = some (l1 ++ l2) := by
  have hmask : ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
      22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43,
      44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63] : List Nat)
      = List.range (2 * 32) := by decide
  rw [hmask]
  exact mapM_range_split 32 h1 h2


/-! ### The block tactic

`block_step_v` covers the vector and `i64` shapes; the width-generic steps are
appended for the prologue's `i32` arithmetic. -/

/-- The lane-list length goals the shuffle and lane-wise steps leave.  The
model's lane constructors have structural lengths (`unpackLanes` has `n` lanes,
a table lookup has its control's, a `zipWith` has the shorter of the two), so a
`simp` battery plus `omega` decides them without the statement restating each. -/
macro "block_len" : tactic => `(tactic|
  (first
   | assumption
   | (simp only [unpackLanes_length, pshufbLanes_length, List.length_zipWith,
        List.length_map, List.length_append, List.length_replicate, List.length_cons,
        List.length_nil, Nat.min_def, if_pos, if_neg] <;> omega)))

macro "block_step_b" : tactic => `(tactic|
  (first
   | rw [denoteCode_callVoid7 _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _]
   | rw [denoteCode_load32_8 _ _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_gep8_imm_m1 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_gep8_imm_m2 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_gep8_imm_m3 _ _ _ _ _ ?_ ?_ _]
   | block_step_v
   | rw [denoteCode_pshufb_b _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_pclmul_b _ _ _ _ ?_ _]
   | rw [denoteCode_usubSat_b _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_ashr_imm _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_gep_reg_elem _ _ _ _ _ _ _ ?_ ?_ ?_ _]
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

/-- Resolve a register read against an environment the chain built one cell at a
time.  The cells are a cons chain, not the `cells` builder, so peeling is
`lookupName_cons_ne` per cell and nothing else: no `simp` walks the whole
environment, which is what a ninety-cell block makes expensive. -/
macro "block_lk_cons" : tactic => `(tactic|
  (first
   | assumption
   | (repeat rw [lookupName_cons_ne _ _ (by decide)]
      first
       | exact lookupName_cons_self _ _ _
       | assumption
       | rfl)))

/-- One close step for a semantic side goal.  Every alternative either closes
its goal or fails, so `repeat` over it terminates. -/
macro "block_close_step" : tactic => `(tactic|
  (first
   | assumption
   | (simp only [evalOperand, stateAt]; block_lk_cons)
   | exact BlockEval.evalOperand_reg_of _ _ _ _ (by block_lk_cons)
   | (simp only [evalOperand, stateAt]; block_lk)
   | exact BlockEval.evalOperand_reg_of _ _ _ _ (by assumption)
   | (simp only [evalOperand, Const.toValue, lanesOf, splatOf]; rfl)
   | exact BlockEval.evalOperand_lit_of _ _ _
   | (refine vecLanes_self ?_; block_len)
   | (simp only [Value.vecLanes]; repeat split; all_goals (first | rfl | contradiction))
   | (simp only [phiIncoming]; rfl)
   | (rw [binopLanes_replicate]; all_goals (first | assumption | (intro x; rfl) | (simp; omega) | rfl))
   | (rw [binopLanes_zipWith]; all_goals (first | assumption | (intro x y; rfl) | (simp; omega) | rfl))
   | (rw [mapM_pick8 (by block_len) (by block_len)]; rfl)
   | (rw [mapM_pick32 (by block_len) (by block_len)]; rfl)
   | assumption
   | rfl
   | decide
   | omega))

open Lean Meta Elab Tactic in
/-- The close that leaves the block's own equation for last: the semantic side
goals fix the lane lists and lane-wise values from the operands, and only then is
the statement's environment read.  A main equation closed first would assign a
lane list from the statement instead of from the operand. -/
elab "block_finish_b" : tactic => do
  let gs ← getGoals
  let mut main : Option MVarId := none
  let mut sides : List MVarId := []
  for g in gs do
    let t ← instantiateMVars (← g.getType)
    let isMain := match t.eq? with
      | some (_, lhs, _) =>
          lhs.getAppFn.isConstOf ``denoteCode || lhs.getAppFn.isConstOf ``denoteRun
      | none => false
    if isMain then main := some g else sides := sides ++ [g]
  replaceMainGoal sides
  evalTactic (← `(tactic| (all_goals (repeat block_close_step))))
  match main with
  | some m =>
      replaceMainGoal [m]
      evalTactic (← `(tactic| (first | rfl | (simp only [cells, denoteCode, State.bindAll]; rfl))))
  | none => pure ()

macro "block_eval_b" : tactic => `(tactic|
  (repeat block_step_b
   block_close_v))

/-- The block run whose statement environment is inferred: the same steps, with
the side-goal-first close. -/
macro "block_eval_infer" : tactic => `(tactic|
  (repeat block_step_b
   block_finish_b))

/-- The close for a statement whose environment is concrete: the phrase adds the
shuffle mask `[0 … 7]`'s value, which the generic close leaves as the `mapM` it
is. -/
macro "block_close_c" : tactic => `(tactic|
  (block_close_v
   all_goals (try (rw [mapM_pick8 (by assumption) (by assumption)]; rfl))
   all_goals (try (rw [mapM_pick32 (by assumption) (by assumption)]; rfl))
   all_goals (try rfl)
   all_goals (try decide)
   all_goals (try omega)))

macro "block_eval_c" : tactic => `(tactic|
  (repeat block_step_b
   block_close_c))

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


/-! ### `if.then` — the escape arm

The arm reads the block's two `<4 x i64>` words, joins them, packs the 64 lanes,
and calls the escape list.  The block's run is stated at an arbitrary call
selection: the escape call's outcome is the caller's, so the run is the block's
own computation plus one `hc`. -/

/-- The shuffle mask `[0 … 7]` at two four-lane operands: the bytes are the
join of the two words, which is what `mapM_pick8` states. -/
def ifThenJoin (a2 a3 : List (BitVec 64)) : List (BitVec 64) := a2 ++ a3

/-- The escape call's four 64-bit mask arguments, as the block passes them. -/
def ifThenQuoteWord (a2 a3 : List (BitVec 64)) : BitVec 64 :=
  BitVec.ofNat 64 (lanesToNat
    (icmpLanes .ult (bitcastVecLanes 8 64 (ifThenJoin a2 a3))
      (List.replicate 64 (BitVec.ofInt 8 32))))

/-- The four cells `if.then` binds before the call. -/
def ifThenOut (env : Env) (a2 a3 : List (BitVec 64)) : Env :=
  cells [("%or.i290", .int 64 (ifThenQuoteWord a2 a3)),
         ("%37", .vec 64 1
           (icmpLanes .ult (bitcastVecLanes 8 64 (ifThenJoin a2 a3))
             (List.replicate 64 (BitVec.ofInt 8 32)))),
         ("%36", .vec 64 8 (bitcastVecLanes 8 64 (ifThenJoin a2 a3))),
         ("%35", .vec 8 64 (ifThenJoin a2 a3))] env

/-- **`if.then`'s run.**  The join, the packed lanes, the zero-test lane mask and
the escape call, which leaves the caller's memory and cursor at `r`. -/
theorem if_then_denote (calls : Calls) (env : Env) (s : State)
    (a2 a3 : List (BitVec 64)) (h2len : a2.length = 4) (h3len : a3.length = 4)
    (or14 xs i : BitVec 64) (xp nxp xcarry : Nat) (r : CallOutcome)
    (h2 : lookupName env "%2" = some (.vec 4 64 a2))
    (h3 : lookupName env "%3" = some (.vec 4 64 a3))
    (hor : lookupName env "%or14.i" = some (.int 64 or14))
    (hxs : lookupName env "%xor.i" = some (.int 64 xs))
    (hi : lookupName env "%i.0510" = some (.int 64 i))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hc : calls "leanllvm_json_escape_list"
      [.int 64 or14, .int 64 (ifThenQuoteWord a2 a3), .int 64 xs, .int 64 i,
       .ptr xp, .ptr nxp, .ptr xcarry] s.mem s.next = some r) :
    denoteCode calls if_thenInstrs (stateAt env s) =
      some (stateAt (ifThenOut env a2 a3) { s with mem := r.mem, next := r.next }) := by
  simp only [if_thenInstrs]
  -- the join: the shuffle's eight lanes are the two words
  rw [denoteCode_shuffleVec (calls := calls) (env := env) (s := s) (d := "%35")
      (n := 4) (w := 64) (a := .reg "%2") (b := .reg "%3")
      (mask := [0, 1, 2, 3, 4, 5, 6, 7]) (l1 := a2) (l2 := a3) (ls := a2 ++ a3)
      (ha := evalOperand_reg_of env s "%2" (.vec 4 64 a2) h2)
      (hb := evalOperand_reg_of env s "%3" (.vec 4 64 a3) h3)
      (h1 := vecLanes_self h2len) (h2 := vecLanes_self h3len)
      (hm := mapM_pick8 h2len h3len)]
  try simp only [List.length_cons, List.length_nil]
  -- bitcast <8 x i64> to <64 x i8>
  rw [denoteCode_vecBitcast (calls := calls)
      (env := ("%35", .vec 8 64 (a2 ++ a3)) :: env) (s := s) (d := "%36")
      (n := 8) (w := 64) (m := 64) (jw := 8) (v := .reg "%35")
      (vv := .vec 8 64 (a2 ++ a3)) (lanes := a2 ++ a3)
      (hv := evalOperand_reg_of _ _ _ _ (by block_lk))
      (hl := vecLanes_self (by simp [List.length_append, h2len, h3len]))
      (hwidth := by decide)]
  try simp only [List.length_cons, List.length_nil]
  -- the byte comparison against 0x20
  rw [denoteCode_icmpVec (calls := calls)
      (env := ("%36", .vec 64 8 (bitcastVecLanes 8 64 (a2 ++ a3)))
        :: ("%35", .vec 8 64 (a2 ++ a3)) :: env) (s := s) (d := "%37")
      (pred := .ult) (n := 64) (w := 8) (a := .reg "%36")
      (b := .imm (.splat 64 8 0x20#8))
      (va := .vec 64 8 (bitcastVecLanes 8 64 (a2 ++ a3)))
      (vb := .vec 64 8 (List.replicate 64 0x20#8))
      (l1 := bitcastVecLanes 8 64 (a2 ++ a3))
      (l2 := List.replicate 64 0x20#8)
      (ha := evalOperand_reg_of _ _ _ _ (by block_lk))
      (hb := by simp [evalOperand, Const.toValue])
      (h1 := vecLanes_self (by simp [bitcastVecLanes, unpackLanes_length]))
      (h2 := vecLanes_self (by simp))]
  try simp only [List.length_cons, List.length_nil]
  -- pack the lane mask
  rw [denoteCode_bitcastMask (calls := calls)
      (env := ("%37", .vec 64 1 (icmpLanes .ult (bitcastVecLanes 8 64 (a2 ++ a3))
          (List.replicate 64 0x20#8)))
        :: ("%36", .vec 64 8 (bitcastVecLanes 8 64 (a2 ++ a3)))
        :: ("%35", .vec 8 64 (a2 ++ a3)) :: env) (s := s) (d := "%or.i290")
      (n := 64) (v := .reg "%37")
      (l := icmpLanes .ult (bitcastVecLanes 8 64 (a2 ++ a3)) (List.replicate 64 0x20#8))
      (hv := evalOperand_reg_of _ _ _ _ (by block_lk))
      (hlen := by simp [icmpLanes, bitcastVecLanes, List.length_zip, List.length_map,
        unpackLanes_length])]
  try simp only [List.length_cons, List.length_nil]
  -- the escape call
  rw [denoteCode_callVoid7 (calls := calls)
      (env := ("%or.i290", .int 64 (BitVec.ofNat 64
          (lanesToNat (icmpLanes .ult (bitcastVecLanes 8 64 (a2 ++ a3))
            (List.replicate 64 0x20#8)))))
        :: ("%37", .vec 64 1 (icmpLanes .ult (bitcastVecLanes 8 64 (a2 ++ a3))
          (List.replicate 64 0x20#8)))
        :: ("%36", .vec 64 8 (bitcastVecLanes 8 64 (a2 ++ a3)))
        :: ("%35", .vec 8 64 (a2 ++ a3)) :: env)
      (s := s) (callee := "leanllvm_json_escape_list")
      (o1 := .reg "%or14.i") (o2 := .reg "%or.i290") (o3 := .reg "%xor.i")
      (o4 := .reg "%i.0510") (o5 := .reg "%xp") (o6 := .reg "%nxp") (o7 := .reg "%xcarry")
      (v1 := .int 64 or14) (v2 := .int 64 (BitVec.ofNat 64
          (lanesToNat (icmpLanes .ult (bitcastVecLanes 8 64 (a2 ++ a3))
            (List.replicate 64 0x20#8)))))
      (v3 := .int 64 xs) (v4 := .int 64 i)
      (v5 := .ptr xp) (v6 := .ptr nxp) (v7 := .ptr xcarry) (r := r)
      (h1 := evalOperand_reg_of _ _ _ _ (by block_lk))
      (h2 := evalOperand_reg_of _ _ _ _ (by block_lk))
      (h3 := evalOperand_reg_of _ _ _ _ (by block_lk))
      (h4 := evalOperand_reg_of _ _ _ _ (by block_lk))
      (h5 := evalOperand_reg_of _ _ _ _ (by block_lk))
      (h6 := evalOperand_reg_of _ _ _ _ (by block_lk))
      (h7 := evalOperand_reg_of _ _ _ _ (by block_lk))
      (hc := hc)]
  try simp only [List.length_cons, List.length_nil]
  simp only [ifThenOut, ifThenQuoteWord, ifThenJoin, cells]
  rfl

/-! ### The caller's escape entry, and the arm's one step

The arm's call is not the block's to decide.  The unit's environment leaves
`leanllvm_json_escape_list` unresolved, so the trace runs it at the caller's own
selection, and what that selection returns is the caller's: the escape unit's own
record is what says the call is defined and what it leaves behind.

The hypothesis below is that record read as a per-call fact.  `CallSatisfies`
quantifies over the argument vectors the record's `pre` admits, so the record's
pre is the hypothesis's *premise* rather than a clause of `s1BlocksPre`: the
block's staging is unchanged, and the refinement statement carries the pre at the
call's argument vector as its own premise.  The record's post is
`escapePositionsPost`, whose `EscapeReach` conjunct is the frame —
`escapeReach_frame` reads it out — so a refinement's memory clause about the
bytes outside the escape regions is a consequence of the hypothesis, not a
promise the block makes. -/

/-- The escape-list selection the block's trace runs with, at the document base
`base`: the caller's entry for `leanllvm_json_escape_list`, required to satisfy
the escape unit's own record at the call site. -/
def escapeEntryAt (esc : Calls) (base : Nat) : Prop :=
  CallSatisfies esc (Γ_escape_positions base escapePositionsBudget) escapeListCallee

/-- **The hypothesis at one call site.**  The premise is the record's own `pre`,
stated at the block's argument vector; the conclusion is the selection's outcome,
the post it satisfies and the cursor's monotonicity. -/
theorem escapeEntry_call {esc : Calls} {base : Nat} (h : escapeEntryAt esc base)
    {args : List Value} {mem : Mem} {next : Nat}
    (hpre : (Γ_escape_positions base escapePositionsBudget).pre args mem next) :
    ∃ r, esc escapeListCallee args mem next = some r ∧
      (Γ_escape_positions base escapePositionsBudget).post args mem next
        (.ret (some r.ret) r.mem) ∧ next ≤ r.next :=
  h args mem next hpre

/-- **The escape unit's frame**, read out of `EscapeReach`: the returned memory
differs from the caller's only inside the three regions the run touched. -/
theorem escapeReach_frame {blk0 : BitVec 64} {xp xn carry xn0 : Nat}
    {position : List Nat} {carryBytes : List UInt8} {mem0 M : Mem}
    (h : EscapeReach blk0 xp xn carry xn0 position carryBytes mem0 M) :
    UnchangedOutside mem0 M
      [(xp, 4 * touchedPositions xn0 position.length), (xn, 8), (carry, 16)] :=
  h.2.2.2.2

/-- **`if.then`'s step, at the caller's escape entry.**  The arm's own computation
(the join, the packed zero-test mask and the four arguments) and the one call; the
block hands `if.end` the escape unit's memory and cursor.  The call's outcome is
the hypothesis's, which is why it is a parameter here. -/
theorem if_then_step_at (esc : Calls) (env : Env) (s : State)
    (a2 a3 : List (BitVec 64)) (h2len : a2.length = 4) (h3len : a3.length = 4)
    (or14 xs i : BitVec 64) (xp nxp xcarry : Nat) (r : CallOutcome)
    (hpc : s.pc = "if.then")
    (h2 : lookupName env "%2" = some (.vec 4 64 a2))
    (h3 : lookupName env "%3" = some (.vec 4 64 a3))
    (hor : lookupName env "%or14.i" = some (.int 64 or14))
    (hxs : lookupName env "%xor.i" = some (.int 64 xs))
    (hi : lookupName env "%i.0510" = some (.int 64 i))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hc : esc escapeListCallee
      [.int 64 or14, .int 64 (ifThenQuoteWord a2 a3), .int 64 xs, .int 64 i,
       .ptr xp, .ptr nxp, .ptr xcarry] s.mem s.next = some r) :
    step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifThenOut env a2 a3)
        { s with pc := "if.end", pre := some "if.then", mem := r.mem, next := r.next }) := by
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some if_thenBlock := by
    rw [show (stateAt env s).pc = s.pc from rfl, hpc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_then
  have hc' : s1BlocksCallsEsc esc "leanllvm_json_escape_list"
      [.int 64 or14, .int 64 (ifThenQuoteWord a2 a3), .int 64 xs, .int 64 i,
       .ptr xp, .ptr nxp, .ptr xcarry] s.mem s.next = some r := by
    rw [show "leanllvm_json_escape_list" = escapeListCallee from rfl,
      s1BlocksCallsEsc_escape]
    exact hc
  rw [step_at hfind (if_then_denote (s1BlocksCallsEsc esc) env s a2 a3 h2len h3len
    or14 xs i xp nxp xcarry r h2 h3 hor hxs hi hxp hnxp hxcarry hc')]
  rw [show if_thenBlock.term = if_thenTerm from rfl]
  simp only [if_thenTerm, execTerm]
  simp only [stateAt, hpc]

/-- **`if.then`'s step under the hypothesis's premise.**  The escape record's
`pre` at the block's argument vector resolves the call through
`escapeEntry_call`; the step is then the one above at the outcome the selection
returned.  This is the form a refinement statement consumes: it carries the
escape pre as a premise and gets the arm's step, the unit's post and the cursor's
monotonicity out of the one hypothesis. -/
theorem if_then_step_of_pre (esc : Calls) (base : Nat) (hEsc : escapeEntryAt esc base)
    (env : Env) (s : State)
    (a2 a3 : List (BitVec 64)) (h2len : a2.length = 4) (h3len : a3.length = 4)
    (or14 xs i : BitVec 64) (xp nxp xcarry : Nat)
    (hpc : s.pc = "if.then")
    (h2 : lookupName env "%2" = some (.vec 4 64 a2))
    (h3 : lookupName env "%3" = some (.vec 4 64 a3))
    (hor : lookupName env "%or14.i" = some (.int 64 or14))
    (hxs : lookupName env "%xor.i" = some (.int 64 xs))
    (hi : lookupName env "%i.0510" = some (.int 64 i))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hescPre : (Γ_escape_positions base escapePositionsBudget).pre
      [.int 64 or14, .int 64 (ifThenQuoteWord a2 a3), .int 64 xs, .int 64 i,
       .ptr xp, .ptr nxp, .ptr xcarry] s.mem s.next) :
    ∃ r, esc escapeListCallee
        [.int 64 or14, .int 64 (ifThenQuoteWord a2 a3), .int 64 xs, .int 64 i,
         .ptr xp, .ptr nxp, .ptr xcarry] s.mem s.next = some r ∧
      (Γ_escape_positions base escapePositionsBudget).post
        [.int 64 or14, .int 64 (ifThenQuoteWord a2 a3), .int 64 xs, .int 64 i,
         .ptr xp, .ptr nxp, .ptr xcarry] s.mem s.next (.ret (some r.ret) r.mem) ∧
      s.next ≤ r.next ∧
      step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
        .jump (stateAt (ifThenOut env a2 a3)
          { s with pc := "if.end", pre := some "if.then", mem := r.mem, next := r.next }) := by
  obtain ⟨r, hcall, hpost, hnext⟩ := escapeEntry_call hEsc hescPre
  exact ⟨r, hcall, hpost, hnext,
    if_then_step_at esc env s a2 a3 h2len h3len or14 xs i xp nxp xcarry r hpc
      h2 h3 hor hxs hi hxp hnxp hxcarry hcall⟩

/-! ### `if.end50` — the hand-off's join

Eight phis select the carried DFA state and the two words, and the terminator's
test is the next block's index bound. -/

def ifEnd50Out (env : Env) (shr17 st0 st9 st15 : BitVec 64)
    (oii or284 : List (BitVec 64)) (inc49 shr : BitVec 64) : Env :=
  cells [("%cmp52516", .int 1 (evalICmp .ult inc49 shr)),
         ("%i.1", .int 64 inc49),
         ("%ascii.0", .vec 4 64 or284),
         ("%u8k.0", .vec 4 64 oii),
         ("%prev_ascii.0", .int 32 0),
         ("%st.sroa.15.1485", .int 64 st15),
         ("%st.sroa.9.1487", .int 64 st9),
         ("%st.sroa.0.1489", .int 64 st0),
         ("%prevS.1491", .int 64 shr17)] env

theorem if_end50_denote (env : Env) (s : State)
    (shr17 st0 st9 st15 : BitVec 64) (oii or284 : List (BitVec 64))
    (inc49 shr : BitVec 64)
    (hpre : s.pre = some "if.then38")
    (hshr17 : lookupName env "%shr17" = some (.int 64 shr17))
    (hst0 : lookupName env "%shr.i.i" = some (.int 64 st0))
    (hst9 : lookupName env "%conv13.i.i" = some (.int 64 st9))
    (hst15 : lookupName env "%shr.i" = some (.int 64 st15))
    (hoii : lookupName env "%or.i.i291" = some (.vec 4 64 oii))
    (hor284 : lookupName env "%or.i284" = some (.vec 4 64 or284))
    (hinc : lookupName env "%inc49" = some (.int 64 inc49))
    (hshr : lookupName env "%shr" = some (.int 64 shr)) :
    denoteCode s1BlocksCalls if_end50Instrs (stateAt env s) =
      some (stateAt (ifEnd50Out env shr17 st0 st9 st15 oii or284 inc49 shr) s) := by
  simp only [if_end50Instrs, ifEnd50Out]
  block_eval_c

/-! ### `for.body` — the ASCII phase's per-block run

The block is ninety-six instructions: five leading phis, the two word loads, the
classifier's entry composition on the loaded words, the two byte-class table
lookups, the DFA's state update and the store of the emitted word.  One close
over the whole list leaves more side goals than a single invocation closes, so
the run is split at seven points into one `denoteCode` equation each, at
explicit intermediate environments; the segments compose by
`denoteCode_append_apply`.

Every value the block binds is a field of `ForBodyValues`, computed once by
`forBodyValues` from the phis the edge selects, the two loaded words and the two
pointers the block addresses.  A cell is stated as its own instruction's
meaning applied to the cells it reads, so a segment's equation is the block's
run and nothing re-derived. -/

/-- The values `for.body` binds, one field per destination, in binding order.
The first nine are the inputs: the five phis, the two loaded words' bytes, and
the two pointers. -/
structure ForBodyValues where
  prevS : BitVec 64
  i : BitVec 64
  st0 : BitVec 64
  st9 : BitVec 64
  st15 : BitVec 64
  bs2 : List UInt8
  bs3 : List UInt8
  b : Nat
  ent : Nat
  shl : BitVec 64
  addPtr : Nat
  addPtr5 : Nat
  w2 : List (BitVec 64)
  w3 : List (BitVec 64)
  byte2 : List (BitVec 8)
  byte3 : List (BitVec 8)
  join : List (BitVec 64)
  joinBytes : List (BitVec 8)
  cmp8 : List (BitVec 1)
  or286 : BitVec 64
  cmp39 : List (BitVec 1)
  mask9 : BitVec 32
  conv9 : BitVec 64
  cmpii : List (BitVec 1)
  mask10 : BitVec 32
  conv12 : BitVec 64
  shl13 : BitVec 64
  or14 : BitVec 64
  andII : BitVec 64
  shlII : BitVec 64
  notII : BitVec 64
  and1II : BitVec 64
  xorII : BitVec 64
  and2II : BitVec 64
  xor3II : BitVec 64
  not4II : BitVec 64
  addII : BitVec 64
  add5II : BitVec 64
  and6II : BitVec 64
  and7II : BitVec 64
  and8II : BitVec 64
  and9II : BitVec 64
  and11II : BitVec 64
  orII : BitVec 64
  or12II : BitVec 64
  cmp45 : BitVec 1
  conv13II : BitVec 64
  shrII : BitVec 64
  notI : BitVec 64
  andI : BitVec 64
  half11 : List (BitVec 16)
  shr12 : List (BitVec 16)
  low13 : List (BitVec 8)
  shuf14 : List (BitVec 8)
  shuf15 : List (BitVec 8)
  low16 : List (BitVec 8)
  shuf17 : List (BitVec 8)
  andClass1 : List (BitVec 8)
  and18 : List (BitVec 8)
  cmp21 : List (BitVec 1)
  mask19 : BitVec 32
  not46 : BitVec 32
  half20 : List (BitVec 16)
  shr21 : List (BitVec 16)
  low22 : List (BitVec 8)
  shuf23 : List (BitVec 8)
  shuf24 : List (BitVec 8)
  low25 : List (BitVec 8)
  shuf26 : List (BitVec 8)
  andClass2 : List (BitVec 8)
  and27 : List (BitVec 8)
  cmp48 : List (BitVec 1)
  mask28 : BitVec 32
  not49 : BitVec 32
  conv16 : BitVec 64
  conv17 : BitVec 64
  shl18 : BitVec 64
  or19 : BitVec 64
  join64 : List (BitVec 8)
  cmp30 : List (BitVec 1)
  or23 : BitVec 64
  vecinit : List (BitVec 64)
  pclmul : List (BitVec 64)
  vecext : BitVec 64
  xorI : BitVec 64
  shrI : BitVec 64
  not8 : BitVec 64
  v32 : BitVec 64
  v33 : BitVec 64
  and9 : BitVec 64
  and11 : BitVec 64
  shl12 : BitVec 64
  or13 : BitVec 64
  not14 : BitVec 64
  and15 : BitVec 64
  v34 : BitVec 64
  or16 : BitVec 64
  shr17 : BitVec 64
  arrayidx : Nat

/-- The first table the byte-class lookups read: per sixteen-byte lane, the
sentinel bytes as `vpshufb`'s second operand expects them. -/
def forBodyTableA : List (BitVec 8) :=
  [0x40#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
   0x00#8, 0x80#8, 0x82#8, 0x14#8, 0x01#8, 0xa8#8, 0x00#8, 0x00#8,
   0x40#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
   0x00#8, 0x80#8, 0x82#8, 0x14#8, 0x01#8, 0xa8#8, 0x00#8, 0x00#8]

/-- The second table the byte-class lookups read. -/
def forBodyTableB : List (BitVec 8) :=
  [0x80#8, 0x00#8, 0x41#8, 0x02#8, 0x00#8, 0x30#8, 0x00#8, 0x0c#8,
   0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8,
   0x80#8, 0x00#8, 0x41#8, 0x02#8, 0x00#8, 0x30#8, 0x00#8, 0x0c#8,
   0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8]

/-- The block's computation, from the nine inputs. -/
def forBodyValues (prevS i st0 st9 st15 : BitVec 64) (bs2 bs3 : List UInt8)
    (b ent : Nat) : ForBodyValues :=
  let shl := i <<< (0x0000000000000006#64).toNat
  let addPtr := b + (shl.signExtend 64).toNat
  let addPtr5 := addPtr + ((0x0000000000000020#64).signExtend 64).toNat
  let w2 := unpackLanes 64 4 (bytesToNat bs2)
  let w3 := unpackLanes 64 4 (bytesToNat bs3)
  let byte2 := bitcastVecLanes 8 32 w2
  let byte3 := bitcastVecLanes 8 32 w3
  let join := w2 ++ w3
  let joinBytes := bitcastVecLanes 8 64 join
  let cmp8 := icmpLanes .eq joinBytes (List.replicate 64 0x22#8)
  let or286 := BitVec.ofNat 64 (lanesToNat cmp8)
  let cmp39 := icmpLanes .eq byte2 (List.replicate 32 0x5c#8)
  let mask9 := BitVec.ofNat 32 (lanesToNat cmp39)
  let conv9 := BitVec.ofNat 64 mask9.toNat
  let cmpii := icmpLanes .eq byte3 (List.replicate 32 0x5c#8)
  let mask10 := BitVec.ofNat 32 (lanesToNat cmpii)
  let conv12 := BitVec.ofNat 64 mask10.toNat
  let shl13 := conv12 <<< (0x0000000000000020#64).toNat
  let or14 := shl13 ||| conv9
  let andII := st0 &&& st9
  let shlII := or14 <<< (0x0000000000000001#64).toNat
  let notII := shlII ^^^ 0xffffffffffffffff#64
  let and1II := or14 &&& notII
  let xorII := andII ^^^ 0x5555555555555555#64
  let and2II := and1II &&& xorII
  let xor3II := and2II ^^^ and1II
  let not4II := or14 ^^^ 0xffffffffffffffff#64
  let addII := and2II + or14
  let add5II := xor3II + or14
  let and6II := not4II &&& 0xaaaaaaaaaaaaaaaa#64
  let and7II := and6II &&& addII
  let and8II := not4II &&& 0x5555555555555555#64
  let and9II := and8II &&& add5II
  let and11II := andII &&& not4II
  let orII := and7II ||| and11II
  let or12II := orII ||| and9II
  let cmp45 := evalICmp .ult add5II or14
  let conv13II := BitVec.ofNat 64 cmp45.toNat
  let shrII := conv12 >>> (0x000000000000001f#64).toNat
  let notI := or12II ^^^ 0xffffffffffffffff#64
  let andI := or286 &&& notI
  let half11 := bitcastVecLanes 16 16 w2
  let shr12 := half11.map fun x : BitVec 16 => x >>> (0x0004#16).toNat
  let low13 := byte2.map fun x => x &&& 0x0f#8
  let shuf14 := pshufbLanes forBodyTableA low13
  let shuf15 := bitcastVecLanes 8 32 shr12
  let low16 := shuf15.map fun x => x &&& 0x0f#8
  let shuf17 := pshufbLanes forBodyTableB low16
  let andClass1 := List.zipWith (fun x y => x &&& y) shuf17 shuf14
  let and18 := andClass1.map fun x => x &&& 0x3f#8
  let cmp21 := icmpLanes .eq and18 (List.replicate 32 0x00#8)
  let mask19 := BitVec.ofNat 32 (lanesToNat cmp21)
  let not46 := mask19 ^^^ 0xffffffff#32
  let half20 := bitcastVecLanes 16 16 w3
  let shr21 := half20.map fun x : BitVec 16 => x >>> (0x0004#16).toNat
  let low22 := byte3.map fun x => x &&& 0x0f#8
  let shuf23 := pshufbLanes forBodyTableA low22
  let shuf24 := bitcastVecLanes 8 32 shr21
  let low25 := shuf24.map fun x => x &&& 0x0f#8
  let shuf26 := pshufbLanes forBodyTableB low25
  let andClass2 := List.zipWith (fun x y => x &&& y) shuf26 shuf23
  let and27 := andClass2.map fun x => x &&& 0x3f#8
  let cmp48 := icmpLanes .eq and27 (List.replicate 32 0x00#8)
  let mask28 := BitVec.ofNat 32 (lanesToNat cmp48)
  let not49 := mask28 ^^^ 0xffffffff#32
  let conv16 := BitVec.ofNat 64 not46.toNat
  let conv17 := BitVec.ofNat 64 not49.toNat
  let shl18 := conv17 <<< (0x0000000000000020#64).toNat
  let or19 := shl18 ||| conv16
  let join64 := andClass1 ++ andClass2
  let cmp30 := icmpLanes .eq join64 (List.replicate 64 0x00#8)
  let or23 := BitVec.ofNat 64 (lanesToNat cmp30)
  let vecinit := [BitVec.ofNat 64 andI.toNat, 0x0000000000000000#64]
  let pclmul := [Pclmul.clmul (BitVec.ofNat 64 andI.toNat) (BitVec.allOnes 64),
    0x0000000000000000#64]
  let vecext := Pclmul.clmul (BitVec.ofNat 64 andI.toNat) (BitVec.allOnes 64)
  let xorI := vecext ^^^ st15
  let shrI := BitVec.sshiftRight xorI (0x000000000000003f#64).toNat
  let not8 := xorI ^^^ 0xffffffffffffffff#64
  let v32 := andI ||| xorI
  let v33 := v32 ^^^ 0xffffffffffffffff#64
  let and9 := or23 &&& v33
  let and11 := or19 &&& not8
  let shl12 := and9 <<< (0x0000000000000001#64).toNat
  let or13 := shl12 ||| prevS
  let not14 := or13 ^^^ 0xffffffffffffffff#64
  let and15 := and9 &&& not14
  let v34 := and11 ||| and15
  let or16 := v34 ||| andI
  let shr17 := and9 >>> (0x000000000000003f#64).toNat
  let arrayidx := ent + (i.signExtend 64).toNat * (Ty.int 64).sizeBytes
  { prevS, i, st0, st9, st15, bs2, bs3, b, ent, shl, addPtr, addPtr5, w2, w3,
    byte2, byte3, join, joinBytes, cmp8, or286, cmp39, mask9, conv9, cmpii,
    mask10, conv12, shl13, or14, andII, shlII, notII, and1II, xorII, and2II,
    xor3II, not4II, addII, add5II, and6II, and7II, and8II, and9II, and11II,
    orII, or12II, cmp45, conv13II, shrII, notI, andI, half11, shr12, low13,
    shuf14, shuf15, low16, shuf17, andClass1, and18, cmp21, mask19, not46,
    half20, shr21, low22, shuf23, shuf24, low25, shuf26, andClass2, and27,
    cmp48, mask28, not49, conv16, conv17, shl18, or19, join64, cmp30, or23,
    vecinit, pclmul, vecext, xorI, shrI, not8, v32, v33, and9, and11, shl12,
    or13, not14, and15, v34, or16, shr17, arrayidx }

/-- `for.body`'s leading `phi` run, as the specs the block writes. -/
def forBodyPhis : List PhiSpec :=
  [{ dst := "%prevS.0511", ty := .int 64,
     incoming := [("for.body.lr.ph", .imm (.int 64 0x0000000000000000#64)),
       ("for.inc", .reg "%shr17")] },
   { dst := "%i.0510", ty := .int 64,
     incoming := [("for.body.lr.ph", .imm (.int 64 0x0000000000000000#64)),
       ("for.inc", .reg "%inc")] },
   { dst := "%st.sroa.0.0509", ty := .int 64,
     incoming := [("for.body.lr.ph", .imm (.int 64 0x0000000000000000#64)),
       ("for.inc", .reg "%shr.i.i")] },
   { dst := "%st.sroa.9.0508", ty := .int 64,
     incoming := [("for.body.lr.ph", .imm (.int 64 0x0000000000000000#64)),
       ("for.inc", .reg "%conv13.i.i")] },
   { dst := "%st.sroa.15.0507", ty := .int 64,
     incoming := [("for.body.lr.ph", .imm (.int 64 0x0000000000000000#64)),
       ("for.inc", .reg "%shr.i")] }]

/-- The bindings the run above installs, in the order the block writes them. -/
def forBodyPhiCells (v : ForBodyValues) : List (String × Value) :=
  [("%prevS.0511", .int 64 v.prevS),
   ("%i.0510", .int 64 v.i),
   ("%st.sroa.0.0509", .int 64 v.st0),
   ("%st.sroa.9.0508", .int 64 v.st9),
   ("%st.sroa.15.0507", .int 64 v.st15)]

/-- The instructions after `for.body`'s leading `phi` run: the shifted index, the
two pointer offsets and the two word loads. -/
def forBodySeg1Tail : List Instr :=
[
                          LeanLLVM.Instr.binop
                            "%shl"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%i.0510")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000006#64)),
                          LeanLLVM.Instr.gep
                            "%add.ptr"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%b")
                            (LeanLLVM.Operand.reg "%shl"),
                          LeanLLVM.Instr.load
                            "%2"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr"),
                          LeanLLVM.Instr.gep
                            "%add.ptr5"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000020#64)),
                          LeanLLVM.Instr.load
                            "%3"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr5"),]

/-- The environment after the phi run and the two loads. -/
def fbEnv1 (env : Env) (v : ForBodyValues) : Env :=
  cells [("%3", .vec 4 64 v.w3),
         ("%add.ptr5", .ptr v.addPtr5),
         ("%2", .vec 4 64 v.w2),
         ("%add.ptr", .ptr v.addPtr),
         ("%shl", .int 64 v.shl)]
    (cells [("%st.sroa.15.0507", .int 64 v.st15),
            ("%st.sroa.9.0508", .int 64 v.st9),
            ("%st.sroa.0.0509", .int 64 v.st0),
            ("%i.0510", .int 64 v.i),
            ("%prevS.0511", .int 64 v.prevS)] env)

/-- The environment after the word join and the byte-mask compare. -/
def fbEnv2 (env : Env) (v : ForBodyValues) : Env :=
  cells [("%or14.i", .int 64 v.or14),
         ("%shl13.i", .int 64 v.shl13),
         ("%conv12.i", .int 64 v.conv12),
         ("%10", .int 32 v.mask10),
         ("%cmp.i.i", .vec 32 1 v.cmpii),
         ("%conv9.i", .int 64 v.conv9),
         ("%9", .int 32 v.mask9),
         ("%cmp.i39.i", .vec 32 1 v.cmp39),
         ("%or.i286", .int 64 v.or286),
         ("%8", .vec 64 1 v.cmp8),
         ("%7", .vec 64 8 v.joinBytes),
         ("%6", .vec 8 64 v.join),
         ("%5", .vec 32 8 v.byte3),
         ("%4", .vec 32 8 v.byte2)] (fbEnv1 env v)

/-- The environment after the byte-class arithmetic. -/
def fbEnv3 (env : Env) (v : ForBodyValues) : Env :=
  cells [("%and.i", .int 64 v.andI),
         ("%not.i", .int 64 v.notI),
         ("%shr.i.i", .int 64 v.shrII),
         ("%conv13.i.i", .int 64 v.conv13II),
         ("%cmp.i45.i", .int 1 v.cmp45),
         ("%or12.i.i", .int 64 v.or12II),
         ("%or.i.i", .int 64 v.orII),
         ("%and11.i.i", .int 64 v.and11II),
         ("%and9.i.i", .int 64 v.and9II),
         ("%and8.i.i", .int 64 v.and8II),
         ("%and7.i.i", .int 64 v.and7II),
         ("%and6.i.i", .int 64 v.and6II),
         ("%add5.i.i", .int 64 v.add5II),
         ("%add.i.i", .int 64 v.addII),
         ("%not4.i.i", .int 64 v.not4II),
         ("%xor3.i.i", .int 64 v.xor3II),
         ("%and2.i.i", .int 64 v.and2II),
         ("%xor.i.i", .int 64 v.xorII),
         ("%and1.i.i", .int 64 v.and1II),
         ("%not.i.i", .int 64 v.notII),
         ("%shl.i.i", .int 64 v.shlII),
         ("%and.i.i", .int 64 v.andII)] (fbEnv2 env v)

/-- The environment after the first table lookup and its zero test. -/
def fbEnv4 (env : Env) (v : ForBodyValues) : Env :=
  cells [("%not.i46.i", .int 32 v.not46),
         ("%19", .int 32 v.mask19),
         ("%cmp.i21.i.i", .vec 32 1 v.cmp21),
         ("%18", .vec 32 8 v.and18),
         ("%and.i2326.i.i", .vec 32 8 v.andClass1),
         ("%17", .vec 32 8 v.shuf17),
         ("%16", .vec 32 8 v.low16),
         ("%15", .vec 32 8 v.shuf15),
         ("%14", .vec 32 8 v.shuf14),
         ("%13", .vec 32 8 v.low13),
         ("%12", .vec 16 16 v.shr12),
         ("%11", .vec 16 16 v.half11)] (fbEnv3 env v)

/-- The environment after the second table lookup and the packed class word. -/
def fbEnv5 (env : Env) (v : ForBodyValues) : Env :=
  cells [("%or19.i", .int 64 v.or19),
         ("%shl18.i", .int 64 v.shl18),
         ("%conv17.i", .int 64 v.conv17),
         ("%conv16.i", .int 64 v.conv16),
         ("%not.i49.i", .int 32 v.not49),
         ("%28", .int 32 v.mask28),
         ("%cmp.i21.i48.i", .vec 32 1 v.cmp48),
         ("%27", .vec 32 8 v.and27),
         ("%and.i2326.i47.i", .vec 32 8 v.andClass2),
         ("%26", .vec 32 8 v.shuf26),
         ("%25", .vec 32 8 v.low25),
         ("%24", .vec 32 8 v.shuf24),
         ("%23", .vec 32 8 v.shuf23),
         ("%22", .vec 32 8 v.low22),
         ("%21", .vec 16 16 v.shr21),
         ("%20", .vec 16 16 v.half20)] (fbEnv4 env v)

/-- The environment after the sixty-four-lane join and the state update. -/
def fbEnv6 (env : Env) (v : ForBodyValues) : Env :=
  cells [("%and11", .int 64 v.and11),
         ("%and9", .int 64 v.and9),
         ("%33", .int 64 v.v33),
         ("%32", .int 64 v.v32),
         ("%not8", .int 64 v.not8),
         ("%shr.i", .int 64 v.shrI),
         ("%xor.i", .int 64 v.xorI),
         ("%vecext.i.i.i", .int 64 v.vecext),
         ("%31", .vec 2 64 v.pclmul),
         ("%vecinit1.i.i.i", .vec 2 64 v.vecinit),
         ("%or23.i", .int 64 v.or23),
         ("%30", .vec 64 1 v.cmp30),
         ("%29", .vec 64 8 v.join64)] (fbEnv5 env v)

/-- The environment after the emit word, the array index and the store (the
store leaves the environment alone, so the last cell is the index). -/
def fbEnv7 (env : Env) (v : ForBodyValues) : Env :=
  cells [("%arrayidx", .ptr v.arrayidx),
         ("%shr17", .int 64 v.shr17),
         ("%or16", .int 64 v.or16),
         ("%34", .int 64 v.v34),
         ("%and15", .int 64 v.and15),
         ("%not14", .int 64 v.not14),
         ("%or13", .int 64 v.or13),
         ("%shl12", .int 64 v.shl12)] (fbEnv6 env v)

/-- `for.body`'s environment: everything the block binds. -/
abbrev forBodyOut (env : Env) (v : ForBodyValues) : Env := fbEnv7 env v
/-- `for.body`'s run: the phi run and the two block loads (instructions 0-9). -/
def forBodySeg1 : List Instr :=
[LeanLLVM.Instr.phi
                            "%prevS.0511"
                            (LeanLLVM.Ty.int 64)
                            [("for.body.lr.ph", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                             ("for.inc", LeanLLVM.Operand.reg "%shr17")],
                          LeanLLVM.Instr.phi
                            "%i.0510"
                            (LeanLLVM.Ty.int 64)
                            [("for.body.lr.ph", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                             ("for.inc", LeanLLVM.Operand.reg "%inc")],
                          LeanLLVM.Instr.phi
                            "%st.sroa.0.0509"
                            (LeanLLVM.Ty.int 64)
                            [("for.body.lr.ph", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                             ("for.inc", LeanLLVM.Operand.reg "%shr.i.i")],
                          LeanLLVM.Instr.phi
                            "%st.sroa.9.0508"
                            (LeanLLVM.Ty.int 64)
                            [("for.body.lr.ph", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                             ("for.inc", LeanLLVM.Operand.reg "%conv13.i.i")],
                          LeanLLVM.Instr.phi
                            "%st.sroa.15.0507"
                            (LeanLLVM.Ty.int 64)
                            [("for.body.lr.ph", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                             ("for.inc", LeanLLVM.Operand.reg "%shr.i")],
                          LeanLLVM.Instr.binop
                            "%shl"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%i.0510")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000006#64)),
                          LeanLLVM.Instr.gep
                            "%add.ptr"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%b")
                            (LeanLLVM.Operand.reg "%shl"),
                          LeanLLVM.Instr.load
                            "%2"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr"),
                          LeanLLVM.Instr.gep
                            "%add.ptr5"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000020#64)),
                          LeanLLVM.Instr.load
                            "%3"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr5"),]

/-- `for.body`'s run: the word join and the byte-mask compare (instructions 10-23). -/
def forBodySeg2 : List Instr :=
[                          LeanLLVM.Instr.vecBitcast "%4" 4 64 32 8 (LeanLLVM.Operand.reg "%2"),
                          LeanLLVM.Instr.vecBitcast "%5" 4 64 32 8 (LeanLLVM.Operand.reg "%3"),
                          LeanLLVM.Instr.shuffleVec
                            "%6"
                            4
                            64
                            (LeanLLVM.Operand.reg "%2")
                            (LeanLLVM.Operand.reg "%3")
                            [0, 1, 2, 3, 4, 5, 6, 7],
                          LeanLLVM.Instr.vecBitcast "%7" 8 64 64 8 (LeanLLVM.Operand.reg "%6"),
                          LeanLLVM.Instr.icmpVec
                            "%8"
                            (LeanLLVM.IPred.eq)
                            64
                            8
                            (LeanLLVM.Operand.reg "%7")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 64 8 0x22#8)),
                          LeanLLVM.Instr.bitcastMask "%or.i286" 64 (LeanLLVM.Operand.reg "%8"),
                          LeanLLVM.Instr.icmpVec
                            "%cmp.i39.i"
                            (LeanLLVM.IPred.eq)
                            32
                            8
                            (LeanLLVM.Operand.reg "%4")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x5c#8)),
                          LeanLLVM.Instr.bitcastMask "%9" 32 (LeanLLVM.Operand.reg "%cmp.i39.i"),
                          LeanLLVM.Instr.zext "%conv9.i" 32 64 (LeanLLVM.Operand.reg "%9"),
                          LeanLLVM.Instr.icmpVec
                            "%cmp.i.i"
                            (LeanLLVM.IPred.eq)
                            32
                            8
                            (LeanLLVM.Operand.reg "%5")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x5c#8)),
                          LeanLLVM.Instr.bitcastMask "%10" 32 (LeanLLVM.Operand.reg "%cmp.i.i"),
                          LeanLLVM.Instr.zext "%conv12.i" 32 64 (LeanLLVM.Operand.reg "%10"),
                          LeanLLVM.Instr.binop
                            "%shl13.i"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%conv12.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000020#64)),
                          LeanLLVM.Instr.binop
                            "%or14.i"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%shl13.i")
                            (LeanLLVM.Operand.reg "%conv9.i"),]

/-- `for.body`'s run: the byte-class arithmetic and the DFA carry (instructions 24-45). -/
def forBodySeg3 : List Instr :=
[                          LeanLLVM.Instr.binop
                            "%and.i.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%st.sroa.0.0509")
                            (LeanLLVM.Operand.reg "%st.sroa.9.0508"),
                          LeanLLVM.Instr.binop
                            "%shl.i.i"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%or14.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000001#64)),
                          LeanLLVM.Instr.binop
                            "%not.i.i"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%shl.i.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and1.i.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or14.i")
                            (LeanLLVM.Operand.reg "%not.i.i"),
                          LeanLLVM.Instr.binop
                            "%xor.i.i"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%and.i.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x5555555555555555#64)),
                          LeanLLVM.Instr.binop
                            "%and2.i.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and1.i.i")
                            (LeanLLVM.Operand.reg "%xor.i.i"),
                          LeanLLVM.Instr.binop
                            "%xor3.i.i"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%and2.i.i")
                            (LeanLLVM.Operand.reg "%and1.i.i"),
                          LeanLLVM.Instr.binop
                            "%not4.i.i"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%or14.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%add.i.i"
                            (LeanLLVM.BinOp.add)
                            64
                            (LeanLLVM.Operand.reg "%and2.i.i")
                            (LeanLLVM.Operand.reg "%or14.i"),
                          LeanLLVM.Instr.binop
                            "%add5.i.i"
                            (LeanLLVM.BinOp.add)
                            64
                            (LeanLLVM.Operand.reg "%xor3.i.i")
                            (LeanLLVM.Operand.reg "%or14.i"),
                          LeanLLVM.Instr.binop
                            "%and6.i.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%not4.i.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xaaaaaaaaaaaaaaaa#64)),
                          LeanLLVM.Instr.binop
                            "%and7.i.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and6.i.i")
                            (LeanLLVM.Operand.reg "%add.i.i"),
                          LeanLLVM.Instr.binop
                            "%and8.i.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%not4.i.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x5555555555555555#64)),
                          LeanLLVM.Instr.binop
                            "%and9.i.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and8.i.i")
                            (LeanLLVM.Operand.reg "%add5.i.i"),
                          LeanLLVM.Instr.binop
                            "%and11.i.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and.i.i")
                            (LeanLLVM.Operand.reg "%not4.i.i"),
                          LeanLLVM.Instr.binop
                            "%or.i.i"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%and7.i.i")
                            (LeanLLVM.Operand.reg "%and11.i.i"),
                          LeanLLVM.Instr.binop
                            "%or12.i.i"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%or.i.i")
                            (LeanLLVM.Operand.reg "%and9.i.i"),
                          LeanLLVM.Instr.icmp
                            "%cmp.i45.i"
                            (LeanLLVM.IPred.ult)
                            64
                            (LeanLLVM.Operand.reg "%add5.i.i")
                            (LeanLLVM.Operand.reg "%or14.i"),
                          LeanLLVM.Instr.zext "%conv13.i.i" 1 64 (LeanLLVM.Operand.reg "%cmp.i45.i"),
                          LeanLLVM.Instr.binop
                            "%shr.i.i"
                            (LeanLLVM.BinOp.lshr)
                            64
                            (LeanLLVM.Operand.reg "%conv12.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000001f#64)),
                          LeanLLVM.Instr.binop
                            "%not.i"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%or12.i.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or.i286")
                            (LeanLLVM.Operand.reg "%not.i"),]

/-- `for.body`'s run: the first shift-and-mask half, through the negated zero test (instructions 46-57). -/
def forBodySeg4 : List Instr :=
[                          LeanLLVM.Instr.vecBitcast "%11" 4 64 16 16 (LeanLLVM.Operand.reg "%2"),
                          LeanLLVM.Instr.binopVec
                            "%12"
                            (LeanLLVM.BinOp.lshr)
                            16
                            16
                            (LeanLLVM.Operand.reg "%11")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 16 16 0x0004#16)),
                          LeanLLVM.Instr.binopVec
                            "%13"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%4")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%14"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x40#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x82#8,
                                   0x14#8,
                                   0x01#8,
                                   0xa8#8,
                                   0x00#8,
                                   0x00#8,
                                   0x40#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x82#8,
                                   0x14#8,
                                   0x01#8,
                                   0xa8#8,
                                   0x00#8,
                                   0x00#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%13")],
                          LeanLLVM.Instr.vecBitcast "%15" 16 16 32 8 (LeanLLVM.Operand.reg "%12"),
                          LeanLLVM.Instr.binopVec
                            "%16"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%15")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%17"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x80#8,
                                   0x00#8,
                                   0x41#8,
                                   0x02#8,
                                   0x00#8,
                                   0x30#8,
                                   0x00#8,
                                   0x0c#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x00#8,
                                   0x41#8,
                                   0x02#8,
                                   0x00#8,
                                   0x30#8,
                                   0x00#8,
                                   0x0c#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%16")],
                          LeanLLVM.Instr.binopVec
                            "%and.i2326.i.i"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%17")
                            (LeanLLVM.Operand.reg "%14"),
                          LeanLLVM.Instr.binopVec
                            "%18"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i2326.i.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x3f#8)),
                          LeanLLVM.Instr.icmpVec
                            "%cmp.i21.i.i"
                            (LeanLLVM.IPred.eq)
                            32
                            8
                            (LeanLLVM.Operand.reg "%18")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x00#8)),
                          LeanLLVM.Instr.bitcastMask "%19" 32 (LeanLLVM.Operand.reg "%cmp.i21.i.i"),
                          LeanLLVM.Instr.binop
                            "%not.i46.i"
                            (LeanLLVM.BinOp.xor)
                            32
                            (LeanLLVM.Operand.reg "%19")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0xffffffff#32)),]

/-- `for.body`'s run: the second half through the packed class word (instructions 58-73). -/
def forBodySeg5 : List Instr :=
[                          LeanLLVM.Instr.vecBitcast "%20" 4 64 16 16 (LeanLLVM.Operand.reg "%3"),
                          LeanLLVM.Instr.binopVec
                            "%21"
                            (LeanLLVM.BinOp.lshr)
                            16
                            16
                            (LeanLLVM.Operand.reg "%20")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 16 16 0x0004#16)),
                          LeanLLVM.Instr.binopVec
                            "%22"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%5")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%23"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x40#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x82#8,
                                   0x14#8,
                                   0x01#8,
                                   0xa8#8,
                                   0x00#8,
                                   0x00#8,
                                   0x40#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x82#8,
                                   0x14#8,
                                   0x01#8,
                                   0xa8#8,
                                   0x00#8,
                                   0x00#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%22")],
                          LeanLLVM.Instr.vecBitcast "%24" 16 16 32 8 (LeanLLVM.Operand.reg "%21"),
                          LeanLLVM.Instr.binopVec
                            "%25"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%24")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%26"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x80#8,
                                   0x00#8,
                                   0x41#8,
                                   0x02#8,
                                   0x00#8,
                                   0x30#8,
                                   0x00#8,
                                   0x0c#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x00#8,
                                   0x41#8,
                                   0x02#8,
                                   0x00#8,
                                   0x30#8,
                                   0x00#8,
                                   0x0c#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%25")],
                          LeanLLVM.Instr.binopVec
                            "%and.i2326.i47.i"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%26")
                            (LeanLLVM.Operand.reg "%23"),
                          LeanLLVM.Instr.binopVec
                            "%27"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i2326.i47.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x3f#8)),
                          LeanLLVM.Instr.icmpVec
                            "%cmp.i21.i48.i"
                            (LeanLLVM.IPred.eq)
                            32
                            8
                            (LeanLLVM.Operand.reg "%27")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x00#8)),
                          LeanLLVM.Instr.bitcastMask "%28" 32 (LeanLLVM.Operand.reg "%cmp.i21.i48.i"),
                          LeanLLVM.Instr.binop
                            "%not.i49.i"
                            (LeanLLVM.BinOp.xor)
                            32
                            (LeanLLVM.Operand.reg "%28")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0xffffffff#32)),
                          LeanLLVM.Instr.zext "%conv16.i" 32 64 (LeanLLVM.Operand.reg "%not.i46.i"),
                          LeanLLVM.Instr.zext "%conv17.i" 32 64 (LeanLLVM.Operand.reg "%not.i49.i"),
                          LeanLLVM.Instr.binop
                            "%shl18.i"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%conv17.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000020#64)),
                          LeanLLVM.Instr.binop
                            "%or19.i"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%shl18.i")
                            (LeanLLVM.Operand.reg "%conv16.i"),]

/-- `for.body`'s run: the sixty-four-lane join, the carry-less product and the state update (instructions 74-86). -/
def forBodySeg6 : List Instr :=
[                          LeanLLVM.Instr.shuffleVec
                            "%29"
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i2326.i.i")
                            (LeanLLVM.Operand.reg "%and.i2326.i47.i")
                            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
                             25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
                             48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63],
                          LeanLLVM.Instr.icmpVec
                            "%30"
                            (LeanLLVM.IPred.eq)
                            64
                            8
                            (LeanLLVM.Operand.reg "%29")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 64 8 0x00#8)),
                          LeanLLVM.Instr.bitcastMask "%or23.i" 64 (LeanLLVM.Operand.reg "%30"),
                          LeanLLVM.Instr.insertelement
                            "%vecinit1.i.i.i"
                            2
                            64
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 2 64 0x0000000000000000#64))
                            (LeanLLVM.Operand.reg "%and.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                          LeanLLVM.Instr.call
                            "%31"
                            (LeanLLVM.Ty.vec 2 (LeanLLVM.Ty.int 64))
                            "llvm.x86.pclmulqdq"
                            [(LeanLLVM.Ty.vec 2 (LeanLLVM.Ty.int 64), LeanLLVM.Operand.reg "%vecinit1.i.i.i"),
                             (LeanLLVM.Ty.vec 2 (LeanLLVM.Ty.int 64),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector 64 [0xffffffffffffffff#64, 0x0000000000000000#64])),
                             (LeanLLVM.Ty.int 8, LeanLLVM.Operand.imm (LeanLLVM.Const.int 8 0x00#8))],
                          LeanLLVM.Instr.extractelement
                            "%vecext.i.i.i"
                            2
                            64
                            (LeanLLVM.Operand.reg "%31")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                          LeanLLVM.Instr.binop
                            "%xor.i"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%vecext.i.i.i")
                            (LeanLLVM.Operand.reg "%st.sroa.15.0507"),
                          LeanLLVM.Instr.binop
                            "%shr.i"
                            (LeanLLVM.BinOp.ashr)
                            64
                            (LeanLLVM.Operand.reg "%xor.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000003f#64)),
                          LeanLLVM.Instr.binop
                            "%not8"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%xor.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%32"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%and.i")
                            (LeanLLVM.Operand.reg "%xor.i"),
                          LeanLLVM.Instr.binop
                            "%33"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%32")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and9"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or23.i")
                            (LeanLLVM.Operand.reg "%33"),
                          LeanLLVM.Instr.binop
                            "%and11"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or19.i")
                            (LeanLLVM.Operand.reg "%not8"),]

/-- `for.body`'s run: the emit word, the array index and the store (instructions 87-95). -/
def forBodySeg7 : List Instr :=
[                          LeanLLVM.Instr.binop
                            "%shl12"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%and9")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000001#64)),
                          LeanLLVM.Instr.binop
                            "%or13"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%shl12")
                            (LeanLLVM.Operand.reg "%prevS.0511"),
                          LeanLLVM.Instr.binop
                            "%not14"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%or13")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and15"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and9")
                            (LeanLLVM.Operand.reg "%not14"),
                          LeanLLVM.Instr.binop
                            "%34"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%and11")
                            (LeanLLVM.Operand.reg "%and15"),
                          LeanLLVM.Instr.binop
                            "%or16"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%34")
                            (LeanLLVM.Operand.reg "%and.i"),
                          LeanLLVM.Instr.binop
                            "%shr17"
                            (LeanLLVM.BinOp.lshr)
                            64
                            (LeanLLVM.Operand.reg "%and9")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000003f#64)),
                          LeanLLVM.Instr.gep
                            "%arrayidx"
                            (LeanLLVM.Ty.int 64)
                            (LeanLLVM.Operand.reg "%ent")
                            (LeanLLVM.Operand.reg "%i.0510"),
                          LeanLLVM.Instr.store
                            (LeanLLVM.Ty.int 64)
                            (LeanLLVM.Operand.reg "%or16")
                            (LeanLLVM.Operand.reg "%arrayidx")]


/-! ### The lane write, the carry-less product and its lane read

The block's `vpshufb`-based class masks end in a lane write, a `pclmulqdq` and a
lane read.  The generic steps leave the written lane set and the read lane as
side goals; these three state them at the spellings the block's own statement
uses, so the segment's close never meets a lane list it cannot name. -/

/-- `%vecinit1.i.i.i`: lane zero of a two-lane zero vector takes `%and.i`. -/
theorem forBody_vecinit (env : Env) (s : State) (x : BitVec 64)
    (h : lookupName env "%and.i" = some (.int 64 x)) (is : List Instr) :
    denoteCode s1BlocksCalls
        (.insertelement "%vecinit1.i.i.i" 2 64
          (.imm (.splat 2 64 0x0000000000000000#64)) (.reg "%and.i")
          (.imm (.int 64 0x0000000000000000#64)) :: is) (stateAt env s) =
      denoteCode s1BlocksCalls is
        (stateAt (("%vecinit1.i.i.i",
          .vec 2 64 [BitVec.ofNat 64 x.toNat, 0x0000000000000000#64]) :: env) s) := by
  rw [denoteCode_insertelement (calls := s1BlocksCalls) (env := env) (s := s)
    (d := "%vecinit1.i.i.i") (n := 2) (w := 64)
    (v := .imm (.splat 2 64 0x0000000000000000#64)) (elt := .reg "%and.i")
    (idx := .imm (.int 64 0x0000000000000000#64))
    (vv := .vec 2 64 (List.replicate 2 0x0000000000000000#64))
    (lanes := List.replicate 2 0x0000000000000000#64)
    (ev := .int 64 x) (x := x.toNat) (wi := 64) (k := 0x0000000000000000#64)
    (hv := by simp [evalOperand, Const.toValue])
    (hl := vecLanes_self (by simp))
    (helt := evalOperand_reg_of env s "%and.i" (.int 64 x) h)
    (hx := rfl) (hi := rfl) (hk := by decide)]
  rfl

/-- `%31`: the carry-less product of the written lane against all ones. -/
theorem forBody_pclmul (env : Env) (s : State) (a : BitVec 64)
    (h : lookupName env "%vecinit1.i.i.i" = some (.vec 2 64 [a, 0x0000000000000000#64]))
    (is : List Instr) :
    denoteCode s1BlocksCalls
        (.call "%31" (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
          [(.vec 2 (.int 64), .reg "%vecinit1.i.i.i"),
           (.vec 2 (.int 64),
             .imm (.vector 64 [0xffffffffffffffff#64, 0x0000000000000000#64])),
           (.int 8, .imm (.int 8 0x00#8))] :: is) (stateAt env s) =
      denoteCode s1BlocksCalls is
        (stateAt (("%31",
          .vec 2 64 [Pclmul.clmul a (BitVec.allOnes 64), 0x0000000000000000#64]) :: env) s) := by
  exact denoteCode_pclmul_b env s "%vecinit1.i.i.i" "%31"
    (a0 := a) (a1 := 0x0000000000000000#64)
    (evalOperand_reg_of env s "%vecinit1.i.i.i" (.vec 2 64 [a, 0x0000000000000000#64]) h) is

/-- `%vecext.i.i.i`: lane zero of the product, which is the product itself. -/
theorem forBody_vecext (env : Env) (s : State) (a : BitVec 64)
    (h : lookupName env "%31" = some (.vec 2 64 [a, 0x0000000000000000#64]))
    (is : List Instr) :
    denoteCode s1BlocksCalls
        (.extractelement "%vecext.i.i.i" 2 64 (.reg "%31")
          (.imm (.int 64 0x0000000000000000#64)) :: is) (stateAt env s) =
      denoteCode s1BlocksCalls is (stateAt (("%vecext.i.i.i", .int 64 a) :: env) s) := by
  exact denoteCode_extractelement (calls := s1BlocksCalls) (env := env) (s := s)
    (d := "%vecext.i.i.i") (n := 2) (w := 64) (v := .reg "%31")
    (idx := .imm (.int 64 0x0000000000000000#64))
    (vv := .vec 2 64 [a, 0x0000000000000000#64])
    (lanes := [a, 0x0000000000000000#64]) (wi := 64)
    (k := 0x0000000000000000#64) (x := a)
    (hv := evalOperand_reg_of env s "%31" (.vec 2 64 [a, 0x0000000000000000#64]) h)
    (hl := vecLanes_self (by simp)) (hi := rfl) (hx := by simp) is

/-- The block steps, with the three lane-shape steps of this block ahead of the
generic battery so their lane lists come out named. -/
macro "fb_step" : tactic => `(tactic|
  (first
   | rw [forBody_vecinit _ _ _ ?_ _]
   | rw [forBody_pclmul _ _ _ ?_ _]
   | rw [forBody_vecext _ _ _ ?_ _]
   | block_step_b))

/-- A segment's chain, closed by the block's close. -/
macro "fb_eval" : tactic => `(tactic|
  (repeat fb_step
   block_close_v))


/-- Splitting a straight-line sequence at a point whose state is already known:
the second half runs from it, so the composition never puts a state under a
`bind`. -/
theorem denoteCode_append_apply {calls : Calls} {a b : List Instr} {s s' : State}
    (h : denoteCode calls a s = some s') (hb : startsWithPhi b = false) :
    denoteCode calls (a ++ b) s = denoteCode calls b s' := by
  rw [LeanLLVM.Refinement.JsonEntrySteps.denoteCode_append (hb := hb), h]
  rfl


/-! ### The seven segments

Each is one `denoteCode` equation at an explicit intermediate environment.  The
first states the phi run and the two loads; the rest are straight-line and start
from the environment the previous segment left. -/

/-- **`for.body`'s first segment.**  The five leading phis select the carried
values off the incoming edge, and the two `<4 x i64>` loads read the block's
thirty-two-byte words. -/
theorem for_body_seg1 (env : Env) (s : State) (p : String)
    (op1 op2 op3 op4 op5 : Operand)
    (prevS i st0 st9 st15 : BitVec 64) (bs2 bs3 : List UInt8) (b ent : Nat)
    (hpre : s.pre = some p)
    (hinc1 : phiIncoming p [("for.body.lr.ph", .imm (.int 64 0x0000000000000000#64)),
      ("for.inc", .reg "%shr17")] = some op1)
    (hop1 : evalOperand (stateAt env s) op1 = some (.int 64 prevS))
    (hinc2 : phiIncoming p [("for.body.lr.ph", .imm (.int 64 0x0000000000000000#64)),
      ("for.inc", .reg "%inc")] = some op2)
    (hop2 : evalOperand (stateAt env s) op2 = some (.int 64 i))
    (hinc3 : phiIncoming p [("for.body.lr.ph", .imm (.int 64 0x0000000000000000#64)),
      ("for.inc", .reg "%shr.i.i")] = some op3)
    (hop3 : evalOperand (stateAt env s) op3 = some (.int 64 st0))
    (hinc4 : phiIncoming p [("for.body.lr.ph", .imm (.int 64 0x0000000000000000#64)),
      ("for.inc", .reg "%conv13.i.i")] = some op4)
    (hop4 : evalOperand (stateAt env s) op4 = some (.int 64 st9))
    (hinc5 : phiIncoming p [("for.body.lr.ph", .imm (.int 64 0x0000000000000000#64)),
      ("for.inc", .reg "%shr.i")] = some op5)
    (hop5 : evalOperand (stateAt env s) op5 = some (.int 64 st15))
    (hb : lookupName env "%b" = some (.ptr b))
    (hshl63 : ((i <<< (0x0000000000000006#64).toNat).signExtend 64).toNat < 2 ^ 63)
    (hread2 : readBytes s.mem
      (b + ((i <<< (0x0000000000000006#64).toNat).signExtend 64).toNat) 32 = some bs2)
    (hread3 : readBytes s.mem
      ((b + ((i <<< (0x0000000000000006#64).toNat).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs3) :
    let v := forBodyValues prevS i st0 st9 st15 bs2 bs3 b ent
    denoteCode s1BlocksCalls forBodySeg1 (stateAt env s) =
      some (stateAt (fbEnv1 env v) s) := by
  intro v
  unfold fbEnv1
  rw [show forBodySeg1 = forBodyPhis.map PhiSpec.instr ++ forBodySeg1Tail from rfl]
  rw [denoteCode_phiRun (calls := s1BlocksCalls) (s := stateAt env s) (p := p)
    (specs := forBodyPhis) (vs := forBodyPhiCells v) (rest := forBodySeg1Tail)
    hpre
    (PhiSelects.cons hinc1 hop1
      (PhiSelects.cons hinc2 hop2
        (PhiSelects.cons hinc3 hop3
          (PhiSelects.cons hinc4 hop4
            (PhiSelects.cons hinc5 hop5 PhiSelects.nil)))))
    (by rfl)]
  rw [stateAt_bindAll_runCells]
  unfold forBodySeg1Tail
  block_eval_b

/-- **`for.body`'s second segment.**  The word join, the byte masks and the two
byte-class compares. -/
theorem for_body_seg2 (env : Env) (s : State)
    (prevS i st0 st9 st15 : BitVec 64) (bs2 bs3 : List UInt8) (b ent : Nat) :
    let v := forBodyValues prevS i st0 st9 st15 bs2 bs3 b ent
    denoteCode s1BlocksCalls forBodySeg2 (stateAt (fbEnv1 env v) s) =
      some (stateAt (fbEnv2 env v) s) := by
  intro v
  unfold forBodySeg2 fbEnv1 fbEnv2
  block_eval_b

/-- **`for.body`'s third segment.**  The byte-class arithmetic and the DFA's
carried state. -/
theorem for_body_seg3 (env : Env) (s : State)
    (prevS i st0 st9 st15 : BitVec 64) (bs2 bs3 : List UInt8) (b ent : Nat) :
    let v := forBodyValues prevS i st0 st9 st15 bs2 bs3 b ent
    denoteCode s1BlocksCalls forBodySeg3 (stateAt (fbEnv2 env v) s) =
      some (stateAt (fbEnv3 env v) s) := by
  intro v
  unfold forBodySeg3 fbEnv2 fbEnv3
  block_eval_b

/-- **`for.body`'s fourth segment.**  The first shift-and-mask half, through the
table lookup and its negated zero test. -/
theorem for_body_seg4 (env : Env) (s : State)
    (prevS i st0 st9 st15 : BitVec 64) (bs2 bs3 : List UInt8) (b ent : Nat) :
    let v := forBodyValues prevS i st0 st9 st15 bs2 bs3 b ent
    denoteCode s1BlocksCalls forBodySeg4 (stateAt (fbEnv3 env v) s) =
      some (stateAt (fbEnv4 env v) s) := by
  intro v
  unfold forBodySeg4 fbEnv3 fbEnv4
  block_eval_b

/-- **`for.body`'s fifth segment.**  The second shift-and-mask half, through the
packed class word and the two widened masks. -/
theorem for_body_seg5 (env : Env) (s : State)
    (prevS i st0 st9 st15 : BitVec 64) (bs2 bs3 : List UInt8) (b ent : Nat) :
    let v := forBodyValues prevS i st0 st9 st15 bs2 bs3 b ent
    denoteCode s1BlocksCalls forBodySeg5 (stateAt (fbEnv4 env v) s) =
      some (stateAt (fbEnv5 env v) s) := by
  intro v
  unfold forBodySeg5 fbEnv4 fbEnv5
  block_eval_b

/-- **`for.body`'s sixth segment.**  The sixty-four-lane join, the carry-less
product and the state update, through the two class words. -/
theorem for_body_seg6 (env : Env) (s : State)
    (prevS i st0 st9 st15 : BitVec 64) (bs2 bs3 : List UInt8) (b ent : Nat) :
    let v := forBodyValues prevS i st0 st9 st15 bs2 bs3 b ent
    denoteCode s1BlocksCalls forBodySeg6 (stateAt (fbEnv5 env v) s) =
      some (stateAt (fbEnv6 env v) s) := by
  intro v
  unfold forBodySeg6 fbEnv5 fbEnv6
  fb_eval

/-- **`for.body`'s seventh segment.**  The emitted word, the array index and the
store, which writes the word at the caller's selection. -/
theorem for_body_seg7 (env : Env) (s : State)
    (prevS i st0 st9 st15 : BitVec 64) (bs2 bs3 : List UInt8) (b ent : Nat)
    (hent : lookupName env "%ent" = some (.ptr ent))
    (hi63 : (i.signExtend 64).toNat < 2 ^ 63) :
    let v := forBodyValues prevS i st0 st9 st15 bs2 bs3 b ent
    denoteCode s1BlocksCalls forBodySeg7 (stateAt (fbEnv6 env v) s) =
      some (stateAt (fbEnv7 env v)
        { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }) := by
  intro v
  unfold forBodySeg7 fbEnv6 fbEnv7
  block_eval_b

/-- The block's instruction list, split at the seven segment boundaries. -/
theorem for_bodyInstrs_split :
    for_bodyInstrs =
      forBodySeg1 ++ (forBodySeg2 ++ (forBodySeg3 ++ (forBodySeg4 ++
        (forBodySeg5 ++ (forBodySeg6 ++ forBodySeg7))))) := rfl

/-- **`for.body`'s run.**  The seven segments compose: the phi run and the two
loads hand their environment to the classifier's entry composition, which hands
its own to the two table lookups, whose class words are the DFA's input, and the
last segment stores the emitted word. -/
theorem for_body_denote (env : Env) (s : State) (p : String)
    (op1 op2 op3 op4 op5 : Operand)
    (prevS i st0 st9 st15 : BitVec 64) (bs2 bs3 : List UInt8) (b ent : Nat)
    (hpre : s.pre = some p)
    (hinc1 : phiIncoming p [("for.body.lr.ph", .imm (.int 64 0x0000000000000000#64)),
      ("for.inc", .reg "%shr17")] = some op1)
    (hop1 : evalOperand (stateAt env s) op1 = some (.int 64 prevS))
    (hinc2 : phiIncoming p [("for.body.lr.ph", .imm (.int 64 0x0000000000000000#64)),
      ("for.inc", .reg "%inc")] = some op2)
    (hop2 : evalOperand (stateAt env s) op2 = some (.int 64 i))
    (hinc3 : phiIncoming p [("for.body.lr.ph", .imm (.int 64 0x0000000000000000#64)),
      ("for.inc", .reg "%shr.i.i")] = some op3)
    (hop3 : evalOperand (stateAt env s) op3 = some (.int 64 st0))
    (hinc4 : phiIncoming p [("for.body.lr.ph", .imm (.int 64 0x0000000000000000#64)),
      ("for.inc", .reg "%conv13.i.i")] = some op4)
    (hop4 : evalOperand (stateAt env s) op4 = some (.int 64 st9))
    (hinc5 : phiIncoming p [("for.body.lr.ph", .imm (.int 64 0x0000000000000000#64)),
      ("for.inc", .reg "%shr.i")] = some op5)
    (hop5 : evalOperand (stateAt env s) op5 = some (.int 64 st15))
    (hb : lookupName env "%b" = some (.ptr b))
    (hent : lookupName env "%ent" = some (.ptr ent))
    (hi63 : (i.signExtend 64).toNat < 2 ^ 63)
    (hshl63 : ((i <<< (0x0000000000000006#64).toNat).signExtend 64).toNat < 2 ^ 63)
    (hread2 : readBytes s.mem
      (b + ((i <<< (0x0000000000000006#64).toNat).signExtend 64).toNat) 32 = some bs2)
    (hread3 : readBytes s.mem
      ((b + ((i <<< (0x0000000000000006#64).toNat).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs3) :
    let v := forBodyValues prevS i st0 st9 st15 bs2 bs3 b ent
    denoteCode s1BlocksCalls for_bodyInstrs (stateAt env s) =
      some (stateAt (forBodyOut env v)
        { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }) := by
  intro v
  have h1 := for_body_seg1 env s p op1 op2 op3 op4 op5 prevS i st0 st9 st15 bs2 bs3
    b ent hpre hinc1 hop1 hinc2 hop2 hinc3 hop3 hinc4 hop4 hinc5 hop5 hb hshl63
    hread2 hread3
  have h2 := for_body_seg2 env s prevS i st0 st9 st15 bs2 bs3 b ent
  have h3 := for_body_seg3 env s prevS i st0 st9 st15 bs2 bs3 b ent
  have h4 := for_body_seg4 env s prevS i st0 st9 st15 bs2 bs3 b ent
  have h5 := for_body_seg5 env s prevS i st0 st9 st15 bs2 bs3 b ent
  have h6 := for_body_seg6 env s prevS i st0 st9 st15 bs2 bs3 b ent
  have h7 := for_body_seg7 env s prevS i st0 st9 st15 bs2 bs3 b ent hent hi63
  calc denoteCode s1BlocksCalls for_bodyInstrs (stateAt env s)
      = denoteCode s1BlocksCalls
          (forBodySeg1 ++ (forBodySeg2 ++ (forBodySeg3 ++ (forBodySeg4 ++
            (forBodySeg5 ++ (forBodySeg6 ++ forBodySeg7)))))) (stateAt env s) := by
        rw [for_bodyInstrs_split]
    _ = denoteCode s1BlocksCalls
          (forBodySeg2 ++ (forBodySeg3 ++ (forBodySeg4 ++
            (forBodySeg5 ++ (forBodySeg6 ++ forBodySeg7)))))
          (stateAt (fbEnv1 env v) s) := denoteCode_append_apply h1 (by rfl)
    _ = denoteCode s1BlocksCalls
          (forBodySeg3 ++ (forBodySeg4 ++ (forBodySeg5 ++
            (forBodySeg6 ++ forBodySeg7))))
          (stateAt (fbEnv2 env v) s) := denoteCode_append_apply h2 (by rfl)
    _ = denoteCode s1BlocksCalls
          (forBodySeg4 ++ (forBodySeg5 ++ (forBodySeg6 ++ forBodySeg7)))
          (stateAt (fbEnv3 env v) s) := denoteCode_append_apply h3 (by rfl)
    _ = denoteCode s1BlocksCalls (forBodySeg5 ++ (forBodySeg6 ++ forBodySeg7))
          (stateAt (fbEnv4 env v) s) := denoteCode_append_apply h4 (by rfl)
    _ = denoteCode s1BlocksCalls (forBodySeg6 ++ forBodySeg7)
          (stateAt (fbEnv5 env v) s) := denoteCode_append_apply h5 (by rfl)
    _ = denoteCode s1BlocksCalls forBodySeg7
          (stateAt (fbEnv6 env v) s) := denoteCode_append_apply h6 (by rfl)
    _ = some (stateAt (forBodyOut env v)
          { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.or16.toNat 8) }) := h7

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
#print axioms for_body_denote

end LeanLLVM.Refinement.JsonS1BlocksRefine
