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

/-! ### The vector intrinsics, at the unit's call environment

`BlockEvalVector` states the table lookup and the carry-less product at the mask
unit's `s1Calls`, because that is where the mask unit's body runs.  The block
unit's environment binds the same two arms, so a block run needs the same two
steps at `s1BlocksCalls`; the arms are `s1BlocksCalls_pshufb` and
`s1BlocksCalls_pclmulqdq` in `JsonS1BlocksReuse`. -/

/-- `pshuf.b` at the block unit's environment: the 32-lane lookup at the literal
table the body spells. -/
theorem step_pshufb_b (env : Env) (s : State) (r dst : String) (tabInt : List Int)
    (tab ctl : List (BitVec 8)) (htabLen : tabInt.length = 32)
    (htab : tabInt.map (BitVec.ofInt 8) = tab)
    (h : evalOperand (stateAt env s) (.reg r) = some (.vec 32 8 ctl)) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.call dst v32i8 "llvm.x86.avx2.pshuf.b"
          [(v32i8, lanesOf 8 tabInt), (v32i8, .reg r)]) =
      some (stateAt ((dst, .vec 32 8 (pshufbLanes tab ctl)) :: env) s) := by
  have hreg : lookupName env r = some (.vec 32 8 ctl) := by
    simp only [evalOperand, stateAt] at h
    split at h
    · cases h
    · exact h
  have ha : evalOperands (stateAt env s) [(v32i8, lanesOf 8 tabInt), (v32i8, .reg r)]
      = some [.vec 32 8 (tabInt.map (BitVec.ofInt 8)), .vec 32 8 ctl] := by
    rw [evalOperands_cons
      (v := .vec 32 8 (tabInt.map (BitVec.ofInt 8))) (vs := [.vec 32 8 ctl])
      (by simp [evalOperand, stateAt, lanesOf, Const.toValue, List.length_map, htabLen])
      (evalOperands_cons (by simp only [evalOperand, stateAt, hreg]) rfl)]
  rw [evalInstr_call (s := stateAt env s) ha
    (s1BlocksCalls_pshufb (tabInt.map (BitVec.ofInt 8)) ctl s.mem s.next), htab]
  rfl

/-- `pclmulqdq` at immediate zero, at the block unit's environment: lane zero is
the carry-less product, lane one zero. -/
theorem step_pclmul_b (env : Env) (s : State) (r dst : String) {a0 a1 : BitVec 64}
    (h : evalOperand (stateAt env s) (.reg r) = some (.vec 2 64 [a0, a1])) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.call dst (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
          [(.vec 2 (.int 64), .reg r), (.vec 2 (.int 64), lanesOf 64 [-1, 0]),
           (.int 8, lit 8 0)]) =
      some (stateAt ((dst, .vec 2 64 [Pclmul.clmul a0 (BitVec.allOnes 64), 0]) :: env) s) := by
  have hneg : (BitVec.ofInt 64 (-1) : BitVec 64) = BitVec.allOnes 64 := by decide
  have hreg : lookupName env r = some (.vec 2 64 [a0, a1]) := by
    simp only [evalOperand, stateAt] at h
    split at h
    · cases h
    · exact h
  have ha : evalOperands (stateAt env s)
      [(.vec 2 (.int 64), .reg r), (.vec 2 (.int 64), lanesOf 64 [-1, 0]),
       (.int 8, lit 8 0)] =
      some [.vec 2 64 [a0, a1],
        .vec 2 64 [BitVec.ofInt 64 (-1), BitVec.ofInt 64 0], .int 8 0] := by
    rw [evalOperands_cons (v := .vec 2 64 [a0, a1])
      (vs := [.vec 2 64 [BitVec.ofInt 64 (-1), BitVec.ofInt 64 0], .int 8 0])
      (by simp only [evalOperand, stateAt, hreg])
      (evalOperands_cons (v := .vec 2 64 [BitVec.ofInt 64 (-1), BitVec.ofInt 64 0])
        (vs := [.int 8 0])
        (by simp [evalOperand, stateAt, lanesOf, Const.toValue]) rfl)]
  rw [evalInstr_call (s := stateAt env s) ha
    (s1BlocksCalls_pclmulqdq a0 a1 (BitVec.ofInt 64 (-1)) (BitVec.ofInt 64 0)
      s.mem s.next)]
  simp only [hneg, stateAt]

/-- The table lookup, as a chain step at the block unit's environment. -/
theorem denoteCode_pshufb_b (env : Env) (s : State) (r dst : String) (tabInt : List Int)
    (tab ctl : List (BitVec 8)) (htabLen : tabInt.length = 32)
    (htab : tabInt.map (BitVec.ofInt 8) = tab)
    (h : evalOperand (stateAt env s) (.reg r) = some (.vec 32 8 ctl))
    (is : List Instr) :
    denoteCode s1BlocksCalls
        (.call dst v32i8 "llvm.x86.avx2.pshuf.b"
          [(v32i8, lanesOf 8 tabInt), (v32i8, .reg r)] :: is) (stateAt env s) =
      denoteCode s1BlocksCalls is
        (stateAt ((dst, .vec 32 8 (pshufbLanes tab ctl)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_pshufb_b env s r dst tabInt tab ctl htabLen htab h)]

/-- The carry-less product, as a chain step at the block unit's environment. -/
theorem denoteCode_pclmul_b (env : Env) (s : State) (r dst : String) {a0 a1 : BitVec 64}
    (h : evalOperand (stateAt env s) (.reg r) = some (.vec 2 64 [a0, a1]))
    (is : List Instr) :
    denoteCode s1BlocksCalls
        (.call dst (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
          [(.vec 2 (.int 64), .reg r), (.vec 2 (.int 64), lanesOf 64 [-1, 0]),
           (.int 8, lit 8 0)] :: is) (stateAt env s) =
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


/-! ### The block tactic

`block_step_v` covers the vector and `i64` shapes; the width-generic steps are
appended for the prologue's `i32` arithmetic. -/

macro "block_step_b" : tactic => `(tactic|
  (first
   | rw [denoteCode_callVoid7 _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _]
   | rw [denoteCode_load32_8 _ _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_gep8_imm_m1 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_gep8_imm_m2 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_gep8_imm_m3 _ _ _ _ _ ?_ ?_ _]
   | block_step_v
   | rw [denoteCode_pshufb_b _ _ _ _ _ _ _ _ ?_ ?_ ?_ _]
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

/-- One close step for a semantic side goal.  Every alternative either closes
its goal or fails, so `repeat` over it terminates. -/
macro "block_close_step" : tactic => `(tactic|
  (first
   | (simp only [evalOperand, stateAt]; block_lk)
   | exact BlockEval.evalOperand_reg_of _ _ _ _ (by assumption)
   | (simp only [evalOperand, Const.toValue, lanesOf, splatOf]; rfl)
   | exact BlockEval.evalOperand_lit_of _ _ _
   | (refine vecLanes_self ?_; simp_all [List.length_append])
   | (simp only [Value.vecLanes]; repeat split; all_goals (first | rfl | contradiction))
   | (simp only [phiIncoming]; rfl)
   | (rw [binopLanes_replicate]; all_goals (first | assumption | (intro x; rfl) | (simp; omega) | rfl))
   | (rw [binopLanes_zipWith]; all_goals (first | assumption | (intro x y; rfl) | (simp; omega) | rfl))
   | (rw [mapM_pick8 (by assumption) (by assumption)]; rfl)
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
