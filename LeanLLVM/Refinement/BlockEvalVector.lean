/-
A block evaluator extension for the vector instruction shapes.

`BlockEval` covers the integer and control shapes; the stage-1 classifier's body
is mostly lane arithmetic (`icmpVec`, `bitcastMask`, `binopVec`, `shuffleVec`,
`vecBitcast`), the two intrinsic calls and the escape-list call.  This module
adds those shapes to the same chain-step vocabulary and a close phase that
discharges a constant operand's read, so a block containing them is still one
tactic invocation.

The steps are stated at the state's own environment (`stateAt env s`) with the
operand reads as hypotheses, exactly as `BlockEval`'s are.  The lane-wise steps
name the operands' *values* generically and carry the lane list as a hypothesis,
so a caller never has to restate a length: the list comes from the previous
step's value.
-/
import LeanLLVM.Refinement.BlockEval
import LeanLLVM.Refinement.JsonS1MasksIR

set_option autoImplicit false

namespace LeanLLVM.Refinement.BlockEvalVector

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.Pclmul (clmul)

/-! ### Lane-list spellings -/

/-- The lane-wise comparison result the step binds. -/
abbrev icmpLanes {w : Nat} (pred : IPred) (l1 l2 : List (BitVec w)) : List (BitVec 1) :=
  (l1.zip l2).map fun (x, y) => evalICmp pred x y

/-- The lane-wise binary result, when the operation is total on every pair. -/
abbrev binopLanes {w : Nat} (op : BinOp) (l1 l2 : List (BitVec w)) :
    Option (List (BitVec w)) :=
  (l1.zip l2).mapM fun (x, y) => evalBinop op x y

/-- The shuffle's chosen lanes. -/
abbrev shuffleLanes {w : Nat} (n : Nat) (l1 l2 : List (BitVec w)) (mask : List Nat) :
    Option (List (BitVec w)) :=
  mask.mapM fun k => if k < n then l1[k]? else l2[k - n]?

/-! ### The vector steps -/

/-- A lane-wise comparison, at the operand values the reads yield. -/
theorem step_icmpVec (calls : Calls) (env : Env) (s : State) (d : String)
    (pred : IPred) (n w : Nat) (a b : Operand)
    {va vb : Value} {l1 l2 : List (BitVec w)}
    (ha : evalOperand (stateAt env s) a = some va)
    (hb : evalOperand (stateAt env s) b = some vb)
    (h1 : va.vecLanes n w = some l1) (h2 : vb.vecLanes n w = some l2) :
    evalInstr calls (stateAt env s) (.icmpVec d pred n w a b) =
      some (stateAt ((d, .vec n 1 (icmpLanes pred l1 l2)) :: env) s) := by
  rw [evalInstr_icmpVec (s := stateAt env s) ha hb h1 h2]
  rfl

/-- A lane mask packed into an integer word. -/
theorem step_bitcastMask (calls : Calls) (env : Env) (s : State) (d : String)
    (n : Nat) (v : Operand) {l : List (BitVec 1)}
    (hv : evalOperand (stateAt env s) v = some (.vec n 1 l)) (hlen : l.length = n) :
    evalInstr calls (stateAt env s) (.bitcastMask d n v) =
      some (stateAt ((d, .int n (BitVec.ofNat n (lanesToNat l))) :: env) s) := by
  rw [evalInstr_bitcastMask (s := stateAt env s) hv hlen]
  rfl

/-- A lane-wise binary operation, at the operand values the reads yield. -/
theorem step_binopVec (calls : Calls) (env : Env) (s : State) (d : String)
    (op : BinOp) (n w : Nat) (a b : Operand)
    {va vb : Value} {l1 l2 ls : List (BitVec w)}
    (ha : evalOperand (stateAt env s) a = some va)
    (hb : evalOperand (stateAt env s) b = some vb)
    (h1 : va.vecLanes n w = some l1) (h2 : vb.vecLanes n w = some l2)
    (hm : binopLanes op l1 l2 = some ls) :
    evalInstr calls (stateAt env s) (.binopVec d op n w a b) =
      some (stateAt ((d, .vec n w ls) :: env) s) := by
  simp only [evalInstr, ha, hb, h1, h2, binopLanes] at hm ⊢
  rw [hm]
  rfl

/-- A reinterpretation at equal total width. -/
theorem step_vecBitcast (calls : Calls) (env : Env) (s : State) (d : String)
    (n w m jw : Nat) (v : Operand) {vv : Value} {lanes : List (BitVec w)}
    (hv : evalOperand (stateAt env s) v = some vv)
    (hl : vv.vecLanes n w = some lanes) (hwidth : n * w = m * jw) :
    evalInstr calls (stateAt env s) (.vecBitcast d n w m jw v) =
      some (stateAt ((d, .vec m jw (bitcastVecLanes jw m lanes)) :: env) s) := by
  rw [evalInstr_vecBitcast (s := stateAt env s) hv hl hwidth]
  rfl

/-- A static lane permutation, at the operand values the reads yield. -/
theorem step_shuffleVec (calls : Calls) (env : Env) (s : State) (d : String)
    (n w : Nat) (a b : Operand) (mask : List Nat)
    {va vb : Value} {l1 l2 ls : List (BitVec w)}
    (ha : evalOperand (stateAt env s) a = some va)
    (hb : evalOperand (stateAt env s) b = some vb)
    (h1 : va.vecLanes n w = some l1) (h2 : vb.vecLanes n w = some l2)
    (hm : shuffleLanes n l1 l2 mask = some ls) :
    evalInstr calls (stateAt env s) (.shuffleVec d n w a b mask) =
      some (stateAt ((d, .vec mask.length w ls) :: env) s) := by
  simp only [evalInstr, ha, hb, h1, h2, shuffleLanes] at hm ⊢
  rw [hm]
  rfl

/-- A lane read. -/
theorem step_extractelement (calls : Calls) (env : Env) (s : State) (d : String)
    (n w : Nat) (v idx : Operand) {vv : Value} {lanes : List (BitVec w)}
    {wi : Nat} {k : BitVec wi} {x : BitVec w}
    (hv : evalOperand (stateAt env s) v = some vv)
    (hl : vv.vecLanes n w = some lanes)
    (hi : evalOperand (stateAt env s) idx = some (.int wi k))
    (hx : lanes[k.toNat]? = some x) :
    evalInstr calls (stateAt env s) (.extractelement d n w v idx) =
      some (stateAt ((d, .int w x) :: env) s) := by
  rw [evalInstr_extractelement (s := stateAt env s) hv hl hi hx]
  rfl

/-- A lane write. -/
theorem step_insertelement (calls : Calls) (env : Env) (s : State) (d : String)
    (n w : Nat) (v elt idx : Operand) {vv : Value} {lanes : List (BitVec w)}
    {ev : Value} {x : Nat} {wi : Nat} {k : BitVec wi}
    (hv : evalOperand (stateAt env s) v = some vv)
    (hl : vv.vecLanes n w = some lanes)
    (helt : evalOperand (stateAt env s) elt = some ev)
    (hx : ev.intToNat w = some x)
    (hi : evalOperand (stateAt env s) idx = some (.int wi k))
    (hk : k.toNat < lanes.length) :
    evalInstr calls (stateAt env s) (.insertelement d n w v elt idx) =
      some (stateAt ((d, .vec n w (lanes.set k.toNat (BitVec.ofNat w x))) :: env) s) := by
  rw [evalInstr_insertelement (s := stateAt env s) hv hl helt hx hi hk]
  rfl

/-- A vector load of `n` lanes at lane width `w` (a whole number of bytes). -/
theorem step_loadVec (calls : Calls) (env : Env) (s : State) (d : String)
    (n w : Nat) (p : Operand) {a : Nat} {bs : List UInt8}
    (hw : w ≠ 8) (hb : n * w % 8 = 0)
    (hp : evalOperand (stateAt env s) p = some (.ptr a))
    (hr : readBytes s.mem a (n * w / 8) = some bs) :
    evalInstr calls (stateAt env s) (.load d (.vec n (.int w)) p) =
      some (stateAt ((d, .vec n w (unpackLanes w n (bytesToNat bs))) :: env) s) := by
  rw [evalInstr_load (s := stateAt env s) hp (loadValue_vec_int hw hb hr)]
  rfl

/-- `%d = getelementptr i8, ptr %base, <c>`. -/
theorem step_gep8_imm (calls : Calls) (env : Env) (s : State) (d base : String)
    (c : BitVec 64) {a : Nat}
    (hb : lookupName env base = some (.ptr a))
    (hpos : (c.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (.int 8) (.reg base) (.imm (.int 64 c))) =
      some (stateAt ((d, .ptr (a + (c.signExtend 64).toNat)) :: env) s) := by
  rw [evalInstr_gep_i8 (s := stateAt env s)
    (hb := BlockEval.evalOperand_reg_of env s base (.ptr a) hb)
    (ho := BlockEval.evalOperand_lit_of _ 64 c) (hpos := hpos)]
  simp only [stateAt, State.bind]

/-! ### The intrinsic calls, at their known outcomes -/

/-- `pshuf.b`: the 32-lane table lookup, at the literal table the body spells. -/
theorem step_pshufb (env : Env) (s : State) (r dst : String) (tabInt : List Int)
    (tab ctl : List (BitVec 8)) (htabLen : tabInt.length = 32)
    (htab : tabInt.map (BitVec.ofInt 8) = tab)
    (h : evalOperand (stateAt env s) (.reg r) = some (.vec 32 8 ctl)) :
    evalInstr s1Calls (stateAt env s)
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
    (s1Calls_pshufb (tabInt.map (BitVec.ofInt 8)) ctl s.mem s.next), htab]
  rfl

/-- `pclmulqdq` at immediate zero: lane zero is the carry-less product, lane one
zero. -/
theorem step_pclmul (env : Env) (s : State) (r dst : String) {a0 a1 : BitVec 64}
    (h : evalOperand (stateAt env s) (.reg r) = some (.vec 2 64 [a0, a1])) :
    evalInstr s1Calls (stateAt env s)
        (.call dst (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
          [(.vec 2 (.int 64), .reg r), (.vec 2 (.int 64), lanesOf 64 [-1, 0]),
           (.int 8, lit 8 0)]) =
      some (stateAt ((dst, .vec 2 64 [clmul a0 (BitVec.allOnes 64), 0]) :: env) s) := by
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
    (s1Calls_pclmulqdq a0 a1 (BitVec.ofInt 64 (-1)) (BitVec.ofInt 64 0)
      s.mem s.next)]
  simp only [hneg, stateAt]

/-! ### The call steps -/

/-- A three-argument call: the shuffle tables and the carry-less product. -/
theorem step_call3 (calls : Calls) (env : Env) (s : State) (d : String) (ty : Ty)
    (callee : String) (o1 o2 o3 : Operand) {v1 v2 v3 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (h3 : evalOperand (stateAt env s) o3 = some v3)
    (hc : calls callee [v1, v2, v3] s.mem s.next = some r) :
    evalInstr calls (stateAt env s) (.call d ty callee
        [(Ty.vec 2 (.int 64), o1), (Ty.vec 2 (.int 64), o2), (.int 8, o3)]) =
      some (stateAt ((d, r.ret) :: env) { s with mem := r.mem, next := r.next }) := by
  have ha : evalOperands (stateAt env s)
      [(Ty.vec 2 (.int 64), o1), (Ty.vec 2 (.int 64), o2), (.int 8, o3)]
      = some [v1, v2, v3] := by
    simp [evalOperands, h1, h2, h3]
  rw [evalInstr_call (s := stateAt env s) ha hc]
  rfl

/-- A seven-argument `void` call: the escape list. -/
theorem step_callVoid7 (calls : Calls) (env : Env) (s : State) (callee : String)
    (o1 o2 o3 o4 o5 o6 o7 : Operand) {v1 v2 v3 v4 v5 v6 v7 : Value}
    {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (h3 : evalOperand (stateAt env s) o3 = some v3)
    (h4 : evalOperand (stateAt env s) o4 = some v4)
    (h5 : evalOperand (stateAt env s) o5 = some v5)
    (h6 : evalOperand (stateAt env s) o6 = some v6)
    (h7 : evalOperand (stateAt env s) o7 = some v7)
    (hc : calls callee [v1, v2, v3, v4, v5, v6, v7] s.mem s.next = some r) :
    evalInstr calls (stateAt env s) (.callVoid callee
        [(.int 64, o1), (.int 64, o2), (.int 64, o3), (.int 64, o4),
         (.ptr, o5), (.ptr, o6), (.ptr, o7)]) =
      some (stateAt env { s with mem := r.mem, next := r.next }) := by
  have ha : evalOperands (stateAt env s)
      [(.int 64, o1), (.int 64, o2), (.int 64, o3), (.int 64, o4),
       (.ptr, o5), (.ptr, o6), (.ptr, o7)] = some [v1, v2, v3, v4, v5, v6, v7] := by
    simp [evalOperands, h1, h2, h3, h4, h5, h6, h7]
  simp only [evalInstr]
  rw [ha]
  change (match calls callee [v1, v2, v3, v4, v5, v6, v7] s.mem s.next with
    | some r => some (stateAt env { s with mem := r.mem, next := r.next })
    | none => none) =
      some (stateAt env { s with mem := r.mem, next := r.next })
  rw [hc]

/-! ### The chain forms -/

theorem denoteCode_icmpVec (calls : Calls) (env : Env) (s : State) (d : String)
    (pred : IPred) (n w : Nat) (a b : Operand)
    {va vb : Value} {l1 l2 : List (BitVec w)}
    (ha : evalOperand (stateAt env s) a = some va)
    (hb : evalOperand (stateAt env s) b = some vb)
    (h1 : va.vecLanes n w = some l1) (h2 : vb.vecLanes n w = some l2) (is : List Instr) :
    denoteCode calls (.icmpVec d pred n w a b :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .vec n 1 (icmpLanes pred l1 l2)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_icmpVec calls env s d pred n w a b ha hb h1 h2)]

theorem denoteCode_bitcastMask (calls : Calls) (env : Env) (s : State) (d : String)
    (n : Nat) (v : Operand) {l : List (BitVec 1)}
    (hv : evalOperand (stateAt env s) v = some (.vec n 1 l)) (hlen : l.length = n)
    (is : List Instr) :
    denoteCode calls (.bitcastMask d n v :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int n (BitVec.ofNat n (lanesToNat l))) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_bitcastMask calls env s d n v hv hlen)]

theorem denoteCode_binopVec (calls : Calls) (env : Env) (s : State) (d : String)
    (op : BinOp) (n w : Nat) (a b : Operand)
    {va vb : Value} {l1 l2 ls : List (BitVec w)}
    (ha : evalOperand (stateAt env s) a = some va)
    (hb : evalOperand (stateAt env s) b = some vb)
    (h1 : va.vecLanes n w = some l1) (h2 : vb.vecLanes n w = some l2)
    (hm : binopLanes op l1 l2 = some ls) (is : List Instr) :
    denoteCode calls (.binopVec d op n w a b :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .vec n w ls) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_binopVec calls env s d op n w a b ha hb h1 h2 hm)]

theorem denoteCode_vecBitcast (calls : Calls) (env : Env) (s : State) (d : String)
    (n w m jw : Nat) (v : Operand) {vv : Value} {lanes : List (BitVec w)}
    (hv : evalOperand (stateAt env s) v = some vv)
    (hl : vv.vecLanes n w = some lanes) (hwidth : n * w = m * jw) (is : List Instr) :
    denoteCode calls (.vecBitcast d n w m jw v :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .vec m jw (bitcastVecLanes jw m lanes)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_vecBitcast calls env s d n w m jw v hv hl hwidth)]

theorem denoteCode_shuffleVec (calls : Calls) (env : Env) (s : State) (d : String)
    (n w : Nat) (a b : Operand) (mask : List Nat)
    {va vb : Value} {l1 l2 ls : List (BitVec w)}
    (ha : evalOperand (stateAt env s) a = some va)
    (hb : evalOperand (stateAt env s) b = some vb)
    (h1 : va.vecLanes n w = some l1) (h2 : vb.vecLanes n w = some l2)
    (hm : shuffleLanes n l1 l2 mask = some ls) (is : List Instr) :
    denoteCode calls (.shuffleVec d n w a b mask :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .vec mask.length w ls) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (step_shuffleVec calls env s d n w a b mask ha hb h1 h2 hm)]

theorem denoteCode_extractelement (calls : Calls) (env : Env) (s : State) (d : String)
    (n w : Nat) (v idx : Operand) {vv : Value} {lanes : List (BitVec w)}
    {wi : Nat} {k : BitVec wi} {x : BitVec w}
    (hv : evalOperand (stateAt env s) v = some vv)
    (hl : vv.vecLanes n w = some lanes)
    (hi : evalOperand (stateAt env s) idx = some (.int wi k))
    (hx : lanes[k.toNat]? = some x) (is : List Instr) :
    denoteCode calls (.extractelement d n w v idx :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w x) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (step_extractelement calls env s d n w v idx hv hl hi hx)]

theorem denoteCode_insertelement (calls : Calls) (env : Env) (s : State) (d : String)
    (n w : Nat) (v elt idx : Operand) {vv : Value} {lanes : List (BitVec w)}
    {ev : Value} {x : Nat} {wi : Nat} {k : BitVec wi}
    (hv : evalOperand (stateAt env s) v = some vv)
    (hl : vv.vecLanes n w = some lanes)
    (helt : evalOperand (stateAt env s) elt = some ev)
    (hx : ev.intToNat w = some x)
    (hi : evalOperand (stateAt env s) idx = some (.int wi k))
    (hk : k.toNat < lanes.length) (is : List Instr) :
    denoteCode calls (.insertelement d n w v elt idx :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .vec n w (lanes.set k.toNat (BitVec.ofNat w x)))
        :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (step_insertelement calls env s d n w v elt idx hv hl helt hx hi hk)]

theorem denoteCode_loadVec (calls : Calls) (env : Env) (s : State) (d : String)
    (n w : Nat) (p : Operand) {a : Nat} {bs : List UInt8}
    (hw : w ≠ 8) (hb : n * w % 8 = 0)
    (hp : evalOperand (stateAt env s) p = some (.ptr a))
    (hr : readBytes s.mem a (n * w / 8) = some bs) (is : List Instr) :
    denoteCode calls (.load d (.vec n (.int w)) p :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .vec n w (unpackLanes w n (bytesToNat bs)))
        :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_loadVec calls env s d n w p hw hb hp hr)]

theorem denoteCode_gep8_imm (calls : Calls) (env : Env) (s : State) (d base : String)
    (c : BitVec 64) {a : Nat}
    (hb : lookupName env base = some (.ptr a))
    (hpos : (c.signExtend 64).toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 8) (.reg base) (.imm (.int 64 c)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a + (c.signExtend 64).toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_gep8_imm calls env s d base c hb hpos)]

theorem denoteCode_pshufb (env : Env) (s : State) (r dst : String) (tabInt : List Int)
    (tab ctl : List (BitVec 8)) (htabLen : tabInt.length = 32)
    (htab : tabInt.map (BitVec.ofInt 8) = tab)
    (h : evalOperand (stateAt env s) (.reg r) = some (.vec 32 8 ctl))
    (is : List Instr) :
    denoteCode s1Calls
        (.call dst v32i8 "llvm.x86.avx2.pshuf.b"
          [(v32i8, lanesOf 8 tabInt), (v32i8, .reg r)] :: is) (stateAt env s) =
      denoteCode s1Calls is (stateAt ((dst, .vec 32 8 (pshufbLanes tab ctl)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_pshufb env s r dst tabInt tab ctl htabLen htab h)]

theorem denoteCode_pclmul (env : Env) (s : State) (r dst : String) {a0 a1 : BitVec 64}
    (h : evalOperand (stateAt env s) (.reg r) = some (.vec 2 64 [a0, a1]))
    (is : List Instr) :
    denoteCode s1Calls
        (.call dst (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
          [(.vec 2 (.int 64), .reg r), (.vec 2 (.int 64), lanesOf 64 [-1, 0]),
           (.int 8, lit 8 0)] :: is) (stateAt env s) =
      denoteCode s1Calls is
        (stateAt ((dst, .vec 2 64 [clmul a0 (BitVec.allOnes 64), 0]) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_pclmul env s r dst h)]

theorem denoteCode_call3 (calls : Calls) (env : Env) (s : State) (d : String) (ty : Ty)
    (callee : String) (o1 o2 o3 : Operand) {v1 v2 v3 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (h3 : evalOperand (stateAt env s) o3 = some v3)
    (hc : calls callee [v1, v2, v3] s.mem s.next = some r) (is : List Instr) :
    denoteCode calls (.call d ty callee
        [(Ty.vec 2 (.int 64), o1), (Ty.vec 2 (.int 64), o2), (.int 8, o3)] :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, r.ret) :: env)
        { s with mem := r.mem, next := r.next }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_call3 calls env s d ty callee o1 o2 o3
    h1 h2 h3 hc)]

theorem denoteCode_callVoid7 (calls : Calls) (env : Env) (s : State) (callee : String)
    (o1 o2 o3 o4 o5 o6 o7 : Operand) {v1 v2 v3 v4 v5 v6 v7 : Value}
    {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (h3 : evalOperand (stateAt env s) o3 = some v3)
    (h4 : evalOperand (stateAt env s) o4 = some v4)
    (h5 : evalOperand (stateAt env s) o5 = some v5)
    (h6 : evalOperand (stateAt env s) o6 = some v6)
    (h7 : evalOperand (stateAt env s) o7 = some v7)
    (hc : calls callee [v1, v2, v3, v4, v5, v6, v7] s.mem s.next = some r)
    (is : List Instr) :
    denoteCode calls (.callVoid callee
        [(.int 64, o1), (.int 64, o2), (.int 64, o3), (.int 64, o4),
         (.ptr, o5), (.ptr, o6), (.ptr, o7)] :: is) (stateAt env s) =
      denoteCode calls is (stateAt env { s with mem := r.mem, next := r.next }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_callVoid7 calls env s callee o1 o2 o3 o4 o5 o6 o7
    h1 h2 h3 h4 h5 h6 h7 hc)]

/-! ### The whole-block tactic -/

macro "block_step_v" : tactic => `(tactic|
  (first
   | block_step
   | rw [denoteCode_icmpVec _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ _]
   | rw [denoteCode_bitcastMask _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_binopVec _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ _]
   | rw [denoteCode_vecBitcast _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_shuffleVec _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ _]
   | rw [denoteCode_extractelement _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ _]
   | rw [denoteCode_insertelement _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ _]
   | rw [denoteCode_pshufb_raw _ _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_pclmul_raw _ _ _ _ ?_ _]
   | rw [denoteCode_loadVec _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ _]
   | rw [denoteCode_gep8_imm _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_call3 _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ _]
   | rw [denoteCode_callVoid7 _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _]))

/-- The close phases: the integer close, then the vector reads' shape facts and
the constant operands. -/
macro "block_close_v" : tactic => `(tactic|
  (block_close
   all_goals (try (first
     | assumption
     | exact evalOperand_reg_of _ _ _ _ (by assumption)
     | block_lk
     | (simp only [Value.vecLanes]; split <;> (first | rfl | contradiction))
     | (simp only [evalOperand, Const.toValue, lanesOf, splatOf]; rfl)
     | exact evalOperand_lit_of _ _ _))
   all_goals (try rfl)
   all_goals (try decide)))

macro "block_eval_v" : tactic => `(tactic|
  (repeat block_step_v
   block_close_v))

end LeanLLVM.Refinement.BlockEvalVector

namespace LeanLLVM.Refinement.BlockEvalVector

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.Pclmul (clmul)

/-! ### Raw-spelling forms of the two literal-bearing calls

`block_eval_v` unfolds the fixture's operand helpers (`lit`, `lanesOf`) before it
steps, so the goal's call operands are constructor terms while the chain lemmas
above spell them through those helpers.  These two are the same lemmas at the
constructor spelling the tactic actually meets.
-/

theorem denoteCode_pshufb_raw (env : Env) (s : State) (r dst : String) (tabInt : List Int)
    (tab ctl : List (BitVec 8)) (htabLen : tabInt.length = 32)
    (htab : tabInt.map (BitVec.ofInt 8) = tab)
    (h : evalOperand (stateAt env s) (.reg r) = some (.vec 32 8 ctl))
    (is : List Instr) :
    denoteCode s1Calls
        (.call dst (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b"
          [(.vec 32 (.int 8), .imm (.vector 8 (tabInt.map (BitVec.ofInt 8)))),
           (.vec 32 (.int 8), .reg r)] :: is)
        (stateAt env s) =
      denoteCode s1Calls is (stateAt ((dst, .vec 32 8 (pshufbLanes tab ctl)) :: env) s) := by
  simpa [v32i8, lanesOf] using
    denoteCode_pshufb env s r dst tabInt tab ctl htabLen htab h is

theorem denoteCode_pclmul_raw (env : Env) (s : State) (r dst : String) {a0 a1 : BitVec 64}
    (h : evalOperand (stateAt env s) (.reg r) = some (.vec 2 64 [a0, a1]))
    (is : List Instr) :
    denoteCode s1Calls
        (.call dst (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
          [(.vec 2 (.int 64), .reg r),
           (.vec 2 (.int 64), .imm (.vector 64 [BitVec.ofInt 64 (-1), BitVec.ofInt 64 0])),
           (.int 8, .imm (.int 8 0))] :: is) (stateAt env s) =
      denoteCode s1Calls is
        (stateAt ((dst, .vec 2 64 [clmul a0 (BitVec.allOnes 64), 0]) :: env) s) := by
  simpa [lanesOf, lit] using denoteCode_pclmul env s r dst h is

end LeanLLVM.Refinement.BlockEvalVector
