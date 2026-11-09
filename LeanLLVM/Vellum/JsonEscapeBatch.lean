/-
The escape list's out-of-line batch, `@xl_batch`, at its own record.

The list entry point hands its remaining set bits to this one-block body eight at
a time, so the list's boundary record is only meaningful where the batch's is:
this module states the batch's record (`Γ_xl_batch`) and proves it of the pinned
body (`xl_batch_satisfies`), and `JsonEscapeSteps` imports it so the list's
theorem can resolve the call at `envForUnit`.

The run is one control step — the body is one straight-line block — and the claim
is the eight four-byte entries it writes at `%o` together with the count
`min (ctpop esc) 8` it returns.  The trace below reads the fifty-seven
instruction lines in order; each step's operands are resolved from the
environment the previous step bound, and the last step's `%cond` is the cell the
returned count is read from.
-/
import LeanLLVM.Vellum.JsonEscapeIR
import LeanLLVM.Vellum.JsonS1MasksIR
import LeanLLVM.Memory

open LeanLLVM
open LeanLLVM.Vellum
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.JsonS1MasksIR (evalInstr_binop evalInstr_store evalInstr_call
  evalOperands_cons)
open LeanLLVM.Vellum.BitLanes (cttz ctpop umin)

namespace LeanLLVM.Vellum

def withEnv (env : Env) (s : State) : State := { s with env := env }

def batchInstrs : List Instr :=
  match xlBatchFunction.blocks with
  | b :: _ => b.instrs
  | [] => []

theorem denoteCode_cons_of (calls : Calls) (i : Instr) (is : List Instr) (s s' : State)
    (h : evalInstr calls s i = some s') :
    denoteCode calls (i :: is) s = denoteCode calls is s' := by
  simp [denoteCode, h]

theorem evalOperand_reg_of (env : Env) (s : State) (n : String) (v : Value)
    (h : lookupName env n = some v) : evalOperand (withEnv env s) (.reg n) = some v := by
  simp only [withEnv, evalOperand, h]

theorem evalOperand_lit_of (s : State) (w : Nat) (c : BitVec w) :
    evalOperand s (.imm (.int w c)) = some (.int w c) := rfl

/-- A register in the run's environment. -/
macro "b_lk " h:term : tactic =>
  `(tactic| ((repeat rw [lookupName_cons_ne _ _ (by decide)]); (first
      | exact lookupName_cons_self _ _ _
      | exact $h)))

/-- `%d = or i64 %src, <c>`. -/
theorem b_or_imm64 (env : Env) (s : State) (d src : String) (x c : BitVec 64)
    (h : lookupName env src = some (.int 64 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.binop d .or 64 (.reg src) (.imm (.int 64 c))) =
      some (withEnv ((d, .int 64 (x ||| c)) :: env) s) := by
  rw [evalInstr_binop (r := (x ||| c).toNat)
    (ha := evalOperand_reg_of env s src (.int 64 x) h)
    (hb := evalOperand_lit_of _ 64 c)
    (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, withEnv, State.bind]

/-- `%d = call i64 @llvm.cttz.i64(i64 %src, i1 true)`. -/
theorem b_call_cttz (env : Env) (s : State) (d src : String) (x : BitVec 64)
    (h : lookupName env src = some (.int 64 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.call d (.int 64) "llvm.cttz.i64"
          [((.int 64), (.reg src)), ((.int 1), (.imm (.int 1 (BitVec.ofInt 1 (-1)))))]) =
      some (withEnv ((d, .int 64 (BitVec.ofNat 64 (cttz x))) :: env) s) := by
  rw [evalInstr_call
    (ha := evalOperands_cons (evalOperand_reg_of env s src (.int 64 x) h)
      (evalOperands_cons (evalOperand_lit_of _ 1 (BitVec.ofInt 1 (-1))) (by rfl)))
    (hc := escapeCalls_cttz x (BitVec.ofInt 1 (-1)) s.mem s.next)]
  simp only [withEnv, State.bind]

/-- `%d = trunc i64 %src to i32`. -/
theorem b_trunc (env : Env) (s : State) (d src : String) (x : BitVec 64)
    (h : lookupName env src = some (.int 64 x)) :
    evalInstr escapeCalls (withEnv env s) (.trunc d 64 32 (.reg src)) =
      some (withEnv ((d, .int 32 (BitVec.ofNat 32 (x.toNat % 2 ^ 32))) :: env) s) := by
  unfold evalInstr
  simp only [evalOperand, withEnv, h]
  simp only [State.bind]
  rfl

/-- `%d = add i32 %a, %b`. -/
theorem b_add32 (env : Env) (s : State) (d a b : String) (x y : BitVec 32)
    (ha : lookupName env a = some (.int 32 x)) (hb : lookupName env b = some (.int 32 y)) :
    evalInstr escapeCalls (withEnv env s)
        (.binop d .add 32 (.reg a) (.reg b)) =
      some (withEnv ((d, .int 32 (BitVec.ofNat 32 ((x.toNat + y.toNat) % 2 ^ 32))) :: env) s) := by
  rw [evalInstr_binop (r := (x.toNat + y.toNat) % 2 ^ 32)
    (ha := evalOperand_reg_of env s a (.int 32 x) ha)
    (hb := evalOperand_reg_of env s b (.int 32 y) hb)
    (hr := by
      simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat, BitVec.toNat_add])]
  simp only [withEnv, State.bind]

/-- `store i32 %v, ptr %p`. -/
theorem b_store32 (env : Env) (s : State) (r p : String) (x : BitVec 32) (a : Nat)
    (hv : lookupName env r = some (.int 32 x))
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr escapeCalls (withEnv env s) (.store (.int 32) (.reg r) (.reg p)) =
      some (withEnv env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
  rw [evalInstr_store (vv := .int 32 x) (a := a)
    (s' := withEnv env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) })
    (hv := evalOperand_reg_of env s r (.int 32 x) hv)
    (hp := evalOperand_reg_of env s p (.ptr a) hp)
    (hs := by simp [storeValue, withEnv])]

theorem cttz64_le (x : BitVec 64) : cttz x ≤ 64 := by
  unfold cttz
  cases h : (List.range 64).find? (fun k => x.getLsbD k) with
  | none => simp [h]
  | some k =>
      have hk : k ∈ List.range 64 := List.mem_of_find?_eq_some h
      simp only [h, Option.getD_some]
      exact Nat.le_of_lt (List.mem_range.mp hk)


/-- `%d = add i64 %src, <c>`. -/
theorem b_add64_imm (env : Env) (s : State) (d src : String) (x c : BitVec 64)
    (h : lookupName env src = some (.int 64 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.binop d .add 64 (.reg src) (.imm (.int 64 c))) =
      some (withEnv ((d, .int 64 (x + c)) :: env) s) := by
  rw [evalInstr_binop (r := (x + c).toNat)
    (ha := evalOperand_reg_of env s src (.int 64 x) h)
    (hb := evalOperand_lit_of _ 64 c)
    (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, withEnv, State.bind]

/-- `%d = and i64 %a, %b`. -/
theorem b_and64 (env : Env) (s : State) (d a b : String) (x y : BitVec 64)
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr escapeCalls (withEnv env s)
        (.binop d .and 64 (.reg a) (.reg b)) =
      some (withEnv ((d, .int 64 (x &&& y)) :: env) s) := by
  rw [evalInstr_binop (r := (x &&& y).toNat)
    (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_reg_of env s b (.int 64 y) hb)
    (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, withEnv, State.bind]

/-- `%d = call i64 @llvm.ctpop.i64(i64 %src)`. -/
theorem b_call_ctpop (env : Env) (s : State) (d src : String) (x : BitVec 64)
    (h : lookupName env src = some (.int 64 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.call d (.int 64) "llvm.ctpop.i64" [((.int 64), (.reg src))]) =
      some (withEnv ((d, .int 64 (BitVec.ofNat 64 (ctpop x))) :: env) s) := by
  rw [evalInstr_call
    (ha := evalOperands_cons (evalOperand_reg_of env s src (.int 64 x) h) (by rfl))
    (hc := escapeCalls_ctpop64 x s.mem s.next)]
  simp only [withEnv, State.bind]

/-- `%d = call i32 @llvm.umin.i32(i32 %src, i32 <c>)`. -/
theorem b_call_umin (env : Env) (s : State) (d src : String) (x c : BitVec 32)
    (h : lookupName env src = some (.int 32 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.call d (.int 32) "llvm.umin.i32"
          [((.int 32), (.reg src)), ((.int 32), (.imm (.int 32 c)))]) =
      some (withEnv ((d, .int 32 (umin x c)) :: env) s) := by
  rw [evalInstr_call
    (ha := evalOperands_cons (evalOperand_reg_of env s src (.int 32 x) h)
      (evalOperands_cons (evalOperand_lit_of _ 32 c) (by rfl)))
    (hc := escapeCalls_umin32 x c s.mem s.next)]
  simp only [withEnv, State.bind]

/-- `%d = getelementptr i8, ptr %base, i64 <c>`, the byte offset as a literal. -/
theorem b_gep8_imm (env : Env) (s : State) (d base : String) (a k : Nat) (c : BitVec 64)
    (hb : lookupName env base = some (.ptr a))
    (hc : (c.signExtend 64).toNat = k)
    (hpos : (c.signExtend 64).toNat < 2 ^ 63) :
    evalInstr escapeCalls (withEnv env s)
        (.gep d (.int 8) (.reg base) (.imm (.int 64 c))) =
      some (withEnv ((d, .ptr (a + k)) :: env) s) := by
  rw [evalInstr_gep_i8 (hb := evalOperand_reg_of env s base (.ptr a) hb)
    (ho := evalOperand_lit_of _ 64 c) (hpos := hpos)]
  simp only [withEnv, State.bind, hc]

/-- The clearing chain, as the body spells it: the word `esc | 2 ^ 63` with the
lowest set bit cleared once per step. -/
def batchChain (esc : BitVec 64) : Nat → BitVec 64
  | 0 => esc ||| (BitVec.ofInt 64 (-9223372036854775808))
  | i + 1 => (batchChain esc i + BitVec.ofInt 64 (-1)) &&& batchChain esc i

/-- The truncated trailing count the body binds at step `i`. -/
def batchCast (esc : BitVec 64) (i : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((BitVec.ofNat 64 (cttz (batchChain esc i))).toNat % 2 ^ 32)

/-- The four bytes the body stores at step `i`, in the form the store writes them:
the sum's low 32 bits, taken through the store's own `toNat`. -/
def batchBytes (base : BitVec 32) (esc : BitVec 64) (i : Nat) : List UInt8 :=
  natToBytes (BitVec.ofNat 32 ((base.toNat + (batchCast esc i).toNat) % 2 ^ 32)).toNat 4

/-- The eight four-byte entries the batch writes, in the order it writes them. -/
def batchMem (base : BitVec 32) (esc : BitVec 64) (o : Nat) (mem : Mem) : Mem :=
  writeBytes
   (writeBytes
    (writeBytes
     (writeBytes
      (writeBytes
       (writeBytes
        (writeBytes
         (writeBytes mem o (batchBytes base esc 0)) (o + 4) (batchBytes base esc 1))
         (o + 8) (batchBytes base esc 2))
        (o + 12) (batchBytes base esc 3))
       (o + 16) (batchBytes base esc 4))
      (o + 20) (batchBytes base esc 5))
     (o + 24) (batchBytes base esc 6))
    (o + 28) (batchBytes base esc 7)

/-- The block's run, as the two facts a caller reads: the memory is the eight
entries, and the returned count is the `%cond` cell on top of the environment. -/
theorem batch_run (env : Env) (s : State) (esc : BitVec 64) (base : BitVec 32) (o : Nat)
    (he : lookupName env "%esc" = some (.int 64 esc))
    (hb : lookupName env "%base" = some (.int 32 base))
    (ho : lookupName env "%o" = some (.ptr o)) :
    Option.map State.mem (denoteCode escapeCalls batchInstrs (withEnv env s)) =
        some (batchMem base esc o s.mem) ∧
      (denoteCode escapeCalls batchInstrs (withEnv env s)).bind
          (fun st => lookupName st.env "%cond") = some (.int 32
        (umin (BitVec.ofNat 32 ((BitVec.ofNat 64 (ctpop esc)).toNat % 2 ^ 32))
          (BitVec.ofInt 32 8))) := by
  unfold batchInstrs xlBatchFunction
  simp only [List.take]
  rw [denoteCode_cons_of _ _ _ _ _ (b_or_imm64 env s "%or" "%esc" esc
    (BitVec.ofInt 64 (-9223372036854775808)) (by b_lk he))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_cttz _ _ "%0" "%or" _ (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast" "%0" _ (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add32 _ _ "%add" "%base" "%cast" _ _
    (by b_lk hb) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store32 _ _ "%add" "%o" _ o
    (by b_lk lookupName_cons_self) (by b_lk ho))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ _ "%sub" "%or" _ (BitVec.ofInt 64 (-1)) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ _ "%and" "%sub" "%or" _ _ (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_cttz _ _ "%1" "%and" _ (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast1" "%1" _ (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add32 _ _ "%add2" "%base" "%cast1" _ _ (by b_lk hb) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%arrayidx3" "%o" _ 4 (BitVec.ofInt 64 4) (by b_lk ho) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store32 _ _ "%add2" "%arrayidx3" _ _ (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ _ "%sub4" "%and" _ (BitVec.ofInt 64 (-1)) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ _ "%and5" "%sub4" "%and" _ _ (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_cttz _ _ "%2" "%and5" _ (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast6" "%2" _ (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add32 _ _ "%add7" "%base" "%cast6" _ _ (by b_lk hb) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%arrayidx8" "%o" _ 8 (BitVec.ofInt 64 8) (by b_lk ho) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store32 _ _ "%add7" "%arrayidx8" _ _ (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ _ "%sub9" "%and5" _ (BitVec.ofInt 64 (-1)) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ _ "%and10" "%sub9" "%and5" _ _ (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_cttz _ _ "%3" "%and10" _ (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast11" "%3" _ (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add32 _ _ "%add12" "%base" "%cast11" _ _ (by b_lk hb) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%arrayidx13" "%o" _ 12 (BitVec.ofInt 64 12) (by b_lk ho) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store32 _ _ "%add12" "%arrayidx13" _ _ (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ _ "%sub14" "%and10" _ (BitVec.ofInt 64 (-1)) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ _ "%and15" "%sub14" "%and10" _ _ (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_cttz _ _ "%4" "%and15" _ (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast16" "%4" _ (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add32 _ _ "%add17" "%base" "%cast16" _ _ (by b_lk hb) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%arrayidx18" "%o" _ 16 (BitVec.ofInt 64 16) (by b_lk ho) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store32 _ _ "%add17" "%arrayidx18" _ _ (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ _ "%sub19" "%and15" _ (BitVec.ofInt 64 (-1)) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ _ "%and20" "%sub19" "%and15" _ _ (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_cttz _ _ "%5" "%and20" _ (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast21" "%5" _ (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add32 _ _ "%add22" "%base" "%cast21" _ _ (by b_lk hb) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%arrayidx23" "%o" _ 20 (BitVec.ofInt 64 20) (by b_lk ho) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store32 _ _ "%add22" "%arrayidx23" _ _ (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ _ "%sub24" "%and20" _ (BitVec.ofInt 64 (-1)) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ _ "%and25" "%sub24" "%and20" _ _ (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_cttz _ _ "%6" "%and25" _ (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast26" "%6" _ (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add32 _ _ "%add27" "%base" "%cast26" _ _ (by b_lk hb) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%arrayidx28" "%o" _ 24 (BitVec.ofInt 64 24) (by b_lk ho) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store32 _ _ "%add27" "%arrayidx28" _ _ (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add64_imm _ _ "%sub29" "%and25" _ (BitVec.ofInt 64 (-1)) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ _ "%and30" "%sub29" "%and25" _ _ (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_cttz _ _ "%7" "%and30" _ (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast31" "%7" _ (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_add32 _ _ "%add32" "%base" "%cast31" _ _ (by b_lk hb) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ _ "%arrayidx33" "%o" _ 28 (BitVec.ofInt 64 28) (by b_lk ho) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_store32 _ _ "%add32" "%arrayidx33" _ _ (by b_lk lookupName_cons_self) (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_ctpop _ _ "%8" "%esc" _ (by b_lk he))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_trunc _ _ "%cast36" "%8" _ (by b_lk lookupName_cons_self))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_call_umin _ _ "%cond" "%cast36" _ (BitVec.ofInt 32 8) (by b_lk lookupName_cons_self))]
  constructor
  · simp only [denoteCode, Option.map_some, withEnv, batchMem, batchBytes, batchCast, batchChain]
  · simp [denoteCode, withEnv]

/-- The count the batch returns, in the form the record states it: the truncated
population count against eight. -/
theorem batchCount_eq (esc : BitVec 64) :
    umin (BitVec.ofNat 32 ((BitVec.ofNat 64 (ctpop esc)).toNat % 2 ^ 32)) (BitVec.ofInt 32 8) =
      umin (BitVec.ofNat 32 (ctpop esc)) (BitVec.ofNat 32 8) := by
  have h1 : BitVec.ofNat 32 ((BitVec.ofNat 64 (ctpop esc)).toNat % 2 ^ 32) =
      BitVec.ofNat 32 (ctpop esc) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat, Nat.mod_mod]
  have h2 : (BitVec.ofInt 32 8 : BitVec 32) = BitVec.ofNat 32 8 := by decide
  rw [h1, h2]

/-- The batch's record: the eight entries it writes and the count it returns. -/
def Γ_xl_batch : MemContract where
  budget := fun _ _ => 1
  pre := fun args _ _ =>
    ∃ (esc : BitVec 64) (base : BitVec 32) (o : Nat),
      args = [.int 64 esc, .int 32 base, .ptr o]
  post := fun args mem _ out =>
    match out with
    | .ret (some (.int 32 c)) m =>
        ∃ (esc : BitVec 64) (base : BitVec 32) (o : Nat),
          args = [.int 64 esc, .int 32 base, .ptr o] ∧
          c = umin (BitVec.ofNat 32 (ctpop esc)) (BitVec.ofNat 32 8) ∧
          m = batchMem base esc o mem
    | _ => False

/-- **The batch satisfies its record.**  One step: the block's fifty-seven
instructions leave the eight entries, and the returned count is the `%cond` cell. -/
theorem xl_batch_satisfies : Satisfies escapeCalls xlBatchFunction Γ_xl_batch := by
  intro args mem next hpre
  obtain ⟨esc, base, o, hargs⟩ := hpre
  subst hargs
  let S : State := EntryState xlBatchFunction [.int 64 esc, .int 32 base, .ptr o] mem next
  have he : lookupName S.env "%esc" = some (.int 64 esc) := by
    simp [S, EntryState, xlBatchFunction]
  have hb : lookupName S.env "%base" = some (.int 32 base) := by
    simp [S, EntryState, xlBatchFunction]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have ho : lookupName S.env "%o" = some (.ptr o) := by
    simp [S, EntryState, xlBatchFunction]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_self]
  obtain ⟨hmemproj, hcondproj⟩ := batch_run S.env S esc base o he hb ho
  have hcode : denoteCode escapeCalls batchInstrs (withEnv S.env S) =
      denoteCode escapeCalls batchInstrs S := rfl
  rw [hcode] at hmemproj hcondproj
  have hSmem : S.mem = mem := rfl
  rw [hSmem] at hmemproj
  let M : Mem := batchMem base esc o mem
  have hmem : Option.map State.mem (denoteCode escapeCalls batchInstrs S) = some M := hmemproj
  have hcond : (denoteCode escapeCalls batchInstrs S).bind
      (fun st => lookupName st.env "%cond") = some (.int 32
        (umin (BitVec.ofNat 32 ((BitVec.ofNat 64 (ctpop esc)).toNat % 2 ^ 32))
          (BitVec.ofInt 32 8))) := hcondproj
  have hstepMatch : step escapeCalls xlBatchFunction S =
      (match denoteCode escapeCalls batchInstrs S with
       | none => (Ctrl.ub : Ctrl)
       | some st => execTerm st (.ret (.int 32) (some (.reg "%cond")))) := by
    have hpc : S.pc = "entry" := rfl
    unfold step
    rw [hpc]
    rfl
  have hstep : ∃ st' : State, step escapeCalls xlBatchFunction S =
      .ret (some (.int 32 (umin (BitVec.ofNat 32 (ctpop esc)) (BitVec.ofNat 32 8)))) st' ∧
      st'.mem = M := by
    rw [hstepMatch]
    cases hd : denoteCode escapeCalls batchInstrs S with
    | none => rw [hd] at hmem; simp at hmem
    | some st =>
        rw [hd] at hmem hcond
        simp only [Option.map_some, Option.some.injEq] at hmem
        simp only [Option.bind_some] at hcond
        refine ⟨st, ?_, hmem⟩
        simp only [execTerm, evalOperand, hcond]
        rw [batchCount_eq]
  obtain ⟨st', hstep', hst'mem⟩ := hstep
  have hrun : runFuel escapeCalls 1 xlBatchFunction S = some
      (.ret (some (.int 32 (umin (BitVec.ofNat 32 (ctpop esc)) (BitVec.ofNat 32 8)))) M) := by
    simp only [runFuel, hstep']
    rw [hst'mem]
  refine ⟨⟨some (.int 32 (umin (BitVec.ofNat 32 (ctpop esc)) (BitVec.ofNat 32 8))), ⟨M, ?_⟩⟩, ?_⟩
  · simpa only [Γ_xl_batch] using hrun
  · intro out hout
    rcases hout with ⟨n, hnub⟩ | ⟨n, hn⟩
    · have h := runFuel_outcome_unique (n := 1) (m := n) hrun hnub
      simp at h
    · have h := runFuel_outcome_unique (n := 1) (m := n) hrun hn
      rw [← h]
      exact ⟨esc, ⟨base, ⟨o, rfl, rfl, rfl⟩⟩⟩

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.withEnv' does not depend on any axioms -/
#guard_msgs in
#print axioms withEnv

/-- info: 'LeanLLVM.Vellum.denoteCode_cons_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms denoteCode_cons_of

/-- info: 'LeanLLVM.Vellum.evalOperand_reg_of' depends on axioms: [propext] -/
#guard_msgs in
#print axioms evalOperand_reg_of

/-- info: 'LeanLLVM.Vellum.evalOperand_lit_of' does not depend on any axioms -/
#guard_msgs in
#print axioms evalOperand_lit_of

/-- info: 'LeanLLVM.Vellum.b_or_imm64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_or_imm64

/-- info: 'LeanLLVM.Vellum.b_call_cttz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_call_cttz

/-- info: 'LeanLLVM.Vellum.b_trunc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_trunc

/-- info: 'LeanLLVM.Vellum.b_add32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_add32

/-- info: 'LeanLLVM.Vellum.b_store32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_store32

/-- info: 'LeanLLVM.Vellum.b_add64_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_add64_imm

/-- info: 'LeanLLVM.Vellum.b_and64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_and64

/-- info: 'LeanLLVM.Vellum.b_call_ctpop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_call_ctpop

/-- info: 'LeanLLVM.Vellum.b_call_umin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_call_umin

/-- info: 'LeanLLVM.Vellum.b_gep8_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms b_gep8_imm

/-- info: 'LeanLLVM.Vellum.cttz64_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cttz64_le

/-- info: 'LeanLLVM.Vellum.batchChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms batchChain

/-- info: 'LeanLLVM.Vellum.batchCast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms batchCast

/-- info: 'LeanLLVM.Vellum.batchBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms batchBytes

/-- info: 'LeanLLVM.Vellum.batchMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms batchMem

/-- info: 'LeanLLVM.Vellum.batch_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms batch_run

/-- info: 'LeanLLVM.Vellum.batchCount_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms batchCount_eq

/-- info: 'LeanLLVM.Vellum.Γ_xl_batch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Γ_xl_batch

/-- info: 'LeanLLVM.Vellum.xl_batch_satisfies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms xl_batch_satisfies

end LeanLLVM.Vellum
