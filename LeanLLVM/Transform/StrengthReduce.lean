/-
Certified strength reduction: `mul x, 2` becomes `shl x, 1`.

The pass is local — it rewrites one instruction in place and needs no
substitution or environment invariant.  The proof obligation is a single
`BitVec` identity, `x * 2 = x <<< 1`, lifted over the instruction list and then
over `runFuel`.
-/
import LeanLLVM.Transform.Basic

namespace LeanLLVM

/-- `x * 2 = x <<< 1` at every width.  The shift amount is the `Nat` obtained
from the literal `1`, so the identity is stated with exactly the amount the
semantics will use. -/
theorem mul_two_eq_shift (w : Nat) (x : BitVec w) :
    x * (2 : BitVec w) = BitVec.shiftLeft x (BitVec.ofNat w 1).toNat := by
  cases w with
  | zero =>
      apply BitVec.toNat_inj.mp
      simp
  | succ w =>
      have h1 : (BitVec.ofNat (w + 1) 1).toNat = 1 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        exact Nat.one_lt_two_pow (Nat.succ_ne_zero w)
      rw [h1]
      apply BitVec.toNat_inj.mp
      simp [BitVec.toNat_mul, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- The same identity at the `Nat` level used by `evalBinopNat`, where the
operands are read back as `BitVec` values. -/
theorem evalBinopNat_mul_two (w x : Nat) :
    evalBinopNat .mul w x ((2 : BitVec w).toNat) =
      evalBinopNat .shl w x ((1 : BitVec w).toNat) := by
  simp only [evalBinopNat, evalBinop, Option.map_some]
  have h2 : BitVec.ofNat w ((2 : BitVec w).toNat) = (2 : BitVec w) := by
    apply BitVec.toNat_inj.mp
    simp [BitVec.toNat_ofNat]
  have h1 : BitVec.ofNat w ((1 : BitVec w).toNat) = (1 : BitVec w) := by
    apply BitVec.toNat_inj.mp
    simp [BitVec.toNat_ofNat]
  rw [h2, h1]
  exact congrArg (fun b => some b.toNat) (mul_two_eq_shift w (BitVec.ofNat w x))

/-- Rewrite `%d = mul i32 %v, 2` to `%d = shl i32 %v, 1`.  The literal must be
at the instruction's width; anything else is left alone. -/
def strengthReduceInstr : Instr → Instr
  | .binop d .mul w lhs (.imm (.int w2 v)) =>
      if h : w2 = w then
        if (h ▸ v) = (2 : BitVec w) then
          .binop d .shl w lhs (.imm (.int w (BitVec.ofNat w 1)))
        else .binop d .mul w lhs (.imm (.int w2 v))
      else .binop d .mul w lhs (.imm (.int w2 v))
  | i => i

/-- One rewritten instruction has the same effect in every state. -/
theorem evalInstr_strengthReduce (s : State) (i : Instr) :
    evalInstr s (strengthReduceInstr i) = evalInstr s i := by
  cases i with
  | binop d op w lhs rhs =>
      cases op with
      | mul =>
          cases rhs with
          | reg n => rfl
          | imm c =>
              cases c with
              | int w2 v =>
                  simp only [strengthReduceInstr]
                  by_cases h : w2 = w
                  · rw [dite_eq_left h]
                    by_cases hv : (h ▸ v) = (2 : BitVec w)
                    · rw [ite_eq_left hv]
                      cases h
                      subst hv
                      simp only [evalInstr]
                      cases hx : evalOperand s lhs with
                      | none => rfl
                      | some val =>
                          cases val with
                          | ptr a =>
                              simp [evalOperand, Const.toValue, Value.intToNat]
                          | int w' x =>
                              by_cases hw : w' = w
                              · subst hw
                                simp only [evalOperand, Const.toValue, Value.intToNat,
                                  ite_true]
                                rw [evalBinopNat_mul_two]
                                rfl
                              · simp [evalOperand, Const.toValue, Value.intToNat, hw]
                    · rw [ite_eq_right hv]
                  · rw [dite_eq_right h]
              | null => rfl
              | undef => rfl
              | poison => rfl
      | add => rfl
      | sub => rfl
      | udiv => rfl
      | sdiv => rfl
      | urem => rfl
      | srem => rfl
      | and => rfl
      | or => rfl
      | xor => rfl
      | shl => rfl
      | lshr => rfl
      | ashr => rfl
  | icmp d p w a b => rfl
  | select d ty c a b => rfl
  | trunc d wi wo v => rfl
  | zext d wi wo v => rfl
  | sext d wi wo v => rfl
  | alloca d ty a => rfl
  | load d ty p => rfl
  | store ty v p => rfl

def strengthReduceBlock (b : Block) : Block :=
  { b with instrs := b.instrs.map strengthReduceInstr }

def strengthReduce (f : Function) : Function :=
  { f with blocks := f.blocks.map strengthReduceBlock }

/-- Rewriting every instruction of a block preserves its denotation. -/
theorem denoteCode_map_strengthReduce (is : List Instr) (s : State) :
    denoteCode (is.map strengthReduceInstr) s = denoteCode is s := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
      simp only [List.map_cons, denoteCode, evalInstr_strengthReduce]
      split
      · rfl
      · rename_i s' _
        exact ih s'

theorem step_strengthReduce (f : Function) (s : State) :
    step (strengthReduce f) s = step f s := by
  simp only [step, strengthReduce, Function.findBlock]
  rw [findBlockList_map (g := strengthReduceBlock) (fun b => rfl) f.blocks s.pc]
  cases hb : findBlockList f.blocks s.pc with
  | none => simp
  | some b =>
      simp only [Option.map_some, strengthReduceBlock]
      rw [denoteCode_map_strengthReduce]

theorem runFuel_strengthReduce (n : Nat) (f : Function) (s : State) :
    runFuel n (strengthReduce f) s = runFuel n f s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [runFuel_succ, runFuel_succ, step_strengthReduce]
      cases hs : step f s with
      | ub => rfl
      | ret v s' => rfl
      | jump s' => exact ih s'

theorem strengthReduceBlock_name (b : Block) : (strengthReduceBlock b).name = b.name := rfl

theorem strengthReduceBlock_name_fun :
    ((fun x => x.name) ∘ strengthReduceBlock) = (fun b => b.name) := by
  funext b
  exact strengthReduceBlock_name b

theorem entry?_strengthReduce (f : Function) :
    (strengthReduce f).entry? = f.entry? := by
  simp [Function.entry?, strengthReduce, List.head?_map, strengthReduceBlock_name_fun]

theorem initState_strengthReduce (f : Function) (args : List Value) :
    initState (strengthReduce f) args = initState f args := by
  simp [initState, strengthReduce, Function.entry?, List.head?_map,
    strengthReduceBlock_name_fun]

theorem strengthReduce_beh (f : Function) (args : List Value) (o : Outcome) :
    Beh (strengthReduce f) args o ↔ Beh f args o := by
  unfold Beh
  simp only [initState_strengthReduce, runFuel_strengthReduce]

def strengthReduction : Pass where
  name := "strength"
  run := strengthReduce

theorem strengthReduction_sound : strengthReduction.Sound :=
  fun f => Refines.of_iff (strengthReduce_beh f)

end LeanLLVM
