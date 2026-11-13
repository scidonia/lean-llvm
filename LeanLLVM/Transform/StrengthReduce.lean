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
theorem evalInstr_strengthReduce (calls : Calls) (s : State) (i : Instr) :
    evalInstr calls s (strengthReduceInstr i) = evalInstr calls s i := by
  cases i with
  | bitcastToDouble d v =>
    rfl
  | bitcastToInt d v =>
    rfl
  | fcmp d pred a b =>
    rfl
  | fneg d v =>
    rfl
  | fdiv d a b =>
    rfl
  | fmul d a b =>
    rfl
  | uitofp d wIn v =>
    rfl
  | inttoptr d v =>
    rfl
  | ptrtoint d v =>
    rfl
  | gep d elemTy base off => rfl
  | binop d op w lhs rhs =>
      cases op with
      | mul =>
          cases rhs with
          | global n =>
            rfl
          | reg n => rfl
          | imm c =>
              cases c with
              | float b =>
                rfl
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
                          | float b =>
                            simp [evalOperand, Const.toValue, Value.intToNat]
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
                          | vec n' w' lanes =>
                              simp [evalOperand, Const.toValue, Value.intToNat]
                    · rw [ite_eq_right hv]
                  · rw [dite_eq_right h]
              | null => rfl
              | undef => rfl
              | poison => rfl
              | splat _ _ _ => rfl
              | vector _ _ => rfl
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
  | icmpPtr d p a b => rfl
  | select d ty c a b => rfl
  | trunc d wi wo v => rfl
  | zext d wi wo v => rfl
  | sext d wi wo v => rfl
  | alloca d ty a => rfl
  | load d ty p => rfl
  | store ty v p => rfl
  | icmpVec d p n w a b => rfl
  | binopVec d op n w a b => rfl
  | bitcastMask d n v => rfl
  | extractelement d n w v idx => rfl
  | insertelement d n w v elt idx => rfl
  | shuffleVec d n w a b mask => rfl
  | vecBitcast d n w m jw v => rfl
  | phi d ty inc => rfl
  | call d ty callee args => rfl
  | callVoid callee args => rfl

def strengthReduceBlock (b : Block) : Block :=
  { b with instrs := b.instrs.map strengthReduceInstr }

def strengthReduce (f : Function) : Function :=
  { f with blocks := f.blocks.map strengthReduceBlock }

/-- The rewrite keeps an instruction's constructor, so it keeps its `phi`
status. -/
theorem strengthReduceInstr_isPhi (i : Instr) :
    (strengthReduceInstr i).isPhi = i.isPhi := by
  cases i with
  | binop d op w a b =>
      simp only [strengthReduceInstr]
      repeat' split
      all_goals rfl
  | _ => rfl

/-- The rewrite leaves a `phi` alone: it has no arithmetic to strengthen. -/
theorem strengthReduceInstr_phi (d : String) (ty : Ty) (inc : List (String × Operand)) :
    strengthReduceInstr (.phi d ty inc) = .phi d ty inc := rfl

/-- Rewriting every instruction of a block preserves its denotation: a leading
`phi` run reads the same selections at the same snapshot on both sides, so the
run installs the same bindings. -/
theorem denoteRun_map_strengthReduce (calls : Calls) :
    ∀ (is : List Instr) (pend : List (String × Value)) (s : State),
      denoteRun calls pend (is.map strengthReduceInstr) s = denoteRun calls pend is s := by
  intro is
  induction is with
  | nil => intro pend s; rfl
  | cons i is ih =>
      intro pend s
      simp only [List.map_cons]
      by_cases hphi : i.isPhi = true
      · obtain ⟨d, ty, inc, rfl⟩ : ∃ d ty inc, i = .phi d ty inc := by
          cases i with
          | phi d ty inc => exact ⟨d, ty, inc, rfl⟩
          | _ => simp_all [Instr.isPhi]
        simp only [strengthReduceInstr_phi, denoteRun]
        cases hs : phiSelect s inc with
        | none => rfl
        | some v => simp only []; exact ih (pend ++ [(d, v)]) s
      · have hi : i.isPhi = false := by
          cases i <;> simp_all [Instr.isPhi]
        have hsubst : (strengthReduceInstr i).isPhi = false := by
          rw [strengthReduceInstr_isPhi]; exact hi
        rw [denoteRun_cons_of hsubst, denoteRun_cons_of hi, evalInstr_strengthReduce]
        cases he : evalInstr calls (s.bindAll pend) i with
        | none => rfl
        | some s' => simp only []; exact ih [] s'

/-- Rewriting every instruction of a block preserves its denotation. -/
theorem denoteCode_map_strengthReduce (calls : Calls) (is : List Instr) (s : State) :
    denoteCode calls (is.map strengthReduceInstr) s = denoteCode calls is s :=
  denoteRun_map_strengthReduce calls is [] s

theorem step_strengthReduce (calls : Calls) (f : Function) (s : State) :
    step calls (strengthReduce f) s = step calls f s := by
  simp only [step, strengthReduce, Function.findBlock]
  rw [findBlockList_map (g := strengthReduceBlock) (fun b => rfl) f.blocks s.pc]
  cases hb : findBlockList f.blocks s.pc with
  | none => simp
  | some b =>
      simp only [Option.map_some, strengthReduceBlock]
      rw [denoteCode_map_strengthReduce]

theorem runFuel_strengthReduce (calls : Calls) (n : Nat) (f : Function) (s : State) :
    runFuel calls n (strengthReduce f) s = runFuel calls n f s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [runFuel_succ, runFuel_succ, step_strengthReduce]
      cases hs : step calls f s with
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

theorem strengthReduce_beh (calls : Calls) (f : Function) (args : List Value)
    (o : Outcome) :
    Beh calls (strengthReduce f) args o ↔ Beh calls f args o := by
  unfold Beh
  simp only [initState_strengthReduce, runFuel_strengthReduce]

def strengthReduction : Pass where
  name := "strength"
  run := strengthReduce

theorem strengthReduction_sound : strengthReduction.Sound :=
  fun calls f => Refines.of_iff (strengthReduce_beh calls f)

end LeanLLVM
