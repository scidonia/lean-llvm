/-
Certified conditional-branch folding.

A `condbr` on a literal `i1` is replaced by the unconditional branch it would
have taken.  The condition is a literal, so both programs take the same edge;
the theorem below is a plain equality of executions.
-/
import LeanLLVM.Transform.Basic

namespace LeanLLVM

/-- The value of a branch condition when it is a literal. -/
def truthValue : Operand → Option Bool
  | .imm (.int w v) =>
      if w = 1 then
        match v.toNat with
        | 0 => some false
        | 1 => some true
        | _ => none
      else none
  | _ => none

def foldTerm : Term → Term
  | .condbr c t f =>
      match truthValue c with
      | some true => .br t
      | some false => .br f
      | none => .condbr c t f
  | t => t

def foldTermBlock (b : Block) : Block :=
  { b with term := foldTerm b.term }

def foldBranches (f : Function) : Function :=
  { f with blocks := f.blocks.map foldTermBlock }

theorem execTerm_foldTerm (s : State) (t : Term) :
    execTerm s (foldTerm t) = execTerm s t := by
  cases t with
  | condbr c a b =>
      simp only [foldTerm]
      cases c with
      | reg n => rfl
      | imm cc =>
          cases cc with
          | int w v =>
              simp only [truthValue]
              by_cases hw : w = 1
              · cases hw
                cases hv : v.toNat with
                | zero =>
                    have h0 : v = (0 : BitVec 1) := by
                      apply BitVec.eq_of_toNat_eq
                      simpa using hv
                    simp [h0, execTerm, evalOperand, Const.toValue]
                | succ n =>
                    cases n with
                    | zero =>
                        have h1 : v = (1 : BitVec 1) := by
                          apply BitVec.eq_of_toNat_eq
                          simpa using hv
                        simp [h1, execTerm, evalOperand, Const.toValue]
                    | succ n =>
                        have := BitVec.isLt v
                        omega
              · simp [hw]
          | null => simp [truthValue]
          | undef => simp [truthValue]
          | poison => simp [truthValue]
  | ret ty v => rfl
  | br d => rfl
  | unreachable => rfl

theorem foldTermBlock_name (b : Block) : (foldTermBlock b).name = b.name := rfl

theorem step_foldBranches (f : Function) (s : State) :
    step (foldBranches f) s = step f s := by
  simp only [step, foldBranches, Function.findBlock]
  rw [findBlockList_map (g := foldTermBlock) (fun b => foldTermBlock_name b) f.blocks s.pc]
  cases hb : findBlockList f.blocks s.pc with
  | none => simp
  | some b =>
      simp only [Option.map_some]
      simp only [foldTermBlock]
      simp only [execTerm_foldTerm]

theorem runFuel_foldBranches (n : Nat) (f : Function) (s : State) :
    runFuel n (foldBranches f) s = runFuel n f s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [runFuel_succ, runFuel_succ, step_foldBranches]
      cases hs : step f s with
      | ub => rfl
      | ret v s' => rfl
      | jump s' => exact ih s'

theorem foldTermBlock_name_fun :
    ((fun x => x.name) ∘ foldTermBlock) = (fun b => b.name) := by
  funext b
  exact foldTermBlock_name b

theorem entry?_foldBranches (f : Function) :
    (foldBranches f).entry? = f.entry? := by
  simp [Function.entry?, foldBranches, List.head?_map, foldTermBlock_name_fun]

theorem initState_foldBranches (f : Function) (args : List Value) :
    initState (foldBranches f) args = initState f args := by
  simp [initState, foldBranches, Function.entry?, List.head?_map, foldTermBlock_name_fun]

theorem foldBranches_beh (f : Function) (args : List Value) (o : Outcome) :
    Beh (foldBranches f) args o ↔ Beh f args o := by
  unfold Beh
  simp only [initState_foldBranches, runFuel_foldBranches]

def branchFolding : Pass where
  name := "foldbr"
  run := foldBranches

theorem branchFolding_sound : branchFolding.Sound :=
  fun f => Refines.of_iff (foldBranches_beh f)

end LeanLLVM
