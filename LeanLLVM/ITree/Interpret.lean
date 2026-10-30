/-
An interaction-tree interpretation of the fuel semantics.

Instructions become events; the deterministic parts are delegated to
`evalInstr`, so the tree and `runFuel` make the same decisions.  `Exec` is the
canonical resolution of a tree: following the responses the machine itself
gives, the tree ends in an outcome, `none` for an exhausted budget and
`some .ub` for undefined behaviour.

`ub` and `timeout` are distinct events with the empty response type: `ub` is a
completed semantic outcome, while `timeout` is a finite-budget artifact that no
run observed by `Beh` produces.
-/
import ITree.Core
import LeanLLVM.Semantics

namespace LeanLLVM.ITree

open LeanLLVM
open _root_.ITree

/-! ### The event signature -/

/-- The events the interpretation can observe. -/
inductive Ev : Type → Type where
  /-- A load of `ty` at `addr`; the response is the value, or `none` when the
  bytes are not present (the semantics' undefined load). -/
  | load (addr : Nat) (ty : Ty) : Ev (Option Value)
  /-- A store; the response acknowledges the write. -/
  | store (addr : Nat) (ty : Ty) (v : Value) : Ev Unit
  /-- A call; the response is the linker's answer, `none` when the symbol is
  unresolved. -/
  | call (callee : String) (args : List Value) : Ev (Option Value)
  /-- Undefined behaviour as a stuck node. -/
  | ub : Ev Empty
  /-- An exhausted budget as a node with no continuation. -/
  | timeout : Ev Empty

/-- Undefined behaviour, as a tree with no continuation. -/
def ubT : Tree Ev Outcome := vis Ev.ub Empty.elim

/-- Exhausted fuel, as a tree with no continuation. -/
def timeoutT : Tree Ev Outcome := vis Ev.timeout Empty.elim

/-! ### The interpretation -/

/-- The memory an event `store addr ty v` leaves behind.  It agrees with
`storeValue` on every case that is not undefined behaviour. -/
def storeMem (m : Mem) (ty : Ty) (v : Value) (addr : Nat) : Mem :=
  match ty, v with
  | .int w, .int w' x =>
      if w' = w then writeBytes m addr (natToBytes x.toNat ((w + 7) / 8)) else m
  | .ptr, .ptr a => writeBytes m addr (natToBytes a 8)
  | _, _ => m

/-- Instructions with no event: the semantics' own decision, lifted. -/
def pureInstrT (calls : Calls) (s : State) (i : Instr)
    (k : State → Tree Ev Outcome) : Tree Ev Outcome :=
  match evalInstr calls s i with
  | some s' => k s'
  | none => ubT

/-- One instruction, as a tree whose leaf is the state after it. -/
def instrT (calls : Calls) (s : State) :
    Instr → (State → Tree Ev Outcome) → Tree Ev Outcome
  | .load d ty p, k =>
      match evalOperand s p with
      | some (.ptr addr) =>
          vis (Ev.load addr ty) fun r =>
            match r with
            | some v => k (s.bind d v)
            | none => ubT
      | _ => ubT
  | .store ty v p, k =>
      match evalOperand s v, evalOperand s p with
      | some vv, some (.ptr addr) =>
          vis (Ev.store addr ty vv) fun _ =>
            match storeValue s ty vv addr with
            | some s' => k s'
            | none => ubT
      | _, _ => ubT
  | .call d _ callee args, k =>
      match evalOperands s args with
      | some vs =>
          vis (Ev.call callee vs) fun r =>
            match r with
            | some v => k (s.bind d v)
            | none => ubT
      | none => ubT
  | i, k => pureInstrT calls s i k

/-- A block's instructions as a tree; `k` receives the block's final state. -/
def codeT (calls : Calls) :
    List Instr → State → (State → Tree Ev Outcome) → Tree Ev Outcome
  | [], s, k => k s
  | i :: is, s, k => instrT calls s i (fun s' => codeT calls is s' k)

/-- The terminator's effect, read off `execTerm` itself so that the tree and the
semantics make the same decision.  A jump continues with `next s'.pc`. -/
def termT (s : State) (next : State → Tree Ev Outcome) (t : Term) : Tree Ev Outcome :=
  match execTerm s t with
  | .ub => ubT
  | .ret v s' => ret (.ret v s'.mem)
  | .jump s' => next s'

/-- The fuel-indexed interpretation: the recursion of `runFuel`, with the
block's instructions turned into events and each jump into a silent step. -/
def runT (calls : Calls) : Nat → Function → State → Tree Ev Outcome
  | 0, _, _ => timeoutT
  | n + 1, f, s =>
      match f.findBlock s.pc with
      | none => ubT
      | some b =>
          codeT calls b.instrs s fun s' =>
            termT s' (fun s'' => tau (runT calls n f s'')) b.term

/-! ### Unfolding lemmas -/

theorem runT_zero (calls : Calls) (f : Function) (s : State) :
    runT calls 0 f s = timeoutT := rfl

theorem runT_succ (calls : Calls) (n : Nat) (f : Function) (s : State) :
    runT calls (Nat.succ n) f s =
      (match f.findBlock s.pc with
       | none => ubT
       | some b =>
           codeT calls b.instrs s fun s' =>
             termT s' (fun s'' => tau (runT calls n f s'')) b.term) := rfl

theorem step_unfold (calls : Calls) (f : Function) (s : State) :
    step calls f s =
      (match f.findBlock s.pc with
       | none => Ctrl.ub
       | some b =>
           match denoteCode calls b.instrs s with
           | none => Ctrl.ub
           | some s' => execTerm s' b.term) := rfl

theorem runFuel_succ (calls : Calls) (n : Nat) (f : Function) (s : State) :
    runFuel calls (Nat.succ n) f s =
      (match step calls f s with
       | .ub => some Outcome.ub
       | .ret v s' => some (.ret v s'.mem)
       | .jump s' => runFuel calls n f s') := rfl

/-! ### The canonical resolution relation

`Exec calls t m r` says: following the responses the machine itself gives
(loads from the replay memory, stores into it, calls from the linker), the tree
`t` started with memory `m` ends in `r`.  `r = none` is `timeout`;
`r = some .ub` is undefined behaviour.
-/

inductive Exec (calls : Calls) : Tree Ev Outcome → Mem → Option Outcome → Prop where
  | ret {o : Outcome} {m : Mem} :
      Exec calls (ret o) m (some o)
  | tau {t : Tree Ev Outcome} {m : Mem} {r : Option Outcome} :
      Exec calls t m r → Exec calls (tau t) m r
  | load {addr : Nat} {ty : Ty} {k : Option Value → Tree Ev Outcome} {m : Mem}
      {r : Option Outcome} :
      Exec calls (k (loadValue m ty addr)) m r →
      Exec calls (vis (Ev.load addr ty) k) m r
  | store {addr : Nat} {ty : Ty} {v : Value} {k : Unit → Tree Ev Outcome}
      {m : Mem} {r : Option Outcome} :
      Exec calls (k ()) (storeMem m ty v addr) r →
      Exec calls (vis (Ev.store addr ty v) k) m r
  | call {callee : String} {args : List Value}
      {k : Option Value → Tree Ev Outcome} {m : Mem} {r : Option Outcome} :
      Exec calls (k (calls callee args)) m r →
      Exec calls (vis (Ev.call callee args) k) m r
  | ub {k : Empty → Tree Ev Outcome} {m : Mem} :
      Exec calls (vis Ev.ub k) m (some Outcome.ub)
  | timeout {k : Empty → Tree Ev Outcome} {m : Mem} :
      Exec calls (vis Ev.timeout k) m none

/-! ### Correspondence with `runFuel`

The proof is constructive: every `runFuel` outcome is a leaf of the tree under
the canonical resolution.
-/

/-- Every instruction except `store` leaves the memory untouched. -/
theorem evalInstr_mem_of_not_store (calls : Calls) (s : State) (i : Instr) (s' : State)
    (hns : ∀ (ty : Ty) (v p : Operand), i ≠ .store ty v p)
    (h : evalInstr calls s i = some s') : s'.mem = s.mem := by
  cases i with
  | store ty v p => exact absurd rfl (hns ty v p)
  | binop d op w a b =>
      simp only [evalInstr] at h
      repeat' split at h
      all_goals (cases h <;> rfl)
  | icmp d pr w a b =>
      simp only [evalInstr] at h
      repeat' split at h
      all_goals (cases h <;> rfl)
  | select d ty c a b =>
      simp only [evalInstr] at h
      repeat' split at h
      all_goals (cases h <;> rfl)
  | trunc d wi wo v =>
      simp only [evalInstr] at h
      repeat' split at h
      all_goals (cases h <;> rfl)
  | zext d wi wo v =>
      simp only [evalInstr] at h
      repeat' split at h
      all_goals (cases h <;> rfl)
  | sext d wi wo v =>
      simp only [evalInstr] at h
      repeat' split at h
      all_goals (cases h <;> rfl)
  | alloca d ty al =>
      simp only [evalInstr] at h
      repeat' split at h
      all_goals (cases h <;> rfl)
  | load d ty p =>
      simp only [evalInstr] at h
      repeat' split at h
      all_goals (cases h <;> rfl)
  | call d rt c args =>
      simp only [evalInstr] at h
      repeat' split at h
      all_goals (cases h <;> rfl)

/-- `storeValue` updates the memory exactly as `storeMem` does. -/
theorem storeValue_mem (s : State) (ty : Ty) (v : Value) (addr : Nat) (s' : State)
    (h : storeValue s ty v addr = some s') : s'.mem = storeMem s.mem ty v addr := by
  cases ty with
  | int w =>
      cases v with
      | int w' x =>
          simp only [storeValue] at h
          split at h
          · rename_i hw
            simp only [Option.some.injEq] at h
            subst h
            simp only [storeMem]
            rw [if_pos hw]
          · exact absurd h (by simp)
      | ptr a => simp [storeValue] at h
  | ptr =>
      cases v with
      | int w x => simp [storeValue] at h
      | ptr a =>
          simp only [storeValue, Option.some.injEq] at h
          subst h
          simp only [storeMem]
  | void => cases v <;> simp [storeValue] at h

theorem exec_pureInstrT (calls : Calls) (s : State) (i : Instr)
    (k : State → Tree Ev Outcome) (r : Option Outcome)
    (hmem : ∀ s', evalInstr calls s i = some s' → s'.mem = s.mem)
    (hok : ∀ s', evalInstr calls s i = some s' → Exec calls (k s') s'.mem r)
    (hub : evalInstr calls s i = none → r = some Outcome.ub) :
    Exec calls (pureInstrT calls s i k) s.mem r := by
  cases hE : evalInstr calls s i with
  | none =>
      rw [hub hE]
      simp only [pureInstrT, hE]
      exact Exec.ub
  | some s' =>
      simp only [pureInstrT, hE]
      have h := hok s' hE
      rw [hmem s' hE] at h
      exact h

theorem exec_instrT_load (calls : Calls) (s : State) (d : String) (ty : Ty) (p : Operand)
    (k : State → Tree Ev Outcome) (r : Option Outcome)
    (hok : ∀ s', evalInstr calls s (.load d ty p) = some s' →
      Exec calls (k s') s'.mem r)
    (hub : evalInstr calls s (.load d ty p) = none → r = some Outcome.ub) :
    Exec calls (instrT calls s (.load d ty p) k) s.mem r := by
  cases hOp : evalOperand s p with
  | none =>
      have hE : evalInstr calls s (.load d ty p) = none := by simp [evalInstr, hOp]
      rw [hub hE]
      simp only [instrT, hOp]
      exact Exec.ub
  | some v =>
      cases v with
      | int w x =>
          have hE : evalInstr calls s (.load d ty p) = none := by simp [evalInstr, hOp]
          rw [hub hE]
          simp only [instrT, hOp]
          exact Exec.ub
      | ptr addr =>
          cases hL : loadValue s.mem ty addr with
          | none =>
              have hE : evalInstr calls s (.load d ty p) = none := by
                simp [evalInstr, hOp, hL]
              rw [hub hE]
              simp only [instrT, hOp]
              refine Exec.load ?_
              simp only [hL]
              exact Exec.ub
          | some val =>
              have hE : evalInstr calls s (.load d ty p) = some (s.bind d val) := by
                simp [evalInstr, hOp, hL]
              simp only [instrT, hOp]
              refine Exec.load ?_
              simp only [hL]
              simpa [State.bind] using hok (s.bind d val) hE

theorem exec_instrT_store (calls : Calls) (s : State) (ty : Ty) (v p : Operand)
    (k : State → Tree Ev Outcome) (r : Option Outcome)
    (hok : ∀ s', evalInstr calls s (.store ty v p) = some s' →
      Exec calls (k s') s'.mem r)
    (hub : evalInstr calls s (.store ty v p) = none → r = some Outcome.ub) :
    Exec calls (instrT calls s (.store ty v p) k) s.mem r := by
  cases hv : evalOperand s v with
  | none =>
      have hE : evalInstr calls s (.store ty v p) = none := by simp [evalInstr, hv]
      rw [hub hE]
      simp only [instrT, hv]
      exact Exec.ub
  | some vv =>
      cases hp : evalOperand s p with
      | none =>
          have hE : evalInstr calls s (.store ty v p) = none := by
            simp [evalInstr, hv, hp]
          rw [hub hE]
          simp only [instrT, hv, hp]
          exact Exec.ub
      | some pv =>
          cases pv with
          | int w x =>
              have hE : evalInstr calls s (.store ty v p) = none := by
                simp [evalInstr, hv, hp]
              rw [hub hE]
              simp only [instrT, hv, hp]
              exact Exec.ub
          | ptr addr =>
              cases hS : storeValue s ty vv addr with
              | none =>
                  have hE : evalInstr calls s (.store ty v p) = none := by
                    simp [evalInstr, hv, hp, hS]
                  rw [hub hE]
                  simp only [instrT, hv, hp]
                  refine Exec.store ?_
                  simp only [hS]
                  exact Exec.ub
              | some s' =>
                  have hE : evalInstr calls s (.store ty v p) = some s' := by
                    simp [evalInstr, hv, hp, hS]
                  simp only [instrT, hv, hp]
                  refine Exec.store ?_
                  simp only [hS]
                  have h := hok s' hE
                  rw [storeValue_mem s ty vv addr s' hS] at h
                  exact h

theorem exec_instrT_call (calls : Calls) (s : State) (d : String) (retTy : Ty)
    (callee : String) (args : List (Ty × Operand))
    (k : State → Tree Ev Outcome) (r : Option Outcome)
    (hok : ∀ s', evalInstr calls s (.call d retTy callee args) = some s' →
      Exec calls (k s') s'.mem r)
    (hub : evalInstr calls s (.call d retTy callee args) = none →
      r = some Outcome.ub) :
    Exec calls (instrT calls s (.call d retTy callee args) k) s.mem r := by
  cases ha : evalOperands s args with
  | none =>
      have hE : evalInstr calls s (.call d retTy callee args) = none := by
        simp [evalInstr, ha]
      rw [hub hE]
      simp only [instrT, ha]
      exact Exec.ub
  | some vs =>
      cases hC : calls callee vs with
      | none =>
          have hE : evalInstr calls s (.call d retTy callee args) = none := by
            simp [evalInstr, ha, hC]
          rw [hub hE]
          simp only [instrT, ha]
          refine Exec.call ?_
          simp only [hC]
          exact Exec.ub
      | some val =>
          have hE : evalInstr calls s (.call d retTy callee args) = some (s.bind d val) := by
            simp [evalInstr, ha, hC]
          simp only [instrT, ha]
          refine Exec.call ?_
          simp only [hC]
          simpa [State.bind] using hok (s.bind d val) hE

/-! ### Straight-line code -/

theorem exec_codeT (calls : Calls) :
    ∀ (is : List Instr) (s : State) (k : State → Tree Ev Outcome)
      (r : Option Outcome),
      (∀ s', denoteCode calls is s = some s' → Exec calls (k s') s'.mem r) →
      (denoteCode calls is s = none → r = some Outcome.ub) →
      Exec calls (codeT calls is s k) s.mem r
  | [], s, k, r, hok, _ => hok s rfl
  | i :: is, s, k, r, hok, hub => by
      have hokK : ∀ s1, evalInstr calls s i = some s1 →
          Exec calls (codeT calls is s1 k) s1.mem r := by
        intro s1 h1
        exact exec_codeT calls is s1 k r
          (fun s' h2 => hok s' (by simp [denoteCode, h1, h2]))
          (fun h2 => hub (by simp [denoteCode, h1, h2]))
      have hubK : evalInstr calls s i = none → r = some Outcome.ub := by
        intro h1
        exact hub (by simp [denoteCode, h1])
      show Exec calls (instrT calls s i (fun s' => codeT calls is s' k)) s.mem r
      cases i with
      | load d ty p => exact exec_instrT_load calls s d ty p _ r hokK hubK
      | store ty v p => exact exec_instrT_store calls s ty v p _ r hokK hubK
      | call d rt c args => exact exec_instrT_call calls s d rt c args _ r hokK hubK
      | binop d op w a b =>
          exact exec_pureInstrT calls s (.binop d op w a b) _ r
            (fun s' h => evalInstr_mem_of_not_store calls s _ s'
              (by intro ty v p hh; cases hh) h) hokK hubK
      | icmp d pr w a b =>
          exact exec_pureInstrT calls s (.icmp d pr w a b) _ r
            (fun s' h => evalInstr_mem_of_not_store calls s _ s'
              (by intro ty v p hh; cases hh) h) hokK hubK
      | select d ty c a b =>
          exact exec_pureInstrT calls s (.select d ty c a b) _ r
            (fun s' h => evalInstr_mem_of_not_store calls s _ s'
              (by intro ty v p hh; cases hh) h) hokK hubK
      | trunc d wi wo v =>
          exact exec_pureInstrT calls s (.trunc d wi wo v) _ r
            (fun s' h => evalInstr_mem_of_not_store calls s _ s'
              (by intro ty v p hh; cases hh) h) hokK hubK
      | zext d wi wo v =>
          exact exec_pureInstrT calls s (.zext d wi wo v) _ r
            (fun s' h => evalInstr_mem_of_not_store calls s _ s'
              (by intro ty v p hh; cases hh) h) hokK hubK
      | sext d wi wo v =>
          exact exec_pureInstrT calls s (.sext d wi wo v) _ r
            (fun s' h => evalInstr_mem_of_not_store calls s _ s'
              (by intro ty v p hh; cases hh) h) hokK hubK
      | alloca d ty al =>
          exact exec_pureInstrT calls s (.alloca d ty al) _ r
            (fun s' h => evalInstr_mem_of_not_store calls s _ s'
              (by intro ty v p hh; cases hh) h) hokK hubK

/-! ### Terminators -/

/-- A jump from `execTerm` keeps the memory. -/
theorem execTerm_jump_mem (s : State) (t : Term) (s' : State)
    (h : execTerm s t = .jump s') : s'.mem = s.mem := by
  cases t with
  | ret ty v =>
      cases ty <;> cases v <;>
        (simp only [execTerm] at h
         try split at h
         all_goals simp_all)
  | br dest => simp only [execTerm] at h; cases h; rfl
  | condbr c tb fb =>
      cases hOp : evalOperand s c with
      | none => simp [execTerm, hOp] at h
      | some v =>
          cases v with
          | ptr a => simp [execTerm, hOp] at h
          | int w b =>
              cases w with
              | zero => simp [execTerm, hOp] at h
              | succ w' =>
                  cases w' with
                  | zero =>
                      by_cases h1 : b = (1 : BitVec 1)
                      · simp only [execTerm, hOp, if_pos h1] at h
                        cases h
                        rfl
                      · by_cases h0 : b = (0 : BitVec 1)
                        · simp only [execTerm, hOp, if_neg h1, if_pos h0] at h
                          cases h
                          rfl
                        · simp only [execTerm, hOp, if_neg h1, if_neg h0] at h
                          exact absurd h (by simp)
                  | succ w'' => simp [execTerm, hOp] at h
  | unreachable => simp [execTerm] at h

theorem exec_termT (calls : Calls) (n : Nat) (f : Function) (s : State) (t : Term)
    (hIH : ∀ (f : Function) (s : State),
      Exec calls (runT calls n f s) s.mem (runFuel calls n f s)) :
    Exec calls (termT s (fun s' => tau (runT calls n f s')) t) s.mem
      (match execTerm s t with
       | .ub => some Outcome.ub
       | .ret v s' => some (.ret v s'.mem)
       | .jump s' => runFuel calls n f s') := by
  cases h : execTerm s t with
  | ub => simp only [termT, h]; exact Exec.ub
  | ret v s' => simp only [termT, h]; exact Exec.ret
  | jump s' =>
      simp only [termT, h]
      have hm : s'.mem = s.mem := execTerm_jump_mem s t s' h
      have h2 := hIH f s'
      rw [hm] at h2
      exact Exec.tau h2

/-! ### The whole run -/

theorem exec_runT (calls : Calls) :
    ∀ (n : Nat) (f : Function) (s : State),
      Exec calls (runT calls n f s) s.mem (runFuel calls n f s) := by
  intro n
  induction n with
  | zero =>
      intro f s
      rw [runT_zero]
      exact Exec.timeout
  | succ n ih =>
      intro f s
      rw [runT_succ, runFuel_succ, step_unfold]
      cases hfind : f.findBlock s.pc with
      | none =>
          simp only [hfind]
          exact Exec.ub
      | some b =>
          simp only [hfind]
          have hcont : ∀ (s0 : State), Exec calls
              (termT s0 (fun s'' => tau (runT calls n f s'')) b.term) s0.mem
              (match execTerm s0 b.term with
               | .ub => some Outcome.ub
               | .ret v s'' => some (.ret v s''.mem)
               | .jump s'' => runFuel calls n f s'') :=
            fun s0 => exec_termT calls n f s0 b.term ih
          cases hD : denoteCode calls b.instrs s with
          | none =>
              simp only [hD]
              exact exec_codeT calls b.instrs s _ (some Outcome.ub)
                (fun s0 h0 => by rw [hD] at h0; exact absurd h0 (by simp))
                (fun _ => rfl)
          | some s' =>
              cases hT : execTerm s' b.term with
              | ub =>
                  simp only [hD, hT]
                  exact exec_codeT calls b.instrs s _ (some Outcome.ub)
                    (fun s0 h0 => by
                      rw [hD] at h0
                      simp only [Option.some.injEq] at h0
                      subst s0
                      simpa only [hT] using hcont s')
                    (fun _ => rfl)
              | ret v s'' =>
                  simp only [hD, hT]
                  exact exec_codeT calls b.instrs s _ (some (.ret v s''.mem))
                    (fun s0 h0 => by
                      rw [hD] at h0
                      simp only [Option.some.injEq] at h0
                      subst s0
                      simpa only [hT] using hcont s')
                    (fun h0 => by rw [hD] at h0; exact absurd h0 (by simp))
              | jump s'' =>
                  simp only [hD, hT]
                  exact exec_codeT calls b.instrs s _ (runFuel calls n f s'')
                    (fun s0 h0 => by
                      rw [hD] at h0
                      simp only [Option.some.injEq] at h0
                      subst s0
                      simpa only [hT] using hcont s')
                    (fun h0 => by rw [hD] at h0; exact absurd h0 (by simp))

end LeanLLVM.ITree
