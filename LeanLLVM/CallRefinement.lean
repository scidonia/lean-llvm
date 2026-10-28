/-
One-directional refinement through a call environment.

A call environment is deterministic, but `none` (an unresolved call) is `ub`,
which admits every outcome.  So the environments do have a non-trivial order:

* `CallRefines calls' calls sym` holds when, on every argument list, either the
  source environment is `ub` (`none`) — and therefore admits every outcome — or
  the two environments agree.  A target that returns a value where the source
  is `ub` is a refinement; a target that is `ub` where the source returns is
  not.
* If every symbol relates this way, a function's behaviours under the target
  environment are included in its behaviours under the source environment.

This is the contextual rule the seam replacement uses, and it is directional:
the candidate may define a call the baseline leaves undefined, never the
reverse.  Memory effects across calls are still outside the model.
-/
import LeanLLVM.Semantics

namespace LeanLLVM

/-- `calls'` refines `calls` at `sym`: on every argument list the source is
`ub`, or the two agree.  `none` is `ub`, so the source then admits every
outcome and the target's result is included. -/
def CallRefines (calls' calls : Calls) (sym : String) : Prop :=
  ∀ args, calls sym args = none ∨ calls' sym args = calls sym args

theorem CallRefines.eq_of_source_defined {calls' calls : Calls} {sym : String}
    (h : CallRefines calls' calls sym) {args : List Value} {v : Value}
    (hs : calls sym args = some v) : calls' sym args = some v := by
  rcases h args with hnone | heq
  · rw [hnone] at hs; cases hs
  · rw [heq]; exact hs

theorem CallRefines.ub_of_target_ub {calls' calls : Calls} {sym : String}
    (h : CallRefines calls' calls sym) {args : List Value}
    (ht : calls' sym args = none) : calls sym args = none := by
  rcases h args with hnone | heq
  · exact hnone
  · rw [heq] at ht; exact ht

/-- A single instruction either has the same effect in both environments or is
undefined in the source. -/
theorem evalInstr_refines {calls' calls : Calls}
    (h : ∀ sym, CallRefines calls' calls sym) (s : State) (i : Instr) :
    ∀ s', evalInstr calls' s i = some s' →
      evalInstr calls s i = some s' ∨ evalInstr calls s i = none := by
  cases i with
  | binop d op w a b => intro s' he; exact Or.inl he
  | icmp d p w a b => intro s' he; exact Or.inl he
  | select d ty c a b => intro s' he; exact Or.inl he
  | trunc d wi wo v => intro s' he; exact Or.inl he
  | zext d wi wo v => intro s' he; exact Or.inl he
  | sext d wi wo v => intro s' he; exact Or.inl he
  | alloca d ty a => intro s' he; exact Or.inl he
  | load d ty p => intro s' he; exact Or.inl he
  | store ty v p => intro s' he; exact Or.inl he
  | call d retTy callee args =>
      intro s' he
      simp only [evalInstr] at he ⊢
      split at he
      · rename_i vs hvs
        split at he
        · rename_i v hv
          rcases h callee vs with hnone | heq
          · exact Or.inr (by simp only [hnone])
          · have hs : calls callee vs = some v := heq ▸ hv
            exact Or.inl (by simpa only [hvs, hs] using he)
        · rename_i hv
          simp at he
      · rename_i hvs
        simp at he

/-- An undefined instruction in the target is undefined in the source.  A call
is the only instruction whose result depends on the environment, and `none`
there means the source is `ub` too. -/
theorem evalInstr_ub_refines {calls' calls : Calls}
    (h : ∀ sym, CallRefines calls' calls sym) (s : State) (i : Instr) :
    evalInstr calls' s i = none → evalInstr calls s i = none := by
  cases i with
  | call d retTy callee args =>
      intro he
      simp only [evalInstr] at he ⊢
      cases hvs : evalOperands s args with
      | none => rfl
      | some vs =>
          rw [hvs] at he
          cases hv : calls' callee vs with
          | none =>
              have hsrc : calls callee vs = none :=
                CallRefines.ub_of_target_ub (h callee) hv
              simp only [hsrc]
          | some v =>
              simp only [hv] at he
              cases he
  | binop d op w a b => intro he; exact he
  | icmp d p w a b => intro he; exact he
  | select d ty c a b => intro he; exact he
  | trunc d wi wo v => intro he; exact he
  | zext d wi wo v => intro he; exact he
  | sext d wi wo v => intro he; exact he
  | alloca d ty a => intro he; exact he
  | load d ty p => intro he; exact he
  | store ty v p => intro he; exact he

/-- A straight-line sequence that is undefined in the target is undefined in
the source. -/
theorem denoteCode_ub_refines {calls' calls : Calls}
    (h : ∀ sym, CallRefines calls' calls sym) :
    ∀ (is : List Instr) (s : State), denoteCode calls' is s = none →
      denoteCode calls is s = none
  | [], _, he => by
      simp only [denoteCode] at he
      cases he
  | i :: is, s, he => by
      simp only [denoteCode] at he ⊢
      cases hstep : evalInstr calls' s i with
      | none => rw [evalInstr_ub_refines h s i hstep]
      | some s' =>
          rw [hstep] at he
          rcases evalInstr_refines h s i s' hstep with hsame | hnone
          · rw [hsame]
            simpa using denoteCode_ub_refines h is s' he
          · rw [hnone]

/-- A straight-line sequence either has the same effect or the source becomes
undefined at some instruction. -/
theorem denoteCode_refines {calls' calls : Calls}
    (h : ∀ sym, CallRefines calls' calls sym) :
    ∀ (is : List Instr) (s s' : State), denoteCode calls' is s = some s' →
      denoteCode calls is s = some s' ∨ denoteCode calls is s = none
  | [], s, s', he => by
      simp only [denoteCode, Option.some.injEq] at he
      subst he
      exact Or.inl rfl
  | i :: is, s, s', he => by
      simp only [denoteCode] at he ⊢
      cases hstep : evalInstr calls' s i with
      | none =>
          rw [hstep] at he
          cases he
      | some s'' =>
          rw [hstep] at he
          rcases evalInstr_refines h s i s'' hstep with hsame | hnone
          · rw [hsame]
            simpa using denoteCode_refines h is s'' s' he
          · rw [hnone]
            simp

/-- One control step either matches or the source reaches `ub`.  `ub` is the
top of the behaviour order, so it admits whatever the target does. -/
theorem step_refines {calls' calls : Calls}
    (h : ∀ sym, CallRefines calls' calls sym) (f : Function) (s : State) :
    ∀ c, step calls' f s = c → step calls f s = c ∨ step calls f s = .ub := by
  intro c hc
  cases hfind : f.findBlock s.pc with
  | none =>
      simp only [step, hfind] at hc ⊢
      exact Or.inl hc
  | some b =>
      simp only [step, hfind] at hc ⊢
      cases hcode : denoteCode calls' b.instrs s with
      | none =>
          rw [denoteCode_ub_refines h b.instrs s hcode]
          exact Or.inr rfl
      | some s' =>
          rw [hcode] at hc
          rcases denoteCode_refines h b.instrs s s' hcode with hsame | hnone
          · rw [hsame]
            exact Or.inl hc
          · rw [hnone]
            exact Or.inr rfl

/-- Lifting over fuel: the source either produces the target's outcome with the
same fuel, or reaches `ub` within that budget. -/
theorem runFuel_refines {calls' calls : Calls}
    (h : ∀ sym, CallRefines calls' calls sym) :
    ∀ (n : Nat) (f : Function) (s : State) (o : Outcome),
      runFuel calls' n f s = some o →
        runFuel calls n f s = some o ∨
          ∃ m, m ≤ n ∧ runFuel calls m f s = some .ub := by
  intro n
  induction n with
  | zero =>
      intro f s o he
      simp only [runFuel] at he
      cases he
  | succ k ih =>
      intro f s o he
      cases hstep : step calls' f s with
      | ub =>
          simp only [runFuel, hstep, Option.some.injEq] at he
          subst he
          rcases step_refines h f s _ hstep with hsame | hub
          · left; simp only [runFuel, hsame]
          · refine Or.inr ⟨1, Nat.succ_le_succ (Nat.zero_le k), ?_⟩
            simp only [runFuel, hub]
      | ret v s' =>
          simp only [runFuel, hstep, Option.some.injEq] at he
          subst he
          rcases step_refines h f s _ hstep with hsame | hub
          · left; simp only [runFuel, hsame]
          · refine Or.inr ⟨1, Nat.succ_le_succ (Nat.zero_le k), ?_⟩
            simp only [runFuel, hub]
      | jump s' =>
          simp only [runFuel, hstep] at he
          rcases step_refines h f s _ hstep with hsame | hub
          · simp only [runFuel, hsame]
            rcases ih f s' o he with hout | ⟨m, hm, hubm⟩
            · exact Or.inl hout
            · refine Or.inr ⟨m + 1, Nat.succ_le_succ hm, ?_⟩
              simp only [runFuel, hsame, hubm]
          · refine Or.inr ⟨1, Nat.succ_le_succ (Nat.zero_le k), ?_⟩
            simp only [runFuel, hub]

/-- Behavioural refinement under pointwise-related call environments. -/
theorem Beh_refines {calls' calls : Calls}
    (h : ∀ sym, CallRefines calls' calls sym) (f : Function) (args : List Value)
    (o : Outcome) : Beh calls' f args o → Beh calls f args o := by
  intro hb
  rcases hb with ⟨n, hn⟩ | ⟨n, hn⟩
  · rcases runFuel_refines h n f (initState f args) _ hn with hout | ⟨m, _, hubm⟩
    · exact Or.inl ⟨n, hout⟩
    · exact Or.inl ⟨m, hubm⟩
  · rcases runFuel_refines h n f (initState f args) o hn with hout | ⟨m, _, hubm⟩
    · exact Or.inr ⟨n, hout⟩
    · exact Or.inl ⟨m, hubm⟩

/-- The contextual rule, in the form a replacement uses: the target
environment's behaviours are included in the source environment's, for the same
function.  The two environments are the two selections, so this is a statement
about the linked unit rather than about the caller's text. -/
theorem Beh_calls_refines {calls' calls : Calls}
    (h : ∀ sym, CallRefines calls' calls sym) (f : Function) (args : List Value)
    (o : Outcome) : Beh calls' f args o → Beh calls f args o :=
  Beh_refines h f args o

end LeanLLVM
