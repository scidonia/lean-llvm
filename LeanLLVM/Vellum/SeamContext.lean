/-
The contextual replacement theorem over emitted IR.

`probes/install/ir/caller.ll` is a caller whose body is one call to the seam
whose result it returns.  The call is resolved by the semantics' call
environment, so the linker's selection is an entry in that environment.  This
module

1. parses and pins the caller;
2. defines the environment each installed body provides;
3. proves the caller's execution under that environment;
4. proves the caller's behaviour is unchanged when the body is replaced.

The environment is deterministic — one result per argument list — so
preservation is an equality of behaviours.  A one-directional contextual
refinement (`target ⊆ source`) needs a relational call environment, in which a
call may have several possible outcomes; `CallRefines` is that relation.  An
environment entry now returns what the callee leaves behind, memory and
allocator state included, so a body that writes is inside the model: the caller
adopts the memory the entry returns.  What the theorem does establish is that
the caller's behaviour goes through the call semantics and the environment entry,
rather than through an inlined body.
-/
import LeanLLVM.Parser
import LeanLLVM.Semantics
import LeanLLVM.Vellum.CommaMaskKernel
import LeanLLVM.CallRefinement

namespace LeanLLVM.Vellum.SeamContext

open LeanLLVM

/-! ### The caller fixture -/

/-- The caller as emitted (`probes/install/ir/caller.ll`). -/
def callerSrc : String := include_str "../../probes/install/ir/caller.ll"

/-- Parse a fixture and take its single function. -/
def firstFunction (src : String) : Option Function :=
  match parseModule src with
  | .ok m => m.functions.head?
  | .error _ => none

/-- The seam's symbol, as the linker and the call environment both name it. -/
def seamSymbol : String := "leanllvm_comma_mask8"

/-- The caller's only instruction. -/
def callerInstrs : List Instr :=
  [.call "%r" (.int 64) seamSymbol [(.int 64, .reg "%arg")]]

/-- The caller block. -/
def callerBody : Block :=
  { name := "entry", instrs := callerInstrs,
    term := .ret (.int 64) (some (.reg "%r")) }

/-- `probes/install/ir/caller.ll`, as an AST. -/
def callerFunction : Function :=
  { name := "leanllvm_caller", retTy := .int 64, params := [("%arg", .int 64)],
    blocks := [callerBody] }

#guard decide (firstFunction callerSrc = some callerFunction)

/-! ### The call environment -/

/-- An environment in which the seam computes `v` and leaves the caller's memory
and allocator exactly as it found them; every other symbol is unresolved, which
the semantics turns into `ub` at the call.  A pure seam must return the caller's
`mem` and `next` unchanged: the caller adopts the returned memory wholesale, so
returning `[]` here would erase everything the caller had stored. -/
def envFor (v : BitVec 64 → BitVec 64) : Calls :=
  fun callee args mem next =>
    if callee = seamSymbol then
      match args with
      | [.int 64 x] => some { ret := .int 64 (v x), mem := mem, next := next }
      | _ => none
    else none

/-- The environment an installed body provides.  The seam runs `f` from the
caller's memory and from an allocator whose next free address is the caller's
`next`, with the parameters bound to the arguments; the caller resumes from
`next + reserve`, the frame the selection reserves for the body.  A run that
reaches `ub`, or that does not return a value within `fuel`, is an unresolved
call.  The reservation is declared rather than read off the run: a callee that
reserves more than it uses is still correct, and `Outcome` (`Semantics.lean:246-251`)
records only the value and the memory, so the allocator the body actually reached
is a separate obligation (`CommaMaskLoop.loopFrameAt_eq`). -/
def envForBody (fuel reserve : Nat) (f : Function) : Calls :=
  fun callee args mem next =>
    if callee = seamSymbol then
      let s : State :=
        { env := (f.params.zip args).map fun p => (p.1.1, p.2)
          mem := mem, next := next, pc := f.entry?.getD "", pre := none }
      match runFuel noCalls fuel f s with
      | some (.ret (some v) m) => some { ret := v, mem := m, next := next + reserve }
      | _ => none
    else none

/-- The two installed bodies induce the same environment. -/
theorem envFor_eq : envFor byteLoop = envFor swar := by
  funext callee args mem next
  by_cases h : callee = seamSymbol
  · simp only [envFor, h, ite_true]
    cases args with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | cons b rest => simp
      | nil =>
        cases a with
        | int w x =>
          by_cases hw : w = 64
          · subst hw
            have e : byteLoop x = swar x :=
              (byteLoop_eq_spec x).trans (swar_eq_spec x).symm
            simp only [e]
          · simp [hw]
        | ptr a => rfl
        | vec n' w' lanes => rfl
  · simp only [envFor, h, ite_false]

/-! ### Execution -/

theorem lookupName_initState_caller (x : BitVec 64) :
    lookupName (initState callerFunction [.int 64 x]).env "%arg" =
      some (.int 64 x) := by
  simp [initState, callerFunction, List.map, List.zip, List.zipWith]

/-- A longer argument list binds the same parameter, because the caller has one
parameter: `zip` truncates at it.  Both behaviours and both runs are therefore
about `initState callerFunction [a]`. -/
theorem initState_cons_caller (a : Value) (rest : List Value) :
    initState callerFunction (a :: rest) = initState callerFunction [a] := rfl

theorem caller_findBlock :
    callerFunction.findBlock (initState callerFunction [.int 64 x]).pc =
      some callerBody := by
  simp [initState, callerFunction, Function.findBlock, findBlockList,
    Function.entry?, List.head?, Option.getD]

theorem caller_block (v : BitVec 64 → BitVec 64) (s : State) (x : BitVec 64)
    (h0 : lookupName s.env "%arg" = some (.int 64 x)) :
    denoteCode (envFor v) callerInstrs s = some (s.bind "%r" (.int 64 (v x))) := by
  simp only [callerInstrs, denoteCode, evalInstr, evalOperands, evalOperand,
    envFor, seamSymbol, h0, ite_true, State.bind]

theorem caller_step (v : BitVec 64 → BitVec 64) (x : BitVec 64) :
    step (envFor v) callerFunction (initState callerFunction [.int 64 x]) =
      .ret (some (.int 64 (v x)))
        ((initState callerFunction [.int 64 x]).bind "%r" (.int 64 (v x))) := by
  have h0 := lookupName_initState_caller x
  simp only [step, caller_findBlock, callerBody]
  rw [caller_block v _ x h0]
  simp only [execTerm, evalOperand, State.bind, lookupName_cons_self]

theorem caller_runFuel_succ (v : BitVec 64 → BitVec 64) (x : BitVec 64) (n : Nat) :
    runFuel (envFor v) (n + 1) callerFunction (initState callerFunction [.int 64 x]) =
      some (.ret (some (.int 64 (v x))) []) := by
  simp only [runFuel, caller_step v x]
  rfl

theorem caller_runFuel_none_or (v : BitVec 64 → BitVec 64) (x : BitVec 64) :
    ∀ n, runFuel (envFor v) n callerFunction (initState callerFunction [.int 64 x]) = none ∨
      runFuel (envFor v) n callerFunction (initState callerFunction [.int 64 x]) =
        some (.ret (some (.int 64 (v x))) []) := by
  intro n
  cases n with
  | zero => exact Or.inl rfl
  | succ k => exact Or.inr (caller_runFuel_succ v x k)

/-- The caller's only observable result under an environment for `v` is `v x`. -/
theorem caller_beh (v : BitVec 64 → BitVec 64) (x : BitVec 64) (o : Outcome) :
    Beh (envFor v) callerFunction [.int 64 x] o ↔
      o = .ret (some (.int 64 (v x))) [] := by
  constructor
  · intro h
    rcases h with ⟨n, hn⟩ | ⟨n, hn⟩
    · rcases caller_runFuel_none_or v x n with h' | h' <;> rw [h'] at hn <;> simp at hn
    · rcases caller_runFuel_none_or v x n with h' | h' <;> rw [h'] at hn
      · simp at hn
      · exact (Option.some.inj hn).symm
  · intro h
    subst h
    exact Or.inr ⟨1, caller_runFuel_succ v x 0⟩

/-- The caller's whole entry block under a body's selection: the call resolves
to `r` and the caller binds the returned value, adopts the returned memory and
resumes from the returned allocator state.  This is the `envForBody` counterpart
of the block computation inside `caller_step`. -/
theorem caller_block_body (fuel reserve : Nat) (f : Function) (s : State)
    (x : BitVec 64) {r : CallOutcome}
    (h0 : lookupName s.env "%arg" = some (.int 64 x))
    (h : envForBody fuel reserve f seamSymbol [.int 64 x] s.mem s.next = some r) :
    denoteCode (envForBody fuel reserve f) callerInstrs s =
      some { s with env := ("%r", r.ret) :: s.env, mem := r.mem, next := r.next } := by
  simp only [callerInstrs, denoteCode, evalInstr, evalOperands, evalOperand, h0]
  rw [h]

/-- The caller's run under a body's selection returns, after one step, the
body's value with the body's memory. -/
theorem caller_runFuel_body_succ (fuel reserve : Nat) (f : Function) (x : BitVec 64)
    {r : CallOutcome}
    (h : envForBody fuel reserve f seamSymbol [.int 64 x] [] 1 = some r) (n : Nat) :
    runFuel (envForBody fuel reserve f) (n + 1) callerFunction
        (initState callerFunction [.int 64 x]) = some (.ret (some r.ret) r.mem) := by
  have h0 := lookupName_initState_caller x
  simp only [runFuel, step, caller_findBlock, callerBody]
  rw [caller_block_body fuel reserve f _ x h0 h]
  simp [execTerm, evalOperand]

theorem caller_runFuel_body_none_or (fuel reserve : Nat) (f : Function) (x : BitVec 64)
    {r : CallOutcome}
    (h : envForBody fuel reserve f seamSymbol [.int 64 x] [] 1 = some r) :
    ∀ n, runFuel (envForBody fuel reserve f) n callerFunction
        (initState callerFunction [.int 64 x]) = none ∨
      runFuel (envForBody fuel reserve f) n callerFunction
        (initState callerFunction [.int 64 x]) = some (.ret (some r.ret) r.mem) := by
  intro n
  cases n with
  | zero => exact Or.inl rfl
  | succ k => exact Or.inr (caller_runFuel_body_succ fuel reserve f x h k)

/-- The emitted caller has exactly one behaviour under an installed body's
selection: the body's return, with the body's memory.  This is the `envForBody`
counterpart of `caller_beh` and it is what `caller_replaces_loop_within` and
scenario `CM4` both consume — the "exactly one" half is what lets CM4 collapse
two behaviours to one and refute the relation at a frame that excludes address
`1`. -/
theorem caller_beh_body (fuel reserve : Nat) (f : Function) (x : BitVec 64)
    {r : CallOutcome}
    (h : envForBody fuel reserve f seamSymbol [.int 64 x] [] 1 = some r) :
    ∀ o, Beh (envForBody fuel reserve f) callerFunction [.int 64 x] o ↔
      o = .ret (some r.ret) r.mem := by
  intro o
  constructor
  · intro hb
    rcases hb with ⟨n, hn⟩ | ⟨n, hn⟩
    · rcases caller_runFuel_body_none_or fuel reserve f x h n with h' | h' <;>
        rw [h'] at hn <;> simp at hn
    · rcases caller_runFuel_body_none_or fuel reserve f x h n with h' | h' <;>
        rw [h'] at hn
      · simp at hn
      · exact (Option.some.inj hn).symm
  · intro ho
    subst ho
    exact Or.inr ⟨1, caller_runFuel_body_succ fuel reserve f x h 0⟩

/-- The caller's block is the entry block, whatever the state's memory and
allocator are. -/
theorem caller_findBlock_entry : callerFunction.findBlock "entry" = some callerBody := by
  simp [callerFunction, callerBody, Function.findBlock, findBlockList]

/-- A block whose instructions leave the caller undefined ends the run in `ub`,
whatever the state's memory and allocator are. -/
theorem caller_step_ub (calls : Calls) (s : State) (hpc : s.pc = "entry")
    (hblock : denoteCode calls callerInstrs s = none) :
    step calls callerFunction s = .ub := by
  simp only [step, hpc, caller_findBlock_entry, callerBody, hblock]

/-- The caller's block under a selection that leaves its call undefined: the
call's argument is read and the unresolved entry makes the instruction, and so
the block, undefined. -/
theorem caller_block_unresolved (fuel reserve : Nat) (f : Function) (s : State)
    (a : Value) (h0 : lookupName s.env "%arg" = some a)
    (hm : s.mem = []) (hn : s.next = 1)
    (h : envForBody fuel reserve f seamSymbol [a] [] 1 = none) :
    denoteCode (envForBody fuel reserve f) callerInstrs s = none := by
  simp only [callerInstrs, denoteCode, evalInstr, evalOperands, evalOperand, h0]
  rw [hm, hn, h]

/-- The caller reaches `ub` at its call whenever the selection leaves that call
undefined, and `ub` admits every outcome, so every outcome is one of its
behaviours.  This is the other-argument case `caller_beh_body` does not cover: an
argument list whose first value is not an `i64` is passed to the seam unchanged,
and the callee's selection refuses it. -/
theorem caller_beh_of_unresolved (fuel reserve : Nat) (f : Function) (a : Value)
    (rest : List Value) (o : Outcome)
    (h : envForBody fuel reserve f seamSymbol [a] [] 1 = none) :
    Beh (envForBody fuel reserve f) callerFunction (a :: rest) o := by
  refine Or.inl ⟨1, ?_⟩
  rw [initState_cons_caller]
  have h0 : lookupName (initState callerFunction [a]).env "%arg" = some a := by
    simp [initState, callerFunction, List.map, List.zip, List.zipWith]
  have hstep : step (envForBody fuel reserve f) callerFunction
      (initState callerFunction [a]) = .ub :=
    caller_step_ub _ _ rfl (caller_block_unresolved fuel reserve f _ a h0 rfl rfl h)
  simp only [runFuel, hstep]

/-- With no argument the caller's parameter is unbound, so its call is undefined
and every outcome is a behaviour. -/
theorem caller_beh_nil (fuel reserve : Nat) (f : Function) (o : Outcome) :
    Beh (envForBody fuel reserve f) callerFunction [] o := by
  refine Or.inl ⟨1, ?_⟩
  have hblock : denoteCode (envForBody fuel reserve f) callerInstrs
      (initState callerFunction ([] : List Value)) = none := by
    simp only [callerInstrs, denoteCode, evalInstr, evalOperands, evalOperand,
      initState, callerFunction, List.map, List.zip, List.zipWith, lookupName]
  have hstep : step (envForBody fuel reserve f) callerFunction
      (initState callerFunction ([] : List Value)) = .ub :=
    caller_step_ub _ _ rfl hblock
  simp only [runFuel, hstep]

theorem seam_callRefines :
    ∀ sym, CallRefines (envFor byteLoop) (envFor swar) sym := by
  intro sym args mem next
  right
  exact congrFun (congrFun (congrFun (congrFun envFor_eq sym) args) mem) next

/-! ### Replacement -/

/-- Replacing the installed body leaves the caller's behaviour unchanged, for
every argument.  The proof goes through the call instruction and the
environment entry: no body is inlined into the caller. -/
theorem caller_seam_replacement (x : BitVec 64) (o : Outcome) :
    Beh (envFor byteLoop) callerFunction [.int 64 x] o ↔
      Beh (envFor swar) callerFunction [.int 64 x] o := by
  have e : byteLoop x = swar x := (byteLoop_eq_spec x).trans (swar_eq_spec x).symm
  rw [caller_beh, caller_beh, e]

/-- The directional form: through the general call-refinement rule, the
candidate environment's caller behaviours are included in the baseline
environment's. -/
theorem caller_refines_under_seam (x : BitVec 64) (o : Outcome) :
    Beh (envFor byteLoop) callerFunction [.int 64 x] o →
      Beh (envFor swar) callerFunction [.int 64 x] o :=
  Beh_calls_refines seam_callRefines callerFunction _ _

/-- An environment that leaves the seam undefined is *not* refined by a
baseline that defines it: the target would be `ub`, which admits outcomes the
source does not. -/
theorem undefined_env_not_refines :
    ¬ CallRefines (fun _ _ _ _ => none) (envFor swar) seamSymbol := by
  intro h
  have hsrc : envFor swar seamSymbol [.int 64 0] [] 1 = none :=
    CallRefines.ub_of_target_ub h rfl
  simp [envFor] at hsrc

end LeanLLVM.Vellum.SeamContext
