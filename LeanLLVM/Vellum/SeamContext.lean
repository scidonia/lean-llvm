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
call may have several possible outcomes; that is the next extension, not a
property of this model.  What the theorem does establish is that the caller's
behaviour goes through the call semantics and the environment entry, rather
than through an inlined body.
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

/-- An environment in which the seam computes `v`; every other symbol is
unresolved, which the semantics turns into `ub` at the call. -/
def envFor (v : BitVec 64 → BitVec 64) : Calls :=
  fun callee args =>
    if callee = seamSymbol then
      match args with
      | [.int 64 x] => some (.int 64 (v x))
      | _ => none
    else none

/-- The two installed bodies induce the same environment. -/
theorem envFor_eq : envFor byteLoop = envFor swar := by
  funext callee args
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
  · simp only [envFor, h, ite_false]

/-! ### Execution -/

theorem lookupName_initState_caller (x : BitVec 64) :
    lookupName (initState callerFunction [.int 64 x]).env "%arg" =
      some (.int 64 x) := by
  simp [initState, callerFunction, List.map, List.zip, List.zipWith]

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

theorem seam_callRefines :
    ∀ sym, CallRefines (envFor byteLoop) (envFor swar) sym := by
  intro sym args
  right
  exact congrFun (congrFun envFor_eq sym) args

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
    ¬ CallRefines (fun _ _ => none) (envFor swar) seamSymbol := by
  intro h
  have hsrc : envFor swar seamSymbol [.int 64 0] = none :=
    CallRefines.ub_of_target_ub h rfl
  simp [envFor] at hsrc

end LeanLLVM.Vellum.SeamContext
