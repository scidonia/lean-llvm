/-
The block unit's evaluation boundary: the call environment it runs at, and the
lemma that moves a mask-unit step across to it.

The mask unit states each step at `s1Calls` and `withEnv`, while the block unit
runs at `s1BlocksCalls` and `stateAt`.  `evalInstr`'s only arms that consult the
call environment are the two call forms, so an instruction that mentions no call
evaluates identically at any pair of environments: `evalInstr_calls_irrelevance`,
with `callsInstr` deciding the premise, and `evalInstr_blocks_of_masks` composing
it with the environment bridge.  One lemma therefore covers every reused step,
which is why the wrappers are not written: a wrapper per reused instruction would
duplicate a proof whose only varying part is the environment argument, and a new
step would need a new wrapper before it could be used.

`s1BlocksCalls` binds the classifier's two table intrinsics (the mask unit's
`s1Calls`), the ASCII probe's 256-bit zero test, the carry-less product at
immediate zero, and the fused loop's `llvm.usub.sat.v32i8` at the UTF-8 stage's
own meaning.  It does not bind the escape list, whose calls write the caller's
`xp` and count slot; a trace that runs those carries its own footprint.
-/
import LeanLLVM.Refinement.BlockEval
import LeanLLVM.Refinement.JsonS1MasksSteps
import LeanLLVM.Refinement.Pclmul
import LeanLLVM.Refinement.BitLanes
import LeanLLVM.Refinement.CallsFootprint

namespace LeanLLVM.Refinement.JsonS1BlocksSteps

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonS1MasksIR (s1Calls)
open LeanLLVM.Refinement.JsonS1MasksSteps (withEnv)
open LeanLLVM.Refinement.BitLanes (ptestz)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ### The unit's call environment -/

/-- The unit's call environment: the mask unit's two intrinsics, the ASCII
probe's 256-bit zero test, and the fused DFA's saturating subtract. -/
def s1BlocksCalls : Calls :=
  fun callee args mem next =>
    match callee, args with
    | "llvm.x86.avx.ptestz.256", [.vec 4 64 a, .vec 4 64 b] =>
        some { ret := .int 32 (ptestz (BitVec.ofNat 256 (packLanes a))
              (BitVec.ofNat 256 (packLanes b))), mem := mem, next := next }
    | "llvm.usub.sat.v32i8", [.vec 32 8 a, .vec 32 8 b] =>
        some { ret := .vec 32 8 (List.zipWith BitLanes.subsSat a b),
               mem := mem, next := next }
    | _, _ => s1Calls callee args mem next

/-- The probe's zero test: the two `<4 x i64>` operands packed little-endian into
one 256-bit word each, and `ptestz` read at that word. -/
theorem s1BlocksCalls_ptestz (a b : List (BitVec 64)) (mem : Mem) (next : Nat) :
    s1BlocksCalls "llvm.x86.avx.ptestz.256" [.vec 4 64 a, .vec 4 64 b] mem next =
      some { ret := .int 32 (ptestz (BitVec.ofNat 256 (packLanes a))
            (BitVec.ofNat 256 (packLanes b))), mem := mem, next := next } :=
  rfl

/-- The two table lookups are the mask unit's own arms. -/
theorem s1BlocksCalls_pshufb (table control : List (BitVec 8)) (mem : Mem) (next : Nat) :
    s1BlocksCalls "llvm.x86.avx2.pshuf.b" [.vec 32 8 table, .vec 32 8 control] mem next =
      some { ret := .vec 32 8 (pshufbLanes table control), mem := mem, next := next } :=
  rfl

/-- The carry-less product at immediate zero is the mask unit's arm. -/
theorem s1BlocksCalls_pclmulqdq (a0 a1 b0 b1 : BitVec 64) (mem : Mem) (next : Nat) :
    s1BlocksCalls "llvm.x86.pclmulqdq"
        [.vec 2 64 [a0, a1], .vec 2 64 [b0, b1], .int 8 (0 : BitVec 8)] mem next =
      some { ret := .vec 2 64 [Pclmul.clmul a0 b0, (0 : BitVec 64)],
             mem := mem, next := next } :=
  rfl

/-- The saturating subtract: the UTF-8 stage's own meaning, lane by lane. -/
theorem s1BlocksCalls_usubSat (a b : List (BitVec 8)) (mem : Mem) (next : Nat) :
    s1BlocksCalls "llvm.usub.sat.v32i8" [.vec 32 8 a, .vec 32 8 b] mem next =
      some { ret := .vec 32 8 (List.zipWith BitLanes.subsSat a b),
             mem := mem, next := next } :=
  rfl

/-- **The footprint of the four intrinsic arms is empty.**  Each is a register
operation on its operands, so no address the caller holds moves across one of
these calls.

This is the footprint of `s1BlocksCalls` only.  The unit's
`leanllvm_json_escape_list` calls write `xp` and the count slot, and they are not
resolved here: they are the escape-parametric environment's arm
(`s1BlocksCallsEsc`), whose footprint is the caller's selection's.  That
selection is the escape unit's own record, whose post carries the
`UnchangedOutside` its frame states, so no footprint bundle is stated for it
here.  A trace that runs those calls therefore carries its own frame, and this
definition is not one. -/
def s1BlocksCallsFootprint : CallsFootprint s1BlocksCalls :=
  CallsFootprint.pure s1BlocksCalls (by
    intro sym args mem next r h
    simp only [s1BlocksCalls] at h
    repeat' split at h
    all_goals (try (simp only [s1Calls] at h))
    all_goals (try (repeat' split at h))
    all_goals (try (cases h))
    all_goals rfl)

/-! ### The escape-parametric environment

`s1BlocksCalls` binds the four intrinsic arms and leaves
`leanllvm_json_escape_list` unresolved: the escape call writes the caller's
stream and count slot, so no intrinsic arm can stand for it, and a trace that
reaches it is undefined there.  The unit's trace runs that call at the caller's
own selection, so this is the same environment with the escape symbol resolved at
`esc` and nothing else differing.

A block that makes no escape call evaluates the same at either environment
(`evalInstr_esc_agree`), and a run of such a block is the same run
(`denoteCode_esc_of_free`): the phase's own blocks keep the traces they have at
`s1BlocksCalls`, and only the escape arm is stated here. -/

/-- The escape list's symbol, as the emitted body spells it. -/
def escapeListCallee : String := "leanllvm_json_escape_list"

/-- Whether an instruction calls the escape list. -/
def callsEscape : Instr → Bool
  | .call _ _ callee _ => decide (callee = escapeListCallee)
  | .callVoid callee _ => decide (callee = escapeListCallee)
  | _ => false

/-- The unit's environment with the escape list resolved at the caller's
selection. -/
def s1BlocksCallsEsc (esc : Calls) : Calls :=
  fun callee args mem next =>
    if callee = escapeListCallee then esc callee args mem next
    else s1BlocksCalls callee args mem next

/-- At the escape list's symbol the environment is the caller's selection. -/
theorem s1BlocksCallsEsc_escape (esc : Calls) (args : List Value) (mem : Mem) (next : Nat) :
    s1BlocksCallsEsc esc escapeListCallee args mem next = esc escapeListCallee args mem next := by
  simp only [s1BlocksCallsEsc, reduceIte]

/-- At any other symbol it is the unit's own environment. -/
theorem s1BlocksCallsEsc_other (esc : Calls) {callee : String}
    (h : callee ≠ escapeListCallee) (args : List Value) (mem : Mem) (next : Nat) :
    s1BlocksCallsEsc esc callee args mem next = s1BlocksCalls callee args mem next := by
  simp only [s1BlocksCallsEsc, ite_eq_right h]

/-- **An instruction that does not call the escape list evaluates the same at
either environment.**  The two environments agree on every other symbol, and the
call forms are the only arms that read the selection. -/
theorem evalInstr_esc_agree (esc : Calls) (s : State) (i : Instr)
    (h : callsEscape i = false) :
    evalInstr (s1BlocksCallsEsc esc) s i = evalInstr s1BlocksCalls s i := by
  cases i <;> simp_all [evalInstr, callsEscape, s1BlocksCallsEsc]

/-- **A run of a block that never calls the escape list is the same at either
environment.**  The leading `phi` run reads no call selection, and every other
instruction is the single step above. -/
theorem denoteRun_esc_of_free (esc : Calls) (pend : List (String × Value))
    (is : List Instr) (s : State) (h : ∀ i ∈ is, callsEscape i = false) :
    denoteRun (s1BlocksCallsEsc esc) pend is s = denoteRun s1BlocksCalls pend is s := by
  induction is generalizing pend s with
  | nil => rfl
  | cons i rest ih =>
      have hi : callsEscape i = false := h i (by simp)
      have hrest : ∀ j ∈ rest, callsEscape j = false := fun j hj => h j (by simp [hj])
      cases i <;>
        first
        | (simp only [denoteRun]
           cases phiSelect s _ with
           | none => rfl
           | some v => exact ih (pend ++ [(_, v)]) s hrest)
        | (rw [denoteRun_cons_of (calls := s1BlocksCallsEsc esc) (hi := by rfl),
              denoteRun_cons_of (calls := s1BlocksCalls) (hi := by rfl)]
           rw [evalInstr_esc_agree esc (s.bindAll pend) _ hi]
           cases evalInstr s1BlocksCalls (s.bindAll pend) _ with
           | none => rfl
           | some s' => exact ih [] s' hrest)

/-- The same at `denoteCode`, which is the empty pending run. -/
theorem denoteCode_esc_of_free (esc : Calls) (is : List Instr) (s : State)
    (h : ∀ i ∈ is, callsEscape i = false) :
    denoteCode (s1BlocksCallsEsc esc) is s = denoteCode s1BlocksCalls is s :=
  denoteRun_esc_of_free esc [] is s h

/-- **A block that never calls the escape list has the same control step at
either environment**, so a trace stated at the unit's environment is a trace at
the escape-parametric one. -/
theorem step_esc_of_free (esc : Calls) (f : Function) (s : State) (b : Block)
    (hfind : f.findBlock s.pc = some b) (h : ∀ i ∈ b.instrs, callsEscape i = false) :
    step (s1BlocksCallsEsc esc) f s = step s1BlocksCalls f s := by
  simp only [step, hfind, denoteCode_esc_of_free esc b.instrs s h]

/-! ### The reuse boundary

The mask unit's steps are stated at its own call environment; these lemmas move
one to this unit's without restating it. -/

/-- Whether evaluating an instruction consults the call environment.  Only the two
call forms do; every other arm of `evalInstr` computes from the state alone. -/
def callsInstr : Instr → Bool
  | .call _ _ _ _ => true
  | .callVoid _ _ => true
  | _ => false

/-- **Evaluation ignores the call environment** for an instruction that makes no
call: the two environments differ only in the `calls` argument, which no other
arm of `evalInstr` reads. -/
theorem evalInstr_calls_irrelevance (c₁ c₂ : Calls) (s : State) (i : Instr)
    (h : callsInstr i = false) : evalInstr c₁ s i = evalInstr c₂ s i := by
  cases i <;> simp_all [evalInstr, callsInstr]

/-- The two environment constructors are one: `withEnv` and `stateAt` both replace
the state's environment and carry every other field through. -/
theorem withEnv_eq_stateAt (env : Env) (s : State) : withEnv env s = stateAt env s := rfl

/-- **A mask-unit step at this unit's environment.**  An instruction that mentions
no call evaluates the same at `s1BlocksCalls`/`stateAt` as at
`s1Calls`/`withEnv`, so a step lemma stated at the mask unit's environment is this
unit's step. -/
theorem evalInstr_blocks_of_masks (env : Env) (s : State) (i : Instr)
    (h : callsInstr i = false) :
    evalInstr s1BlocksCalls (stateAt env s) i = evalInstr s1Calls (withEnv env s) i := by
  rw [← withEnv_eq_stateAt]
  exact evalInstr_calls_irrelevance _ _ _ _ h

/-- The same bridge with `withEnv` on both sides: a run that a mask-unit step has
already left in `withEnv` form continues at `s1BlocksCalls` the same way. -/
theorem evalInstr_blocks_of_masks_w (env : Env) (s : State) (i : Instr)
    (h : callsInstr i = false) :
    evalInstr s1BlocksCalls (withEnv env s) i = evalInstr s1Calls (withEnv env s) i := by
  rw [withEnv_eq_stateAt]
  exact evalInstr_blocks_of_masks env s i h

end LeanLLVM.Refinement.JsonS1BlocksSteps
