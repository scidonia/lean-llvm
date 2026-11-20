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
`s1Calls`), the ASCII probe's 256-bit zero test, and the carry-less product at
immediate zero.  It does not bind the escape list, whose calls write the caller's
`xp` and count slot; a trace that runs those carries its own footprint.  Nor does
it bind the fused loop's `llvm.usub.sat.v32i8`: that arm belongs to the fused
DFA's environment, and an unbound symbol stays `ub` rather than being read as
something it is not.
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

/-- The unit's call environment: the mask unit's two intrinsics, and the ASCII
probe's 256-bit zero test. -/
def s1BlocksCalls : Calls :=
  fun callee args mem next =>
    match callee, args with
    | "llvm.x86.avx.ptestz.256", [.vec 4 64 a, .vec 4 64 b] =>
        some { ret := .int 32 (ptestz (BitVec.ofNat 256 (packLanes a))
              (BitVec.ofNat 256 (packLanes b))), mem := mem, next := next }
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

/-- **The footprint of the three intrinsic arms is empty.**  Each is a register
operation on its operands, so no address the caller holds moves across one of
these calls.

This is the footprint of `s1BlocksCalls` only.  The unit's two
`leanllvm_json_escape_list` calls write `xp` and the count slot, and they are not
in this environment; their footprint is the escape environment's, which is what
`s1BlocksPost`'s `UnchangedOutside` list records.  A trace that runs those calls
therefore has to carry its own footprint, and this definition is not one. -/
def s1BlocksCallsFootprint : CallsFootprint s1BlocksCalls :=
  CallsFootprint.pure s1BlocksCalls (by
    intro sym args mem next r h
    simp only [s1BlocksCalls] at h
    repeat' split at h
    all_goals (try (simp only [s1Calls] at h))
    all_goals (try (repeat' split at h))
    all_goals (try (cases h))
    all_goals rfl)

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
