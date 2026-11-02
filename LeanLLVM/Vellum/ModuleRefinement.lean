/-
Contextual replacement across two call environments.

`Frames.RefinesWithin` compares a target and a source under a single `Calls`, so
it cannot say what a module replacement says: the same caller text observed
under two different selections of an external body.  This module states that
relation — `RefinesWithinAcross` — and proves it composed from the directional
environment relation `CallRefines`: replacing the external call environment
preserves the caller's behaviour at the framed relation.

`Calls` now carries a memory channel — an entry returns the value, the memory
and the allocator state the callee leaves behind — so a call's result includes
the memory the caller adopts, and a callee that writes is inside the model.
`CallRefines` demands *complete* agreement of the two outcomes, memory and
allocator included, so for that hypothesis the two runs agree on memory exactly
as they agree on value, and this module's statements hold at every frame.  The
conclusion is a directed inclusion, not an equality of behaviours:
`Beh_calls_refines` matches each target outcome with the same source outcome,
and the source may also exhibit outcomes (such as `ub`) that the target does
not.  The frame is carried because the memory-effectful form of the relation —
one that permits the callee's memory to differ inside the footprint — needs it;
the load-bearing hypothesis here is the environment relation, and the negative
controls in `LeanLLVMTest/Vellum.lean` show that it can fail and that the
conclusion fails with it.
-/
import LeanLLVM.Semantics
import LeanLLVM.Frames
import LeanLLVM.CallRefinement
import LeanLLVM.Vellum.SeamContext
import LeanLLVM.Vellum.CommaMaskLoop

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.Vellum.SeamContext   -- envFor, seamSymbol, callerFunction, caller_beh
open LeanLLVM.Vellum.CommaMaskLoop -- loopFunction, candidateFunction, loop_returns_spec
open LeanLLVM.Vellum.CommaMaskIR   -- candidate_beh_int

/-! ### The two-environment relation -/

/-- Framed refinement across *two* call environments: `target` under `calls'`
is matched by `source` under `calls`, outside `frame`.  This is the relation
`RefinesWithin` would be if it took two environments; it is what a module
replacement actually compares. -/
def RefinesWithinAcross (calls' calls : Calls) (target source : Function)
    (frame : Nat → Prop) : Prop :=
  BehsWithin (Beh calls' target) (Beh calls source) frame

/-- `replaceFunction_sound`.  Replacing the seam — a change of call
environment, not of the caller's text — preserves the caller's behaviour, at
the framed relation, under the directional environment refinement `h`.  `h` is
the load-bearing hypothesis: the conclusion relates `calls'` to `calls`, and
fails when `h` fails (the adversarial example in `LeanLLVMTest/Vellum.lean`).
`CallRefines` demands complete agreement of the returned outcome, memory and
allocator included, so the matched outcomes carry the same memory and the frame
in the conclusion is inert for this hypothesis. -/
theorem replaceFunction_sound
    {calls' calls : Calls} {C : Function} {frame : Nat → Prop}
    (h : ∀ sym, CallRefines calls' calls sym) :
    RefinesWithinAcross calls' calls C C frame :=
  fun args o ho => ⟨o, Beh_calls_refines h C args o ho, Outcome.agreesOutside_refl o frame⟩

/-! ### A caller with its own footprint -/

/-- A caller with its own scratch local: allocate one `i64`, call the seam,
store the result, load it back, return it.  The `alloca` and the `store` are the
caller's own memory effects, so the caller has a footprint of its own to name.
The two selections it is compared under return the caller's memory unchanged, so
the callee's memory here is the caller's own; a callee that writes inside this
footprint is what the memory-effectful form of the relation exists to permit. -/
def memCaller : Function :=
  { name := "leanllvm_mem_caller", retTy := .int 64, params := [("%arg", .int 64)],
    blocks := [
      { name := "entry",
        instrs := [
          .alloca "%buf" (.int 64) 8,
          .call "%r" (.int 64) seamSymbol [(.int 64, .reg "%arg")],
          .store (.int 64) (.reg "%r") (.reg "%buf"),
          .load "%out" (.int 64) (.reg "%buf") ],
        term := .ret (.int 64) (some (.reg "%out")) } ] }

/-- The caller's footprint: the one `i64` local its `alloca` hands out, from the
reserved address `1`.  Read off the allocator it is
`AllocFrame (initState memCaller args) s₁ = Band 1 9`: `initState` starts the
allocator at address `1`, and the `alloca` of an `i64` advances it by eight
bytes, so the state after the entry block's instructions allocates exactly
`[1, 9)`.  As `loopFrame_eq` does for the loop, the band is written as the
computed value rather than kept as an `AllocFrame` expression. -/
def callerFrame : Nat → Prop := Band 1 9

/-! ### The two seam selections -/

-- Value-level justification of the environments (the frame is inert here; see
-- the module header):
--   loop_returns_spec  (`CommaMaskLoop`): the loop body returns `spec x`.
--   candidate_beh_int  (`CommaMaskIR`): the candidate returns `byteLoop x`.
--   byteLoop_eq_spec   (`CommaMaskKernel`): `byteLoop x = spec x`.
/-- The two seam selections are pointwise-related environments: the loop's
selection (`spec`) and the candidate's (`byteLoop`) agree because their values
agree, and both leave the caller's memory and allocator untouched. -/
theorem loop_seam_callRefines :
    ∀ sym, CallRefines (envFor spec) (envFor byteLoop) sym := by
  intro sym args mem next
  right
  by_cases h : sym = seamSymbol
  · subst h
    cases args with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | cons b rest => simp [envFor]
      | nil =>
        cases a with
        | int w x =>
          by_cases hw : w = 64
          · subst hw
            simp [envFor, (byteLoop_eq_spec x).symm]
          · simp [envFor, hw]
        | ptr a => simp [envFor]
  · simp [envFor, h]

/-- The contextual replacement: the caller under the memory-backed loop's
selection refines the caller under the unrolled candidate's selection, at the
caller's own footprint.  Because `envFor spec = envFor byteLoop` follows from
`byteLoop_eq_spec`, this instance's `h` is a value equality and its conclusion
follows by reflexivity (through `replaceFunction_sound`); the load-bearing
witness for the general theorem is the negative control
`caller_not_refined_by_undefined_env` in `LeanLLVMTest/Vellum.lean`, not this
instance.  The instance is stated because it records the value-level content of
the two selections (`loop_returns_spec`, `candidate_beh_int`) and gives the
milestone a caller with a footprint of its own. -/
theorem memCaller_replaces_loop :
    RefinesWithinAcross (envFor spec) (envFor byteLoop) memCaller memCaller callerFrame :=
  replaceFunction_sound loop_seam_callRefines

end LeanLLVM.Vellum
