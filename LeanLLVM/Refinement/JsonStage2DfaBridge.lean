/-
The pipeline's stage-2 selection over an arbitrary body.

`satisfies_calls_stage2_fixed` (`JsonStage2WalkFlushPost`) turns a walk's
`Satisfies` at `Γ_stage2work` into the call-site guarantee the pipeline asks
for, but it names `stage2Body` in three places: the call environment, the
body's rets-valued fact, and the `Γ_stage2work` instantiation.  This module
states the same two lemmas with the body as a parameter:

* `envForStage2WorkOf body tab sub` — the selection's environment, whose callee
  runs `body` at the workspace's eight addresses;
* `satisfies_calls_stage2_fixed_of_body` — the call-site guarantee from
  `Satisfies (JsonStage2IR.stage2Calls sub) body (Γ_stage2work …)` and `retsValued body`;
* `pipeline_satisfies_at_stage2_of_body` — the pipeline's member swap, at
  `pipelineCalls`, `Γ_pipeline_units` and `pipelineBody`, with the tail still
  `pipelineBodyFacts_of_exitStage2`.

Instantiating `body := stage2Body` and `sub := stage2SubCalls` is the certified
theorem; the DFA's obligation is exactly the `hwalk` premise at its own body
fixture.  Nothing here changes `Γ_pipeline_units`, `pipelineUnitsPost` or
`routePost`.
-/
import LeanLLVM.Refinement.PipelineDischarge

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonPipelineIR
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- The stage-2 record at the pipeline's workspace, named once. -/
def stage2WorkRec (tab : Nat) : MemContract :=
  Γ_stage2work (stage2WorkD tab) (stage2WorkC tab) (stage2WorkCtype tab)
    (stage2WorkCst tab) (stage2WorkTok tab) (stage2WorkS tab)
    (stage2WorkZ tab) (stage2WorkE tab)

/-- The pipeline's stage-2 selection for an arbitrary body: the ABI's thirteen
arguments are appended with the workspace's eight pointers and the callee runs
`body` at `Γ_stage2work` there. -/
def envForStage2WorkOf (body : Function) (tab : Nat) (sub : Calls) : Calls :=
  fun callee args mem next =>
    envForUnit "leanllvm_json_stage2" (stage2WorkRec tab)
      (JsonStage2IR.stage2Calls sub) body callee
      (JsonStage2IR.stage2Args args (stage2WorkD tab) (stage2WorkC tab) (stage2WorkCtype tab)
        (stage2WorkCst tab) (stage2WorkTok tab) (stage2WorkS tab)
        (stage2WorkZ tab) (stage2WorkE tab)) mem next

/-- **An arbitrary stage-2 body resolves at the fixed record.**  This is
`satisfies_calls_stage2_fixed` with `stage2Body` replaced by the parameter and
`stage2Body_retsValued` by the caller's `retsValued` fact. -/
theorem satisfies_calls_stage2_fixed_of_body {body : Function} {tab : Nat}
    {sub : Calls} (hrets : retsValued body = true)
    (hwalk : Satisfies (JsonStage2IR.stage2Calls sub) body (stage2WorkRec tab)) :
    CallSatisfies (envForStage2WorkOf body tab sub) (Γ_stage2fixed tab)
      "leanllvm_json_stage2" := by
  intro args mem next hpre
  obtain ⟨nkSlot, nxpSlot, hpre13, hstaged⟩ := hpre
  have hlen : args.length = 13 := JsonStage2IR.stage2Pre_length hpre13
  have htake : (JsonStage2IR.stage2Args args (stage2WorkD tab) (stage2WorkC tab)
      (stage2WorkCtype tab) (stage2WorkCst tab) (stage2WorkTok tab)
      (stage2WorkS tab) (stage2WorkZ tab) (stage2WorkE tab)).take 13 = args :=
    JsonStage2IR.stage2Args_take13 args hlen (stage2WorkD tab) (stage2WorkC tab)
      (stage2WorkCtype tab) (stage2WorkCst tab) (stage2WorkTok tab)
      (stage2WorkS tab) (stage2WorkZ tab) (stage2WorkE tab)
  have hpreW : (stage2WorkRec tab).pre
      (JsonStage2IR.stage2Args args (stage2WorkD tab) (stage2WorkC tab) (stage2WorkCtype tab)
        (stage2WorkCst tab) (stage2WorkTok tab) (stage2WorkS tab)
        (stage2WorkZ tab) (stage2WorkE tab)) mem next :=
    ⟨args, nkSlot, nxpSlot, rfl, hpre13, hstaged⟩
  obtain ⟨hcom, hpost⟩ := hwalk _ _ _ hpreW
  obtain ⟨v, m, hrun⟩ := hcom
  have hsome : v.isSome := ret_some_of_retsValued hrets hrun
  cases v with
  | none => simp at hsome
  | some v' =>
      refine ⟨{ ret := v', mem := m, next := next + 0 }, ?_, ?_, ?_⟩
      · simp only [envForStage2WorkOf, envForUnit, hrun, ↓reduceIte]
      · have h := hpost (.ret (some v') m) (Or.inr ⟨_, hrun⟩)
        simpa only [Γ_stage2fixed, stage2WorkRec, Γ_stage2work, htake] using h
      · exact Nat.le_refl _

end WalkScope

open WalkScope

/-- **The pipeline satisfies its unit record with an arbitrary stage-2 body.**
The member swap keeps `pipelineCalls`, `Γ_pipeline_units` and `pipelineBody`;
the stage-2 slot is the only thing the body changes, and its call-site guarantee
is `satisfies_calls_stage2_fixed_of_body`. -/
theorem pipeline_satisfies_at_stage2_of_body (tab : Nat) (body : Function)
    (hrets : retsValued body = true) {sub : Calls}
    (hwalk : Satisfies (JsonStage2IR.stage2Calls sub) body (stage2WorkRec tab)) :
    ∀ base, Satisfies
      (pipelineCalls tab base (envForStage2WorkOf body tab sub))
      pipelineBody (Γ_pipeline_units tab base) := by
  refine pipeline_satisfies_of_units tab (envForStage2WorkOf body tab sub)
    (Γ_stage2fixed tab)
    (fun b => pipelineUnits_of_records tab b (envForStage2WorkOf body tab sub)
      (Γ_stage2fixed tab)
      (satisfies_calls_stage2_fixed_of_body hrets hwalk)
      (stage2fixed_verdict_bounded (tab := tab))) ?_
  intro base args mem next hpre units
  exact pipelineBodyFacts_of_exitStage2 hpre.1 hpre.2.1 hpre.2.2 units

end LeanLLVM.Refinement
