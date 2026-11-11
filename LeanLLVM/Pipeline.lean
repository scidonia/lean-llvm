/-
The shipped optimisation pipeline.

Constant propagation runs first, which makes branch conditions literal; branch
folding then removes the conditional edge; strength reduction turns
multiplication by the literal `2` into a shift.  All three passes are certified,
so the pipeline is certified by composition.
-/
import LeanLLVM.Transform.ConstantFold
import LeanLLVM.Transform.FoldBranches
import LeanLLVM.Transform.StrengthReduce

namespace LeanLLVM

/-- The default pipeline, in execution order. -/
def defaultPipeline : List Pass := [constantPropagation, branchFolding, strengthReduction]

/-- The composed pass. -/
def optimisationPipeline : Pass := Pass.pipeline defaultPipeline

theorem optimisationPipeline_sound : optimisationPipeline.Sound := by
  apply Pass.pipeline_sound
  intro p hp
  simp [defaultPipeline] at hp
  rcases hp with rfl | rfl | rfl
  · exact constantPropagation_sound
  · exact branchFolding_sound
  · exact strengthReduction_sound

/-! ### Completion as a separate conjunct of the pass claim

`Pass.Sound` is behaviour inclusion and nothing more.  By `Refines`'s definition
a pass whose output never terminates is sound, because the output produces no
behaviour to include: the vacuity is the target-side one `Refinement.Relation`
exhibits.  The certificate below adds the conjunct a replacement needs — the
output reaches a defined return at the declared step count whenever the input
does — as a **separate** claim rather than by changing `Refines`.

Keeping it separate is what preserves the relation's use: `Refines.refl` would
fail if completion were folded into it, since a function need not terminate, and
every existing soundness proof would have to be restated.  `Pass.Sound` keeps its
meaning; `Pass.SoundCompleting` is the claim a candidate that loops forever
fails.

The budget is a completion witness: the number of control steps at which the
output's run is counted down to its return, not a performance bound.
-/

/-- A pass preserves completion: at every declared step count, if the input's
run reaches a defined return then so does the output's, at the same count. -/
def Pass.PreservesCompletion (p : Pass) : Prop :=
  ∀ (calls : Calls) (budget : List Value → Nat) (f : Function) (args : List Value),
    (∃ v m, runFuel calls (budget args) f (initState f args) = some (.ret v m)) →
    ∃ v m, runFuel calls (budget args) (p.run f) (initState (p.run f) args)
      = some (.ret v m)

/-- The pass claim with completion: soundness and completion preservation. -/
def Pass.SoundCompleting (p : Pass) : Prop := p.Sound ∧ p.PreservesCompletion

theorem Pass.id_preservesCompletion : Pass.id.PreservesCompletion := by
  intro calls budget f args h
  simpa [Pass.id] using h

theorem Pass.comp_preservesCompletion {p₁ p₂ : Pass}
    (h₁ : p₁.PreservesCompletion) (h₂ : p₂.PreservesCompletion) :
    (p₁.comp p₂).PreservesCompletion := by
  intro calls budget f args h
  exact h₂ calls budget (p₁.run f) args (h₁ calls budget f args h)

theorem Pass.pipeline_preservesCompletion (ps : List Pass)
    (h : ∀ p ∈ ps, p.PreservesCompletion) :
    (Pass.pipeline ps).PreservesCompletion := by
  induction ps with
  | nil => exact Pass.id_preservesCompletion
  | cons p ps ih =>
      exact Pass.comp_preservesCompletion (h p (by simp))
        (ih (fun q hq => h q (by simp [hq])))

theorem Pass.id_soundCompleting : Pass.id.SoundCompleting :=
  ⟨Pass.id_sound, Pass.id_preservesCompletion⟩

theorem Pass.comp_soundCompleting {p₁ p₂ : Pass}
    (h₁ : p₁.SoundCompleting) (h₂ : p₂.SoundCompleting) :
    (p₁.comp p₂).SoundCompleting :=
  ⟨Pass.comp_sound h₁.1 h₂.1, Pass.comp_preservesCompletion h₁.2 h₂.2⟩

theorem Pass.pipeline_soundCompleting (ps : List Pass)
    (h : ∀ p ∈ ps, p.SoundCompleting) :
    (Pass.pipeline ps).SoundCompleting :=
  ⟨Pass.pipeline_sound ps (fun p hp => (h p hp).1),
   Pass.pipeline_preservesCompletion ps (fun p hp => (h p hp).2)⟩

theorem constantPropagation_preservesCompletion :
    constantPropagation.PreservesCompletion := by
  intro calls budget f args h
  obtain ⟨v, m, hrun⟩ := h
  exact ⟨v, m, by
    simpa only [constantPropagation, initState_foldConstants, runFuel_foldConstants] using hrun⟩

theorem branchFolding_preservesCompletion :
    branchFolding.PreservesCompletion := by
  intro calls budget f args h
  obtain ⟨v, m, hrun⟩ := h
  exact ⟨v, m, by
    simpa only [branchFolding, initState_foldBranches, runFuel_foldBranches] using hrun⟩

theorem strengthReduction_preservesCompletion :
    strengthReduction.PreservesCompletion := by
  intro calls budget f args h
  obtain ⟨v, m, hrun⟩ := h
  exact ⟨v, m, by
    simpa only [strengthReduction, initState_strengthReduce, runFuel_strengthReduce] using hrun⟩

theorem optimisationPipeline_preservesCompletion :
    optimisationPipeline.PreservesCompletion := by
  apply Pass.pipeline_preservesCompletion
  intro p hp
  simp [defaultPipeline] at hp
  rcases hp with rfl | rfl | rfl
  · exact constantPropagation_preservesCompletion
  · exact branchFolding_preservesCompletion
  · exact strengthReduction_preservesCompletion

/-- The shipped pipeline's claim, with completion as the second conjunct. -/
theorem optimisationPipeline_soundCompleting :
    optimisationPipeline.SoundCompleting :=
  ⟨optimisationPipeline_sound, optimisationPipeline_preservesCompletion⟩

def optimizeFunction (f : Function) : Function :=
  optimisationPipeline.run f

def optimizeModule (m : Module) : Module :=
  m.mapPass optimisationPipeline

end LeanLLVM
