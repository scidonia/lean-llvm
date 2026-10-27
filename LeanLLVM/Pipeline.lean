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

def optimizeFunction (f : Function) : Function :=
  optimisationPipeline.run f

def optimizeModule (m : Module) : Module :=
  m.mapPass optimisationPipeline

end LeanLLVM
