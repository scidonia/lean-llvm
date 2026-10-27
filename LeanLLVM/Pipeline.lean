/-
The shipped optimisation pipeline.

Constant propagation runs first, which makes branch conditions literal; branch
folding then removes the conditional edge.  Both passes are certified, so the
pipeline is certified by composition.
-/
import LeanLLVM.Transform.ConstantFold
import LeanLLVM.Transform.FoldBranches

namespace LeanLLVM

/-- The default pipeline, in execution order. -/
def defaultPipeline : List Pass := [constantPropagation, branchFolding]

/-- The composed pass. -/
def optimisationPipeline : Pass := Pass.pipeline defaultPipeline

theorem optimisationPipeline_sound : optimisationPipeline.Sound := by
  apply Pass.pipeline_sound
  intro p hp
  simp [defaultPipeline] at hp
  rcases hp with rfl | rfl
  · exact constantPropagation_sound
  · exact branchFolding_sound

def optimizeFunction (f : Function) : Function :=
  optimisationPipeline.run f

def optimizeModule (m : Module) : Module :=
  m.mapPass optimisationPipeline

end LeanLLVM
