/-
The transformation framework.

A pass is a function on functions together with a proof that it refines its
input.  Refinement is one-directional (`target ⊆ source`), so a pass may
remove behaviours — that is what an optimiser does — but may never add one.

Passes compose, and the composition is sound whenever each component is.
-/
import LeanLLVM.Semantics

namespace LeanLLVM

/-- A transformation of one function. -/
structure Pass where
  name : String
  run : Function → Function

/-- A pass is sound when its result refines its input. -/
def Pass.Sound (p : Pass) : Prop :=
  ∀ f, Refines (p.run f) f

theorem Refines.refl (f : Function) : Refines f f := fun _ _ h => h

theorem Refines.trans {a b c : Function} (hab : Refines a b) (hbc : Refines b c) :
    Refines a c :=
  fun args o h => hbc args o (hab args o h)

/-- A soundness proof from behavioural equivalence. -/
theorem Refines.of_iff {t s : Function} (h : ∀ args o, Beh t args o ↔ Beh s args o) :
    Refines t s :=
  fun args o ht => (h args o).mp ht

/-- Sequential composition: `p₁` then `p₂`. -/
def Pass.comp (p₁ p₂ : Pass) : Pass where
  name := p₁.name ++ "," ++ p₂.name
  run := fun f => p₂.run (p₁.run f)

theorem Pass.comp_sound {p₁ p₂ : Pass} (h₁ : p₁.Sound) (h₂ : p₂.Sound) :
    (p₁.comp p₂).Sound :=
  fun f => Refines.trans (h₂ (p₁.run f)) (h₁ f)

/-- The identity pass. -/
def Pass.id : Pass := ⟨"id", fun f => f⟩

theorem Pass.id_sound : Pass.id.Sound := fun f => Refines.refl f

/-- Apply a pipeline of passes in order. -/
def Pass.pipeline : List Pass → Pass
  | [] => Pass.id
  | p :: ps => p.comp (Pass.pipeline ps)

theorem Pass.pipeline_sound (ps : List Pass) (h : ∀ p ∈ ps, p.Sound) :
    (Pass.pipeline ps).Sound := by
  induction ps with
  | nil => exact Pass.id_sound
  | cons p ps ih =>
      exact Pass.comp_sound (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

/-- Block lookup commutes with a name-preserving map. -/
theorem findBlockList_map {g : Block → Block} (hname : ∀ b, (g b).name = b.name) :
    ∀ (bs : List Block) (pc : String),
      findBlockList (bs.map g) pc = (findBlockList bs pc).map g
  | [], _ => rfl
  | b :: bs, pc => by
      simp only [List.map_cons, findBlockList]
      rw [hname b]
      split
      · rfl
      · exact findBlockList_map hname bs pc

/-- Unfolding lemma for `runFuel` at a successor. -/
theorem runFuel_succ (n : Nat) (f : Function) (s : State) :
    runFuel (n + 1) f s =
      (match step f s with
       | .ub => some .ub
       | .ret v s' => some (.ret v s'.mem)
       | .jump s' => runFuel n f s') := rfl

/-- Apply a pass to every function of a module. -/
def Module.mapPass (p : Pass) (m : Module) : Module :=
  { m with functions := m.functions.map p.run }

end LeanLLVM
