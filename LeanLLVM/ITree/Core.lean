/-
The public interaction-tree API.

Clients of this library construct and observe trees through `Tree`, `ret`,
`tau`, `vis` and `dMatchOn`; they never mention `PFunctor.M`, `MIntl` or
`CofixA`.  The coinductive encoding lives in `Internal.Basic` and the mathlib
dependency it needs in `Internal.PFunctor`.

The library is adapted from `mit-plv/lean4-itree`; provenance and deviations
are recorded in `LeanLLVM/ITree/README.md`.
-/
import LeanLLVM.ITree.Internal.Basic

namespace LeanLLVM.ITree
namespace ITree

open LeanLLVM.ITree.Internal

/-- The public tree type. -/
abbrev Tree (ε : Type → Type) (ρ : Type) := ITree ε ρ

section
variable {ε : Type → Type} {ρ : Type}

/-! ### Distinct constructors

The three shapes are disjoint, which is what lets a relation's terminal cases
reject a tree of a different shape without unfolding the coinductive encoding.
-/

theorem ret_ne_tau {v : ρ} {t : ITree ε ρ} : (ret v : ITree ε ρ) ≠ tau t := by
  intro h
  have hs := (Sigma.mk.inj (PFunctor.M.mk_inj h)).left
  cases hs

theorem ret_ne_vis {v : ρ} {α : Type} (e : ε α) (k : α → ITree ε ρ) :
    (ret v : ITree ε ρ) ≠ vis e k := by
  intro h
  have hs := (Sigma.mk.inj (PFunctor.M.mk_inj h)).left
  cases hs

theorem tau_ne_vis {t : ITree ε ρ} {α : Type} (e : ε α) (k : α → ITree ε ρ) :
    (tau t : ITree ε ρ) ≠ vis e k := by
  intro h
  have hs := (Sigma.mk.inj (PFunctor.M.mk_inj h)).left
  cases hs

/-- Trees whose visible events have different response types are different:
the response type is part of the shape. -/
theorem vis_ne_of_type_ne {α β : Type} {e : ε α} {e' : ε β}
    {k : α → ITree ε ρ} {k' : β → ITree ε ρ} (h : α ≠ β) :
    (vis e k : ITree ε ρ) ≠ vis e' k' := by
  intro heq
  exact h (vis_inj_α heq)

end

end ITree
end LeanLLVM.ITree
