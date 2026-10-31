/-
The exact-equality relation on interaction trees.

`IEq` is coinductive and shape-by-shape: two trees are related when their
constructors agree, a `tau` is related only to a `tau`, and visible events agree
with pointwise-related continuations.  A `tau` is therefore never related to the
tree behind it — this is not the silent-step closure, and erasing a silent step
is not a use of this relation.

`ieq_iff_eq` identifies `IEq` with strict equality.  That is what lets the monad
laws of `ITree/Monad.lean` be equations about trees rather than equations about
a coarser equivalence: a law proved through `IEq` is a law at `Eq`.

Adapted from `mit-plv/lean4-itree` at revision
`7f48fefaa2f12f599e6c4aa2be1ef39d5466122b` (`ITree/Basic.lean`, the `IEqF`/
`IEq` definitions and the `ieq_iff_eq` argument); see `ITree/README.md` for
provenance and deviations.
-/
import ITree.Core
import ITree.Coinduction

namespace ITree

open ITree.Internal

universe u1 v u2

section
variable {ε : Type u1 → Type v} {ρ : Type u2}

/-! ### Tactics for the constructor shapes

These are the small proof helpers upstream defines beside its constructors; the
equality proofs below use them. -/

macro "simp_itree_basic" : tactic => `(tactic|(
  simp only [
    ret', vis', tau',
    ret , vis , tau ,
    PFunctor.M.dest_mk
  ]
))

macro "subst_itree_inj " h:term : tactic => `(tactic|(
  first
  | have hv := ret_inj $h
    subst hv
  | have ht := tau_inj $h
    subst ht
  | have hα := vis_inj_α $h
    subst hα
    have ⟨he, hk⟩ := vis_inj $h
    subst he hk
))

/-- Close a goal from an equation between trees of incompatible shapes. -/
macro "itree_elim " h:term : tactic => `(tactic|(
  try (have := (Sigma.mk.inj (PFunctor.M.mk_inj $h)).left; contradiction)
))

/-! ### The one-step functional and its monotonicity -/

/-- One unfolding of exact tree equality: matching result, matching `tau`, or the
same visible event with pointwise-related continuations. -/
@[grind]
inductive IEqF (sim : ITree ε ρ → ITree ε ρ → Prop) : ITree ε ρ → ITree ε ρ → Prop where
  | ret (v : ρ) : IEqF sim (ret v) (ret v)
  | vis {α : Type u1} (e : ε α) (k1 k2 : α → ITree ε ρ)
      (h : ∀ a : α, sim (k1 a) (k2 a)) : IEqF sim (vis e k1) (vis e k2)
  | tau (t1 t2 : ITree ε ρ) (h : sim t1 t2) : IEqF sim (tau t1) (tau t2)

/-- Inversion of one unfolding. -/
theorem IEqF_inv (sim : ITree ε ρ → ITree ε ρ → Prop) {t1 t2 : ITree ε ρ}
    (h : IEqF sim t1 t2) :
    (∃ v, t1 = ret v ∧ t2 = ret v) ∨
    (∃ (α : Type u1) (e : ε α) (k1 k2 : α → ITree ε ρ),
      (∀ a : α, sim (k1 a) (k2 a)) ∧ t1 = vis e k1 ∧ t2 = vis e k2) ∨
    (∃ t1' t2', sim t1' t2' ∧ t1 = tau t1' ∧ t2 = tau t2') := by
  cases h with
  | ret v => exact Or.inl ⟨v, rfl, rfl⟩
  | vis e k1 k2 hs => exact Or.inr (Or.inl ⟨_, e, k1, k2, hs, rfl, rfl⟩)
  | tau t1 t2 hs => exact Or.inr (Or.inr ⟨t1, t2, hs, rfl, rfl⟩)

/-- `IEqF` is monotone in its relation argument. -/
theorem IEqF_monotone (sim sim' : ITree ε ρ → ITree ε ρ → Prop)
    (hsim : ∀ (t1 t2 : ITree ε ρ), sim t1 t2 → sim' t1 t2) :
    ∀ t1 t2, IEqF sim t1 t2 → IEqF sim' t1 t2 := by
  intro t1 t2 h
  cases h with
  | ret v => exact IEqF.ret v
  | vis e k1 k2 hs => exact IEqF.vis e k1 k2 (fun a => hsim _ _ (hs a))
  | tau t1 t2 hs => exact IEqF.tau t1 t2 (hsim _ _ hs)

/-! ### The relation -/

/-- Exact equality of interaction trees, as a coinductive relation. -/
def IEq (t1 t2 : ITree ε ρ) : Prop :=
  IEqF IEq t1 t2
  coinductive_fixpoint monotonicity fun sim' sim hsim =>
    IEqF_monotone sim sim' hsim

/-- One unfolding of `IEq`, read off its coinductive defining equation. -/
theorem IEq.unfold (t1 t2 : ITree ε ρ) : IEq t1 t2 ↔ IEqF IEq t1 t2 :=
  (IEq.eq_1 t1 t2).to_iff

/-- Coinduction: a relation contained in its own `IEqF` unfolding is contained
in `IEq`. -/
theorem IEq.coind (pred : ITree ε ρ → ITree ε ρ → Prop)
    (h : ∀ t1 t2, pred t1 t2 → IEqF pred t1 t2) :
    ∀ t1 t2, pred t1 t2 → IEq t1 t2 :=
  IEq.coinduct pred h

/-- `IEqF` holds reflexively for any relation that does. -/
theorem IEqF_refl {sim : ITree ε ρ → ITree ε ρ → Prop} (h : ∀ t, sim t t)
    (t : ITree ε ρ) : IEqF sim t t := by
  apply dMatchOn (x := t)
  · intro v heq
    rw [heq]; exact IEqF.ret v
  · intro c heq
    rw [heq]; exact IEqF.tau c c (h c)
  · intro α e k heq
    rw [heq]; exact IEqF.vis e k k (fun a => h (k a))

/-- A tree is `IEq`-related to itself. -/
theorem ieq_refl (t : ITree ε ρ) : IEq t t :=
  IEq.coind Eq (fun t1 _ h => by subst h; exact IEqF_refl (fun _ => rfl) t1) t t rfl

/-! ### Exactness

Because `IEq` compares constructors one at a time, it is exactly equality: the
two directions are a bisimulation and a reflexive coinduction.  This is the
lemma that keeps every later law an equation. -/

theorem ieq_iff_eq (t1 t2 : ITree ε ρ) : IEq t1 t2 ↔ t1 = t2 := by
  constructor
  · intro h
    refine PFunctor.M.bisim (fun t1 t2 => IEq t1 t2) ?_ t1 t2 h
    intro x y hxy
    rcases IEqF_inv IEq ((IEq.unfold x y).mp hxy) with
      ⟨v, rfl, rfl⟩ | ⟨α, e, k1, k2, hs, rfl, rfl⟩ | ⟨x', y', hs, rfl, rfl⟩
    · refine ⟨Shape.ret v, elim0, elim0, ?_, ?_, ?_⟩
      · exact dest_ret
      · exact dest_ret
      · intro i; exact elim0 i
    · refine ⟨Shape.vis α e, k1, k2, ?_, ?_, ?_⟩
      · exact dest_vis
      · exact dest_vis
      · exact hs
    · refine ⟨Shape.tau, fin1Const x', fin1Const y', ?_, ?_, ?_⟩
      · exact dest_tau
      · exact dest_tau
      · intro i
        match i with
        | .up (.ofNat' 0) => exact hs
  · intro h
    subst h
    exact ieq_refl t1

/-- `IEq` is symmetric. -/
theorem ieq_symm {t1 t2 : ITree ε ρ} (h : IEq t1 t2) : IEq t2 t1 := by
  rw [ieq_iff_eq] at h ⊢
  exact h.symm

/-- `IEq` is transitive. -/
theorem ieq_trans {t1 t2 t3 : ITree ε ρ} (h1 : IEq t1 t2) (h2 : IEq t2 t3) :
    IEq t1 t3 := by
  rw [ieq_iff_eq] at h1 h2 ⊢
  exact h1.trans h2

/-- Strict equality implies `IEq`. -/
theorem ieq_of_eq {t1 t2 : ITree ε ρ} (h : t1 = t2) : IEq t1 t2 := by
  rw [ieq_iff_eq]; exact h

/-- `IEqF` holds reflexively for any relation that contains `IEq`.  This is the
lemma the coinductive law proofs use to close a branch in which both sides have
become the same tree. -/
theorem ieq_rfl {sim : ITree ε ρ → ITree ε ρ → Prop}
    (hsim : ∀ t1 t2, IEq t1 t2 → sim t1 t2) (t : ITree ε ρ) : IEqF sim t t :=
  IEqF_monotone IEq sim hsim t t ((IEq.unfold t t).mp (ieq_refl t))

end

end ITree
