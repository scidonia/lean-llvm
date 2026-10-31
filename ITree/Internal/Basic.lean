/-
Interaction trees: the coinductive carrier, its constructors, and the
destructor-based eliminator.

Adapted from `mit-plv/lean4-itree` at revision
`7f48fefaa2f12f599e6c4aa2be1ef39d5466122b` (`ITree/Basic.lean`), restricted to
the carrier, constructors and eliminator; the exact-equality relation `IEq` and
the monad instances are adapted in `ITree/IEq.lean` and `ITree/Monad.lean`, and
the delay object and effect algebra are local designs in `ITree/TauClosure.lean`
and `ITree/EffectAlgebra.lean`.  See `ITree/README.md` for provenance and
deviations.
-/
import ITree.Internal.PFunctor

-- The tree type and its namespace coincide (`ITree.ITree`), as the public API
-- requires; the duplicate-namespace linter has nothing to report here.
set_option linter.dupNamespace false

namespace ITree

open ITree.Internal

/-- The one-step shape of an interaction tree: a result, a silent step, or a
visible event with its response type. -/
inductive Shape.{u1, v, u2} (ε : Type u1 → Type v) (ρ : Type u2)
    : Type (max (max (u1 + 1) u2) v)
  | ret (v : ρ)
  | tau
  | vis (α : Type u1) (e : ε α)

/-- The arity of each shape: no children at a result, one after a silent step,
and the response type after a visible event. -/
def children.{u1, v, u2} {ε : Type u1 → Type v} {ρ : Type u2}
    : Shape ε ρ → Type u1
  | .ret _   => ULift (Fin2 0)
  | .tau     => ULift (Fin2 1)
  | .vis α _ => α

/-- The polynomial functor whose final coalgebra is the tree type. -/
def P.{u1, v, u2} (ε : Type u1 → Type v) (ρ : Type u2) : PFunctor :=
  ⟨Shape.{u1, v, u2} ε ρ, children.{u1, v, u2}⟩

/--
Coinductive interaction trees.  Written out, the shape is
```
coinductive ITree (ε : Type → Type) (ρ : Type)
| ret (v : ρ)
| tau (t : ITree ε ρ)
| vis {α : Type} (e : ε α) (k : α → ITree ε ρ)
```
-/
def ITree.{u1, v, u2} (ε : Type u1 → Type v) (ρ : Type u2) :=
  (P ε ρ).M

/-- A continuation from one response to a tree. -/
abbrev KTree.{u1, v, u2} (ε : Type u1 → Type v) (α : Type u1) (β : Type u2) :=
  α → ITree ε β

instance {ε ρ} : OfNat ((P ε ρ).B Shape.tau) 0 := ⟨.up <| .ofNat' 0⟩

section
variable {ε : Type u1 → Type v} {ρ : Type u2}

/-! ### Constructors -/

section
variable {X : Type u}

@[simp]
def ret' (v : ρ) : P ε ρ X :=
  .mk (.ret v) elim0

@[simp]
def tau' (t : X) : P ε ρ X :=
  .mk .tau (fin1Const t)

@[simp]
def vis' {α : Type u1} (e : ε α) (k : α → X) : P ε ρ X :=
  .mk (.vis α e) (k ·)

end

@[match_pattern, simp]
def ret (v : ρ) : ITree ε ρ :=
  .mk <| ret' v

@[match_pattern, simp]
def tau (t : ITree ε ρ) : ITree ε ρ :=
  .mk <| tau' t

/-- `n` silent steps in front of a tree. -/
def tauN (n : Nat) (t : ITree ε ρ) : ITree ε ρ :=
  match n with
  | 0     => t
  | n + 1 => tau (tauN n t)

@[match_pattern, simp]
def vis {α : Type u1} (e : ε α) (k : α → ITree ε ρ) : ITree ε ρ :=
  .mk <| vis' e k

/-- An event followed by returning its response. -/
def trigger {α : Type u1} (e : ε α) : ITree ε α :=
  vis e (λ x => ret x)

/-! ### Injectivity of the constructors -/

theorem ret_inj {x y} (h : @ret ε ρ x = ret y) : x = y := by
  simp only [ret, ret'] at h
  have := (Sigma.mk.inj (PFunctor.M.mk_inj h)).left
  exact Shape.ret.inj this

theorem vis_inj_α {ε α1 α2 ρ}
    {k1 : KTree ε α1 ρ} {k2 : KTree ε α2 ρ}
    {e1 : ε α1} {e2 : ε α2}
    (h : vis e1 k1 = vis e2 k2) : α1 = α2 := by
  simp only [vis, vis'] at h
  have := (Sigma.mk.inj (PFunctor.M.mk_inj h)).left
  exact (Shape.vis.inj this).left

theorem vis_inj {ε α ρ}
    {e1 e2 : ε α} {k1 k2 : KTree ε α ρ}
    (h : vis e1 k1 = vis e2 k2) : e1 = e2 ∧ k1 = k2 := by
  simp only [vis, vis'] at h
  have := Sigma.mk.inj (PFunctor.M.mk_inj h)
  apply And.intro
  · exact eq_of_heq (Shape.vis.inj this.left).right
  · have := eq_of_heq this.right
    funext x
    have := congr (a₁ := x) this rfl
    exact this

theorem tau_inj {ε ρ} {t1 t2 : ITree ε ρ} (h : tau t1 = tau t2) : t1 = t2 := by
  simp only [tau, tau'] at h
  have := eq_of_heq (Sigma.mk.inj (PFunctor.M.mk_inj h)).right
  exact fin1Const_inj this

/-- Dependent matching on a tree, driven by `dest` rather than by case analysis
on the coinductive value. -/
def dMatchOn {motive : ITree ε ρ → Sort u} (x : ITree ε ρ)
    (ret : (v : ρ) → x = ret v → motive x)
    (tau : (c : ITree ε ρ) → x = tau c → motive x)
    (vis : (α : Type u1) → (e : ε α) → (k : α → ITree ε ρ) → x = vis e k → motive x)
    : motive x :=
  match hm : x.dest with
  | ⟨.ret v, snd⟩ =>
    ret v (by
      rw [elim0_eq_all snd] at hm
      simp only [ITree.ret, ret']
      exact (PFunctor.M.mk_dest x).symm.trans (congrArg PFunctor.M.mk hm)
    )
  | ⟨.tau, c⟩ =>
    tau (c 0) (by
      simp only [ITree.tau, tau']
      trans
      symm; apply PFunctor.M.mk_dest
      congr
      rw [hm]
      congr
      symm; apply fin1Const_fin0
    )
  | ⟨.vis α e, k⟩ =>
    vis α e k (by
      simp only [ITree.vis, vis']
      exact (PFunctor.M.mk_dest x).symm.trans (congrArg PFunctor.M.mk hm)
    )

/-! ### Destructor equations -/

theorem dest_ret {v} : PFunctor.M.dest (F := P ε ρ) (ret v) = ⟨.ret v, elim0⟩ :=
  rfl

theorem dest_tau {t} : PFunctor.M.dest (F := P ε ρ) (tau t) = ⟨.tau, fin1Const t⟩ :=
  rfl

theorem dest_vis {ε α ρ} {e : ε α} {k : KTree ε α ρ}
    : PFunctor.M.dest (F := P ε ρ) (vis e k) = ⟨.vis _ e, k⟩ :=
  rfl

/-! ### Infinite silent steps -/

/-- The tree of infinitely many silent steps. -/
def infTau : ITree ε ρ :=
  PFunctor.M.corec' (fun rec x =>
    .inr <| tau' (rec x)
  ) ()

theorem infTau_eq : @infTau ε ρ = tau infTau := by
  conv =>
    lhs
    simp [infTau]
  rw [PFunctor.M.unfold_corec']
  simp only [tau, tau']
  congr; funext i
  match i with
  | 0 => rfl

end

end ITree
