/-
A one-step effect handler and its interpreter.

A `Handler ε δ σ` decides, for one source event `ε α` and the current state `σ`,
either to answer the event privately — returning the response and a new state,
which the interpreter performs as a silent step — or to re-emit exactly one
observable event `δ β`, whose response is mapped back to a response for the
source event together with a new state.

`interp h finish m t` is the tree obtained by running that decision procedure
over `t` from state `m`; a returned `r` becomes `ret (finish r m)`, which is how
the handler's final state reaches the leaves.

Two limits belong to this API rather than to a future effect algebra:

* the handler is **one step**: a single source event produces either silence or
  one observable event, never a tree of them;
* this is **not** `ITree.EffectAlgebra.interp`, the tree-valued interpreter in
  this same library (nor upstream's `iter`-based one): that interpreter runs a
  handler *tree* against the source continuation, has its own five laws, and is
  a different function from this computable one-step fold.  See
  `ITree/README.md` for the two interpreters.

`interp` itself is computable: the whole decision is the handler's, and the
coiteration below is `PFunctor.M.corec'` over the source's destructor.
-/
import ITree.Core

namespace ITree
namespace Effect

open ITree.Internal

universe u v w u₂

/-- One step of an event handler.  The state is threaded explicitly; the left
branch answers the event privately, and the right branch re-emits one observable
event and maps its response back to a source response and a new state. -/
abbrev Handler (ε : Type u → Type v) (δ : Type u → Type v) (σ : Type w) :=
  ∀ {α : Type u}, σ → ε α → Sum (α × σ) (Σ β : Type u, δ β × (β → α × σ))

/-- The coiteration step of `interp`: the source tree is destructed, and each
constructor becomes the corresponding constructor of the interpreted tree. -/
def step {ε : Type u → Type v} {δ : Type u → Type v} {σ : Type w}
    {ρ : Type u₂} {γ : Type u₂}
    (h : Handler ε δ σ) (finish : ρ → σ → γ) {X : Type _}
    (rec : σ × ITree ε ρ → X) : σ × ITree ε ρ → (P δ γ).M ⊕ P δ γ X :=
  fun x =>
    match PFunctor.M.dest x.2 with
    | ⟨.ret r, _⟩ => .inl (PFunctor.M.mk (ret' (finish r x.1)))
    | ⟨.tau, c⟩ => .inr (tau' (rec (x.1, c 0)))
    | ⟨.vis _ e, k⟩ =>
        match h x.1 e with
        | .inl (a, m') => .inr (tau' (rec (m', k a)))
        | .inr ⟨β', e', g⟩ =>
            .inr ⟨.vis β' e', fun i => rec ((g i).2, k (g i).1)⟩

/-- Interpret `t` under a one-step handler, starting in state `m`.  A returned
`r` is finished as `finish r m`, so the handler's final state is the one the
leaf reports. -/
def interp {ε : Type u → Type v} {δ : Type u → Type v} {σ : Type w}
    {ρ : Type u₂} {γ : Type u₂}
    (h : Handler ε δ σ) (finish : ρ → σ → γ) (m : σ) (t : ITree ε ρ) : ITree δ γ :=
  PFunctor.M.corec' (step h finish) (m, t)

/-! ### Unfolding

`PFunctor.M.mk_dest` is a theorem rather than a definitional equality, so each
equation below is proved by `PFunctor.M.unfold_corec'`.  The visible-event
equations are conditional on the handler's own decision, because that decision
is what selects the branch.
-/

theorem interp_ret {ε : Type u → Type v} {δ : Type u → Type v} {σ : Type w}
    {ρ : Type u₂} {γ : Type u₂}
    (h : Handler ε δ σ) (finish : ρ → σ → γ) (m : σ) (v : ρ) :
    interp h finish m (ITree.ret v) = ITree.ret (finish v m) := by
  unfold interp
  rw [PFunctor.M.unfold_corec']
  simp only [step, ret, ret', PFunctor.M.dest_mk]
  rfl

theorem interp_tau {ε : Type u → Type v} {δ : Type u → Type v} {σ : Type w}
    {ρ : Type u₂} {γ : Type u₂}
    (h : Handler ε δ σ) (finish : ρ → σ → γ) (m : σ) (t : ITree ε ρ) :
    interp h finish m (ITree.tau t) = ITree.tau (interp h finish m t) := by
  unfold interp
  conv_lhs => rw [PFunctor.M.unfold_corec']
  simp only [step, tau, tau', PFunctor.M.dest_mk]
  refine congrArg PFunctor.M.mk ?_
  refine congrArg (PFunctor.Obj.mk (P := P δ γ) Shape.tau) ?_
  funext i
  match i with
  | 0 => rfl

/-- A handler branch that answers privately becomes a silent step. -/
theorem interp_vis_left {ε : Type u → Type v} {δ : Type u → Type v} {σ : Type w}
    {ρ : Type u₂} {γ : Type u₂}
    (h : Handler ε δ σ) (finish : ρ → σ → γ) (m : σ) {α : Type u}
    (e : ε α) (k : α → ITree ε ρ) (a : α) (m' : σ) (hh : h m e = .inl (a, m')) :
    interp h finish m (ITree.vis e k) = ITree.tau (interp h finish m' (k a)) := by
  unfold interp
  conv_lhs => rw [PFunctor.M.unfold_corec']
  simp only [step, vis, vis', tau, tau', PFunctor.M.dest_mk, hh]
  refine congrArg PFunctor.M.mk ?_
  refine congrArg (PFunctor.Obj.mk (P := P δ γ) Shape.tau) ?_
  funext i
  match i with
  | 0 => rfl

/-- A handler branch that re-emits an observable event produces that event, and
its response is mapped back to a source response and state. -/
theorem interp_vis_right {ε : Type u → Type v} {δ : Type u → Type v} {σ : Type w}
    {ρ : Type u₂} {γ : Type u₂}
    (h : Handler ε δ σ) (finish : ρ → σ → γ) (m : σ) {α : Type u}
    (e : ε α) (k : α → ITree ε ρ) {β : Type u} (e' : δ β) (g : β → α × σ)
    (hh : h m e = .inr ⟨β, e', g⟩) :
    interp h finish m (ITree.vis e k) =
      ITree.vis e' (fun b => interp h finish (g b).2 (k (g b).1)) := by
  unfold interp
  conv_lhs => rw [PFunctor.M.unfold_corec']
  simp only [step, vis, vis', PFunctor.M.dest_mk, hh]
  rfl

end Effect
end ITree
