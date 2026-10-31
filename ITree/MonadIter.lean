/-
Monadic iteration over interaction trees.

`iter step i` runs `step`'s tree for seed `i`, and when that tree returns
`.done r` the iteration returns `r`; when it returns `.recur j` the iteration
goes round again with seed `j`.  A visible event and a silent step of the
stepped tree are preserved, so the iterator is productive on every tree.

The exact equations, which are the ported upstream ones and not the interpreter
laws:

* `iter step i = tau (bindStep step (step i))` — one `tau` before the first
  step's tree, so an immediate `.done r` is `tau (ret r)`;
* `bindStep step (ret (.done r)) = ret r`;
* `bindStep step (ret (.recur j)) = tau (bindStep step (step j))` — with the
  initial `tau` above, an immediate `.recur j` is `tau (tau ...)`, i.e. two
  stages before the next step's result;
* `bindStep step (tau t) = tau (bindStep step t)`;
* `bindStep step (vis e k) = vis e (fun a => bindStep step (k a))`.

Each initial and `.recur` transition carries a positive
`TauClosure.FiniteLater` witness whose `flatten` is that exact transition, so
the guard is the tree's own one-step delay rather than a token mention.

`IterState`, `MonadIter` and `iter` are adapted from `mit-plv/lean4-itree` at
revision `7f48fefaa2f12f599e6c4aa2be1ef39d5466122b`
(`ITree/EffectAlgebra.lean:28-66`), placed under the `ITree` namespace.  The
upstream `Add (Type → Type)`/`Coe` instances and the `StateT` lifting are not
ported: nothing here composes effect signatures, and this slice has no
state-transformer client.
-/
import ITree.Monad
import ITree.TauClosure

namespace ITree

open ITree.Internal
open ITree.TauClosure

universe u1 v u2

/-- The state an iteration step returns: stop with a result, or go round again
with a new seed. -/
inductive IterState (ι : Type u2) (ρ : Type u2) : Type u2 where
  | done (r : ρ)
  | recur (i : ι)

/-- Monadic iteration: `iter step i` runs `step` at seed `i` until it returns
`.done`. -/
class MonadIter (m : Type u2 → Type v) where
  iter : {ρ ι : Type u2} → (ι → m (IterState ι ρ)) → ι → m ρ

section
variable {ε : Type u1 → Type v} {ρ : Type u2} {ι : Type u2}

/-- The internal state of `iter`: the next seed, or a tree of iteration states
whose results the iterator binds. -/
inductive IterMode (ε : Type u1 → Type v) (ρ ι : Type u2) :
    Type (max (max (u1 + 1) u2) v) where
  | iterS (i : ι)
  | bindS (t : ITree ε (IterState ι ρ))

/-- One coiteration step of the iterator. -/
def iterStep (step : ι → ITree ε (IterState ι ρ)) :
    ∀ {X : Type (max (max (u1 + 1) u2) v)},
      (IterMode ε ρ ι → X) → IterMode ε ρ ι → (P ε ρ).M ⊕ P ε ρ X
  | _, rec, .iterS i => .inr (tau' (rec (.bindS (step i))))
  | _, rec, .bindS t =>
    match t.dest with
    | ⟨.ret v, _⟩ =>
      match v with
      | .done r => .inl (ret r)
      | .recur l => .inr (tau' (rec (.bindS (step l))))
    | ⟨.tau, c⟩ => .inr (tau' (rec (.bindS (c 0))))
    | ⟨.vis _ e, k⟩ => .inr (vis' e (fun a => rec (.bindS (k a))))

/-- Iterate `step` from seed `i`. -/
def iter (step : ι → ITree ε (IterState ι ρ)) (i : ι) : ITree ε ρ :=
  .corec' (iterStep step) (.iterS i)

/-- The iterator's internal position: a tree of iteration states, bound as its
results arrive.  This is the state the `.recur` equation counts in. -/
def bindStep (step : ι → ITree ε (IterState ι ρ)) (t : ITree ε (IterState ι ρ)) :
    ITree ε ρ :=
  .corec' (iterStep step) (.bindS t)

instance : MonadIter (ITree ε) where
  iter := iter

/-! ### The equations -/

/-- The initial `tau`: `iter` takes one silent step before the first step's
tree. -/
theorem iter_eq_tau (step : ι → ITree ε (IterState ι ρ)) (i : ι) :
    iter step i = tau (bindStep step (step i)) := by
  unfold iter
  conv_lhs => rw [PFunctor.M.unfold_corec']
  simp only [iterStep, tau, tau']
  refine congrArg PFunctor.M.mk ?_
  refine congrArg (PFunctor.Obj.mk (P := P ε ρ) Shape.tau) ?_
  funext i
  match i with
  | 0 => rfl

/-- A completed step returns its result. -/
theorem bindStep_ret_done (step : ι → ITree ε (IterState ι ρ)) (r : ρ) :
    bindStep step (ret (.done r)) = ret r := by
  unfold bindStep
  rw [PFunctor.M.unfold_corec']
  rfl

/-- A `.recur` step adds a `tau` and continues with the next step's tree. -/
theorem bindStep_ret_recur (step : ι → ITree ε (IterState ι ρ)) (j : ι) :
    bindStep step (ret (.recur j)) = tau (bindStep step (step j)) := by
  unfold bindStep
  conv_lhs => rw [PFunctor.M.unfold_corec']
  simp only [iterStep, tau, tau']
  refine congrArg PFunctor.M.mk ?_
  refine congrArg (PFunctor.Obj.mk (P := P ε ρ) Shape.tau) ?_
  funext i
  match i with
  | 0 => rfl

/-- A silent step of the stepped tree stays a silent step. -/
theorem bindStep_tau (step : ι → ITree ε (IterState ι ρ))
    (t : ITree ε (IterState ι ρ)) :
    bindStep step (tau t) = tau (bindStep step t) := by
  unfold bindStep
  conv_lhs => rw [PFunctor.M.unfold_corec']
  simp only [iterStep, tau, tau']
  refine congrArg PFunctor.M.mk ?_
  refine congrArg (PFunctor.Obj.mk (P := P ε ρ) Shape.tau) ?_
  funext i
  match i with
  | 0 => rfl

/-- A visible event of the stepped tree is preserved, with the iteration
continuing after each response. -/
theorem bindStep_vis {δ : Type u1} (step : ι → ITree ε (IterState ι ρ))
    (e : ε δ) (k : δ → ITree ε (IterState ι ρ)) :
    bindStep step (vis e k) = vis e (fun a => bindStep step (k a)) := by
  unfold bindStep
  conv_lhs => rw [PFunctor.M.unfold_corec']
  simp only [iterStep, vis, vis', PFunctor.M.dest_mk]
  rfl

/-! ### The two consequences the port is pinned by -/

/-- An immediate `.done` costs exactly one `tau`. -/
theorem iter_done (step : ι → ITree ε (IterState ι ρ)) {i : ι} {r : ρ}
    (h : step i = ret (.done r)) : iter step i = tau (ret r) := by
  rw [iter_eq_tau, h, bindStep_ret_done]

/-- An immediate `.recur` costs two `tau` stages before the next step's result:
the iterator's `tau`, then the `.recur` `tau`, then `iter`'s own initial `tau`. -/
theorem iter_recur (step : ι → ITree ε (IterState ι ρ)) {i j : ι}
    (h : step i = ret (.recur j)) : iter step i = tau (iter step j) := by
  rw [iter_eq_tau, h, bindStep_ret_recur, iter_eq_tau]

/-! ### The recursive guards

The initial and `.recur` transitions are positive finite delays of the tree the
iteration actually produces; a `now` witness would be the unguarded backedge
that `TauClosure.FiniteLater` excludes. -/

/-- The initial guard: one `later` in front of the first step's tree. -/
theorem iter_guard (step : ι → ITree ε (IterState ι ρ)) (i : ι) :
    ∃ d : TauClosure (ITree ε ρ), FiniteLater d (bindStep step (step i)) ∧
      flatten d = iter step i :=
  ⟨later (now (bindStep step (step i))), finiteLater_later_now _,
    by rw [flatten_later, flatten_now, iter_eq_tau]⟩

/-- The `.recur` guard: the backedge is a positive finite delay of the next
iteration, whose own initial `tau` is the second stage. -/
theorem iter_recur_guard (step : ι → ITree ε (IterState ι ρ)) {i j : ι}
    (h : step i = ret (.recur j)) :
    ∃ d : TauClosure (ITree ε ρ), FiniteLater d (iter step j) ∧
      flatten d = iter step i :=
  ⟨later (now (iter step j)), finiteLater_later_now _,
    by rw [flatten_later, flatten_now, iter_recur step h]⟩

/-- The same guard at the internal position, before the initial `tau` is
counted. -/
theorem bindStep_recur_guard (step : ι → ITree ε (IterState ι ρ)) (j : ι) :
    ∃ d : TauClosure (ITree ε ρ), FiniteLater d (bindStep step (step j)) ∧
      flatten d = bindStep step (ret (.recur j)) :=
  ⟨later (now (bindStep step (step j))), finiteLater_later_now _,
    by rw [flatten_later, flatten_now, bindStep_ret_recur]⟩

end

end ITree
