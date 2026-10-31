/-
A tree-valued effect handler and its monadic interpreter.

A `Handler ε δ` sends one source event to a **tree** of target events whose
results are the source event's responses, so one source event can become several
target events.  `interp h t` runs those trees over `t`.

The interpreter is defined by directly guarded coiteration over two seed modes:

* **source mode** — a source tree: a `ret` emits its result, a `tau` emits one
  `tau`, and a `vis e k` enters handler mode on `h e`;
* **handler mode** — a handler tree together with the source continuation: the
  handler's own `ret a` emits exactly one `tau` and resumes source mode at
  `k a`; its `tau` and visible events are preserved, continuing in handler mode.

That completion `tau` is the whole difference from pinned upstream's
`ITree/EffectAlgebra.lean:68-78`, which routes through `iter` and therefore
emits an initial `tau` even for a `ret`, plus another for each `.recur`.  Here a
return is not delayed at all, a source `tau` is emitted once, and each handled
event costs exactly one completion `tau`.  Consequently an identity-trigger
handler is *not* the identity tree: it adds one silent step after every
responded event.  `ITree.Effect.interp` — the host's computable one-step fold —
is a different function and is untouched.

The exact laws are stated at strict tree equality:

```
interp h (ret r)          = ret r
interp h (tau t)          = tau (interp h t)
interp h (vis e k)        = bind (h e) (fun a => tau (interp h (k a)))
interp h (bind t f)       = bind (interp h t) (fun a => interp h (f a))
interp g (interp h t)     = interp (comp h g) t
```

They are proved by coinduction: the two sides of a law are put in a relation
closed under the one-step `IEqF` functional (`DelayR` below), and `ieq_iff_eq`
turns the result into an equation.

`MonadIter` remains a separate export: the interpreter does not use upstream's
`iterS` fold, and no law here is a law of `MonadIter`.
-/
import ITree.Monad
import ITree.TauClosure

namespace ITree
namespace EffectAlgebra

open ITree.Internal
open ITree.TauClosure

universe u v1 v2 v3

section

variable {ε : Type u → Type v1} {δ : Type u → Type v2} {ρ : Type u}

/-- A tree-valued handler: one source event becomes a target tree whose results
are the source responses. -/
abbrev Handler (ε : Type u → Type v1) (δ : Type u → Type v2) :=
  ∀ {α : Type u}, ε α → ITree δ α

/-! ### The two seed modes -/

/-- The interpreter's coiteration seed: a source tree, or a handler tree with
the source continuation to resume when it completes. -/
inductive Mode (ε : Type u → Type v1) (δ : Type u → Type v2) (ρ : Type u) :
    Type (max (u + 1) (max v1 v2)) where
  | src (t : ITree ε ρ)
  | hnd {α : Type u} (u : ITree δ α) (k : α → ITree ε ρ)

/-- Handler mode: preserve the handler tree's shapes, and on its result emit
exactly one `tau` and resume the source continuation. -/
def hndStep {X : Type (max (u + 1) (max v1 v2))}
    (rec : Mode ε δ ρ → X) {α : Type u} (u : ITree δ α) (k : α → ITree ε ρ) :
    (P δ ρ).M ⊕ P δ ρ X :=
  match u.dest with
  | ⟨.ret a, _⟩ => .inr (tau' (rec (.src (k a))))
  | ⟨.tau, c⟩ => .inr (tau' (rec (.hnd (c 0) k)))
  | ⟨.vis _ e', k'⟩ => .inr (vis' e' (fun b => rec (.hnd (k' b) k)))

/-- One coiteration step of the interpreter. -/
def modeStep (h : Handler ε δ) :
    ∀ {X : Type (max (u + 1) (max v1 v2))},
      (Mode ε δ ρ → X) → Mode ε δ ρ → (P δ ρ).M ⊕ P δ ρ X
  | _, rec, .src t =>
    match t.dest with
    | ⟨.ret r, _⟩ => .inl (ret r)
    | ⟨.tau, c⟩ => .inr (tau' (rec (.src (c 0))))
    | ⟨.vis _ e, k⟩ => hndStep rec (h e) k
  | _, rec, .hnd u k => hndStep rec u k

/-- Interpret a source tree under a tree-valued handler. -/
def interp (h : Handler ε δ) (t : ITree ε ρ) : ITree δ ρ :=
  .corec' (modeStep h) (.src t)

/-- Interpret from handler mode: run a handler tree to its result and resume the
source continuation.  This is the name the laws of the handler's completion step
are stated for. -/
def interpHnd (h : Handler ε δ) {α : Type u} (u : ITree δ α) (k : α → ITree ε ρ) :
    ITree δ ρ :=
  .corec' (modeStep h) (.hnd u k)

/-! ### Unfoldings -/

/-- A source return is emitted immediately: no initial `tau`. -/
theorem interp_ret (h : Handler ε δ) (r : ρ) :
    interp h (ret r : ITree ε ρ) = ret r := by
  unfold interp
  rw [PFunctor.M.unfold_corec']
  rfl

/-- A source `tau` is emitted exactly once. -/
theorem interp_tau (h : Handler ε δ) (t : ITree ε ρ) :
    interp h (tau t) = tau (interp h t) := by
  unfold interp
  conv_lhs => rw [PFunctor.M.unfold_corec']
  simp only [modeStep, tau, tau']
  refine congrArg PFunctor.M.mk ?_
  refine congrArg (PFunctor.Obj.mk (P := P δ ρ) Shape.tau) ?_
  funext i
  match i with
  | 0 => rfl

/-- A source visible event enters handler mode on the handler's tree. -/
theorem interp_vis_hnd (h : Handler ε δ) {α : Type u} (e : ε α)
    (k : α → ITree ε ρ) : interp h (vis e k) = interpHnd h (h e) k := by
  unfold interp interpHnd
  conv_lhs => rw [PFunctor.M.unfold_corec']
  conv_rhs => rw [PFunctor.M.unfold_corec']
  rfl

/-- A handler's result emits exactly one `tau` and resumes the source. -/
theorem interpHnd_ret (h : Handler ε δ) {α : Type u} (a : α)
    (k : α → ITree ε ρ) :
    interpHnd h (ret a : ITree δ α) k = tau (interp h (k a)) := by
  unfold interpHnd
  conv_lhs => rw [PFunctor.M.unfold_corec']
  simp only [modeStep, hndStep, tau, tau']
  refine congrArg PFunctor.M.mk ?_
  refine congrArg (PFunctor.Obj.mk (P := P δ ρ) Shape.tau) ?_
  funext i
  match i with
  | 0 => rfl

/-- A handler's `tau` is preserved. -/
theorem interpHnd_tau (h : Handler ε δ) {α : Type u} (c : ITree δ α)
    (k : α → ITree ε ρ) :
    interpHnd h (tau c) k = tau (interpHnd h c k) := by
  unfold interpHnd
  conv_lhs => rw [PFunctor.M.unfold_corec']
  simp only [modeStep, hndStep, tau, tau']
  refine congrArg PFunctor.M.mk ?_
  refine congrArg (PFunctor.Obj.mk (P := P δ ρ) Shape.tau) ?_
  funext i
  match i with
  | 0 => rfl

/-- A handler's visible event is preserved, and the source continuation is
carried past it. -/
theorem interpHnd_vis (h : Handler ε δ) {α β : Type u} (e : δ β)
    (k' : β → ITree δ α) (k : α → ITree ε ρ) :
    interpHnd h (vis e k') k = vis e (fun b => interpHnd h (k' b) k) := by
  unfold interpHnd
  conv_lhs => rw [PFunctor.M.unfold_corec']
  simp only [modeStep, hndStep, vis, vis']
  rfl

/-! ### The closure relation of the laws

A pair of target trees is in `DelayR base` when it is a `base` pair, when the two
sides are equal, when both sides take one `tau`, or when both sides bind the
same tree over pointwise-related continuations.  That is exactly the closure
needed to compare the interpreter's two machines, and it is closed under the
one-step functional. -/

inductive DelayR (base : ITree δ ρ → ITree δ ρ → Prop) : ITree δ ρ → ITree δ ρ → Prop where
  /-- A pair the law starts from. -/
  | of_base {p q : ITree δ ρ} : base p q → DelayR base p q
  /-- A pair that has become the same tree. -/
  | of_eq {p q : ITree δ ρ} : p = q → DelayR base p q
  /-- One silent step on both sides. -/
  | tau {p q : ITree δ ρ} : DelayR base p q → DelayR base (tau p) (tau q)
  /-- The same tree bound with pointwise-related continuations. -/
  | of_bind {α : Type u} (u : ITree δ α) {A B : α → ITree δ ρ} :
      (∀ a, DelayR base (A a) (B a)) → DelayR base (bind u A) (bind u B)

/-- `DelayR base` is contained in `DelayR base'` when `base` is. -/
theorem delayR_mono {base base' : ITree δ ρ → ITree δ ρ → Prop}
    (h : ∀ p q, base p q → base' p q) : ∀ p q, DelayR base p q → DelayR base' p q := by
  intro p q hpq
  induction hpq with
  | of_base hb => exact DelayR.of_base (h _ _ hb)
  | of_eq heq => exact DelayR.of_eq heq
  | tau _ ih => exact DelayR.tau ih
  | of_bind u _ ih => exact DelayR.of_bind u fun a => ih a

/-- `DelayR base` is closed under the one-step functional whenever `base` is. -/
theorem delayR_ieqF {base : ITree δ ρ → ITree δ ρ → Prop}
    (hbase : ∀ p q, base p q → IEqF (DelayR base) p q) :
    ∀ p q, DelayR base p q → IEqF (DelayR base) p q := by
  intro p q hpq
  induction hpq with
  | of_base hb => exact hbase _ _ hb
  | of_eq heq => subst heq; exact IEqF_refl (fun t => DelayR.of_eq rfl) _
  | tau h' _ => exact IEqF.tau _ _ h'
  | of_bind u hh ih =>
      apply dMatchOn (x := u)
      · intro a heq
        rw [heq, bind_ret, bind_ret]
        exact ih a
      · intro c heq
        rw [heq, bind_tau, bind_tau]
        exact IEqF.tau _ _ (DelayR.of_bind c hh)
      · intro β e k' heq
        rw [heq, bind_vis, bind_vis]
        exact IEqF.vis e _ _ (fun b => DelayR.of_bind (k' b) hh)

/-- Coinduction in `DelayR`: a `base` pair is an `IEq` pair. -/
theorem delayR_ieq {base : ITree δ ρ → ITree δ ρ → Prop}
    (hbase : ∀ p q, base p q → IEqF (DelayR base) p q) :
    ∀ p q, base p q → IEq p q :=
  fun p q hb => IEq.coind (DelayR base) (delayR_ieqF hbase) p q (DelayR.of_base hb)

/-- A `base` pair is an equation between trees. -/
theorem delayR_eq {base : ITree δ ρ → ITree δ ρ → Prop}
    (hbase : ∀ p q, base p q → IEqF (DelayR base) p q)
    {p q : ITree δ ρ} (h : base p q) : p = q :=
  (ieq_iff_eq p q).mp (delayR_ieq hbase p q h)

end

/-! ### The handler-completion law

Handler mode is exactly binding the handler's tree with one `tau` in front of
each resumed source tree. -/

section
variable {ε : Type u → Type v1} {δ : Type u → Type v2} {ρ : Type u}

/-- The base pairs of the completion law. -/
def HndBase (h : Handler ε δ) (p q : ITree δ ρ) : Prop :=
  ∃ (α : Type u) (u : ITree δ α) (k : α → ITree ε ρ),
    p = interpHnd h u k ∧ q = bind u (fun a => tau (interp h (k a)))

theorem hndBase_ieqF (h : Handler ε δ) (p q : ITree δ ρ) (hpq : HndBase h p q) :
    IEqF (DelayR (HndBase h)) p q := by
  rcases hpq with ⟨α, u, k, rfl, rfl⟩
  apply dMatchOn
    (motive := fun x => IEqF (DelayR (HndBase h)) (interpHnd h x k)
      (bind x (fun a => tau (interp h (k a))))) u
  · intro a heq
    rw [heq, interpHnd_ret, bind_ret]
    exact IEqF.tau _ _ (DelayR.of_eq rfl)
  · intro c heq
    rw [heq, interpHnd_tau, bind_tau]
    exact IEqF.tau _ _ (DelayR.of_base ⟨_, c, k, rfl, rfl⟩)
  · intro β e k' heq
    rw [heq, interpHnd_vis, bind_vis]
    exact IEqF.vis e _ _ (fun a => DelayR.of_base ⟨_, k' a, k, rfl, rfl⟩)

/-- Handler mode is the handler's tree bound to the completion `tau` and the
resumed source tree. -/
theorem interpHnd_eq (h : Handler ε δ) {α : Type u} (u : ITree δ α)
    (k : α → ITree ε ρ) :
    interpHnd h u k = bind u (fun a => tau (interp h (k a))) :=
  delayR_eq (hndBase_ieqF h) ⟨α, u, k, rfl, rfl⟩

/-- The handler equation: a source event becomes its handler's tree, with
exactly one completion `tau` in front of each resumed source tree. -/
theorem interp_vis (h : Handler ε δ) {α : Type u} (e : ε α)
    (k : α → ITree ε ρ) :
    interp h (vis e k) = bind (h e) (fun a => tau (interp h (k a))) := by
  rw [interp_vis_hnd, interpHnd_eq]

/-! ### Binding over a source tree

The interpreter distributes over `bind`: interpreting `bind t f` is binding the
interpreted `t` to the interpreted continuations. -/

/-- The base pairs of the bind law. -/
def BindBase (h : Handler ε δ) (p q : ITree δ ρ) : Prop :=
  ∃ (α : Type u) (t : ITree ε α) (f : α → ITree ε ρ),
    p = interp h (bind t f) ∧ q = bind (interp h t) (fun a => interp h (f a))

theorem bindBase_ieqF (h : Handler ε δ) (p q : ITree δ ρ) (hpq : BindBase h p q) :
    IEqF (DelayR (BindBase h)) p q := by
  rcases hpq with ⟨α, t, f, rfl, rfl⟩
  apply dMatchOn
    (motive := fun x => IEqF (DelayR (BindBase h)) (interp h (bind x f))
      (bind (interp h x) (fun a => interp h (f a)))) t
  · intro v heq
    rw [heq, bind_ret]
    have : interp h (f v) = bind (interp h (ret v)) (fun a => interp h (f a)) := by
      rw [interp_ret, bind_ret]
    rw [this]
    exact IEqF_refl (fun t => DelayR.of_eq rfl) _
  · intro c heq
    rw [heq]
    simp only [interp_tau, bind_tau]
    exact IEqF.tau _ _ (DelayR.of_base ⟨α, c, f, rfl, rfl⟩)
  · intro β e k heq
    rw [heq]
    simp only [bind_vis, interp_vis, bind_assoc, bind_tau]
    -- both sides now bind the handler's tree over related continuations
    apply dMatchOn
      (motive := fun x => IEqF (DelayR (BindBase h)) (bind x (fun a => tau (interp h (bind (k a) f))))
        (bind x (fun a => tau (bind (interp h (k a)) (fun a' => interp h (f a')))))) (h e)
    · intro a heq'
      rw [heq', bind_ret, bind_ret]
      exact IEqF.tau _ _ (DelayR.of_base ⟨α, k a, f, rfl, rfl⟩)
    · intro c heq'
      rw [heq', bind_tau, bind_tau]
      exact IEqF.tau _ _ (DelayR.of_bind c fun a =>
        DelayR.tau (DelayR.of_base ⟨α, k a, f, rfl, rfl⟩))
    · intro γ e' k' heq'
      rw [heq', bind_vis, bind_vis]
      exact IEqF.vis e' _ _ (fun b => DelayR.of_bind (k' b) fun a =>
        DelayR.tau (DelayR.of_base ⟨α, k a, f, rfl, rfl⟩))

/-- The bind law: interpreting a bind is binding the interpretations. -/
theorem interp_bind (h : Handler ε δ) {α : Type u} (t : ITree ε α)
    (f : α → ITree ε ρ) :
    interp h (bind t f) = bind (interp h t) (fun a => interp h (f a)) :=
  delayR_eq (bindBase_ieqF h) ⟨α, t, f, rfl, rfl⟩

end

/-! ### Composition of handlers -/

section
variable {ε : Type u → Type v1} {δ : Type u → Type v2} {ζ : Type u → Type v3}
variable {ρ : Type u}

/-- Compose handlers: interpret each handler tree of the first under the
second. -/
def comp (h : Handler ε δ) (g : Handler δ ζ) : Handler ε ζ :=
  fun {_} e => interp g (h e)

/-- The base pairs of the composition law. -/
def CompBase (h : Handler ε δ) (g : Handler δ ζ) (p q : ITree ζ ρ) : Prop :=
  ∃ t : ITree ε ρ, p = interp g (interp h t) ∧ q = interp (comp h g) t

theorem compBase_ieqF (h : Handler ε δ) (g : Handler δ ζ)
    (p q : ITree ζ ρ) (hpq : CompBase h g p q) :
    IEqF (DelayR (CompBase h g)) p q := by
  rcases hpq with ⟨t, rfl, rfl⟩
  apply dMatchOn
    (motive := fun x => IEqF (DelayR (CompBase h g)) (interp g (interp h x))
      (interp (comp h g) x)) t
  · intro r heq
    rw [heq]
    simp only [interp_ret]
    exact IEqF_refl (fun t => DelayR.of_eq rfl) _
  · intro c heq
    rw [heq]
    simp only [interp_tau]
    exact IEqF.tau _ _ (DelayR.of_base ⟨c, rfl, rfl⟩)
  · intro β e k heq
    rw [heq]
    simp only [comp, interp_vis_hnd, interpHnd_eq, interp_bind, interp_tau]
    apply dMatchOn
      (motive := fun x => IEqF (DelayR (CompBase h g))
        (bind x (fun a => tau (interp g (interp h (k a)))))
        (bind x (fun a => tau (interp (comp h g) (k a))))) (interp g (h e))
    · intro a heq'
      rw [heq']
      simp only [bind_ret]
      exact IEqF.tau _ _ (DelayR.of_base ⟨k a, rfl, rfl⟩)
    · intro c heq'
      rw [heq']
      simp only [bind_tau]
      exact IEqF.tau _ _ (DelayR.of_bind c fun a =>
        DelayR.tau (DelayR.of_base ⟨k a, rfl, rfl⟩))
    · intro γ e' k' heq'
      rw [heq']
      simp only [bind_vis]
      exact IEqF.vis e' _ _ (fun b => DelayR.of_bind (k' b) fun a =>
        DelayR.tau (DelayR.of_base ⟨k a, rfl, rfl⟩))

/-- The composition law: interpreting twice is interpreting under the composed
handler, with no extra outer `tau`. -/
theorem interp_comp (h : Handler ε δ) (g : Handler δ ζ) (t : ITree ε ρ) :
    interp g (interp h t) = interp (comp h g) t :=
  delayR_eq (compBase_ieqF h g) ⟨t, rfl, rfl⟩

end

/-! ### The guards of the interpreter's transitions -/

section
variable {ε : Type u → Type v1} {δ : Type u → Type v2} {ρ : Type u}

/-- A source return emits `now`: no delay at all. -/
theorem interp_ret_witness (h : Handler ε δ) (r : ρ) :
    Finite (now (ret r) : TauClosure (ITree δ ρ)) (ret r) ∧
      flatten (now (ret r) : TauClosure (ITree δ ρ)) = interp h (ret r) :=
  ⟨finite_now _, by rw [flatten_now, interp_ret]⟩

/-- A source `tau` is one positive finite delay of the interpreted
continuation. -/
theorem interp_tau_witness (h : Handler ε δ) (t : ITree ε ρ) :
    FiniteLater (later (now (interp h t))) (interp h t) ∧
      flatten (later (now (interp h t))) = interp h (tau t) :=
  ⟨finiteLater_later_now _, by rw [flatten_later, flatten_now, interp_tau]⟩

/-- The handler's completion step is one positive finite delay of the resumed
source tree: exactly the `tau` the visible-event law puts there. -/
theorem interp_completion_witness (h : Handler ε δ) {α : Type u}
    (k : α → ITree ε ρ) (a : α) :
    FiniteLater (later (now (interp h (k a)))) (interp h (k a)) ∧
      flatten (later (now (interp h (k a)))) = tau (interp h (k a)) :=
  ⟨finiteLater_later_now _, by rw [flatten_later, flatten_now]⟩

end

end EffectAlgebra
end ITree
