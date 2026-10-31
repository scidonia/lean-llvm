/-
The public surface of the generic library: a client imports `ITree` only.

This file declares its own event signature and its own handler, so it is a check
that the public entrypoint is self-sufficient: the constructors, the one-step
interpreter and its unfolding equations, and the coinduction layer are all
reachable without importing an `Internal` module and without importing anything
from the LLVM instantiation.

Elaborated by `lake env lean tests/itree-import.lean`.
-/
import ITree

namespace ITreeImportCheck

open ITree

/-- A two-event signature, declared here rather than taken from an instance. -/
inductive Tick : Type → Type where
  /-- An observable poke. -/
  | unit : Tick Unit
  /-- A silent question. -/
  | ask : Tick Nat

/-! ### The one-step interpreter

`ask` is answered privately, so it becomes a silent step; `unit` is re-emitted
with its response mapped back into the source continuation. -/
def handler : Effect.Handler Tick Tick Nat :=
  fun {_} m e =>
    match e with
    | Tick.unit => Sum.inr ⟨Unit, Tick.unit, fun () => ((), m + 1)⟩
    | Tick.ask => Sum.inl (m, m + 1)

/-- A tree with both events. -/
def sample : ITree.Tree Tick Nat :=
  ITree.vis Tick.ask (fun n => ITree.tau (ITree.vis Tick.unit (fun _ => ITree.ret (n + 1))))

/-- The interpreted tree. -/
def interpreted : ITree.Tree Tick Nat :=
  Effect.interp handler (fun r _ => r) 0 sample

/-- A returned leaf is finished with the handler's state. -/
example : Effect.interp handler (fun (r : Nat) (m : Nat) => r + m) 7 (ITree.ret 3) =
    ITree.ret 10 := by
  rw [Effect.interp_ret]

/-- A source `tau` stays a `tau`. -/
example (t : ITree.Tree Tick Nat) :
    Effect.interp handler (fun r _ => r) 0 (ITree.tau t) =
      ITree.tau (Effect.interp handler (fun r _ => r) 0 t) :=
  Effect.interp_tau _ _ _ t

/-- A privately answered event is silent, and the state advances. -/
example : Effect.interp handler (fun r _ => r) 0 (ITree.vis Tick.ask (fun n => ITree.ret n)) =
    ITree.tau (ITree.ret 0) := by
  rw [Effect.interp_vis_left handler (fun r _ => r) 0 Tick.ask (fun n => ITree.ret n) 0 1 rfl]
  rw [Effect.interp_ret]

/-- A re-emitted event is observable, its response is mapped back into the
source continuation, and the continuation starts from the new state. -/
example : Effect.interp handler (fun r _ => r) 3 (ITree.vis Tick.unit (fun _ => ITree.ret 9)) =
    ITree.vis Tick.unit (fun () => ITree.ret 9) := by
  rw [Effect.interp_vis_right handler (fun r _ => r) 3 Tick.unit (fun _ => ITree.ret 9)
    Tick.unit (fun () => ((), 4)) rfl]
  rw [Effect.interp_ret]

/-! ### The public tree API -/

/-- `tauN` and `trigger` are part of the public surface. -/
example : (ITree.tauN 2 (ITree.ret 5) : ITree.Tree Tick Nat) =
    ITree.tau (ITree.tau (ITree.ret 5)) := rfl

example : (ITree.trigger Tick.ask : ITree.Tree Tick Nat) =
    ITree.vis Tick.ask (fun n => ITree.ret n) := rfl

/-- The constructors are distinguishable, which is what the relation's terminal
cases use. -/
example : (ITree.ret 5 : ITree.Tree Tick Nat) ≠ ITree.tau (ITree.ret 5) :=
  ITree.ret_ne_tau

/-- `infTau` unfolds to a `tau` of itself. -/
example : (ITree.infTau : ITree.Tree Tick Nat) = ITree.tau ITree.infTau :=
  ITree.infTau_eq

/-! ### The coinduction layer -/

#check @plfp
#check @uplfp
#check @plfp_unfold
#check @plfp_acc

set_option autoImplicit false in
/-! ### Exact equality

`IEq` is exact: it is identified with strict equality, so it is an equivalence
and it refuses the silent step. -/

/-- `IEq` is strict equality. -/
example (t1 t2 : ITree.Tree Tick Nat) : ITree.IEq t1 t2 ↔ t1 = t2 :=
  ITree.ieq_iff_eq t1 t2

/-- A silent step is not equal to the tree behind it. -/
example : ¬ ITree.IEq (ITree.tau (ITree.ret 5) : ITree.Tree Tick Nat) (ITree.ret 5) := by
  rw [ITree.ieq_iff_eq]
  exact fun h => ITree.ret_ne_tau h.symm

/-- `IEq` is symmetric. -/
example {t1 t2 : ITree.Tree Tick Nat} (h : ITree.IEq t1 t2) : ITree.IEq t2 t1 :=
  ITree.ieq_symm h

/-- `IEq` is transitive. -/
example {t1 t2 t3 : ITree.Tree Tick Nat} (h1 : ITree.IEq t1 t2) (h2 : ITree.IEq t2 t3) :
    ITree.IEq t1 t3 :=
  ITree.ieq_trans h1 h2

/-! ### Lawful instances

The tree is a lawful functor and a lawful monad at strict equality. -/

/-- The functor instance is lawful. -/
example : LawfulFunctor (ITree.Tree Tick) := inferInstance

/-- The monad instance is lawful. -/
example : LawfulMonad (ITree.Tree Tick) := inferInstance

/-- Identity and composition of `map`, at strict equality. -/
example (t : ITree.Tree Tick Nat) : ITree.map id t = t := ITree.id_map t

example (t : ITree.Tree Tick Nat) :
    ITree.map (fun n => n + 1) (ITree.map (fun n => n * 2) t) =
      ITree.map ((fun n => n + 1) ∘ (fun n => n * 2)) t :=
  (ITree.comp_map (fun n => n * 2) (fun n => n + 1) t).symm

/-- Both monad identities and associativity, at strict equality. -/
example (v : Nat) (f : Nat → ITree.Tree Tick Nat) :
    ITree.bind (ITree.ret v) f = f v := ITree.bind_ret v f

example (f : Nat → Nat) (t : ITree.Tree Tick Nat) :
    ITree.bind t (pure ∘ f) = ITree.map f t :=
  ITree.bind_pure_comp f t

example (t : ITree.Tree Tick Nat) (f : Nat → ITree.Tree Tick Nat)
    (g : Nat → ITree.Tree Tick Nat) :
    ITree.bind (ITree.bind t f) g = ITree.bind t (fun a => ITree.bind (f a) g) :=
  ITree.bind_assoc t f g

/-! ### Iteration

`iter` is the ported upstream iterator: one initial `tau`, a completed step
returning immediately afterwards, and two `tau` stages on an immediate `.recur`.
-/

/-- One completed step: `tau (ret r)`. -/
example : ITree.iter (fun _ : Nat => (ITree.ret (.done 7) : ITree.Tree Tick (ITree.IterState Nat Nat))) 0
    = ITree.tau (ITree.ret 7) :=
  ITree.iter_done _ rfl

/-- An immediate `.recur` is two `tau` stages before the next step's result. -/
example (step : Nat → ITree.Tree Tick (ITree.IterState Nat Nat)) (j : Nat)
    (h : step 0 = ITree.ret (.recur j)) :
    ITree.iter step 0 = ITree.tau (ITree.iter step j) :=
  ITree.iter_recur step h

/-- The visible case of the iterator: the event is preserved and the iteration
continues after each response. -/
example (step : Nat → ITree.Tree Tick (ITree.IterState Nat Nat)) (k : Unit → ITree.Tree Tick (ITree.IterState Nat Nat)) :
    ITree.bindStep step (ITree.vis Tick.unit k) =
      ITree.vis Tick.unit (fun a => ITree.bindStep step (k a)) :=
  ITree.bindStep_vis step Tick.unit k

/-- The public instance is a `MonadIter`. -/
example : ITree.MonadIter (ITree.Tree Tick) := inferInstance

/-! ### A tree-valued handler -/

/-- A handler that answers one source event with two target events. -/
def twoEvent : ITree.EffectAlgebra.Handler Tick Tick :=
  fun {_} e =>
    match e with
    | Tick.unit => ITree.vis Tick.unit (fun _ => ITree.vis Tick.unit (fun _ => ITree.ret ()))
    | Tick.ask => ITree.vis Tick.ask (fun n => ITree.vis Tick.unit (fun _ => ITree.ret (n + 1)))

/-- One source event becomes two target events, with one completion `tau` after
the handler's tree. -/
example :
    ITree.bind (twoEvent Tick.unit) (fun _ => ITree.tau (ITree.ret (5 : Nat))) =
      ITree.vis Tick.unit (fun () => ITree.vis Tick.unit (fun () => ITree.tau (ITree.ret 5))) := by
  rw [show twoEvent Tick.unit = ITree.vis Tick.unit
      (fun _ => ITree.vis Tick.unit (fun _ => ITree.ret ())) from rfl]
  rw [ITree.bind_vis, ITree.bind_vis, ITree.bind_ret]

/-- The tree-valued interpreter on the same source event: two target events, then
exactly one completion `tau`, then the source return. -/
example :
    ITree.EffectAlgebra.interp twoEvent (ITree.vis Tick.unit (fun _ => ITree.ret 5)) =
      ITree.vis Tick.unit
        (fun _ => ITree.vis Tick.unit (fun _ => ITree.tau (ITree.ret (5 : Nat)))) := by
  rw [ITree.EffectAlgebra.interp_vis]
  rw [show twoEvent Tick.unit = ITree.vis Tick.unit
      (fun _ => ITree.vis Tick.unit (fun _ => ITree.ret ())) from rfl]
  rw [ITree.bind_vis, ITree.bind_vis, ITree.bind_ret, ITree.EffectAlgebra.interp_ret]

/-- The one-step host fold is a different function and keeps its equations. -/
example : Effect.interp handler (fun (r : Nat) (m : Nat) => r + m) 7 (ITree.ret 3) =
    ITree.ret 10 := by
  rw [Effect.interp_ret]

/-! ### The interpreter's laws

Each of the five equations at strict equality, with the exact `tau` counts. -/

/-- A source return is not delayed. -/
example (hh : ITree.EffectAlgebra.Handler Tick Tick) (r : Nat) :
    ITree.EffectAlgebra.interp hh (ITree.ret r) = ITree.ret r :=
  ITree.EffectAlgebra.interp_ret hh r

/-- A source `tau` is emitted exactly once. -/
example (hh : ITree.EffectAlgebra.Handler Tick Tick) (t : ITree.Tree Tick Nat) :
    ITree.EffectAlgebra.interp hh (ITree.tau t) =
      ITree.tau (ITree.EffectAlgebra.interp hh t) :=
  ITree.EffectAlgebra.interp_tau hh t

/-- A source event becomes the handler's tree with one completion `tau` in front
of each resumed source tree. -/
example (hh : ITree.EffectAlgebra.Handler Tick Tick) (e : Tick Nat)
    (k : Nat → ITree.Tree Tick Nat) :
    ITree.EffectAlgebra.interp hh (ITree.vis e k) =
      ITree.bind (hh e) (fun a => ITree.tau (ITree.EffectAlgebra.interp hh (k a))) :=
  ITree.EffectAlgebra.interp_vis hh e k

/-- Interpreting a `bind` is binding the interpretations. -/
example (hh : ITree.EffectAlgebra.Handler Tick Tick) (t : ITree.Tree Tick Nat)
    (f : Nat → ITree.Tree Tick Nat) :
    ITree.EffectAlgebra.interp hh (ITree.bind t f) =
      ITree.bind (ITree.EffectAlgebra.interp hh t)
        (fun a => ITree.EffectAlgebra.interp hh (f a)) :=
  ITree.EffectAlgebra.interp_bind hh t f

/-- Interpreting twice is interpreting under the composed handler, with no extra
outer `tau`. -/
example (h1 h2 : ITree.EffectAlgebra.Handler Tick Tick) (t : ITree.Tree Tick Nat) :
    ITree.EffectAlgebra.interp h2 (ITree.EffectAlgebra.interp h1 t) =
      ITree.EffectAlgebra.interp (ITree.EffectAlgebra.comp h1 h2) t :=
  ITree.EffectAlgebra.interp_comp h1 h2 t

/-- The identity-trigger handler, on one event: exactly one completion `tau`
after the responded event. -/
theorem idTrigger_interp :
    ITree.EffectAlgebra.interp (fun {α} (e : Tick α) => ITree.trigger e)
        (ITree.vis Tick.unit (fun _ => ITree.ret ())) =
      ITree.vis Tick.unit (fun () => ITree.tau (ITree.ret ())) := by
  rw [ITree.EffectAlgebra.interp_vis]
  rw [show ITree.trigger Tick.unit = ITree.vis Tick.unit (fun x => ITree.ret x) from rfl]
  rw [ITree.bind_vis]
  congr 1
  funext x
  cases x
  rw [ITree.bind_ret, ITree.EffectAlgebra.interp_ret]

/-- The near miss: the identity-trigger interpreter is *not* the identity, so
`interp trigger t = t` is not a law. -/
example : ¬ (ITree.EffectAlgebra.interp (fun {α} (e : Tick α) => ITree.trigger e)
      (ITree.vis Tick.unit (fun _ => ITree.ret ()))
    = ITree.vis Tick.unit (fun _ => ITree.ret ())) := by
  intro h
  rw [idTrigger_interp] at h
  have hk := (ITree.vis_inj h).2
  have := congrFun hk ()
  exact ITree.ret_ne_tau this.symm

/-! ### Compatibility with `IEq` -/

/-- `map` preserves `IEq`. -/
example {t1 t2 : ITree.Tree Tick Nat} (f : Nat → Nat) (h : ITree.IEq t1 t2) :
    ITree.IEq (ITree.map f t1) (ITree.map f t2) :=
  ITree.map_congr f h

/-- `bind` preserves `IEq` when the continuations are related. -/
example {t1 t2 : ITree.Tree Tick Nat} {f g : Nat → ITree.Tree Tick Nat}
    (h : ITree.IEq t1 t2) (hf : ∀ a, ITree.IEq (f a) (g a)) :
    ITree.IEq (ITree.bind t1 f) (ITree.bind t2 g) :=
  ITree.bind_congr h hf

/-- The tree-valued interpreter preserves `IEq`. -/
example (hh : ITree.EffectAlgebra.Handler Tick Tick) {t1 t2 : ITree.Tree Tick Nat}
    (h : ITree.IEq t1 t2) :
    ITree.IEq (ITree.EffectAlgebra.interp hh t1) (ITree.EffectAlgebra.interp hh t2) := by
  rw [ITree.ieq_iff_eq] at h ⊢
  rw [h]


/-! ### The delay closure

`TauClosure` is a real object: it returns or steps, never shows an event;
`Finite` inducts over the `later`s and `Infinite` coinducts through them, and
the two are disjoint for every delay and result. -/

/-- `now` returns immediately and `later` takes exactly one step. -/
example : (ITree.TauClosure.now 5 : ITree.TauClosure Nat) = ITree.ret 5 := rfl

example (d : ITree.TauClosure Nat) : ITree.TauClosure.later d = ITree.tau d := rfl

/-- The delay's event signature is empty, so its visible branch has no event. -/
example : ¬ Nonempty (ITree.EmptyEv Unit) := fun ⟨e⟩ => nomatch e

/-- An ordinary tree *does* have a visible `Unit` event. -/
example : (ITree.vis Tick.unit (fun _ => ITree.ret 0) : ITree.Tree Tick Nat) ≠ ITree.ret 0 :=
  fun h => ITree.ret_ne_vis Tick.unit _ h.symm

/-- A returning delay is not a stepping one. -/
example (a : Nat) (d : ITree.TauClosure Nat) :
    ITree.TauClosure.now a ≠ ITree.TauClosure.later d :=
  ITree.TauClosure.now_ne_later a d

/-- `now`, and one `later` in front of it, are finite delays. -/
example : ITree.TauClosure.Finite (ITree.TauClosure.now 5) 5 :=
  ITree.TauClosure.finite_now 5

example : ITree.TauClosure.Finite (ITree.TauClosure.later (ITree.TauClosure.now 5)) 5 :=
  ITree.TauClosure.finite_later (ITree.TauClosure.finite_now 5)

/-- `forever` is not finite, under the same predicate. -/
example : ¬ ITree.TauClosure.Finite (ITree.TauClosure.forever : ITree.TauClosure Nat) 5 :=
  ITree.TauClosure.not_finite_forever 5

/-- The finite principle inducts over exactly the `later`s: its inversion says a
finite delay either returns now or takes one `later` step to a finite delay. -/
theorem finite_inv {d : ITree.TauClosure Nat} {a : Nat}
    (h : ITree.TauClosure.Finite d a) :
    d = ITree.TauClosure.now a ∨
      ∃ d' : ITree.TauClosure Nat, d = ITree.TauClosure.later d' ∧
        ITree.TauClosure.Finite d' a := by
  induction h with
  | now a => exact Or.inl rfl
  | later h ih => exact Or.inr ⟨_, rfl, h⟩

/-- `forever` is infinite. -/
example : ITree.TauClosure.Infinite (ITree.TauClosure.forever : ITree.TauClosure Nat) :=
  ITree.TauClosure.infinite_forever

/-- A returning delay is not infinite. -/
example : ¬ ITree.TauClosure.Infinite (ITree.TauClosure.now 5) :=
  ITree.TauClosure.not_infinite_now 5

-- The infinite principle is a coinduction with an unfolding equation.
#check @ITree.TauClosure.Infinite.coind
#check @ITree.TauClosure.Infinite.unfold

/-- Flattening adds no step for `now`, exactly one for `later`, and is `infTau`
for `forever`. -/
example (t : ITree.Tree Tick Nat) : ITree.TauClosure.flatten (ITree.TauClosure.now t) = t :=
  ITree.TauClosure.flatten_now t

example (d : ITree.TauClosure (ITree.Tree Tick Nat)) :
    ITree.TauClosure.flatten (ITree.TauClosure.later d) =
      ITree.tau (ITree.TauClosure.flatten d) :=
  ITree.TauClosure.flatten_later d

example : ITree.TauClosure.flatten
      (ITree.TauClosure.forever : ITree.TauClosure (ITree.Tree Tick Nat)) = ITree.infTau :=
  ITree.TauClosure.flatten_forever

/-- For every type, delay and result, a finite delay is not an infinite one. -/
example {α : Type} (d : ITree.TauClosure α) (a : α) (hf : ITree.TauClosure.Finite d a) :
    ¬ ITree.TauClosure.Infinite d :=
  ITree.TauClosure.Finite.not_infinite hf

/-! ### The recursive guards

The iterator's initial and `.recur` transitions, and the interpreter's source
`tau` and handler-completion transitions, are positive finite delays whose
flattening is that exact transition. -/

/-- The iterator's initial guard. -/
example (step : Nat → ITree.Tree Tick (ITree.IterState Nat Nat)) (i : Nat) :
    ∃ d : ITree.TauClosure (ITree.Tree Tick Nat),
      ITree.TauClosure.FiniteLater d (ITree.bindStep step (step i)) ∧
        ITree.TauClosure.flatten d = ITree.iter step i :=
  ITree.iter_guard step i

/-- The `.recur` guard, whose flattened form carries the second stage. -/
example (step : Nat → ITree.Tree Tick (ITree.IterState Nat Nat)) {i j : Nat}
    (h : step i = ITree.ret (.recur j)) :
    ∃ d : ITree.TauClosure (ITree.Tree Tick Nat),
      ITree.TauClosure.FiniteLater d (ITree.iter step j) ∧
        ITree.TauClosure.flatten d = ITree.iter step i :=
  ITree.iter_recur_guard step h

/-- An unguarded `now` backedge is refused by the same guard. -/
example : ¬ ITree.TauClosure.FiniteLater (ITree.TauClosure.now 5) 5 :=
  ITree.TauClosure.not_finiteLater_now 5

/-- A return emits `now`: the interpreter adds no initial `tau`. -/
example (hh : ITree.EffectAlgebra.Handler Tick Tick) (r : Nat) :
    ITree.TauClosure.Finite
        (ITree.TauClosure.now (ITree.ret r) : ITree.TauClosure (ITree.Tree Tick Nat))
        (ITree.ret r) ∧
      ITree.TauClosure.flatten
        (ITree.TauClosure.now (ITree.ret r) : ITree.TauClosure (ITree.Tree Tick Nat))
        = ITree.EffectAlgebra.interp hh (ITree.ret r) :=
  ITree.EffectAlgebra.interp_ret_witness hh r

/-- A source `tau` is one positive finite delay of the interpreted
continuation. -/
example (hh : ITree.EffectAlgebra.Handler Tick Tick) (t : ITree.Tree Tick Nat) :
    ITree.TauClosure.FiniteLater
        (ITree.TauClosure.later (ITree.TauClosure.now (ITree.EffectAlgebra.interp hh t)))
        (ITree.EffectAlgebra.interp hh t) ∧
      ITree.TauClosure.flatten
        (ITree.TauClosure.later (ITree.TauClosure.now (ITree.EffectAlgebra.interp hh t)))
        = ITree.EffectAlgebra.interp hh (ITree.tau t) :=
  ITree.EffectAlgebra.interp_tau_witness hh t

/-- The handler's completion step is exactly one positive finite delay. -/
example (hh : ITree.EffectAlgebra.Handler Tick Tick) (k : Nat → ITree.Tree Tick Nat)
    (a : Nat) :
    ITree.TauClosure.FiniteLater
        (ITree.TauClosure.later (ITree.TauClosure.now (ITree.EffectAlgebra.interp hh (k a))))
        (ITree.EffectAlgebra.interp hh (k a)) ∧
      ITree.TauClosure.flatten
        (ITree.TauClosure.later (ITree.TauClosure.now (ITree.EffectAlgebra.interp hh (k a))))
        = ITree.tau (ITree.EffectAlgebra.interp hh (k a)) :=
  ITree.EffectAlgebra.interp_completion_witness hh k a

/-! ### The still-open recursive fixpoint -/

-- The public iterator exists.
#check @ITree.iter

-- There is no `mfix`: the general recursive fixpoint is not part of this
-- library, and its future rule must supply a positive `FiniteLater` backedge
-- witness.
/-- error: Unknown identifier `_root_.ITree.mfix` -/
#guard_msgs in
#check _root_.ITree.mfix



/-! ### The axiom footprint

Every new generic theorem is pinned at the footprint it was observed to have.
The carrier sets the ceiling: mathlib's `PFunctor.M.dest` already depends on
`[propext, Classical.choice, Quot.sound]` at this revision, so even the base
revision's `ITree.dest_ret` — a `rfl` lemma — carries it, and no generic
statement mentioning the tree destructor can be narrower.  The delay's
constructor-level lemmas are narrower (`[propext]` only), and no theorem adds a
fourth axiom: the generic layer introduces no classical decision of its own,
`Classical.choice` here is mathlib's `PFunctor.M` destructor.
-/

/-- info: 'ITree.ieq_iff_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.ieq_iff_eq

/-- info: 'ITree.ieq_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.ieq_symm

/-- info: 'ITree.ieq_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.ieq_trans

/-- info: 'ITree.ieq_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.ieq_refl

/-- info: 'ITree.ieq_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.ieq_of_eq

/-- info: 'ITree.ieq_rfl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.ieq_rfl

/-- info: 'ITree.IEq.unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.IEq.unfold

/-- info: 'ITree.map_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.map_ret

/-- info: 'ITree.map_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.map_tau

/-- info: 'ITree.map_vis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.map_vis

/-- info: 'ITree.id_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.id_map

/-- info: 'ITree.comp_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.comp_map

/-- info: 'ITree.bind_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.bind_ret

/-- info: 'ITree.bind_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.bind_tau

/-- info: 'ITree.bind_vis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.bind_vis

/-- info: 'ITree.bind_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.bind_assoc

/-- info: 'ITree.bind_pure_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.bind_pure_comp

/-- info: 'ITree.pure_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.pure_bind

/-- info: 'ITree.pure_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.pure_seq

/-- info: 'ITree.seqLeft_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.seqLeft_eq

/-- info: 'ITree.seqRight_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.seqRight_eq

/-- info: 'ITree.bind_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.bind_map

/-- info: 'ITree.map_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.map_congr

/-- info: 'ITree.bind_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.bind_congr

/-- info: 'ITree.bind_congr_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.bind_congr_left

/-- info: 'ITree.bind_congr_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.bind_congr_right

/-- info: 'ITree.iter_eq_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.iter_eq_tau

/-- info: 'ITree.bindStep_ret_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.bindStep_ret_done

/-- info: 'ITree.bindStep_ret_recur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.bindStep_ret_recur

/-- info: 'ITree.bindStep_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.bindStep_tau

/-- info: 'ITree.bindStep_vis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.bindStep_vis

/-- info: 'ITree.iter_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.iter_done

/-- info: 'ITree.iter_recur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.iter_recur

/-- info: 'ITree.iter_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.iter_guard

/-- info: 'ITree.iter_recur_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.iter_recur_guard

/-- info: 'ITree.bindStep_recur_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.bindStep_recur_guard

/-- info: 'ITree.TauClosure.now_ne_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.now_ne_later

/-- info: 'ITree.TauClosure.later_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.later_inj

/-- info: 'ITree.TauClosure.finite_now' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ITree.TauClosure.finite_now

/-- info: 'ITree.TauClosure.finite_later' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ITree.TauClosure.finite_later

/-- info: 'ITree.TauClosure.infinite_forever' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.infinite_forever

/-- info: 'ITree.TauClosure.not_infinite_now' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.not_infinite_now

/-- info: 'ITree.TauClosure.Finite.not_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.Finite.not_infinite

/-- info: 'ITree.TauClosure.not_finite_forever' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.not_finite_forever

/-- info: 'ITree.TauClosure.finiteLater_later' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ITree.TauClosure.finiteLater_later

/-- info: 'ITree.TauClosure.FiniteLater.finite' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ITree.TauClosure.FiniteLater.finite

/-- info: 'ITree.TauClosure.finiteLater_later_now' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ITree.TauClosure.finiteLater_later_now

/-- info: 'ITree.TauClosure.not_finiteLater_now' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.not_finiteLater_now

/-- info: 'ITree.TauClosure.flatten_now' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.flatten_now

/-- info: 'ITree.TauClosure.flatten_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.flatten_later

/-- info: 'ITree.TauClosure.flatten_forever_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.flatten_forever_eq

/-- info: 'ITree.TauClosure.flatten_forever' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.flatten_forever

/-- info: 'ITree.TauClosure.Infinite.unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.Infinite.unfold

/-- info: 'ITree.TauClosure.Infinite.coind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.Infinite.coind

/-- info: 'ITree.EffectAlgebra.interp_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.interp_ret

/-- info: 'ITree.EffectAlgebra.interp_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.interp_tau

/-- info: 'ITree.EffectAlgebra.interp_vis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.interp_vis

/-- info: 'ITree.EffectAlgebra.interp_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.interp_bind

/-- info: 'ITree.EffectAlgebra.interp_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.interp_comp

/-- info: 'ITree.EffectAlgebra.interpHnd_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.interpHnd_eq

/-- info: 'ITree.EffectAlgebra.interp_ret_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.interp_ret_witness

/-- info: 'ITree.EffectAlgebra.interp_tau_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.interp_tau_witness

/-- info: 'ITree.EffectAlgebra.interp_completion_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.interp_completion_witness

/-- info: 'ITree.dest_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.dest_ret

/-- info: 'PFunctor.M.dest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PFunctor.M.dest


/-- info: 'ITree.IEqF_inv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ITree.IEqF_inv

/-- info: 'ITree.IEqF_monotone' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ITree.IEqF_monotone

/-- info: 'ITree.IEqF_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.IEqF_refl

/-- info: 'ITree.map_const_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.map_const_left

/-- info: 'ITree.map_const_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.map_const_right

/-- info: 'ITree.IEq.coind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.IEq.coind

/-- info: 'ITree.IEq.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.IEq.eq_1

/-- info: 'ITree.EffectAlgebra.interpHnd_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.interpHnd_ret

/-- info: 'ITree.EffectAlgebra.interpHnd_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.interpHnd_tau

/-- info: 'ITree.EffectAlgebra.interpHnd_vis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.interpHnd_vis

/-- info: 'ITree.EffectAlgebra.interp_vis_hnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.interp_vis_hnd

/- The delay relation behind the handler laws: monotonicity, its one-step
closure, the coinductive conclusion, and the equation it yields. -/
/-- info: 'ITree.EffectAlgebra.delayR_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.delayR_mono

/-- info: 'ITree.EffectAlgebra.delayR_ieqF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.delayR_ieqF

/-- info: 'ITree.EffectAlgebra.delayR_ieq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.delayR_ieq

/-- info: 'ITree.EffectAlgebra.delayR_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.delayR_eq

/- The base relations the completion, bind and composition laws feed to
`delayR_ieqF`. -/
/-- info: 'ITree.EffectAlgebra.hndBase_ieqF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.hndBase_ieqF

/-- info: 'ITree.EffectAlgebra.bindBase_ieqF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.bindBase_ieqF

/-- info: 'ITree.EffectAlgebra.compBase_ieqF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.EffectAlgebra.compBase_ieqF

/-- info: 'ITree.TauClosure.forever_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.forever_eq

/-- info: 'ITree.TauClosure.InfF_monotone' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ITree.TauClosure.InfF_monotone

/-- info: 'ITree.TauClosure.InfF.of_later_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ITree.TauClosure.InfF.of_later_eq

/-- info: 'ITree.TauClosure.Infinite.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.Infinite.eq_1


/-- info: 'ITree.TauClosure.finite_map_delay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.finite_map_delay

/-- info: 'ITree.TauClosure.infinite_map_delay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.infinite_map_delay

/-- info: 'ITree.TauClosure.flatten_map_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.flatten_map_bind

/-- info: 'ITree.TauClosure.finite_tauN' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ITree.TauClosure.finite_tauN

/-- info: 'ITree.TauClosure.infinite_tauN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.infinite_tauN

/-- info: 'ITree.TauClosure.flatten_tauN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.flatten_tauN

/-- info: 'ITree.TauClosure.flatten_finite_tauN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.flatten_finite_tauN

/-- info: 'ITree.TauClosure.flatten_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ITree.TauClosure.flatten_infinite

end ITreeImportCheck
