/-
Finite and infinite silent delay, as a first-class object.

`TauClosure α` is a tree over the **empty** event signature: it can return a
result of type `α` or take a silent step, and no visible event can occur — the
`vis` branch is eliminated by `Empty`, not excluded by convention.  `now a`
returns immediately, `later d` adds exactly one `tau`, and `forever` is
infinitely many `later`s.

The object carries its own two proof principles, which is why it exists at all:

* `Finite d a` is **inductive** — finitely many `later`s then `a`;
* `Infinite d` is a **greatest fixed point** — an infinite chain of `later`s.

They are disjoint for every delay and every result (`Finite.not_infinite`), so a
proof of one is never evidence for the other.

`flatten` turns a delay in front of a tree into that tree with the delay's
silent steps in front of it: `flatten (now t) = t`, `flatten (later d) =
tau (flatten d)`, `flatten forever = infTau`.  The last equation is why an
infinite delay is a real divergent tree and not a bottom element.

`FiniteLater d a` is the *positive* finite guard: `d` is exactly one `later` in
front of a delay that finitely reaches `a`.  It excludes `now a`, which is what
makes it usable as a witness that a recursive step really was guarded.

This module is not a port: the pinned upstream `lean4-itree` has no delay
object, its finite silent closure being `Relation.ReflTransGen` and its
divergence a `coinductive_fixpoint` predicate.  It is designed here so both
principles share one carrier, and it uses only `ITree.Core`/`ITree.IEq`.
-/
import ITree.Monad

namespace ITree

open ITree.Internal

universe u1 v u2

/-- The empty event signature: no visible event exists. -/
def EmptyEv : Type → Type := fun _ => Empty

/-- A delay in front of a result: finitely or infinitely many silent steps,
then the result.  The event signature is empty, so nothing else can happen. -/
abbrev TauClosure (α : Type u2) : Type _ := ITree EmptyEv α

namespace TauClosure

section
variable {α : Type u2}

/-! ### The delay constructors -/

/-- No delay: the result is available immediately. -/
def now (a : α) : TauClosure α := ret a

/-- One more silent step in front of a delay. -/
def later (d : TauClosure α) : TauClosure α := tau d

/-- Infinitely many silent steps: no result is ever produced. -/
def forever : TauClosure α := infTau

/-- `forever` is one `later` in front of itself. -/
theorem forever_eq : (forever : TauClosure α) = later forever :=
  infTau_eq

/-- `now` and `later` are different delays: a delay that returns is not a delay
that steps.  Stated here rather than reused from `ITree.Core`, whose
disjointness lemmas fix the result universe, because a delay's result may live
above it. -/
theorem now_ne_later (a : α) (d : TauClosure α) : now a ≠ later d := by
  intro h
  have hs := (Sigma.mk.inj (PFunctor.M.mk_inj h)).left
  cases hs

/-- One `later` is injective. -/
theorem later_inj {d d' : TauClosure α} (h : later d = later d') : d = d' := by
  simp only [later, tau, tau'] at h
  have := eq_of_heq (Sigma.mk.inj (PFunctor.M.mk_inj h)).right
  exact fin1Const_inj this

/-! ### The finite principle -/

/-- Finitely many silent steps followed by a result.  The principle is
inductive: a proof has a last `later`. -/
inductive Finite : TauClosure α → α → Prop where
  | now (a : α) : Finite (now a) a
  | later {d : TauClosure α} {a : α} : Finite d a → Finite (later d) a

/-- `now a` is a finite delay. -/
theorem finite_now (a : α) : Finite (now a) a := Finite.now a

/-- One `later` in front of a finite delay is a finite delay. -/
theorem finite_later {d : TauClosure α} {a : α} (h : Finite d a) :
    Finite (later d) a := Finite.later h

/-! ### The infinite principle -/

/-- One unfolding of infinite delay: one `later`, then again infinitely many. -/
def InfF (inf : TauClosure α → Prop) (d : TauClosure α) : Prop :=
  ∃ d' : TauClosure α, d = later d' ∧ inf d'

/-- One `later` step unfolds an infinite delay. -/
theorem InfF.of_later_eq {inf : TauClosure α → Prop} {d d' : TauClosure α}
    (heq : d = later d') (h : inf d') : InfF inf d :=
  ⟨d', heq, h⟩

theorem InfF_monotone {inf inf' : TauClosure α → Prop} (h : ∀ d, inf d → inf' d) :
    ∀ d, InfF inf d → InfF inf' d := by
  rintro d ⟨d', heq, h'⟩
  exact ⟨d', heq, h _ h'⟩

/-- Infinitely many silent steps, as the greatest fixed point of one `later`
step. -/
def Infinite (d : TauClosure α) : Prop :=
  InfF Infinite d
  coinductive_fixpoint monotonicity fun _ _ h => InfF_monotone h

/-- One unfolding of `Infinite`. -/
theorem Infinite.unfold (d : TauClosure α) : Infinite d ↔ InfF Infinite d :=
  (Infinite.eq_1 d).to_iff

/-- Coinduction: a relation contained in its own one-step unfolding is
contained in `Infinite`. -/
theorem Infinite.coind (pred : TauClosure α → Prop)
    (h : ∀ d, pred d → InfF pred d) : ∀ d, pred d → Infinite d :=
  Infinite.coinduct pred h

/-- `forever` is an infinite delay. -/
theorem infinite_forever : Infinite (forever : TauClosure α) := by
  apply Infinite.coind (fun d => d = forever)
  · intro d hd
    subst hd
    exact InfF.of_later_eq (inf := fun d : TauClosure α => d = forever) forever_eq rfl
  · rfl

/-- A delay that returns is not an infinite delay. -/
theorem not_infinite_now (a : α) : ¬ Infinite (now a) := by
  intro h
  obtain ⟨d', heq, _⟩ := (Infinite.unfold _).mp h
  exact now_ne_later a d' heq

/-! ### Disjointness

The two principles are exclusive for every delay and result: a proof of
finiteness is a proof that there is no infinite `later` chain. -/

/-- For every type, delay and result, a finite delay is not an infinite one. -/
theorem Finite.not_infinite {d : TauClosure α} {a : α} (h : Finite d a) :
    ¬ Infinite d := by
  induction h with
  | now a => exact not_infinite_now a
  | later _ ih =>
      intro hinf
      obtain ⟨d', heq, hd⟩ := (Infinite.unfold _).mp hinf
      exact ih ((later_inj heq).symm ▸ hd)

/-- `forever` is never finite. -/
theorem not_finite_forever (a : α) : ¬ Finite (forever : TauClosure α) a :=
  fun h => h.not_infinite infinite_forever

/-! ### The positive finite guard -/

/-- A delay that takes at least one `later` step and then finitely reaches the
result.  Unlike `Finite`, this excludes `now a`: it is the witness that a
recursive step was actually guarded. -/
def FiniteLater (d : TauClosure α) (a : α) : Prop :=
  ∃ d' : TauClosure α, d = later d' ∧ Finite d' a

/-- A finite delay behind one `later` is a positive finite guard. -/
theorem finiteLater_later {d : TauClosure α} {a : α} (h : Finite d a) :
    FiniteLater (later d) a :=
  ⟨d, rfl, h⟩

/-- A positive finite guard is a finite delay. -/
theorem FiniteLater.finite {d : TauClosure α} {a : α} (h : FiniteLater d a) :
    Finite d a := by
  obtain ⟨d', rfl, h'⟩ := h
  exact Finite.later h'

/-- The one-step guard of a result. -/
theorem finiteLater_later_now (a : α) : FiniteLater (later (now a)) a :=
  finiteLater_later (finite_now a)

/-- A guard that returns immediately is not a positive guard: `now a` takes no
step, so it cannot witness a guarded backedge. -/
theorem not_finiteLater_now (a : α) : ¬ FiniteLater (now a) a := by
  rintro ⟨d', h, _⟩
  exact now_ne_later a d' h

end

/-! ### Transporting a delay's results

A delay's leaf is a value; mapping it with `ITree.map` adds no silent step, only
changes the leaf.  These transports move a delay witness along a function of its
result, which is what the host relation needs to push a witness through `bind`:
the delay keeps its steps and its leaf becomes `bind · f`. -/

section Transport
variable {α : Type u2} {β : Type u2}

/-- Mapping a delay's result keeps the delay finite, and changes its result. -/
theorem finite_map_delay (g : α → β) {d : TauClosure α} {a : α}
    (h : Finite d a) : Finite (ITree.map g d) (g a) := by
  induction h with
  | now a =>
      simp only [now, ITree.map_ret]
      exact Finite.now (g a)
  | later h ih =>
      simp only [later, ITree.map_tau]
      exact Finite.later ih

/-- Mapping a delay's result keeps an infinite delay infinite.  The coinduction
predicate lives on the *target* carrier, with the source delay and its mapping as
the evidence. -/
theorem infinite_map_delay (g : α → β) {d : TauClosure α} (h : Infinite d) :
    Infinite (ITree.map g d) := by
  apply Infinite.coind
    (fun e : TauClosure β => ∃ d : TauClosure α, Infinite d ∧ e = ITree.map g d)
  · rintro e ⟨d, hd, rfl⟩
    obtain ⟨d', hd_eq, hd'⟩ := (Infinite.unfold d).mp hd
    refine ⟨ITree.map g d', ?_, ⟨d', hd', rfl⟩⟩
    rw [hd_eq, later, ITree.map_tau, later]
  · exact ⟨d, h, rfl⟩

end Transport

/-! ### Flattening a delay into a tree -/

section
variable {ε : Type u1 → Type v} {ρ : Type u2}

/-- Put the delay's silent steps in front of the tree it precedes.  Defined by
guarded coiteration: the impossible visible event is eliminated by `Empty`. -/
def flatten (d : TauClosure (ITree ε ρ)) : ITree ε ρ :=
  .corec' (fun rec d =>
    match d.dest with
    | ⟨.ret t, _⟩ => .inl t
    | ⟨.tau, c⟩ => .inr <| tau' <| rec <| c 0
    | ⟨.vis _ e, _⟩ => nomatch e
  ) d

/-- An immediate delay flattens to the tree itself, with no extra step. -/
theorem flatten_now (t : ITree ε ρ) : flatten (now t) = t := by
  unfold flatten
  rw [PFunctor.M.unfold_corec']
  rfl

/-- One `later` flattens to exactly one `tau`. -/
theorem flatten_later (d : TauClosure (ITree ε ρ)) :
    flatten (later d) = tau (flatten d) := by
  unfold flatten
  conv_lhs => rw [PFunctor.M.unfold_corec']
  simp only [later, tau, tau', PFunctor.M.dest_mk]
  refine congrArg PFunctor.M.mk ?_
  refine congrArg (PFunctor.Obj.mk (P := P ε ρ) Shape.tau) ?_
  funext i
  match i with
  | 0 => rfl

/-- `forever` flattens to one `tau` in front of itself. -/
theorem flatten_forever_eq :
    flatten (forever : TauClosure (ITree ε ρ)) =
      tau (flatten (forever : TauClosure (ITree ε ρ))) := by
  conv_lhs => rw [forever_eq]
  exact flatten_later _

/-- `forever` flattens to the tree of infinitely many silent steps, with no
extra step and no bottom element. -/
theorem flatten_forever :
    flatten (forever : TauClosure (ITree ε ρ)) = (infTau : ITree ε ρ) := by
  refine PFunctor.M.bisim
    (fun x y => x = flatten (forever : TauClosure (ITree ε ρ)) ∧ y = infTau) ?_
    _ _ ⟨rfl, rfl⟩
  rintro x y ⟨rfl, rfl⟩
  refine ⟨Shape.tau, fin1Const (flatten (forever : TauClosure (ITree ε ρ))),
    fin1Const (infTau : ITree ε ρ), ?_, ?_, ?_⟩
  · conv_lhs => rw [flatten_forever_eq]
    exact dest_tau
  · conv_lhs => rw [infTau_eq]
    exact dest_tau
  · intro i
    match i with
    | .up (.ofNat' 0) => exact ⟨rfl, rfl⟩

/-- Flattening commutes with `bind`: mapping a delay's leaf through
`fun t => bind t f` keeps the delay's steps and turns its leaf into the binding,
so the delayed result of `bind (flatten d) f` is that leaf. -/
theorem flatten_map_bind (d : TauClosure (ITree ε ρ)) (f : ρ → ITree ε ρ) :
    flatten (ITree.map (fun t => ITree.bind t f) d) = ITree.bind (flatten d) f := by
  let g : ITree ε ρ → ITree ε ρ := fun t => ITree.bind t f
  change flatten (ITree.map g d) = ITree.bind (flatten d) f
  refine PFunctor.M.bisim (fun x y => x = y ∨ ∃ e : TauClosure (ITree ε ρ),
    x = flatten (ITree.map g e) ∧ y = ITree.bind (flatten e) f) ?_ _ _
    (Or.inr ⟨d, rfl, rfl⟩)
  rintro x y (hxy | ⟨e, rfl, rfl⟩)
  · subst hxy
    refine ⟨(PFunctor.M.dest x).1, (PFunctor.M.dest x).2, (PFunctor.M.dest x).2,
      (PFunctor.Obj.eta _).symm, (PFunctor.Obj.eta _).symm, fun i => Or.inl rfl⟩
  · apply dMatchOn (x := e)
    · intro t heq
      rw [heq]
      have h1 : flatten (ITree.map g (ret t)) = ITree.bind t f := by
        have hm : ITree.map g (ret t) = ret (g t) := ITree.map_ret (ε := EmptyEv) g t
        rw [hm]
        have hnow : flatten (ret (g t)) = g t := flatten_now (g t)
        rw [hnow]
      have h2 : flatten (ret t) = t := flatten_now t
      rw [h1, h2]
      refine ⟨(PFunctor.M.dest (ITree.bind t f)).1, (PFunctor.M.dest (ITree.bind t f)).2,
        (PFunctor.M.dest (ITree.bind t f)).2,
        (PFunctor.Obj.eta _).symm, (PFunctor.Obj.eta _).symm, fun i => Or.inl rfl⟩
    · intro c heq
      rw [heq]
      have h1 : flatten (ITree.map g (tau c)) = tau (flatten (ITree.map g c)) := by
        have hm : ITree.map g (tau c) = tau (ITree.map g c) := ITree.map_tau (ε := EmptyEv) g c
        rw [hm]
        exact flatten_later _
      have h2 : flatten (tau c) = tau (flatten c) := flatten_later c
      rw [h1, h2, ITree.bind_tau]
      refine ⟨Shape.tau, fin1Const (flatten (ITree.map g c)),
        fin1Const (ITree.bind (flatten c) f), ?_, ?_, ?_⟩
      · exact dest_tau
      · exact dest_tau
      · intro i
        match i with
        | .up (.ofNat' 0) => exact Or.inr ⟨c, rfl, rfl⟩
    · intro β' e' _ _
      nomatch e'

end

/-! ### Silent towers in front of a delay

`tauN n d` is the delay `d` behind `n` more `later`s.  The two principles and
`flatten` cross such a tower unchanged apart from the count, which is what lets a
finite delay be composed in front of another delay without leaving the carrier. -/

section Towers
variable {α : Type u2}

/-- A finite delay behind a tower of `later`s is still finite, at the same
result. -/
theorem finite_tauN {d : TauClosure α} {a : α} (n : Nat) (h : Finite d a) :
    Finite (tauN n d) a := by
  induction n with
  | zero => exact h
  | succ n ih =>
      change Finite (later (tauN n d)) a
      exact Finite.later ih

/-- An infinite delay behind a tower of `later`s is still infinite. -/
theorem infinite_tauN {d : TauClosure α} (n : Nat) (h : Infinite d) :
    Infinite (tauN n d) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      exact (Infinite.unfold (tauN (n + 1) d)).mpr ⟨tauN n d, rfl, ih⟩

end Towers

section TowersFlatten
variable {ε : Type u1 → Type v} {ρ : Type u2}

/-- A tower of `later`s in front of a delay flattens to the same tower of `tau`s
in front of the delay's flattening. -/
theorem flatten_tauN (n : Nat) (d : TauClosure (ITree ε ρ)) :
    flatten (tauN n d) = tauN n (flatten d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change flatten (later (tauN n d)) = tauN (n + 1) (flatten d)
      rw [flatten_later, ih]
      rfl

/-- A finite delay flattens to exactly its number of `tau`s in front of the tree
it reaches. -/
theorem flatten_finite_tauN {d : TauClosure (ITree ε ρ)} {q : ITree ε ρ}
    (h : Finite d q) : ∃ n : Nat, flatten d = tauN n q := by
  induction h with
  | now q => exact ⟨0, flatten_now q⟩
  | later _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by rw [flatten_later, hn]; rfl⟩

/-- Every infinite delay flattens to the tree of infinitely many silent
steps. -/
theorem flatten_infinite {d : TauClosure (ITree ε ρ)} (h : Infinite d) :
    flatten d = (infTau : ITree ε ρ) := by
  refine PFunctor.M.bisim
    (fun x y => (∃ d : TauClosure (ITree ε ρ), Infinite d ∧ flatten d = x) ∧
      y = (infTau : ITree ε ρ)) ?_ _ _ ⟨⟨d, h, rfl⟩, rfl⟩
  rintro x y ⟨⟨d, hd, hfl⟩, rfl⟩
  subst hfl
  obtain ⟨d', hd_eq, hd'⟩ := (Infinite.unfold d).mp hd
  refine ⟨Shape.tau, fin1Const (flatten d'), fin1Const (infTau : ITree ε ρ), ?_, ?_, ?_⟩
  · conv_lhs => rw [hd_eq, flatten_later]
    exact dest_tau
  · conv_lhs => rw [infTau_eq]
    exact dest_tau
  · intro i
    match i with
    | .up (.ofNat' 0) => exact ⟨⟨d', hd', rfl⟩, rfl⟩

end TowersFlatten

end TauClosure

end ITree
