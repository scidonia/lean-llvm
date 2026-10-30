/-
Postcondition-indexed, directed simulation of handled interaction trees.

The trees compared here are **bare handled trees**: `handle frame m t` has
already folded memory into the tree, so the relation has no memory index and no
frame parameter of its own.  What used to be a private memory access is now a
`tau` that the handler inserted, and what used to be a visible access is now an
`ObsEv` node whose annotation the handler computed from its own memory.  The
frame survives in the postcondition a caller chooses
(`simtt (Outcome.AgreesOutside frame)`) and in the handler that produced the two
trees.

`SilentStep` is therefore exactly `tau`.  `SilentHead` is its inductive
reflexive-transitive closure — finitely many silent steps — and
`SilentDiverges` is the greatest fixed point of the same step, so divergence is
a coinductive statement and does not follow from a budget.

`simtt post` is the greatest fixed point of `SimttF`: after finitely many silent
steps on either side, matching terminals are related.

* a `ret` leaf carrying a defined outcome on both sides is related when `post`
  holds of the two outcomes; `post` sees only `.ret`-valued outcomes and never
  `ub`;
* `timeout` matches only `timeout`;
* a UB terminal is a `ret` leaf carrying `Outcome.ub` or a `vis ObsEv.ub` node.
  The two shapes are one class in both directions: a left UB terminal requires a
  right one, and a right UB terminal admits any completed left return, defined or
  `ub`, without consulting `post`;
* a left silent divergence is the bottom: it is related to any right behaviour
  that does not reach `timeout` through silent steps;
* a right silent divergence requires a left silent divergence;
* a visible load matches only the same address, type and handler annotation —
  including `none` on both sides — and then compares its unit continuations; a
  visible store matches address, type and value and continues with each side's
  own continuation; a visible call matches callee and arguments and quantifies
  over all responses.

The left tree is the target and the right tree the source.  There is no
symmetric equivalence: symmetry, where wanted, is the conjunction of the two
directions.
-/
import LeanLLVM.ITree.MemoryEffect
import ITree.Coinduction

namespace LeanLLVM.ITree

open LeanLLVM
open _root_.ITree
open Lean.Order

/-! ### Distinct response types and events

The terminal cases below reject a silent closure that ends at the wrong node, so
the shapes have to be provably different.
-/

theorem empty_ne_option_value : (Empty : Type) ≠ Option Value := by
  intro h
  exact nomatch (Eq.mpr h (some (.int 64 0)))

theorem empty_ne_unit : (Empty : Type) ≠ Unit := by
  intro h
  exact nomatch (Eq.mpr h ())

/-- Two loads differing in address, type or annotation are different events. -/
theorem obs_load_inj {addr : Nat} {ty : Ty} {r : Option Value} {addr' : Nat} {ty' : Ty}
    {r' : Option Value} (h : (ObsEv.load addr ty r : ObsEv Unit) = ObsEv.load addr' ty' r') :
    addr = addr' ∧ ty = ty' ∧ r = r' := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- Two stores differing in address, type or value are different events. -/
theorem obs_store_inj {addr : Nat} {ty : Ty} {v : Value} {addr' : Nat} {ty' : Ty}
    {v' : Value} (h : (ObsEv.store addr ty v : ObsEv Unit) = ObsEv.store addr' ty' v') :
    addr = addr' ∧ ty = ty' ∧ v = v' := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- Two calls differing in callee or arguments are different events. -/
theorem obs_call_inj {callee : String} {args : List Value} {callee' : String}
    {args' : List Value}
    (h : (ObsEv.call callee args : ObsEv (Option Value)) = ObsEv.call callee' args') :
    callee = callee' ∧ args = args' := by
  cases h
  exact ⟨rfl, rfl⟩

theorem ev_load_ne_store (addr : Nat) (ty : Ty) (r : Option Value) (addr' : Nat)
    (ty' : Ty) (v' : Value) :
    (ObsEv.load addr ty r : ObsEv Unit) ≠ ObsEv.store addr' ty' v' := by
  intro h
  cases h

theorem unit_ne_option_value : (Unit : Type) ≠ Option Value := by
  intro h
  have : Subsingleton (Option Value) := h ▸ (inferInstance : Subsingleton Unit)
  cases Subsingleton.elim (none : Option Value) (some (.int 64 0))


theorem vis_load_ne_store {addr : Nat} {ty : Ty} {r : Option Value}
    {addr' : Nat} {ty' : Ty} {v : Value} {k k' : Unit → OTree} :
    (vis (ObsEv.load addr ty r) k : OTree) ≠ vis (ObsEv.store addr' ty' v) k' := by
  intro h
  exact ev_load_ne_store addr ty r addr' ty' v (vis_inj h).1

theorem vis_load_ne_call {addr : Nat} {ty : Ty} {r : Option Value} {callee : String}
    {args : List Value} {k : Unit → OTree} {k' : Option Value → OTree} :
    (vis (ObsEv.load addr ty r) k : OTree) ≠ vis (ObsEv.call callee args) k' :=
  vis_ne_of_type_ne (h := unit_ne_option_value)

theorem vis_store_ne_call {addr : Nat} {ty : Ty} {v : Value} {callee : String}
    {args : List Value} {k : Unit → OTree} {k' : Option Value → OTree} :
    (vis (ObsEv.store addr ty v) k : OTree) ≠ vis (ObsEv.call callee args) k' :=
  vis_ne_of_type_ne (h := unit_ne_option_value)

theorem vis_ub_ne_load (k : Empty → OTree) (addr : Nat) (ty : Ty) (r : Option Value)
    (k' : Unit → OTree) :
    (vis ObsEv.ub k : OTree) ≠ vis (ObsEv.load addr ty r) k' :=
  vis_ne_of_type_ne (h := empty_ne_unit)
theorem vis_ub_ne_store (k : Empty → OTree) (addr : Nat) (ty : Ty) (v : Value)
    (k' : Unit → OTree) :
    (vis ObsEv.ub k : OTree) ≠ vis (ObsEv.store addr ty v) k' :=
  vis_ne_of_type_ne (h := empty_ne_unit)

theorem vis_ub_ne_call (k : Empty → OTree) (callee : String) (args : List Value)
    (k' : Option Value → OTree) :
    (vis ObsEv.ub k : OTree) ≠ vis (ObsEv.call callee args) k' :=
  vis_ne_of_type_ne (h := empty_ne_option_value)

theorem vis_timeout_ne_load (k : Empty → OTree) (addr : Nat) (ty : Ty) (r : Option Value)
    (k' : Unit → OTree) :
    (vis ObsEv.timeout k : OTree) ≠ vis (ObsEv.load addr ty r) k' :=
  vis_ne_of_type_ne (h := empty_ne_unit)
theorem vis_timeout_ne_store (k : Empty → OTree) (addr : Nat) (ty : Ty) (v : Value)
    (k' : Unit → OTree) :
    (vis ObsEv.timeout k : OTree) ≠ vis (ObsEv.store addr ty v) k' :=
  vis_ne_of_type_ne (h := empty_ne_unit)

theorem vis_timeout_ne_call (k : Empty → OTree) (callee : String) (args : List Value)
    (k' : Option Value → OTree) :
    (vis ObsEv.timeout k : OTree) ≠ vis (ObsEv.call callee args) k' :=
  vis_ne_of_type_ne (h := empty_ne_option_value)

theorem ub_ne_timeout : (ObsEv.ub : ObsEv Empty) ≠ ObsEv.timeout := by
  intro h
  cases h

theorem vis_ub_ne_timeout (k k' : Empty → OTree) :
    (vis ObsEv.ub k : OTree) ≠ vis ObsEv.timeout k' := by
  intro h
  exact ub_ne_timeout (vis_inj h).1
/-- One silent step: a `tau`.  A private memory access is silent because the
handler inserted the `tau`, never because this relation inspects a memory. -/
inductive SilentStep : OTree → OTree → Prop where
  | step (t : OTree) : SilentStep (tau t) t

/-- The reflexive-transitive closure of `SilentStep`: finitely many silent
steps.  It is inductive, so it never witnesses divergence. -/
def SilentHead : OTree → OTree → Prop :=
  Relation.ReflTransGen SilentStep

theorem SilentHead.refl (p : OTree) : SilentHead p p :=
  Relation.ReflTransGen.refl

theorem SilentHead.trans {p q r : OTree}
    (h1 : SilentHead p q) (h2 : SilentHead q r) : SilentHead p r :=
  Relation.ReflTransGen.trans h1 h2

theorem SilentHead.step {p q r : OTree} (h1 : SilentStep p q)
    (h2 : SilentHead q r) : SilentHead p r :=
  Relation.ReflTransGen.head h1 h2

/-- A closure either is already finished or begins with one step. -/
theorem SilentHead_inv {p q : OTree} (h : SilentHead p q) :
    p = q ∨ ∃ p', SilentStep p p' ∧ SilentHead p' q := by
  induction h with
  | refl => exact Or.inl rfl
  | tail hrest hstep ih =>
      rcases ih with hpq | ⟨p', hstep', hrest'⟩
      · subst hpq
        exact Or.inr ⟨_, hstep, SilentHead.refl _⟩
      · exact Or.inr ⟨p', hstep', Relation.ReflTransGen.tail hrest' hstep⟩

/-- Induction along a closure through a set of trees closed under `SilentStep`. -/
theorem SilentHead.cases_of_closed {P : OTree → Prop}
    (hP : ∀ p, P p → ∀ q, SilentStep p q → P q)
    {p q : OTree} (h : SilentHead p q) : P p → P q := by
  induction h with
  | refl => exact id
  | tail _ hstep ih => intro hp; exact hP _ (ih hp) _ hstep

/-- Inversion of one silent step. -/
theorem SilentStep_inv {p q : OTree} (h : SilentStep p q) :
    ∃ t : OTree, p = tau t ∧ q = t := by
  cases h
  exact ⟨_, rfl, rfl⟩

/-- A tree has at most one silent step. -/
theorem SilentStep.det {p q r : OTree} (h1 : SilentStep p q)
    (h2 : SilentStep p r) : q = r := by
  obtain ⟨t, hp, hq⟩ := SilentStep_inv h1
  obtain ⟨t', hp', hr⟩ := SilentStep_inv h2
  have htt : tau t = tau t' := by rw [← hp, hp']
  rw [hq, hr, tau_inj htt]

/-- A tree from which no silent step is possible is its own only closure. -/
theorem SilentHead.eq_of_no_step {p q : OTree}
    (hno : ∀ r, SilentStep p r → False) (h : SilentHead p q) : q = p :=
  SilentHead.cases_of_closed (P := fun r => r = p)
    (fun r hr s hstep => by subst hr; exact (hno s hstep).elim) h rfl

/-- No silent step leaves a returned outcome. -/
theorem ret_no_step {o : Outcome} : ∀ q : OTree, ¬ SilentStep (ret o) q := by
  intro q h
  obtain ⟨t, ht, _⟩ := SilentStep_inv h
  exact ret_ne_tau ht

/-- No silent step leaves a visible `ObsEv` node. -/
theorem vis_no_step {α : Type} (e : ObsEv α) (k : α → OTree) :
    ∀ q : OTree, ¬ SilentStep (vis e k) q := by
  intro q h
  obtain ⟨t, ht, _⟩ := SilentStep_inv h
  exact tau_ne_vis e k ht.symm

theorem ub_no_step {k : Empty → OTree} :
    ∀ q : OTree, ¬ SilentStep (vis ObsEv.ub k) q :=
  vis_no_step ObsEv.ub k

theorem timeout_no_step {k : Empty → OTree} :
    ∀ q : OTree, ¬ SilentStep (vis ObsEv.timeout k) q :=
  vis_no_step ObsEv.timeout k

theorem SilentHead_ret_self {o : Outcome} {q : OTree}
    (h : SilentHead (ret o) q) : q = ret o :=
  SilentHead.eq_of_no_step ret_no_step h

theorem SilentHead_vis_self {α : Type} {e : ObsEv α} {k : α → OTree} {q : OTree}
    (h : SilentHead (vis e k) q) : q = vis e k :=
  SilentHead.eq_of_no_step (vis_no_step e k) h

theorem SilentHead_ub_self {k : Empty → OTree} {q : OTree}
    (h : SilentHead (vis ObsEv.ub k) q) : q = vis ObsEv.ub k :=
  SilentHead_vis_self h

theorem SilentHead_timeout_self {k : Empty → OTree} {q : OTree}
    (h : SilentHead (vis ObsEv.timeout k) q) : q = vis ObsEv.timeout k :=
  SilentHead_vis_self h

/-- A closure from a `tau` is empty, or begins through that `tau`. -/
theorem SilentHead.tau_strip {t : OTree} {q : OTree} (h : SilentHead (tau t) q)
    (hne : q ≠ tau t) : SilentHead t q := by
  rcases SilentHead_inv h with hpq | ⟨p', hstep, hrest⟩
  · exact absurd hpq.symm hne
  · obtain ⟨t', hp, hq⟩ := SilentStep_inv hstep
    rw [hq] at hrest
    rw [← tau_inj hp] at hrest
    exact hrest

/-! ### Silent divergence -/

/-- One silent step with a divergent continuation. -/
inductive DivF (sim : OTree → Prop) : OTree → Prop where
  | step {p q : OTree} (h : SilentStep p q) (hs : sim q) : DivF sim p

theorem DivF_monotone {sim sim' : OTree → Prop}
    (h : ∀ p, sim p → sim' p) : ∀ p, DivF sim p → DivF sim' p := by
  intro p hp
  cases hp with
  | step hs hsim => exact DivF.step hs (h _ hsim)

/-- Infinite silent progress: the greatest fixed point of `DivF`.  It is not a
finite fuel-exhaustion marker; it witnesses a genuinely infinite path. -/
def SilentDiverges : OTree → Prop :=
  DivF SilentDiverges
  coinductive_fixpoint monotonicity fun _ _ hsim => DivF_monotone hsim

theorem SilentDiverges.coind (pred : OTree → Prop)
    (h : ∀ p, pred p → DivF pred p) : ∀ p, pred p → SilentDiverges p :=
  SilentDiverges.coinduct pred h

theorem SilentDiverges.intro {p q : OTree} (hstep : SilentStep p q)
    (h : SilentDiverges q) : SilentDiverges p :=
  (congrFun SilentDiverges.eq_1 p).mpr (DivF.step hstep h)

/-- Prepending a finite silent closure to an infinite silent path keeps it
divergent. -/
theorem SilentDiverges.of_silentHead {p q : OTree} (hhead : SilentHead p q) :
    SilentDiverges q → SilentDiverges p := by
  induction hhead with
  | refl => exact id
  | tail _ hstep ih => intro hd; exact ih (SilentDiverges.intro hstep hd)

/-- One silent step from `infTau` stays at `infTau`. -/
theorem infTau_step_eq {q : OTree} (h : SilentStep infTau q) : q = infTau := by
  obtain ⟨t, ht, hq⟩ := SilentStep_inv h
  rw [infTau_eq] at ht
  rw [hq]
  exact (tau_inj ht).symm

/-- Every finite silent closure of `infTau` stays at `infTau`. -/
theorem SilentHead_infTau_self {q : OTree} (h : SilentHead infTau q) : q = infTau :=
  SilentHead.cases_of_closed (P := fun r => r = infTau)
    (fun p hp q hstep => by subst hp; exact infTau_step_eq hstep) h rfl

/-- `infTau` takes a silent step to itself. -/
theorem infTau_self_step : SilentStep infTau infTau :=
  Eq.mp (congrArg (fun t => SilentStep t infTau) infTau_eq.symm) (SilentStep.step infTau)

/-- `infTau` diverges silently. -/
theorem infTau_diverges : SilentDiverges infTau := by
  apply SilentDiverges.coind (fun p => p = infTau)
  · intro p hp
    subst hp
    exact DivF.step infTau_self_step rfl
  · rfl

theorem not_silentDiverges_of_no_step {p : OTree}
    (hno : ∀ q, SilentStep p q → False) : ¬ SilentDiverges p := by
  intro h
  have h' : DivF SilentDiverges p := (congrFun SilentDiverges.eq_1 p).mp h
  cases h' with
  | step hstep _ => exact hno _ hstep

theorem not_silentDiverges_ret {o : Outcome} : ¬ SilentDiverges (ret o) :=
  not_silentDiverges_of_no_step ret_no_step

theorem not_silentDiverges_ub {k : Empty → OTree} :
    ¬ SilentDiverges (vis ObsEv.ub k) :=
  not_silentDiverges_of_no_step ub_no_step

theorem not_silentDiverges_timeout {k : Empty → OTree} :
    ¬ SilentDiverges (vis ObsEv.timeout k) :=
  not_silentDiverges_of_no_step timeout_no_step

theorem not_silentDiverges_vis {α : Type} (e : ObsEv α) (k : α → OTree) :
    ¬ SilentDiverges (vis e k) :=
  not_silentDiverges_of_no_step (vis_no_step e k)

/-! ### Timeout reachability -/

/-- A tree from which silent progress reaches `timeout` through finitely many
steps.  This is the semantic notion of a budget timeout. -/
def TimeoutReachable (p : OTree) : Prop :=
  ∃ q, SilentHead p q ∧ ∃ k : Empty → OTree, q = vis ObsEv.timeout k

theorem not_timeoutReachable_ret {o : Outcome} : ¬ TimeoutReachable (ret o) := by
  rintro ⟨q, hq, k, hk⟩
  rw [SilentHead_ret_self hq] at hk
  exact ret_ne_vis ObsEv.timeout k hk

theorem not_timeoutReachable_ub {k : Empty → OTree} :
    ¬ TimeoutReachable (vis ObsEv.ub k) := by
  rintro ⟨q, hq, k', hk⟩
  rw [SilentHead_ub_self hq] at hk
  exact ub_ne_timeout (vis_inj hk).1
/-- A silent step cannot make a tree that reaches `timeout` out of one that does
not: the step is unique, so every closure either stops at the source or
continues through it. -/
theorem not_timeoutReachable_of_silentStep {p q : OTree}
    (h : SilentStep p q) (hnt : ¬ TimeoutReachable q) : ¬ TimeoutReachable p := by
  intro hp
  rcases hp with ⟨r, hr, k, hk⟩
  rcases SilentHead_inv hr with hpr | ⟨p', hstep, hrest⟩
  · rw [← hpr] at hk
    rw [hk] at h
    exact timeout_no_step (k := k) q h
  · have hpq : p' = q := SilentStep.det hstep h
    subst hpq
    exact hnt ⟨r, hrest, k, hk⟩

/-- The same for a finite silent closure. -/
theorem not_timeoutReachable_of_silentHead {p q : OTree}
    (h : SilentHead p q) : ¬ TimeoutReachable q → ¬ TimeoutReachable p := by
  induction h with
  | refl => intro hnt; exact hnt
  | tail hrest hstep ih =>
      intro hnt
      exact ih (not_timeoutReachable_of_silentStep hstep hnt)

/-! ### UB terminals -/

/-- The two shapes a UB terminal takes: a `ret` leaf carrying `Outcome.ub`, or a
`vis ObsEv.ub` node.  The relation treats them as one class, so neither shape can
slip past the left-UB rule through `post`, and either shape admits a completed
left return on the right. -/
inductive UbTerminal : OTree → Prop where
  | retLeaf : UbTerminal (ret Outcome.ub)
  | ubNode (k : Empty → OTree) : UbTerminal (vis ObsEv.ub k)

/-- A tree whose silent closure ends in a UB terminal. -/
inductive ReachesUb : OTree → Prop where
  | retLeaf {p : OTree} (h : SilentHead p (ret Outcome.ub)) : ReachesUb p
  | ubNode {p : OTree} {k : Empty → OTree} (h : SilentHead p (vis ObsEv.ub k)) :
      ReachesUb p

/-- A UB terminal reaches itself through the empty closure. -/
theorem reachesUb_of_terminal {p : OTree} (h : UbTerminal p) : ReachesUb p := by
  cases h with
  | retLeaf => exact ReachesUb.retLeaf (SilentHead.refl _)
  | ubNode k => exact ReachesUb.ubNode (SilentHead.refl _)

/-- Prepending a silent closure keeps a tree that reaches a UB terminal reaching
one. -/
theorem ReachesUb.of_silentHead {p p' : OTree} (h : SilentHead p p')
    (hp' : ReachesUb p') : ReachesUb p := by
  cases hp' with
  | retLeaf h2 => exact ReachesUb.retLeaf (SilentHead.trans h h2)
  | ubNode h2 => exact ReachesUb.ubNode (SilentHead.trans h h2)

/-- A defined return is not a UB terminal. -/
theorem not_reachesUb_ret {v : Option Value} {mem : Mem} :
    ¬ ReachesUb (ret (Outcome.ret v mem)) := by
  intro h
  cases h with
  | retLeaf h' =>
      exact Outcome.noConfusion (ret_inj (SilentHead_ret_self h'))
  | ubNode h' =>
      exact (ret_ne_vis ObsEv.ub _).symm (SilentHead_ret_self h')

/-- A budget timeout is not a UB terminal. -/
theorem not_reachesUb_timeout {k : Empty → OTree} :
    ¬ ReachesUb (vis ObsEv.timeout k) := by
  intro h
  cases h with
  | retLeaf h' =>
      exact ret_ne_vis ObsEv.timeout _ (SilentHead_timeout_self h')
  | ubNode h' =>
      exact ub_ne_timeout (vis_inj (SilentHead_timeout_self h')).1

/-- A silent divergence is not a UB terminal. -/
theorem not_reachesUb_infTau : ¬ ReachesUb infTau := by
  intro h
  cases h with
  | retLeaf h' =>
      have e := SilentHead_infTau_self h'
      rw [infTau_eq] at e
      exact ret_ne_tau e
  | ubNode h' =>
      have e := SilentHead_infTau_self h'
      rw [infTau_eq] at e
      exact (tau_ne_vis ObsEv.ub _).symm e

/-! ### The relation -/

/-- One unfolding of `simtt`: after finitely many silent steps on both sides,
matching terminals. -/
inductive SimttF (post : Outcome → Outcome → Prop) (sim : OTree → OTree → Prop) :
    OTree → OTree → Prop where
  /-- Two defined outcomes related by `post`.  The outcomes are `.ret`-valued:
  `post` is never applied to `ub`. -/
  | ret_ret {p q : OTree} {v₁ v₂ : Option Value} {mem₁ mem₂ : Mem}
      (h1 : SilentHead p (ret (Outcome.ret v₁ mem₁)))
      (h2 : SilentHead q (ret (Outcome.ret v₂ mem₂)))
      (hp : post (Outcome.ret v₁ mem₁) (Outcome.ret v₂ mem₂)) : SimttF post sim p q
  /-- A right UB terminal admits any completed left return, defined or `ub`, and
  `post` is not consulted. -/
  | right_ub_ret {p q : OTree} {o : Outcome}
      (h1 : SilentHead p (ret o)) (h2 : ReachesUb q) : SimttF post sim p q
  /-- A left UB terminal requires a right UB terminal; the `ret` leaf carrying
  `Outcome.ub` and the `vis ObsEv.ub` node are one class. -/
  | ub {p q : OTree} (h1 : ReachesUb p) (h2 : ReachesUb q) : SimttF post sim p q
  /-- A budget timeout matches only a budget timeout. -/
  | timeout {p q : OTree} (k1 k2 : Empty → OTree)
      (h1 : SilentHead p (vis ObsEv.timeout k1))
      (h2 : SilentHead q (vis ObsEv.timeout k2)) : SimttF post sim p q
  /-- Left silent divergence is the bottom against a right side that cannot
  silently reach `timeout`. -/
  | left_diverges {p q : OTree} (hdiv : SilentDiverges p)
      (hnt : ¬ TimeoutReachable q) : SimttF post sim p q
  /-- Right silent divergence requires left silent divergence. -/
  | right_diverges {p q : OTree} (hdiv2 : SilentDiverges q)
      (hdiv1 : SilentDiverges p) : SimttF post sim p q
  /-- The same visible load matches: the handler annotated it identically, and
  the unit continuations are related. -/
  | vis_load {p q : OTree} (addr : Nat) (ty : Ty) (r : Option Value)
      (k1 k2 : Unit → OTree)
      (h1 : SilentHead p (vis (ObsEv.load addr ty r) k1))
      (h2 : SilentHead q (vis (ObsEv.load addr ty r) k2))
      (hs : sim (k1 ()) (k2 ())) : SimttF post sim p q
  /-- The same visible store matches and its continuations are related. -/
  | vis_store {p q : OTree} (addr : Nat) (ty : Ty) (v : Value)
      (k1 k2 : Unit → OTree)
      (h1 : SilentHead p (vis (ObsEv.store addr ty v) k1))
      (h2 : SilentHead q (vis (ObsEv.store addr ty v) k2))
      (hs : sim (k1 ()) (k2 ())) : SimttF post sim p q
  /-- The same call matches for every response. -/
  | vis_call {p q : OTree} (callee : String) (args : List Value)
      (k1 k2 : Option Value → OTree)
      (h1 : SilentHead p (vis (ObsEv.call callee args) k1))
      (h2 : SilentHead q (vis (ObsEv.call callee args) k2))
      (hs : ∀ r, sim (k1 r) (k2 r)) : SimttF post sim p q

theorem SimttF_monotone {post} {sim sim' : OTree → OTree → Prop}
    (h : ∀ p q, sim p q → sim' p q) :
    ∀ p q, SimttF post sim p q → SimttF post sim' p q := by
  intro p q hpq
  cases hpq with
  | ret_ret h1 h2 hp => exact SimttF.ret_ret h1 h2 hp
  | right_ub_ret h1 h2 => exact SimttF.right_ub_ret h1 h2
  | ub h1 h2 => exact SimttF.ub h1 h2
  | timeout k1 k2 h1 h2 => exact SimttF.timeout k1 k2 h1 h2
  | left_diverges hdiv hnt => exact SimttF.left_diverges hdiv hnt
  | right_diverges h2 h1 => exact SimttF.right_diverges h2 h1
  | vis_load addr ty r k1 k2 h1 h2 hs =>
      exact SimttF.vis_load addr ty r k1 k2 h1 h2 (h _ _ hs)
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact SimttF.vis_store addr ty v k1 k2 h1 h2 (h _ _ hs)
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact SimttF.vis_call callee args k1 k2 h1 h2 (fun r => h _ _ (hs r))

/-- The reverse-implication complete lattice on `Prop`, lifted to the two tree
indices; the same instance Lean's `coinductive_fixpoint` builds for a
coinductive predicate. -/
private instance instSimttPartialOrder : Lean.Order.PartialOrder (OTree → OTree → Prop) :=
  inferInstanceAs (Lean.Order.PartialOrder (OTree → OTree → ReverseImplicationOrder))

private instance instSimttLattice : Lean.Order.CompleteLattice (OTree → OTree → Prop) :=
  inferInstanceAs (Lean.Order.CompleteLattice (OTree → OTree → ReverseImplicationOrder))

/-- `SimttF` is monotone in the reverse-implication order, which is what `plfp`
needs. -/
theorem SimttF_monotone_order (post) : monotone (SimttF post) := by
  intro x y hxy
  exact SimttF_monotone hxy

/-- The directed simulation: left is the target, right the source.  It is Paco's
parameterised least fixed point of `SimttF` at the top assumption; in the
reverse-implication order that is its greatest fixed point. -/
def simtt (post : Outcome → Outcome → Prop) : OTree → OTree → Prop :=
  plfp (SimttF post) (hm := SimttF_monotone_order post)
    (Lean.Order.top : OTree → OTree → Prop)

/-- `simtt` is Paco's parameterised least fixed point at the top assumption. -/
theorem simtt_eq_plfp (post) :
    simtt post = plfp (SimttF post) (hm := SimttF_monotone_order post)
      (Lean.Order.top : OTree → OTree → Prop) := rfl

/-- Unfolding of `simtt`, by Paco's `plfp_unfold` and the fact that the top
assumption is inert. -/
theorem simtt_unfold (post) : simtt post = SimttF post (simtt post) := by
  have h : plfp (SimttF post) (hm := SimttF_monotone_order post)
      (Lean.Order.top : OTree → OTree → Prop) =
      SimttF post (plfp (SimttF post) (hm := SimttF_monotone_order post)
        (Lean.Order.top : OTree → OTree → Prop)) := by
    conv_lhs => rw [plfp_unfold (hm := SimttF_monotone_order post)]
    congr 1
    simp only [uplfp]
    rw [CompleteLattice.meet_comm, CompleteLattice.meet_top]
  rw [simtt]
  exact h

/-- Unfolding of `simtt` into its one-step functional. -/
theorem simtt_iff (post) (p q : OTree) :
    simtt post p q ↔ SimttF post (simtt post) p q :=
  (congrArg (fun f => f p q) (simtt_unfold post)).to_iff

/-- Coinduction: a relation contained in `SimttF` is contained in `simtt`. -/
theorem simtt.coind (post) (pred : OTree → OTree → Prop)
    (h : ∀ p q, pred p q → SimttF post pred p q) :
    ∀ p q, pred p q → simtt post p q := by
  intro p q hpq
  rw [simtt, ← plfp_init (hm := SimttF_monotone_order post)]
  exact lfp_le_of_le_monotone (SimttF post) (hm := SimttF_monotone_order post) pred h p q hpq

/-! ### Positive and negative rules -/

/-- Return inversion: two `ret` leaves carrying defined outcomes are related
exactly when `post` holds of those outcomes.  A `ret` leaf carrying `Outcome.ub`
is a UB terminal, not a return, and `post` never sees it. -/
theorem simtt_ret_ret_iff (post) (v v' : Option Value) (mem mem' : Mem) :
    simtt post (ret (Outcome.ret v mem)) (ret (Outcome.ret v' mem')) ↔
      post (Outcome.ret v mem) (Outcome.ret v' mem') := by
  constructor
  · intro h
    have hF := (simtt_iff post _ _).mp h
    cases hF with
    | ret_ret h1 h2 hp =>
        have e1 := ret_inj (SilentHead_ret_self h1)
        have e2 := ret_inj (SilentHead_ret_self h2)
        rw [← e1, ← e2]
        exact hp
    | right_ub_ret h1 h2 => exact (not_reachesUb_ret h2).elim
    | ub h1 h2 => exact (not_reachesUb_ret h1).elim
    | timeout k1 k2 h1 h2 =>
        exact ((ret_ne_vis ObsEv.timeout k1).symm (SilentHead_ret_self h1)).elim
    | left_diverges hdiv hnt => exact (not_silentDiverges_ret hdiv).elim
    | right_diverges hdiv2 hdiv1 => exact (not_silentDiverges_ret hdiv2).elim
    | vis_load addr ty r k1 k2 h1 h2 hs =>
        exact ((ret_ne_vis (ObsEv.load addr ty r) k1).symm (SilentHead_ret_self h1)).elim
    | vis_store addr ty v k1 k2 h1 h2 hs =>
        exact ((ret_ne_vis (ObsEv.store addr ty v) k1).symm (SilentHead_ret_self h1)).elim
    | vis_call callee args k1 k2 h1 h2 hs =>
        exact ((ret_ne_vis (ObsEv.call callee args) k1).symm (SilentHead_ret_self h1)).elim
  · intro hp
    exact (simtt_iff post _ _).mpr (SimttF.ret_ret (SilentHead.refl _) (SilentHead.refl _) hp)

/-- Two UB terminals are related, whatever their shape and regardless of
`post`. -/
theorem simtt_ub_terminal (post) {p q : OTree} (hp : UbTerminal p)
    (hq : UbTerminal q) : simtt post p q :=
  (simtt_iff post _ _).mpr (SimttF.ub (reachesUb_of_terminal hp) (reachesUb_of_terminal hq))

/-- A right UB terminal admits any completed left return, defined or `ub`. -/
theorem simtt_ret_ub_terminal (post) (o : Outcome) {q : OTree}
    (hq : UbTerminal q) : simtt post (ret o) q :=
  (simtt_iff post _ _).mpr (SimttF.right_ub_ret (SilentHead.refl _) (reachesUb_of_terminal hq))

/-- A right `ub` node admits a completed left return. -/
theorem simtt_ret_ub (post) (o : Outcome) :
    simtt post (ret o) (vis ObsEv.ub Empty.elim) :=
  simtt_ret_ub_terminal post o (UbTerminal.ubNode Empty.elim)

/-- A left `ub` node is related to a right `ub` node. -/
theorem simtt_ub_ub (post) (k1 k2 : Empty → OTree) :
    simtt post (vis ObsEv.ub k1) (vis ObsEv.ub k2) :=
  simtt_ub_terminal post (UbTerminal.ubNode k1) (UbTerminal.ubNode k2)

/-- A budget timeout matches itself. -/
theorem simtt_timeout_timeout (post) (k1 k2 : Empty → OTree) :
    simtt post (vis ObsEv.timeout k1) (vis ObsEv.timeout k2) :=
  (simtt_iff post _ _).mpr (SimttF.timeout k1 k2 (SilentHead.refl _) (SilentHead.refl _))

/-- Left silent divergence is the bottom against a right side that cannot
silently reach a timeout. -/
theorem simtt_diverges (post) {p q : OTree}
    (hdiv : SilentDiverges p) (hnt : ¬ TimeoutReachable q) : simtt post p q :=
  (simtt_iff post _ _).mpr (SimttF.left_diverges hdiv hnt)

/-- A left silent divergence is related to any right return. -/
theorem simtt_diverges_ret (post) (o : Outcome) :
    simtt post infTau (ret o) :=
  simtt_diverges post infTau_diverges not_timeoutReachable_ret

/-- A left silent divergence is related to a right `ub`. -/
theorem simtt_diverges_ub (post) (k : Empty → OTree) :
    simtt post infTau (vis ObsEv.ub k) :=
  simtt_diverges post infTau_diverges not_timeoutReachable_ub

/-- Two silent divergences are related: the right-divergence clause requires a
left one and admits it here. -/
theorem simtt_diverges_diverges (post) :
    simtt post infTau infTau :=
  (simtt_iff post _ _).mpr (SimttF.right_diverges infTau_diverges infTau_diverges)

/-- A left UB terminal is not related to a defined return: the UB class matches
only itself on the right, and `post` never sees `ub`. -/
theorem not_simtt_ub_terminal_ret (post) {p : OTree} (hp : UbTerminal p)
    (v : Option Value) (mem : Mem) :
    ¬ simtt post p (ret (Outcome.ret v mem)) := by
  intro h
  have hF := (simtt_iff post _ _).mp h
  cases hF with
  | ret_ret h1 h2 _ =>
      cases hp with
      | retLeaf =>
          exact Outcome.noConfusion (ret_inj (SilentHead_ret_self h1))
      | ubNode k =>
          exact ret_ne_vis ObsEv.ub k (SilentHead_ub_self h1)
  | right_ub_ret h1 h2 => exact not_reachesUb_ret h2
  | ub h1 h2 => exact not_reachesUb_ret h2
  | timeout k1 k2 h1 h2 =>
      cases hp with
      | retLeaf => exact (ret_ne_vis ObsEv.timeout k1).symm (SilentHead_ret_self h1)
      | ubNode k => exact ub_ne_timeout.symm (vis_inj (SilentHead_ub_self h1)).1
  | left_diverges hdiv hnt =>
      cases hp with
      | retLeaf => exact not_silentDiverges_ret hdiv
      | ubNode k => exact not_silentDiverges_ub hdiv
  | right_diverges hdiv2 hdiv1 => exact not_silentDiverges_ret hdiv2
  | vis_load addr ty r k1 k2 h1 h2 hs =>
      cases hp with
      | retLeaf => exact (ret_ne_vis (ObsEv.load addr ty r) k1).symm (SilentHead_ret_self h1)
      | ubNode k => exact (vis_ub_ne_load k addr ty r k1).symm (SilentHead_ub_self h1)
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      cases hp with
      | retLeaf => exact (ret_ne_vis (ObsEv.store addr ty v) k1).symm (SilentHead_ret_self h1)
      | ubNode k => exact (vis_ub_ne_store k addr ty v k1).symm (SilentHead_ub_self h1)
  | vis_call callee args k1 k2 h1 h2 hs =>
      cases hp with
      | retLeaf => exact (ret_ne_vis (ObsEv.call callee args) k1).symm (SilentHead_ret_self h1)
      | ubNode k => exact (vis_ub_ne_call k callee args k1).symm (SilentHead_ub_self h1)

/-- A left `ub` node is not matched by a defined return. -/
theorem not_simtt_ub_ret (post) (v : Option Value) (mem : Mem)
    (k : Empty → OTree) :
    ¬ simtt post (vis ObsEv.ub k) (ret (Outcome.ret v mem)) :=
  not_simtt_ub_terminal_ret post (UbTerminal.ubNode k) v mem

/-- The `ret` leaf carrying `Outcome.ub` is the same UB terminal: a defined
return does not match it either. -/
theorem not_simtt_ret_ub_ret (post) (v : Option Value) (mem : Mem) :
    ¬ simtt post (ret Outcome.ub) (ret (Outcome.ret v mem)) :=
  not_simtt_ub_terminal_ret post UbTerminal.retLeaf v mem

/-- A left return is not matched by a right budget timeout. -/
theorem not_simtt_ret_timeout (post) (o : Outcome) (k : Empty → OTree) :
    ¬ simtt post (ret o) (vis ObsEv.timeout k) := by
  intro h
  have hF := (simtt_iff post _ _).mp h
  cases hF with
  | ret_ret h1 h2 hp =>
      exact ret_ne_vis ObsEv.timeout k (SilentHead_timeout_self h2)
  | right_ub_ret h1 h2 => exact not_reachesUb_timeout h2
  | ub h1 h2 => exact not_reachesUb_timeout h2
  | timeout k1 k2 h1 h2 =>
      exact (ret_ne_vis ObsEv.timeout k1).symm (SilentHead_ret_self h1)
  | left_diverges hdiv hnt => exact not_silentDiverges_ret hdiv
  | right_diverges hdiv2 hdiv1 => exact not_silentDiverges_timeout hdiv2
  | vis_load addr ty r k1 k2 h1 h2 hs =>
      exact (vis_timeout_ne_load k addr ty r k2).symm (SilentHead_timeout_self h2)
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact (vis_timeout_ne_store k addr ty v k2).symm (SilentHead_timeout_self h2)
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact (vis_timeout_ne_call k callee args k2).symm (SilentHead_timeout_self h2)

/-- A left budget timeout is not matched by a right return. -/
theorem not_simtt_timeout_ret (post) (o : Outcome) (k : Empty → OTree) :
    ¬ simtt post (vis ObsEv.timeout k) (ret o) := by
  intro h
  have hF := (simtt_iff post _ _).mp h
  cases hF with
  | ret_ret h1 h2 hp =>
      exact ret_ne_vis ObsEv.timeout k (SilentHead_timeout_self h1)
  | right_ub_ret h1 h2 =>
      exact ret_ne_vis ObsEv.timeout k (SilentHead_timeout_self h1)
  | ub h1 h2 => exact not_reachesUb_timeout h1
  | timeout k1 k2 h1 h2 =>
      exact (ret_ne_vis ObsEv.timeout k2).symm (SilentHead_ret_self h2)
  | left_diverges hdiv hnt => exact not_silentDiverges_timeout hdiv
  | right_diverges hdiv2 hdiv1 => exact not_silentDiverges_ret hdiv2
  | vis_load addr ty r k1 k2 h1 h2 hs =>
      exact (vis_timeout_ne_load k addr ty r k1).symm (SilentHead_timeout_self h1)
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact (vis_timeout_ne_store k addr ty v k1).symm (SilentHead_timeout_self h1)
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact (vis_timeout_ne_call k callee args k1).symm (SilentHead_timeout_self h1)

/-- A left budget timeout is not matched by a right `ub`. -/
theorem not_simtt_timeout_ub (post) (k k' : Empty → OTree) :
    ¬ simtt post (vis ObsEv.timeout k) (vis ObsEv.ub k') := by
  intro h
  have hF := (simtt_iff post _ _).mp h
  cases hF with
  | ret_ret h1 h2 hp =>
      exact ret_ne_vis ObsEv.timeout k (SilentHead_timeout_self h1)
  | right_ub_ret h1 h2 =>
      exact ret_ne_vis ObsEv.timeout k (SilentHead_timeout_self h1)
  | ub h1 h2 => exact not_reachesUb_timeout h1
  | timeout k1 k2 h1 h2 =>
      exact ub_ne_timeout ((vis_inj (SilentHead_ub_self h2)).1).symm
  | left_diverges hdiv hnt => exact not_silentDiverges_timeout hdiv
  | right_diverges hdiv2 hdiv1 => exact not_silentDiverges_ub hdiv2
  | vis_load addr ty r k1 k2 h1 h2 hs =>
      exact (vis_timeout_ne_load k addr ty r k1).symm (SilentHead_timeout_self h1)
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact (vis_timeout_ne_store k addr ty v k1).symm (SilentHead_timeout_self h1)
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact (vis_timeout_ne_call k callee args k1).symm (SilentHead_timeout_self h1)

/-- A left `ub` is not matched by a right budget timeout. -/
theorem not_simtt_ub_timeout (post) (k k' : Empty → OTree) :
    ¬ simtt post (vis ObsEv.ub k) (vis ObsEv.timeout k') := by
  intro h
  have hF := (simtt_iff post _ _).mp h
  cases hF with
  | ret_ret h1 h2 hp =>
      exact ret_ne_vis ObsEv.ub k (SilentHead_ub_self h1)
  | right_ub_ret h1 h2 => exact not_reachesUb_timeout h2
  | ub h1 h2 => exact not_reachesUb_timeout h2
  | timeout k1 k2 h1 h2 =>
      exact ub_ne_timeout ((vis_inj (SilentHead_ub_self h1)).1).symm
  | left_diverges hdiv hnt => exact not_silentDiverges_ub hdiv
  | right_diverges hdiv2 hdiv1 => exact not_silentDiverges_timeout hdiv2
  | vis_load addr ty r k1 k2 h1 h2 hs =>
      exact (vis_ub_ne_load k addr ty r k1).symm (SilentHead_ub_self h1)
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact (vis_ub_ne_store k addr ty v k1).symm (SilentHead_ub_self h1)
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact (vis_ub_ne_call k callee args k1).symm (SilentHead_ub_self h1)

/-- A right silent divergence is not matched by a left return. -/
theorem not_simtt_ret_diverges (post) (o : Outcome) :
    ¬ simtt post (ret o) infTau := by
  intro h
  have hF := (simtt_iff post _ _).mp h
  cases hF with
  | ret_ret h1 h2 hp =>
      have e := SilentHead_infTau_self h2
      rw [infTau_eq] at e
      exact ret_ne_tau e
  | right_ub_ret h1 h2 => exact not_reachesUb_infTau h2
  | ub h1 h2 => exact not_reachesUb_infTau h2
  | timeout k1 k2 h1 h2 =>
      have e := SilentHead_infTau_self h2
      rw [infTau_eq] at e
      exact (tau_ne_vis ObsEv.timeout k2).symm e
  | left_diverges hdiv hnt => exact not_silentDiverges_ret hdiv
  | right_diverges hdiv2 hdiv1 => exact not_silentDiverges_ret hdiv1
  | vis_load addr ty r k1 k2 h1 h2 hs =>
      have e := SilentHead_infTau_self h2
      rw [infTau_eq] at e
      exact (tau_ne_vis (ObsEv.load addr ty r) k2).symm e
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      have e := SilentHead_infTau_self h2
      rw [infTau_eq] at e
      exact (tau_ne_vis (ObsEv.store addr ty v) k2).symm e
  | vis_call callee args k1 k2 h1 h2 hs =>
      have e := SilentHead_infTau_self h2
      rw [infTau_eq] at e
      exact (tau_ne_vis (ObsEv.call callee args) k2).symm e

/-! ### Mismatched visible events

A visible node has no silent step, so the only clause that can relate two of them
is the one for the same event.  The three lemmas below are therefore the
refusals for a differing load annotation, store payload or call target; each is
paired in `LeanLLVMTest/Vellum.lean` with an affirmative under the same detector.
-/

/-- Two visible loads that differ in address, type or annotation are refused. -/
theorem not_simtt_load_ne (post) {addr : Nat} {ty : Ty} {r : Option Value}
    {addr' : Nat} {ty' : Ty} {r' : Option Value}
    (hne : (addr, ty, r) ≠ (addr', ty', r')) (k k' : Unit → OTree) :
    ¬ simtt post (vis (ObsEv.load addr ty r) k) (vis (ObsEv.load addr' ty' r') k') := by
  intro h
  have hF := (simtt_iff post _ _).mp h
  cases hF with
  | ret_ret h1 h2 hp => exact ret_ne_vis _ _ (SilentHead_vis_self h1)
  | right_ub_ret h1 h2 => exact ret_ne_vis _ _ (SilentHead_vis_self h1)
  | ub h1 h2 =>
      cases h1 with
      | retLeaf hr => exact ret_ne_vis _ _ (SilentHead_vis_self hr)
      | ubNode hv => exact (vis_ub_ne_load _ addr ty r k) (SilentHead_vis_self hv)
  | timeout k1 k2 h1 h2 =>
      exact vis_timeout_ne_load k1 addr ty r k (SilentHead_vis_self h1)
  | left_diverges hdiv hnt => exact not_silentDiverges_vis _ _ hdiv
  | right_diverges hdiv2 hdiv1 => exact not_silentDiverges_vis _ _ hdiv1
  | vis_load addr'' ty'' r'' k1 k2 h1 h2 hs =>
      have e1 := (vis_inj (SilentHead_vis_self h1)).1
      have e2 := (vis_inj (SilentHead_vis_self h2)).1
      have e : (ObsEv.load addr ty r : ObsEv Unit) = ObsEv.load addr' ty' r' :=
        e1.symm.trans e2
      obtain ⟨ha, ht, hr⟩ := obs_load_inj e
      exact hne (by rw [ha, ht, hr])
  | vis_store addr'' ty'' v k1 k2 h1 h2 hs =>
      exact (vis_load_ne_store (k := k) (k' := k1)).symm (SilentHead_vis_self h1)
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact (vis_load_ne_call (k := k) (k' := k1)).symm (SilentHead_vis_self h1)

/-- Two visible stores that differ in address, type or value are refused. -/
theorem not_simtt_store_ne (post) {addr : Nat} {ty : Ty} {v : Value}
    {addr' : Nat} {ty' : Ty} {v' : Value}
    (hne : (addr, ty, v) ≠ (addr', ty', v')) (k k' : Unit → OTree) :
    ¬ simtt post (vis (ObsEv.store addr ty v) k) (vis (ObsEv.store addr' ty' v') k') := by
  intro h
  have hF := (simtt_iff post _ _).mp h
  cases hF with
  | ret_ret h1 h2 hp => exact ret_ne_vis _ _ (SilentHead_vis_self h1)
  | right_ub_ret h1 h2 => exact ret_ne_vis _ _ (SilentHead_vis_self h1)
  | ub h1 h2 =>
      cases h1 with
      | retLeaf hr => exact ret_ne_vis _ _ (SilentHead_vis_self hr)
      | ubNode hv => exact (vis_ub_ne_store _ addr ty v k) (SilentHead_vis_self hv)
  | timeout k1 k2 h1 h2 =>
      exact vis_timeout_ne_store k1 addr ty v k (SilentHead_vis_self h1)
  | left_diverges hdiv hnt => exact not_silentDiverges_vis _ _ hdiv
  | right_diverges hdiv2 hdiv1 => exact not_silentDiverges_vis _ _ hdiv1
  | vis_load addr'' ty'' r k1 k2 h1 h2 hs =>
      exact vis_load_ne_store (k := k1) (k' := k) (SilentHead_vis_self h1)
  | vis_store addr'' ty'' v'' k1 k2 h1 h2 hs =>
      have e1 := (vis_inj (SilentHead_vis_self h1)).1
      have e2 := (vis_inj (SilentHead_vis_self h2)).1
      have e : (ObsEv.store addr ty v : ObsEv Unit) = ObsEv.store addr' ty' v' :=
        e1.symm.trans e2
      obtain ⟨ha, ht, hr⟩ := obs_store_inj e
      exact hne (by rw [ha, ht, hr])
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact (vis_store_ne_call (k := k) (k' := k1)).symm (SilentHead_vis_self h1)

/-- Two visible calls that differ in callee or arguments are refused. -/
theorem not_simtt_call_ne (post) {callee : String} {args : List Value}
    {callee' : String} {args' : List Value}
    (hne : callee ≠ callee' ∨ args ≠ args')
    (k k' : Option Value → OTree) :
    ¬ simtt post (vis (ObsEv.call callee args) k) (vis (ObsEv.call callee' args') k') := by
  intro h
  have hF := (simtt_iff post _ _).mp h
  cases hF with
  | ret_ret h1 h2 hp => exact ret_ne_vis _ _ (SilentHead_vis_self h1)
  | right_ub_ret h1 h2 => exact ret_ne_vis _ _ (SilentHead_vis_self h1)
  | ub h1 h2 =>
      cases h1 with
      | retLeaf hr => exact ret_ne_vis _ _ (SilentHead_vis_self hr)
      | ubNode hv => exact (vis_ub_ne_call _ callee args k) (SilentHead_vis_self hv)
  | timeout k1 k2 h1 h2 =>
      exact vis_timeout_ne_call k1 callee args k (SilentHead_vis_self h1)
  | left_diverges hdiv hnt => exact not_silentDiverges_vis _ _ hdiv
  | right_diverges hdiv2 hdiv1 => exact not_silentDiverges_vis _ _ hdiv1
  | vis_load addr ty r k1 k2 h1 h2 hs =>
      exact vis_load_ne_call (k := k1) (k' := k) (SilentHead_vis_self h1)
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact vis_store_ne_call (k := k1) (k' := k) (SilentHead_vis_self h1)
  | vis_call callee'' args'' k1 k2 h1 h2 hs =>
      have e1 := (vis_inj (SilentHead_vis_self h1)).1
      have e2 := (vis_inj (SilentHead_vis_self h2)).1
      have e : (ObsEv.call callee args : ObsEv (Option Value)) = ObsEv.call callee' args' :=
        e1.symm.trans e2
      obtain ⟨hc, ha⟩ := obs_call_inj e
      exact hne.elim (fun h => h hc) (fun h => h ha)
/-- A `tau` on the left has no silent divergence behind it if its successor does
not. -/
theorem SilentDiverges.tau_strip {t : OTree} :
    SilentDiverges (tau t) → SilentDiverges t := by
  intro h
  have h' : DivF SilentDiverges (tau t) := (congrFun SilentDiverges.eq_1 _).mp h
  cases h' with
  | step hstep hs =>
      obtain ⟨u, hp, hq⟩ := SilentStep_inv hstep
      rw [hq] at hs
      exact (tau_inj hp).symm ▸ hs

/-- The same for a UB terminal. -/
theorem ReachesUb.tau_strip {t : OTree} : ReachesUb (tau t) → ReachesUb t := by
  intro h
  cases h with
  | retLeaf h' =>
      exact ReachesUb.retLeaf (SilentHead.tau_strip h'
        (by intro hh; exact ret_ne_tau hh))
  | ubNode h' =>
      exact ReachesUb.ubNode (SilentHead.tau_strip h'
        (by intro hh; exact tau_ne_vis ObsEv.ub _ hh.symm))
/-- A `tau` on the left of the relation can be read off its closure, so the
relation also holds one step later. -/
theorem simtt_tau_left {post} {t q : OTree} (h : simtt post (tau t) q) :
    simtt post t q := by
  have hF := (simtt_iff post _ _).mp h
  refine (simtt_iff post _ _).mpr ?_
  cases hF with
  | ret_ret h1 h2 hp =>
      exact SimttF.ret_ret (SilentHead.tau_strip h1
        (by intro hh; exact ret_ne_tau hh)) h2 hp
  | right_ub_ret h1 h2 =>
      exact SimttF.right_ub_ret (SilentHead.tau_strip h1
        (by intro hh; exact ret_ne_tau hh)) h2
  | ub h1 h2 => exact SimttF.ub (ReachesUb.tau_strip h1) h2
  | timeout k1 k2 h1 h2 =>
      exact SimttF.timeout k1 k2 (SilentHead.tau_strip h1
        (by intro hh; exact tau_ne_vis ObsEv.timeout k1 hh.symm)) h2
  | left_diverges hdiv hnt =>
      exact SimttF.left_diverges (SilentDiverges.tau_strip hdiv) hnt
  | right_diverges hdiv2 hdiv1 =>
      exact SimttF.right_diverges hdiv2 (SilentDiverges.tau_strip hdiv1)
  | vis_load addr ty r k1 k2 h1 h2 hs =>
      exact SimttF.vis_load addr ty r k1 k2 (SilentHead.tau_strip h1
        (by intro hh; exact tau_ne_vis (ObsEv.load addr ty r) k1 hh.symm)) h2 hs
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact SimttF.vis_store addr ty v k1 k2 (SilentHead.tau_strip h1
        (by intro hh; exact tau_ne_vis (ObsEv.store addr ty v) k1 hh.symm)) h2 hs
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact SimttF.vis_call callee args k1 k2 (SilentHead.tau_strip h1
        (by intro hh; exact tau_ne_vis (ObsEv.call callee args) k1 hh.symm)) h2 hs

/-! ### Transporting a raw private derivation

The loop's finite derivation is stated on raw `(tree, memory)` states, where a
defined in-frame load or an in-frame store is one step.  Nothing else uses that
form: this lemma is the only bridge from it, and it produces the handled trees'
`tau` closure.
-/

theorem RawSilentStep.handle {frame : Nat → Prop} {p q : RawTS}
    (h : RawSilentStep frame p q) :
    SilentHead (handle frame p.2 p.1) (handle frame q.2 q.1) := by
  cases h with
  | step t m =>
      rw [handle_tau]
      exact SilentHead.step (SilentStep.step _) (SilentHead.refl _)
  | load addr ty k m v hv hf =>
      rw [handle_load_private hf hv]
      exact SilentHead.step (SilentStep.step _) (SilentHead.refl _)
  | store addr ty v k m hf =>
      rw [handle_store_private hf]
      exact SilentHead.step (SilentStep.step _) (SilentHead.refl _)

/-- Finitely many raw private steps are finitely many silent steps of the
handled trees. -/
theorem RawSilentHead.handle {frame : Nat → Prop} {p q : RawTS}
    (h : RawSilentHead frame p q) :
    SilentHead (handle frame p.2 p.1) (handle frame q.2 q.1) := by
  induction h with
  | refl => exact SilentHead.refl _
  | tail _ hstep ih => exact ih.trans (RawSilentStep.handle hstep)

end LeanLLVM.ITree
