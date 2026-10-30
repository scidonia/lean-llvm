/-
Postcondition-indexed, directed simulation of interaction trees.

The relation is about a tree paired with the memory its events read and write.
A state `(t, m)` can take a *silent* step: a `tau`, or a `load`/`store` whose
whole byte span lies in the private frame.  Calls, out-of-frame accesses,
undefined loads, `ub` and `timeout` are not silent.

`simtt frame post` is the greatest fixed point of `SimttF`: after finitely many
silent steps on either side, matching terminals are related.

* a `ret` leaf carrying a defined outcome on both sides is related when `post`
  holds of the two outcomes, memories included; `post` sees only `.ret`-valued
  outcomes and never `ub`;
* `timeout` matches only `timeout`;
* a UB terminal is a `ret` leaf carrying `Outcome.ub` or a `vis Ev.ub` node.
  The two shapes are one class in both directions: a left UB terminal requires
  a right one, and a right UB terminal admits any completed left return,
  defined or `ub`, without consulting `post`;
* a left silent divergence is the bottom: it is related to any right behaviour
  that does not reach `timeout` through silent steps;
* a right silent divergence requires a left silent divergence;
* the same visible event matches, with the response threaded into the
  continuations and stores advancing both memories.  A visible load matches
  only when the two memories give the same canonical response
  (`loadValue m₁ ty addr = loadValue m₂ ty addr`): two equal defined values or
  two undefined loads, never a defined answer on one side against an undefined
  load on the other.

The left tree is the target and the right tree the source.  There is no
symmetric equivalence: symmetry, where wanted, is the conjunction of the two
directions.
-/
import LeanLLVM.ITree.Interpret
import LeanLLVM.ITree.Internal.Paco

namespace LeanLLVM.ITree

open LeanLLVM
open ITree
open Lean.Order

/-- A tree together with the memory its events read and write. -/
abbrev TS := ITree Ev Outcome × Mem

/-- The whole byte span of a typed access lies in the frame. -/
def InFrame (frame : Nat → Prop) (addr : Nat) (ty : Ty) : Prop :=
  ∀ k, k < ty.sizeBytes → frame (addr + k)

/-! ### Silent steps and their closure -/

/-- One private step: a `tau`, a defined in-frame load, or an in-frame store. -/
inductive SilentStep (frame : Nat → Prop) : TS → TS → Prop where
  | tau (t : ITree Ev Outcome) (m : Mem) :
      SilentStep frame (ITree.tau t, m) (t, m)
  | load (addr : Nat) (ty : Ty) (k : Option Value → ITree Ev Outcome) (m : Mem)
      (v : Value) (hv : loadValue m ty addr = some v) (hf : InFrame frame addr ty) :
      SilentStep frame (ITree.vis (Ev.load addr ty) k, m) (k v, m)
  | store (addr : Nat) (ty : Ty) (v : Value) (k : Unit → ITree Ev Outcome) (m : Mem)
      (hf : InFrame frame addr ty) :
      SilentStep frame (ITree.vis (Ev.store addr ty v) k, m)
        (k (), storeMem m ty v addr)

/-- The reflexive-transitive closure of `SilentStep`: finitely many private
steps.  It is inductive, so it never witnesses divergence. -/
def SilentHead (frame : Nat → Prop) : TS → TS → Prop :=
  Relation.ReflTransGen (SilentStep frame)

theorem SilentHead.refl (frame) (p : TS) : SilentHead frame p p :=
  Relation.ReflTransGen.refl

theorem SilentHead.trans {frame} {p q r : TS}
    (h1 : SilentHead frame p q) (h2 : SilentHead frame q r) : SilentHead frame p r :=
  Relation.ReflTransGen.trans h1 h2

theorem SilentHead.step {frame} {p q r : TS} (h1 : SilentStep frame p q)
    (h2 : SilentHead frame q r) : SilentHead frame p r :=
  Relation.ReflTransGen.head h1 h2

/-- A closure either is already finished or begins with one step. -/
theorem SilentHead_inv {frame} {p q : TS} (h : SilentHead frame p q) :
    p = q ∨ ∃ p', SilentStep frame p p' ∧ SilentHead frame p' q := by
  induction h with
  | refl => exact Or.inl rfl
  | tail hrest hstep ih =>
      rcases ih with hpq | ⟨p', hstep', hrest'⟩
      · subst hpq
        exact Or.inr ⟨_, hstep, SilentHead.refl _ _⟩
      · exact Or.inr ⟨p', hstep', Relation.ReflTransGen.tail hrest' hstep⟩

/-- Induction along a closure through a set of states closed under `SilentStep`. -/
theorem SilentHead.cases_of_closed {frame} {P : TS → Prop}
    (hP : ∀ p, P p → ∀ q, SilentStep frame p q → P q)
    {p q : TS} (h : SilentHead frame p q) : P p → P q := by
  induction h with
  | refl => exact id
  | tail _ hstep ih => intro hp; exact hP _ (ih hp) _ hstep

/-- Inversion of one silent step.  The source is a variable, so this is a
plain case analysis rather than an attempt to eliminate a coinductive index. -/
theorem SilentStep_inv {frame} {p q : TS} (h : SilentStep frame p q) :
    (∃ t m, p = (ITree.tau t, m) ∧ q = (t, m)) ∨
    (∃ addr ty k m v, loadValue m ty addr = some v ∧ InFrame frame addr ty ∧
        p = (ITree.vis (Ev.load addr ty) k, m) ∧ q = (k v, m)) ∨
    (∃ addr ty v k m, InFrame frame addr ty ∧
        p = (ITree.vis (Ev.store addr ty v) k, m) ∧
        q = (k (), storeMem m ty v addr)) := by
  cases h with
  | tau t m => exact Or.inl ⟨t, m, rfl, rfl⟩
  | load addr ty k m v hv hf =>
      exact Or.inr (Or.inl ⟨addr, ty, k, m, v, hv, hf, rfl, rfl⟩)
  | store addr ty v k m hf =>
      exact Or.inr (Or.inr ⟨addr, ty, v, k, m, hf, rfl, rfl⟩)


/-- `Option Value` and `Unit` are not the same type: the former has a `none`
and a `some`, while the latter is a subsingleton. -/
theorem option_value_ne_unit : Option Value ≠ Unit := by
  intro h
  have : Subsingleton (Option Value) := h ▸ (inferInstance : Subsingleton Unit)
  cases Subsingleton.elim (none : Option Value) (some (.int 64 0))

/-- A state has at most one silent step. -/
theorem SilentStep.det {frame} {p q r : TS} (h1 : SilentStep frame p q)
    (h2 : SilentStep frame p r) : q = r := by
  rcases SilentStep_inv h1 with ⟨t1, m1, hp1, hq1⟩ |
    ⟨a1, ty1, k1, m1, v1, hv1, _, hp1, hq1⟩ |
    ⟨a1, ty1, v1, k1, m1, _, hp1, hq1⟩
  · rcases SilentStep_inv h2 with ⟨t2, m2, hp2, hq2⟩ |
      ⟨a2, ty2, k2, m2, v2, _, _, hp2, hq2⟩ |
      ⟨a2, ty2, v2, k2, m2, _, hp2, hq2⟩
    · have hp : (ITree.tau t1, m1) = (ITree.tau t2, m2) := hp1.symm.trans hp2
      rw [hq1, hq2, ITree.tau_inj (Prod.mk.inj hp).1, (Prod.mk.inj hp).2]
    · have hp : (ITree.tau t1, m1) = (ITree.vis (Ev.load a2 ty2) k2, m2) :=
        hp1.symm.trans hp2
      exact absurd (Prod.mk.inj hp).1 (ITree.tau_ne_vis (Ev.load a2 ty2) k2)
    · have hp : (ITree.tau t1, m1) = (ITree.vis (Ev.store a2 ty2 v2) k2, m2) :=
        hp1.symm.trans hp2
      exact absurd (Prod.mk.inj hp).1 (ITree.tau_ne_vis (Ev.store a2 ty2 v2) k2)
  · rcases SilentStep_inv h2 with ⟨t2, m2, hp2, hq2⟩ |
      ⟨a2, ty2, k2, m2, v2, hv2, _, hp2, hq2⟩ |
      ⟨a2, ty2, v2, k2, m2, _, hp2, hq2⟩
    · have hp : (ITree.vis (Ev.load a1 ty1) k1, m1) = (ITree.tau t2, m2) :=
        hp1.symm.trans hp2
      exact absurd (Prod.mk.inj hp).1 (ITree.tau_ne_vis (Ev.load a1 ty1) k1).symm
    · have hp : (ITree.vis (Ev.load a1 ty1) k1, m1) =
          (ITree.vis (Ev.load a2 ty2) k2, m2) := hp1.symm.trans hp2
      obtain ⟨hev, hk⟩ := ITree.vis_inj (Prod.mk.inj hp).1
      have hm : m1 = m2 := (Prod.mk.inj hp).2
      subst hm
      cases hev
      have hval : v1 = v2 := Option.some.inj (hv1.symm.trans hv2)
      rw [hq1, hq2, hk, hval]
    · have hp : (ITree.vis (Ev.load a1 ty1) k1, m1) =
          (ITree.vis (Ev.store a2 ty2 v2) k2, m2) := hp1.symm.trans hp2
      exact (option_value_ne_unit (ITree.vis_inj_α (Prod.mk.inj hp).1)).elim
  · rcases SilentStep_inv h2 with ⟨t2, m2, hp2, hq2⟩ |
      ⟨a2, ty2, k2, m2, v2, _, _, hp2, hq2⟩ |
      ⟨a2, ty2, v2, k2, m2, _, hp2, hq2⟩
    · have hp : (ITree.vis (Ev.store a1 ty1 v1) k1, m1) = (ITree.tau t2, m2) :=
        hp1.symm.trans hp2
      exact absurd (Prod.mk.inj hp).1 (ITree.tau_ne_vis (Ev.store a1 ty1 v1) k1).symm
    · have hp : (ITree.vis (Ev.store a1 ty1 v1) k1, m1) =
          (ITree.vis (Ev.load a2 ty2) k2, m2) := hp1.symm.trans hp2
      exact (option_value_ne_unit.symm (ITree.vis_inj_α (Prod.mk.inj hp).1)).elim
    · have hp : (ITree.vis (Ev.store a1 ty1 v1) k1, m1) =
          (ITree.vis (Ev.store a2 ty2 v2) k2, m2) := hp1.symm.trans hp2
      obtain ⟨hev, hk⟩ := ITree.vis_inj (Prod.mk.inj hp).1
      cases hev
      rw [hq1, hq2, hk, (Prod.mk.inj hp).2]

/-- A state from which no silent step is possible is its own only closure. -/
theorem SilentHead.eq_of_no_step {frame} {p q : TS}
    (hno : ∀ r, SilentStep frame p r → False) (h : SilentHead frame p q) :
    q = p :=
  SilentHead.cases_of_closed (P := fun r => r = p)
    (fun r hr s hstep => by subst hr; exact (hno s hstep).elim) h rfl

/-- No silent step leaves a returned outcome. -/
theorem ret_no_step {frame} {o : Outcome} {m : Mem} :
    ∀ q : TS, ¬ SilentStep frame (ITree.ret o, m) q := by
  intro q
  intro h
  rcases SilentStep_inv h with ⟨t, m', hp, _⟩ | ⟨addr, ty, k, m', v, _, _, hp, _⟩ |
    ⟨addr, ty, v, k, m', _, hp, _⟩
  · exact ITree.ret_ne_tau ((Prod.mk.inj hp).1)
  · exact ITree.ret_ne_vis _ _ ((Prod.mk.inj hp).1)
  · exact ITree.ret_ne_vis _ _ ((Prod.mk.inj hp).1)

/-- `Empty` is not `Option Value`. -/
theorem empty_ne_option_value : (Empty : Type) ≠ Option Value := by
  intro h
  exact nomatch (Eq.mpr h (some (.int 64 0)))

/-- `Empty` is not `Unit`. -/
theorem empty_ne_unit : (Empty : Type) ≠ Unit := by
  intro h
  exact nomatch (Eq.mpr h ())

/-- No silent step leaves an undefined-behaviour node. -/
theorem ub_no_step {frame} {k : Empty → ITree Ev Outcome} {m : Mem} :
    ∀ q : TS, ¬ SilentStep frame (ITree.vis Ev.ub k, m) q := by
  intro q
  intro h
  rcases SilentStep_inv h with ⟨t, m', hp, _⟩ | ⟨addr, ty, k', m', v, _, _, hp, _⟩ |
    ⟨addr, ty, v, k', m', _, hp, _⟩
  · exact ITree.tau_ne_vis Ev.ub k ((Prod.mk.inj hp).1).symm
  · exact ITree.vis_ne_of_type_ne (h := empty_ne_option_value) ((Prod.mk.inj hp).1)
  · exact ITree.vis_ne_of_type_ne (h := empty_ne_unit) ((Prod.mk.inj hp).1)

/-- No silent step leaves a budget-timeout node. -/
theorem timeout_no_step {frame} {k : Empty → ITree Ev Outcome} {m : Mem} :
    ∀ q : TS, ¬ SilentStep frame (ITree.vis Ev.timeout k, m) q := by
  intro q
  intro h
  rcases SilentStep_inv h with ⟨t, m', hp, _⟩ | ⟨addr, ty, k', m', v, _, _, hp, _⟩ |
    ⟨addr, ty, v, k', m', _, hp, _⟩
  · exact ITree.tau_ne_vis Ev.timeout k ((Prod.mk.inj hp).1).symm
  · exact ITree.vis_ne_of_type_ne (h := empty_ne_option_value) ((Prod.mk.inj hp).1)
  · exact ITree.vis_ne_of_type_ne (h := empty_ne_unit) ((Prod.mk.inj hp).1)

theorem SilentHead_ret_self {frame} {o : Outcome} {m : Mem} {q : TS}
    (h : SilentHead frame (ITree.ret o, m) q) : q = (ITree.ret o, m) :=
  SilentHead.eq_of_no_step ret_no_step h

theorem SilentHead_ub_self {frame} {k : Empty → ITree Ev Outcome} {m : Mem} {q : TS}
    (h : SilentHead frame (ITree.vis Ev.ub k, m) q) :
    q = (ITree.vis Ev.ub k, m) :=
  SilentHead.eq_of_no_step ub_no_step h

theorem SilentHead_timeout_self {frame} {k : Empty → ITree Ev Outcome} {m : Mem} {q : TS}
    (h : SilentHead frame (ITree.vis Ev.timeout k, m) q) :
    q = (ITree.vis Ev.timeout k, m) :=
  SilentHead.eq_of_no_step timeout_no_step h

/-! ### Silent divergence -/

/-- One silent step with a divergent continuation. -/
inductive DivF (frame : Nat → Prop) (sim : TS → Prop) : TS → Prop where
  | step {p q : TS} (h : SilentStep frame p q) (hs : sim q) : DivF frame sim p

theorem DivF_monotone {frame} {sim sim' : TS → Prop}
    (h : ∀ p, sim p → sim' p) : ∀ p, DivF frame sim p → DivF frame sim' p := by
  intro p hp
  cases hp with
  | step hs hsim => exact DivF.step hs (h _ hsim)

/-- Infinite silent progress: the greatest fixed point of `DivF`.  It is not a
finite fuel-exhaustion marker; it witnesses a genuinely infinite path. -/
def SilentDiverges (frame : Nat → Prop) : TS → Prop :=
  DivF frame (SilentDiverges frame)
  coinductive_fixpoint monotonicity fun _ _ hsim => DivF_monotone hsim

theorem SilentDiverges.coind (frame) (pred : TS → Prop)
    (h : ∀ p, pred p → DivF frame pred p) : ∀ p, pred p → SilentDiverges frame p :=
  SilentDiverges.coinduct frame pred h

theorem SilentDiverges.intro (frame) {p q : TS} (hstep : SilentStep frame p q)
    (h : SilentDiverges frame q) : SilentDiverges frame p :=
  (congrFun (SilentDiverges.eq_1 frame) p).mpr (DivF.step hstep h)

/-- Prepending a finite silent closure to an infinite silent path keeps it
divergent. -/
theorem SilentDiverges.of_silentHead {frame} {p q : TS} (hhead : SilentHead frame p q) :
    SilentDiverges frame q → SilentDiverges frame p := by
  induction hhead with
  | refl => exact id
  | tail _ hstep ih => intro hd; exact ih (SilentDiverges.intro frame hstep hd)

/-- One silent step from `infTau` stays at `infTau`. -/
theorem infTau_step_eq {frame} {m : Mem} {q : TS}
    (h : SilentStep frame (ITree.infTau, m) q) : q = (ITree.infTau, m) := by
  rw [ITree.infTau_eq] at h
  rcases SilentStep_inv h with ⟨t, m', hp, hq⟩ | ⟨addr, ty, k, m', v, _, _, hp, _⟩ |
    ⟨addr, ty, v, k, m', _, hp, _⟩
  · have ht : ITree.infTau = t := ITree.tau_inj ((Prod.mk.inj hp).1)
    have hm : m = m' := (Prod.mk.inj hp).2
    rw [hq, ← ht, ← hm]
  · exact absurd ((Prod.mk.inj hp).1) (ITree.tau_ne_vis (Ev.load addr ty) k)
  · exact absurd ((Prod.mk.inj hp).1) (ITree.tau_ne_vis (Ev.store addr ty v) k)

/-- Every finite silent closure of `infTau` stays at `infTau`. -/
theorem SilentHead_infTau_self {frame} {m : Mem} {q : TS}
    (h : SilentHead frame (ITree.infTau, m) q) : q = (ITree.infTau, m) :=
  SilentHead.cases_of_closed (P := fun r => r = (ITree.infTau, m))
    (fun p hp q hstep => by subst hp; exact infTau_step_eq hstep) h rfl

/-- `infTau` takes a silent step to itself. -/
theorem infTau_self_step {frame} {m : Mem} :
    SilentStep frame (ITree.infTau, m) (ITree.infTau, m) := by
  have h : SilentStep frame (ITree.tau ITree.infTau, m) (ITree.infTau, m) :=
    SilentStep.tau ITree.infTau m
  exact Eq.mp (congrArg (fun t => SilentStep frame (t, m) (ITree.infTau, m))
    ITree.infTau_eq.symm) h

/-- `infTau` diverges silently. -/
theorem infTau_diverges (frame) (m : Mem) :
    SilentDiverges frame (ITree.infTau, m) := by
  apply SilentDiverges.coind frame (fun p => p = (ITree.infTau, m))
  · intro p hp
    subst hp
    exact DivF.step infTau_self_step rfl
  · rfl

theorem not_silentDiverges_ret {frame} {o : Outcome} {m : Mem} :
    ¬ SilentDiverges frame (ITree.ret o, m) := by
  intro h
  have h' : DivF frame (SilentDiverges frame) (ITree.ret o, m) :=
    (congrFun (SilentDiverges.eq_1 frame) _).mp h
  cases h' with
  | step hstep _ => exact ret_no_step _ hstep

theorem not_silentDiverges_ub {frame} {k : Empty → ITree Ev Outcome} {m : Mem} :
    ¬ SilentDiverges frame (ITree.vis Ev.ub k, m) := by
  intro h
  have h' : DivF frame (SilentDiverges frame) (ITree.vis Ev.ub k, m) :=
    (congrFun (SilentDiverges.eq_1 frame) _).mp h
  cases h' with
  | step hstep _ => exact ub_no_step _ hstep

theorem not_silentDiverges_timeout {frame} {k : Empty → ITree Ev Outcome} {m : Mem} :
    ¬ SilentDiverges frame (ITree.vis Ev.timeout k, m) := by
  intro h
  have h' : DivF frame (SilentDiverges frame) (ITree.vis Ev.timeout k, m) :=
    (congrFun (SilentDiverges.eq_1 frame) _).mp h
  cases h' with
  | step hstep _ => exact timeout_no_step _ hstep

/-! ### Timeout reachability -/

/-- A state from which silent progress reaches `timeout` through finitely many
private steps.  This is the semantic notion of a budget timeout. -/
def TimeoutReachable (frame : Nat → Prop) (p : TS) : Prop :=
  ∃ q, SilentHead frame p q ∧ ∃ k : Empty → ITree Ev Outcome, q.1 = ITree.vis Ev.timeout k

theorem not_timeoutReachable_ret {frame} {o : Outcome} {m : Mem} :
    ¬ TimeoutReachable frame (ITree.ret o, m) := by
  rintro ⟨q, hq, k, hk⟩
  rw [SilentHead_ret_self hq] at hk
  exact ITree.ret_ne_vis Ev.timeout k hk

theorem ub_ne_timeout : (Ev.ub : Ev Empty) ≠ Ev.timeout := by
  intro h
  cases h

theorem not_timeoutReachable_ub {frame} {k : Empty → ITree Ev Outcome} {m : Mem} :
    ¬ TimeoutReachable frame (ITree.vis Ev.ub k, m) := by
  rintro ⟨q, hq, k', hk⟩
  rw [SilentHead_ub_self hq] at hk
  exact ub_ne_timeout (ITree.vis_inj hk).1

/-- A silent step cannot make a state that reaches `timeout` out of one that
does not: the step is unique, so every closure either stops at the source or
continues through it. -/
theorem not_timeoutReachable_of_silentStep {frame} {p q : TS}
    (h : SilentStep frame p q) (hnt : ¬ TimeoutReachable frame q) :
    ¬ TimeoutReachable frame p := by
  intro hp
  rcases hp with ⟨r, hr, k, hk⟩
  rcases SilentHead_inv hr with hpr | ⟨p', hstep, hrest⟩
  · have hp1 : p.1 = ITree.vis Ev.timeout k := by rw [hpr]; exact hk
    have hpEq : p = (ITree.vis Ev.timeout k, p.2) := Prod.ext hp1 rfl
    rw [hpEq] at h
    exact timeout_no_step _ h
  · have hpq : p' = q := SilentStep.det hstep h
    subst hpq
    exact hnt ⟨r, hrest, k, hk⟩

/-- The same for a finite silent closure. -/
theorem not_timeoutReachable_of_silentHead {frame} {p q : TS}
    (h : SilentHead frame p q) : ¬ TimeoutReachable frame q →
    ¬ TimeoutReachable frame p := by
  induction h with
  | refl => intro hnt; exact hnt
  | tail hrest hstep ih =>
      intro hnt
      exact ih (not_timeoutReachable_of_silentStep hstep hnt)

/-! ### UB terminals -/

/-- The two shapes a UB terminal takes: a `ret` leaf carrying `Outcome.ub`, or a
`vis Ev.ub` node.  The relation treats them as one class, so neither shape can
slip past the left-UB rule through `post`, and either shape admits a completed
left return on the right. -/
inductive UbTerminal : TS → Prop where
  | ret (m : Mem) : UbTerminal (ITree.ret Outcome.ub, m)
  | vis (k : Empty → ITree Ev Outcome) (m : Mem) : UbTerminal (ITree.vis Ev.ub k, m)

/-- A state whose silent closure ends in a UB terminal. -/
inductive ReachesUb (frame : Nat → Prop) : TS → Prop where
  | ret {p : TS} {m : Mem} (h : SilentHead frame p (ITree.ret Outcome.ub, m)) :
      ReachesUb frame p
  | vis {p : TS} {k : Empty → ITree Ev Outcome} {m : Mem}
      (h : SilentHead frame p (ITree.vis Ev.ub k, m)) : ReachesUb frame p

/-- A UB terminal reaches itself through the empty closure. -/
theorem reachesUb_of_terminal {frame} {p : TS} (h : UbTerminal p) : ReachesUb frame p := by
  cases h with
  | ret m => exact ReachesUb.ret (SilentHead.refl _ _)
  | vis k m => exact ReachesUb.vis (SilentHead.refl _ _)

/-- Prepending a silent closure keeps a state that reaches a UB terminal
reaching one. -/
theorem ReachesUb.of_silentHead {frame} {p p' : TS} (h : SilentHead frame p p')
    (hp' : ReachesUb frame p') : ReachesUb frame p := by
  cases hp' with
  | ret h2 => exact ReachesUb.ret (SilentHead.trans h h2)
  | vis h2 => exact ReachesUb.vis (SilentHead.trans h h2)

/-- A defined return is not a UB terminal. -/
theorem not_reachesUb_ret {frame} {v : Option Value} {mem : Mem} {m : Mem} :
    ¬ ReachesUb frame (ITree.ret (Outcome.ret v mem), m) := by
  intro h
  cases h with
  | ret h' =>
      exact Outcome.noConfusion (ITree.ret_inj (Prod.mk.inj (SilentHead_ret_self h')).1)
  | vis h' =>
      exact (ITree.ret_ne_vis Ev.ub _).symm (Prod.mk.inj (SilentHead_ret_self h')).1

/-- A budget timeout is not a UB terminal. -/
theorem not_reachesUb_timeout {frame} {k : Empty → ITree Ev Outcome} {m : Mem} :
    ¬ ReachesUb frame (ITree.vis Ev.timeout k, m) := by
  intro h
  cases h with
  | ret h' =>
      exact ITree.ret_ne_vis Ev.timeout _ (Prod.mk.inj (SilentHead_timeout_self h')).1
  | vis h' =>
      exact ub_ne_timeout (ITree.vis_inj (Prod.mk.inj (SilentHead_timeout_self h')).1).1

/-- A silent divergence is not a UB terminal. -/
theorem not_reachesUb_infTau {frame} {m : Mem} :
    ¬ ReachesUb frame (ITree.infTau, m) := by
  intro h
  cases h with
  | ret h' =>
      have e := (Prod.mk.inj (SilentHead_infTau_self h')).1
      rw [ITree.infTau_eq] at e
      exact ITree.ret_ne_tau e
  | vis h' =>
      have e := (Prod.mk.inj (SilentHead_infTau_self h')).1
      rw [ITree.infTau_eq] at e
      exact (ITree.tau_ne_vis Ev.ub _).symm e

/-! ### The relation -/

/-- One unfolding of `simtt`: after finitely many silent steps on both sides,
matching terminals. -/
inductive SimttF (frame : Nat → Prop) (post : Outcome → Outcome → Prop)
    (sim : TS → TS → Prop) : TS → TS → Prop where
  /-- Two defined outcomes related by `post`.  The outcomes are `.ret`-valued:
  `post` is never applied to `ub`. -/
  | ret {p q : TS} {v₁ v₂ : Option Value} {mem₁ mem₂ : Mem} {m₁ m₂ : Mem}
      (h1 : SilentHead frame p (ITree.ret (Outcome.ret v₁ mem₁), m₁))
      (h2 : SilentHead frame q (ITree.ret (Outcome.ret v₂ mem₂), m₂))
      (hp : post (Outcome.ret v₁ mem₁) (Outcome.ret v₂ mem₂)) : SimttF frame post sim p q
  /-- A right UB terminal admits any completed left return, defined or `ub`,
  and `post` is not consulted. -/
  | right_ub_ret {p q : TS} {o : Outcome} {m₁ : Mem}
      (h1 : SilentHead frame p (ITree.ret o, m₁))
      (h2 : ReachesUb frame q) : SimttF frame post sim p q
  /-- A left UB terminal requires a right UB terminal; the `ret` leaf carrying
  `Outcome.ub` and the `vis Ev.ub` node are one class. -/
  | ub {p q : TS} (h1 : ReachesUb frame p) (h2 : ReachesUb frame q) :
      SimttF frame post sim p q
  /-- A budget timeout matches only a budget timeout. -/
  | timeout {p q : TS} {m₁ m₂ : Mem}
      (k1 k2 : Empty → ITree Ev Outcome)
      (h1 : SilentHead frame p (ITree.vis Ev.timeout k1, m₁))
      (h2 : SilentHead frame q (ITree.vis Ev.timeout k2, m₂)) : SimttF frame post sim p q
  /-- Left silent divergence is the bottom against a right side that cannot
  silently reach `timeout`. -/
  | left_diverges {p q : TS} (hdiv : SilentDiverges frame p)
      (hnt : ¬ TimeoutReachable frame q) : SimttF frame post sim p q
  /-- Right silent divergence requires left silent divergence. -/
  | right_diverges {p q : TS} (hdiv2 : SilentDiverges frame q)
      (hdiv1 : SilentDiverges frame p) : SimttF frame post sim p q
  /-- The same load matches when the two memories define the same canonical
  response — the same value, or both undefined — and the response is threaded
  into both continuations from each side's own memory. -/
  | vis_load {p q : TS} (addr : Nat) (ty : Ty) {m₁ m₂ : Mem}
      (k1 k2 : Option Value → ITree Ev Outcome)
      (h1 : SilentHead frame p (ITree.vis (Ev.load addr ty) k1, m₁))
      (h2 : SilentHead frame q (ITree.vis (Ev.load addr ty) k2, m₂))
      (hm : loadValue m₁ ty addr = loadValue m₂ ty addr)
      (hs : ∀ v, sim (k1 v, m₁) (k2 v, m₂)) : SimttF frame post sim p q
  /-- The same store matches and advances both memories. -/
  | vis_store {p q : TS} (addr : Nat) (ty : Ty) (v : Value) {m₁ m₂ : Mem}
      (k1 k2 : Unit → ITree Ev Outcome)
      (h1 : SilentHead frame p (ITree.vis (Ev.store addr ty v) k1, m₁))
      (h2 : SilentHead frame q (ITree.vis (Ev.store addr ty v) k2, m₂))
      (hs : sim (k1 (), storeMem m₁ ty v addr) (k2 (), storeMem m₂ ty v addr)) :
      SimttF frame post sim p q
  /-- The same call matches. -/
  | vis_call {p q : TS} (callee : String) (args : List Value) {m₁ m₂ : Mem}
      (k1 k2 : Option Value → ITree Ev Outcome)
      (h1 : SilentHead frame p (ITree.vis (Ev.call callee args) k1, m₁))
      (h2 : SilentHead frame q (ITree.vis (Ev.call callee args) k2, m₂))
      (hs : ∀ r, sim (k1 r, m₁) (k2 r, m₂)) : SimttF frame post sim p q

theorem SimttF_monotone {frame post} {sim sim' : TS → TS → Prop}
    (h : ∀ p q, sim p q → sim' p q) :
    ∀ p q, SimttF frame post sim p q → SimttF frame post sim' p q := by
  intro p q hpq
  cases hpq with
  | ret h1 h2 hp => exact SimttF.ret h1 h2 hp
  | right_ub_ret h1 h2 => exact SimttF.right_ub_ret h1 h2
  | ub h1 h2 => exact SimttF.ub h1 h2
  | timeout k1 k2 h1 h2 => exact SimttF.timeout k1 k2 h1 h2
  | left_diverges hdiv hnt => exact SimttF.left_diverges hdiv hnt
  | right_diverges h2 h1 => exact SimttF.right_diverges h2 h1
  | vis_load addr ty k1 k2 h1 h2 hm hs =>
      exact SimttF.vis_load addr ty k1 k2 h1 h2 hm (fun v => h _ _ (hs v))
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact SimttF.vis_store addr ty v k1 k2 h1 h2 (h _ _ hs)
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact SimttF.vis_call callee args k1 k2 h1 h2 (fun r => h _ _ (hs r))

/-- The reverse-implication complete lattice on `Prop`, lifted to the two
tree/memory indices; the same instance Lean's `coinductive_fixpoint` builds for
a coinductive predicate. -/
private instance instSimttPartialOrder : Lean.Order.PartialOrder (TS → TS → Prop) :=
  inferInstanceAs (Lean.Order.PartialOrder (TS → TS → ReverseImplicationOrder))

private instance instSimttLattice : Lean.Order.CompleteLattice (TS → TS → Prop) :=
  inferInstanceAs (Lean.Order.CompleteLattice (TS → TS → ReverseImplicationOrder))

/-- `SimttF` is monotone in the reverse-implication order, which is what
`plfp` needs. -/
theorem SimttF_monotone_order (frame) (post) : monotone (SimttF frame post) := by
  intro x y hxy
  exact SimttF_monotone hxy

/-- The directed simulation: left is the target, right the source.  It is
Paco's parameterised least fixed point of `SimttF` at the top assumption; in the
reverse-implication order that is its greatest fixed point. -/
def simtt (frame : Nat → Prop) (post : Outcome → Outcome → Prop) : TS → TS → Prop :=
  plfp (SimttF frame post) (hm := SimttF_monotone_order frame post)
    (Lean.Order.top : TS → TS → Prop)

/-- `simtt` is Paco's parameterised least fixed point of `SimttF` at the top
assumption: with the reverse-implication order that is the greatest fixed
point of the one-step functional. -/
theorem simtt_eq_plfp (frame) (post) :
    simtt frame post = plfp (SimttF frame post) (hm := SimttF_monotone_order frame post)
      (Lean.Order.top : TS → TS → Prop) := rfl

/-- Unfolding of `simtt`, by Paco's `plfp_unfold` and the fact that the top
assumption is inert. -/
theorem simtt_unfold (frame) (post) :
    simtt frame post = SimttF frame post (simtt frame post) := by
  have h : plfp (SimttF frame post) (hm := SimttF_monotone_order frame post)
      (Lean.Order.top : TS → TS → Prop) =
      SimttF frame post (plfp (SimttF frame post) (hm := SimttF_monotone_order frame post)
        (Lean.Order.top : TS → TS → Prop)) := by
    conv_lhs => rw [plfp_unfold (hm := SimttF_monotone_order frame post)]
    congr 1
    simp only [uplfp]
    rw [CompleteLattice.meet_comm, CompleteLattice.meet_top]
  rw [simtt]
  exact h

/-- Unfolding of `simtt` into its one-step functional. -/
theorem simtt_iff (frame) (post) (p q : TS) :
    simtt frame post p q ↔ SimttF frame post (simtt frame post) p q :=
  (congrArg (fun f => f p q) (simtt_unfold frame post)).to_iff

/-- Coinduction: a relation contained in `SimttF` is contained in `simtt`.
After `simtt_eq_plfp` this is Paco's `plfp_init` and the least-fixed-point
principle for the reverse-implication order. -/
theorem simtt.coind (frame) (post) (pred : TS → TS → Prop)
    (h : ∀ p q, pred p q → SimttF frame post pred p q) :
    ∀ p q, pred p q → simtt frame post p q := by
  intro p q hpq
  rw [simtt, ← plfp_init (hm := SimttF_monotone_order frame post)]
  exact lfp_le_of_le_monotone (SimttF frame post)
    (hm := SimttF_monotone_order frame post) pred h p q hpq

/-! ### Distinct visible events

The visible events carry different response types or different constructors, so
the terminal cases below can reject a closure that ends at the wrong event.
-/

theorem vis_ub_ne_load (k : Empty → ITree Ev Outcome) (addr : Nat) (ty : Ty)
    (k' : Option Value → ITree Ev Outcome) :
    (ITree.vis Ev.ub k : ITree Ev Outcome) ≠ ITree.vis (Ev.load addr ty) k' :=
  ITree.vis_ne_of_type_ne (h := empty_ne_option_value)

theorem vis_ub_ne_store (k : Empty → ITree Ev Outcome) (addr : Nat) (ty : Ty) (v : Value)
    (k' : Unit → ITree Ev Outcome) :
    (ITree.vis Ev.ub k : ITree Ev Outcome) ≠ ITree.vis (Ev.store addr ty v) k' :=
  ITree.vis_ne_of_type_ne (h := empty_ne_unit)

theorem vis_ub_ne_call (k : Empty → ITree Ev Outcome) (callee : String) (args : List Value)
    (k' : Option Value → ITree Ev Outcome) :
    (ITree.vis Ev.ub k : ITree Ev Outcome) ≠ ITree.vis (Ev.call callee args) k' :=
  ITree.vis_ne_of_type_ne (h := empty_ne_option_value)

theorem vis_timeout_ne_load (k : Empty → ITree Ev Outcome) (addr : Nat) (ty : Ty)
    (k' : Option Value → ITree Ev Outcome) :
    (ITree.vis Ev.timeout k : ITree Ev Outcome) ≠ ITree.vis (Ev.load addr ty) k' :=
  ITree.vis_ne_of_type_ne (h := empty_ne_option_value)

theorem vis_timeout_ne_store (k : Empty → ITree Ev Outcome) (addr : Nat) (ty : Ty)
    (v : Value) (k' : Unit → ITree Ev Outcome) :
    (ITree.vis Ev.timeout k : ITree Ev Outcome) ≠ ITree.vis (Ev.store addr ty v) k' :=
  ITree.vis_ne_of_type_ne (h := empty_ne_unit)

theorem vis_timeout_ne_call (k : Empty → ITree Ev Outcome) (callee : String)
    (args : List Value) (k' : Option Value → ITree Ev Outcome) :
    (ITree.vis Ev.timeout k : ITree Ev Outcome) ≠ ITree.vis (Ev.call callee args) k' :=
  ITree.vis_ne_of_type_ne (h := empty_ne_option_value)

theorem vis_ub_ne_timeout (k k' : Empty → ITree Ev Outcome) :
    (ITree.vis Ev.ub k : ITree Ev Outcome) ≠ ITree.vis Ev.timeout k' := by
  intro h
  exact ub_ne_timeout (ITree.vis_inj h).1

/-- Return inversion: two `ret` leaves carrying defined outcomes are related
exactly when `post` holds of those outcomes.  A `ret` leaf carrying
`Outcome.ub` is a UB terminal, not a return, and `post` never sees it. -/
theorem simtt_ret_ret_iff (frame) (post) (v v' : Option Value) (mem mem' : Mem)
    (m m' : Mem) :
    simtt frame post (ITree.ret (Outcome.ret v mem), m)
      (ITree.ret (Outcome.ret v' mem'), m') ↔
      post (Outcome.ret v mem) (Outcome.ret v' mem') := by
  constructor
  · intro h
    have hF := (simtt_iff frame post _ _).mp h
    cases hF with
    | ret h1 h2 hp =>
        have e1 := ITree.ret_inj (Prod.mk.inj (SilentHead_ret_self h1)).1
        have e2 := ITree.ret_inj (Prod.mk.inj (SilentHead_ret_self h2)).1
        rw [e1, e2] at hp
        exact hp
    | right_ub_ret h1 h2 => exact (not_reachesUb_ret h2).elim
    | ub h1 h2 => exact (not_reachesUb_ret h1).elim
    | timeout k1 k2 h1 h2 =>
        exact ((ITree.ret_ne_vis Ev.timeout k1).symm
          (Prod.mk.inj (SilentHead_ret_self h1)).1).elim
    | left_diverges hdiv hnt => exact (not_silentDiverges_ret hdiv).elim
    | right_diverges hdiv2 hdiv1 => exact (not_silentDiverges_ret hdiv2).elim
    | vis_load addr ty k1 k2 h1 h2 _ hs =>
        exact ((ITree.ret_ne_vis (Ev.load addr ty) k1).symm
          (Prod.mk.inj (SilentHead_ret_self h1)).1).elim
    | vis_store addr ty v k1 k2 h1 h2 hs =>
        exact ((ITree.ret_ne_vis (Ev.store addr ty v) k1).symm
          (Prod.mk.inj (SilentHead_ret_self h1)).1).elim
    | vis_call callee args k1 k2 h1 h2 hs =>
        exact ((ITree.ret_ne_vis (Ev.call callee args) k1).symm
          (Prod.mk.inj (SilentHead_ret_self h1)).1).elim
  · intro hp
    exact (simtt_iff frame post _ _).mpr
      (SimttF.ret (SilentHead.refl _ _) (SilentHead.refl _ _) hp)

/-! ### Finite stutter -/

/-- Finitely many silent steps on the left preserve the relation. -/
theorem simtt_silentHead_left {frame post} {p p' q : TS}
    (hstep : SilentHead frame p p') (h : simtt frame post p' q) :
    simtt frame post p q := by
  apply simtt.coind frame post (fun r s => ∃ r', SilentHead frame r r' ∧ simtt frame post r' s)
  · intro r s ⟨r', hr', hrs⟩
    have hF := (simtt_iff frame post r' s).mp hrs
    cases hF with
    | ret h1 h2 hp => exact SimttF.ret (SilentHead.trans hr' h1) h2 hp
    | right_ub_ret h1 h2 => exact SimttF.right_ub_ret (SilentHead.trans hr' h1) h2
    | ub h1 h2 => exact SimttF.ub (ReachesUb.of_silentHead hr' h1) h2
    | timeout k1 k2 h1 h2 => exact SimttF.timeout k1 k2 (SilentHead.trans hr' h1) h2
    | left_diverges hdiv hnt =>
        exact SimttF.left_diverges (SilentDiverges.of_silentHead hr' hdiv) hnt
    | right_diverges hdiv2 hdiv1 =>
        exact SimttF.right_diverges hdiv2 (SilentDiverges.of_silentHead hr' hdiv1)
    | vis_load addr ty k1 k2 h1 h2 hm hs =>
        exact SimttF.vis_load addr ty k1 k2 (SilentHead.trans hr' h1) h2 hm
          (fun v => ⟨_, SilentHead.refl _ _, hs v⟩)
    | vis_store addr ty v k1 k2 h1 h2 hs =>
        exact SimttF.vis_store addr ty v k1 k2 (SilentHead.trans hr' h1) h2
          ⟨_, SilentHead.refl _ _, hs⟩
    | vis_call callee args k1 k2 h1 h2 hs =>
        exact SimttF.vis_call callee args k1 k2 (SilentHead.trans hr' h1) h2
          (fun r => ⟨_, SilentHead.refl _ _, hs r⟩)
  · exact ⟨p', hstep, h⟩

/-- Finitely many silent steps on the right preserve the relation. -/
theorem simtt_silentHead_right {frame post} {p q q' : TS}
    (hstep : SilentHead frame q q') (h : simtt frame post p q') :
    simtt frame post p q := by
  apply simtt.coind frame post (fun r s => ∃ s', SilentHead frame s s' ∧ simtt frame post r s')
  · intro r s ⟨s', hs', hrs⟩
    have hF := (simtt_iff frame post r s').mp hrs
    cases hF with
    | ret h1 h2 hp => exact SimttF.ret h1 (SilentHead.trans hs' h2) hp
    | right_ub_ret h1 h2 => exact SimttF.right_ub_ret h1 (ReachesUb.of_silentHead hs' h2)
    | ub h1 h2 => exact SimttF.ub h1 (ReachesUb.of_silentHead hs' h2)
    | timeout k1 k2 h1 h2 => exact SimttF.timeout k1 k2 h1 (SilentHead.trans hs' h2)
    | left_diverges hdiv hnt =>
        exact SimttF.left_diverges hdiv (not_timeoutReachable_of_silentHead hs' hnt)
    | right_diverges hdiv2 hdiv1 =>
        exact SimttF.right_diverges (SilentDiverges.of_silentHead hs' hdiv2) hdiv1
    | vis_load addr ty k1 k2 h1 h2 hm hs =>
        exact SimttF.vis_load addr ty k1 k2 h1 (SilentHead.trans hs' h2) hm
          (fun v => ⟨_, SilentHead.refl _ _, hs v⟩)
    | vis_store addr ty v k1 k2 h1 h2 hs =>
        exact SimttF.vis_store addr ty v k1 k2 h1 (SilentHead.trans hs' h2)
          ⟨_, SilentHead.refl _ _, hs⟩
    | vis_call callee args k1 k2 h1 h2 hs =>
        exact SimttF.vis_call callee args k1 k2 h1 (SilentHead.trans hs' h2)
          (fun r => ⟨_, SilentHead.refl _ _, hs r⟩)
  · exact ⟨q', hstep, h⟩

/-! ### Positive directional rules -/

/-- Two UB terminals are related, whatever their shape and regardless of
`post`: the `ret` leaf carrying `Outcome.ub` and the `vis Ev.ub` node are the
same class. -/
theorem simtt_ub_terminal (frame) (post) {p q : TS} (hp : UbTerminal p)
    (hq : UbTerminal q) : simtt frame post p q :=
  (simtt_iff frame post _ _).mpr
    (SimttF.ub (reachesUb_of_terminal hp) (reachesUb_of_terminal hq))

/-- A right UB terminal admits any completed left return, defined or `ub`, and
`post` is not consulted. -/
theorem simtt_ret_ub_terminal (frame) (post) (o : Outcome) (m : Mem) {q : TS}
    (hq : UbTerminal q) : simtt frame post (ITree.ret o, m) q :=
  (simtt_iff frame post _ _).mpr
    (SimttF.right_ub_ret (SilentHead.refl _ _) (reachesUb_of_terminal hq))

/-- A right `ub` node admits a completed left return. -/
theorem simtt_ret_ub (frame) (post) (o : Outcome) (m m' : Mem) :
    simtt frame post (ITree.ret o, m)
      (ITree.vis Ev.ub (Empty.elim : Empty → ITree Ev Outcome), m') :=
  simtt_ret_ub_terminal frame post o m (UbTerminal.vis Empty.elim m')

/-- A left `ub` node is related to a right `ub` node. -/
theorem simtt_ub_ub (frame) (post)
    (k1 k2 : Empty → ITree Ev Outcome) (m m' : Mem) :
    simtt frame post (ITree.vis Ev.ub k1, m) (ITree.vis Ev.ub k2, m') :=
  simtt_ub_terminal frame post (UbTerminal.vis k1 m) (UbTerminal.vis k2 m')

/-- A budget timeout matches itself. -/
theorem simtt_timeout_timeout (frame) (post)
    (k1 k2 : Empty → ITree Ev Outcome) (m m' : Mem) :
    simtt frame post (ITree.vis Ev.timeout k1, m) (ITree.vis Ev.timeout k2, m') :=
  (simtt_iff frame post _ _).mpr
    (SimttF.timeout k1 k2 (SilentHead.refl _ _) (SilentHead.refl _ _))

/-- Left silent divergence is the bottom against a right side that cannot
silently reach a timeout. -/
theorem simtt_diverges (frame) (post) {p q : TS}
    (hdiv : SilentDiverges frame p) (hnt : ¬ TimeoutReachable frame q) :
    simtt frame post p q :=
  (simtt_iff frame post _ _).mpr (SimttF.left_diverges hdiv hnt)

/-- A left silent divergence is related to any right return. -/
theorem simtt_diverges_ret (frame) (post) (o : Outcome) (m m' : Mem) :
    simtt frame post (ITree.infTau, m) (ITree.ret o, m') :=
  simtt_diverges frame post (infTau_diverges frame m) not_timeoutReachable_ret

/-- A left silent divergence is related to a right `ub`. -/
theorem simtt_diverges_ub (frame) (post) (k : Empty → ITree Ev Outcome) (m m' : Mem) :
    simtt frame post (ITree.infTau, m) (ITree.vis Ev.ub k, m') :=
  simtt_diverges frame post (infTau_diverges frame m) not_timeoutReachable_ub

/-- Two silent divergences are related: the right-divergence clause requires a
left one and admits it here, so right divergence is not rejected wholesale. -/
theorem simtt_diverges_diverges (frame) (post) (m m' : Mem) :
    simtt frame post (ITree.infTau, m) (ITree.infTau, m') :=
  (simtt_iff frame post _ _).mpr
    (SimttF.right_diverges (infTau_diverges frame m') (infTau_diverges frame m))

/-! ### Mismatched terminals are rejected -/

/-- A left UB terminal is not related to a defined return: the UB class matches
only itself on the right, and `post` never sees `ub`. -/
theorem not_simtt_ub_terminal_ret (frame) (post) {p : TS} (hp : UbTerminal p)
    (v : Option Value) (mem : Mem) (m : Mem) :
    ¬ simtt frame post p (ITree.ret (Outcome.ret v mem), m) := by
  intro h
  have hF := (simtt_iff frame post _ _).mp h
  cases hF with
  | ret h1 h2 _ =>
      cases hp with
      | ret m' =>
          exact Outcome.noConfusion
            (ITree.ret_inj (Prod.mk.inj (SilentHead_ret_self h1)).1)
      | vis k m' =>
          exact ITree.ret_ne_vis Ev.ub k (Prod.mk.inj (SilentHead_ub_self h1)).1
  | right_ub_ret h1 h2 => exact not_reachesUb_ret h2
  | ub h1 h2 => exact not_reachesUb_ret h2
  | timeout k1 k2 h1 h2 =>
      cases hp with
      | ret m' =>
          exact (ITree.ret_ne_vis Ev.timeout k1).symm
            (Prod.mk.inj (SilentHead_ret_self h1)).1
      | vis k m' =>
          exact ub_ne_timeout.symm
            (ITree.vis_inj (Prod.mk.inj (SilentHead_ub_self h1)).1).1
  | left_diverges hdiv hnt =>
      cases hp with
      | ret m' => exact not_silentDiverges_ret hdiv
      | vis k m' => exact not_silentDiverges_ub hdiv
  | right_diverges hdiv2 hdiv1 => exact not_silentDiverges_ret hdiv2
  | vis_load addr ty k1 k2 h1 h2 _ hs =>
      cases hp with
      | ret m' =>
          exact (ITree.ret_ne_vis (Ev.load addr ty) k1).symm
            (Prod.mk.inj (SilentHead_ret_self h1)).1
      | vis k m' =>
          exact (vis_ub_ne_load k addr ty k1).symm
            (Prod.mk.inj (SilentHead_ub_self h1)).1
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      cases hp with
      | ret m' =>
          exact (ITree.ret_ne_vis (Ev.store addr ty v) k1).symm
            (Prod.mk.inj (SilentHead_ret_self h1)).1
      | vis k m' =>
          exact (vis_ub_ne_store k addr ty v k1).symm
            (Prod.mk.inj (SilentHead_ub_self h1)).1
  | vis_call callee args k1 k2 h1 h2 hs =>
      cases hp with
      | ret m' =>
          exact (ITree.ret_ne_vis (Ev.call callee args) k1).symm
            (Prod.mk.inj (SilentHead_ret_self h1)).1
      | vis k m' =>
          exact (vis_ub_ne_call k callee args k1).symm
            (Prod.mk.inj (SilentHead_ub_self h1)).1

/-- A left `ub` node is not matched by a defined return. -/
theorem not_simtt_ub_ret (frame) (post) (v : Option Value) (mem : Mem) (m m' : Mem)
    (k : Empty → ITree Ev Outcome) :
    ¬ simtt frame post (ITree.vis Ev.ub k, m) (ITree.ret (Outcome.ret v mem), m') :=
  not_simtt_ub_terminal_ret frame post (UbTerminal.vis k m) v mem m'

/-- The `ret` leaf carrying `Outcome.ub` is the same UB terminal: a defined
return does not match it either. -/
theorem not_simtt_ret_ub_ret (frame) (post) (v : Option Value) (mem : Mem) (m m' : Mem) :
    ¬ simtt frame post (ITree.ret Outcome.ub, m) (ITree.ret (Outcome.ret v mem), m') :=
  not_simtt_ub_terminal_ret frame post (UbTerminal.ret m) v mem m'

/-- A left return is not matched by a right budget timeout. -/
theorem not_simtt_ret_timeout (frame) (post) (o : Outcome) (m m' : Mem)
    (k : Empty → ITree Ev Outcome) :
    ¬ simtt frame post (ITree.ret o, m) (ITree.vis Ev.timeout k, m') := by
  intro h
  have hF := (simtt_iff frame post _ _).mp h
  cases hF with
  | ret h1 h2 hp =>
      exact ITree.ret_ne_vis Ev.timeout k (Prod.mk.inj (SilentHead_timeout_self h2)).1
  | right_ub_ret h1 h2 => exact not_reachesUb_timeout h2
  | ub h1 h2 => exact not_reachesUb_timeout h2
  | timeout k1 k2 h1 h2 =>
      exact (ITree.ret_ne_vis Ev.timeout k1).symm
        (Prod.mk.inj (SilentHead_ret_self h1)).1
  | left_diverges hdiv hnt => exact not_silentDiverges_ret hdiv
  | right_diverges hdiv2 hdiv1 => exact not_silentDiverges_timeout hdiv2
  | vis_load addr ty k1 k2 h1 h2 _ hs =>
      exact (vis_timeout_ne_load k addr ty k2).symm
        (Prod.mk.inj (SilentHead_timeout_self h2)).1
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact (vis_timeout_ne_store k addr ty v k2).symm
        (Prod.mk.inj (SilentHead_timeout_self h2)).1
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact (vis_timeout_ne_call k callee args k2).symm
        (Prod.mk.inj (SilentHead_timeout_self h2)).1

/-- A left budget timeout is not matched by a right return. -/
theorem not_simtt_timeout_ret (frame) (post) (o : Outcome) (m m' : Mem)
    (k : Empty → ITree Ev Outcome) :
    ¬ simtt frame post (ITree.vis Ev.timeout k, m) (ITree.ret o, m') := by
  intro h
  have hF := (simtt_iff frame post _ _).mp h
  cases hF with
  | ret h1 h2 hp =>
      exact ITree.ret_ne_vis Ev.timeout k (Prod.mk.inj (SilentHead_timeout_self h1)).1
  | right_ub_ret h1 h2 =>
      exact ITree.ret_ne_vis Ev.timeout k (Prod.mk.inj (SilentHead_timeout_self h1)).1
  | ub h1 h2 => exact not_reachesUb_timeout h1
  | timeout k1 k2 h1 h2 =>
      exact (ITree.ret_ne_vis Ev.timeout k2).symm
        (Prod.mk.inj (SilentHead_ret_self h2)).1
  | left_diverges hdiv hnt => exact not_silentDiverges_timeout hdiv
  | right_diverges hdiv2 hdiv1 => exact not_silentDiverges_ret hdiv2
  | vis_load addr ty k1 k2 h1 h2 _ hs =>
      exact (vis_timeout_ne_load k addr ty k1).symm
        (Prod.mk.inj (SilentHead_timeout_self h1)).1
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact (vis_timeout_ne_store k addr ty v k1).symm
        (Prod.mk.inj (SilentHead_timeout_self h1)).1
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact (vis_timeout_ne_call k callee args k1).symm
        (Prod.mk.inj (SilentHead_timeout_self h1)).1

/-- A left budget timeout is not matched by a right `ub`. -/
theorem not_simtt_timeout_ub (frame) (post)
    (k k' : Empty → ITree Ev Outcome) (m m' : Mem) :
    ¬ simtt frame post (ITree.vis Ev.timeout k, m) (ITree.vis Ev.ub k', m') := by
  intro h
  have hF := (simtt_iff frame post _ _).mp h
  cases hF with
  | ret h1 h2 hp =>
      exact ITree.ret_ne_vis Ev.timeout k (Prod.mk.inj (SilentHead_timeout_self h1)).1
  | right_ub_ret h1 h2 =>
      exact ITree.ret_ne_vis Ev.timeout k (Prod.mk.inj (SilentHead_timeout_self h1)).1
  | ub h1 h2 => exact not_reachesUb_timeout h1
  | timeout k1 k2 h1 h2 =>
      exact ub_ne_timeout ((ITree.vis_inj (Prod.mk.inj (SilentHead_ub_self h2)).1).1).symm
  | left_diverges hdiv hnt => exact not_silentDiverges_timeout hdiv
  | right_diverges hdiv2 hdiv1 => exact not_silentDiverges_ub hdiv2
  | vis_load addr ty k1 k2 h1 h2 _ hs =>
      exact (vis_timeout_ne_load k addr ty k1).symm
        (Prod.mk.inj (SilentHead_timeout_self h1)).1
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact (vis_timeout_ne_store k addr ty v k1).symm
        (Prod.mk.inj (SilentHead_timeout_self h1)).1
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact (vis_timeout_ne_call k callee args k1).symm
        (Prod.mk.inj (SilentHead_timeout_self h1)).1

/-- A left `ub` is not matched by a right budget timeout. -/
theorem not_simtt_ub_timeout (frame) (post)
    (k k' : Empty → ITree Ev Outcome) (m m' : Mem) :
    ¬ simtt frame post (ITree.vis Ev.ub k, m) (ITree.vis Ev.timeout k', m') := by
  intro h
  have hF := (simtt_iff frame post _ _).mp h
  cases hF with
  | ret h1 h2 hp =>
      exact ITree.ret_ne_vis Ev.ub k (Prod.mk.inj (SilentHead_ub_self h1)).1
  | right_ub_ret h1 h2 => exact not_reachesUb_timeout h2
  | ub h1 h2 => exact not_reachesUb_timeout h2
  | timeout k1 k2 h1 h2 =>
      exact ub_ne_timeout ((ITree.vis_inj (Prod.mk.inj (SilentHead_ub_self h1)).1).1).symm
  | left_diverges hdiv hnt => exact not_silentDiverges_ub hdiv
  | right_diverges hdiv2 hdiv1 => exact not_silentDiverges_timeout hdiv2
  | vis_load addr ty k1 k2 h1 h2 _ hs =>
      exact (vis_ub_ne_load k addr ty k1).symm
        (Prod.mk.inj (SilentHead_ub_self h1)).1
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact (vis_ub_ne_store k addr ty v k1).symm
        (Prod.mk.inj (SilentHead_ub_self h1)).1
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact (vis_ub_ne_call k callee args k1).symm
        (Prod.mk.inj (SilentHead_ub_self h1)).1

/-- A right silent divergence is not matched by a left return. -/
theorem not_simtt_ret_diverges (frame) (post) (o : Outcome) (m m' : Mem) :
    ¬ simtt frame post (ITree.ret o, m) (ITree.infTau, m') := by
  intro h
  have hF := (simtt_iff frame post _ _).mp h
  cases hF with
  | ret h1 h2 hp =>
      exact absurd (Prod.mk.inj (SilentHead_infTau_self h2)).1
        (fun hvis => by rw [ITree.infTau_eq] at hvis; exact ITree.ret_ne_tau hvis)
  | right_ub_ret h1 h2 => exact not_reachesUb_infTau h2
  | ub h1 h2 => exact not_reachesUb_infTau h2
  | timeout k1 k2 h1 h2 =>
      exact absurd (Prod.mk.inj (SilentHead_infTau_self h2)).1
        (fun hvis => by
          rw [ITree.infTau_eq] at hvis
          exact (ITree.tau_ne_vis Ev.timeout k2).symm hvis)
  | left_diverges hdiv hnt => exact not_silentDiverges_ret hdiv
  | right_diverges hdiv2 hdiv1 => exact not_silentDiverges_ret hdiv1
  | vis_load addr ty k1 k2 h1 h2 _ hs =>
      exact absurd (Prod.mk.inj (SilentHead_infTau_self h2)).1
        (fun hvis => by
          rw [ITree.infTau_eq] at hvis
          exact (ITree.tau_ne_vis (Ev.load addr ty) k2).symm hvis)
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact absurd (Prod.mk.inj (SilentHead_infTau_self h2)).1
        (fun hvis => by
          rw [ITree.infTau_eq] at hvis
          exact (ITree.tau_ne_vis (Ev.store addr ty v) k2).symm hvis)
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact absurd (Prod.mk.inj (SilentHead_infTau_self h2)).1
        (fun hvis => by
          rw [ITree.infTau_eq] at hvis
          exact (ITree.tau_ne_vis (Ev.call callee args) k2).symm hvis)

end LeanLLVM.ITree
