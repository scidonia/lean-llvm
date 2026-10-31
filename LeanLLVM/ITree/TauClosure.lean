/-
The delay closure, at the host relation.

`TauHead p q` says `p` is `q` behind finitely many silent steps, witnessed by a
first-class `TauClosure` delay whose `flatten` is `p`; `TauDiverges p` says `p`
is an infinite delay whose `flatten` is `p`.  Both are exactly the existing
`SilentHead`/`SilentDiverges`: the equivalence is proved in both directions here,
so the new carrier restates the same predicates rather than installing a second
relation.

The one-step functional `TauSimttF` repeats the nine terminal/event clauses of
`SimttF` with the delay-indexed predicates.  It is *equivalent clause by clause*
to `SimttF` on the same `post`, `sim`, `p` and `q`, so `simtt post` is exactly
the greatest fixed point of the delay-indexed functional; `Simtt.lean` keeps the
accepted definition and this module only characterizes it.  The classification
and the direction are untouched: a defined return still consults `post` on the
two outcomes, a right UB still admits any completed left return without `post`, a
left UB still requires a right UB, timeout still matches only timeout, left
divergence is still bottom only against an unreachable right timeout, and visible
events still match the same payload for every response.
-/
import LeanLLVM.ITree.Simtt
import ITree.TauClosure

namespace LeanLLVM.ITree

open LeanLLVM
open _root_.ITree
open _root_.ITree.Internal
open _root_.ITree.TauClosure
open Lean.Order

/-! ### Finite delay -/

/-- `p` is `q` behind finitely many silent steps, witnessed by a delay. -/
def TauHead (p q : OTree) : Prop :=
  ∃ d : TauClosure OTree, Finite d q ∧ flatten d = p

/-- `p` is an infinite delay. -/
def TauDiverges (p : OTree) : Prop :=
  ∃ d : TauClosure OTree, Infinite d ∧ flatten d = p

/-- A tree whose delay reaches a UB terminal. -/
def TauReachesUb (p : OTree) : Prop :=
  ∃ q : OTree, TauHead p q ∧ UbTerminal q

/-- A tree whose delay reaches a budget timeout. -/
def TauTimeoutReachable (p : OTree) : Prop :=
  ∃ q : OTree, TauHead p q ∧ ∃ k : Empty → OTree, q = vis ObsEv.timeout k

/-! #### Finite delay is silent closure

The bridge is `tauN`: a delay with `n` `later`s flattens to `n` silent steps. -/

theorem tauN_tau (n : Nat) (t : OTree) : tauN n (tau t) = tauN (n + 1) t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tauN, ih]

/-- A finite silent closure is a finite tower of `tau`s, and every such tower is
a finite silent closure. -/
theorem silentHead_tauN (n : Nat) (q : OTree) :
    SilentHead (tauN n q) q := by
  induction n with
  | zero => exact SilentHead.refl q
  | succ n ih => exact SilentHead.step (SilentStep.step _) ih

theorem exists_tauN_of_silentHead {p q : OTree} (h : SilentHead p q) :
    ∃ n : Nat, p = tauN n q := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨t, hmid, hq⟩ := SilentStep_inv hstep
      refine ⟨n + 1, ?_⟩
      rw [hn, hmid, hq, tauN_tau]

private theorem finite_tauN_now (n : Nat) (q : OTree) : Finite (tauN n (now q)) q := by
  induction n with
  | zero => exact finite_now q
  | succ n ih => exact Finite.later ih

private theorem flatten_tauN_now (n : Nat) (q : OTree) :
    flatten (tauN n (now q)) = tauN n q := by
  induction n with
  | zero => exact flatten_now q
  | succ n ih =>
      rw [tauN]
      change flatten (later (tauN n (now q))) = tauN (n + 1) q
      rw [flatten_later, ih, tauN]

theorem tauHead_iff_silentHead {p q : OTree} : TauHead p q ↔ SilentHead p q := by
  constructor
  · rintro ⟨d, hf, hfl⟩
    induction hf generalizing p with
    | now q =>
        rw [flatten_now] at hfl
        rw [← hfl]
        exact SilentHead.refl q
    | later _ ih =>
        rw [flatten_later] at hfl
        subst hfl
        exact SilentHead.step (SilentStep.step _) (ih rfl)
  · intro h
    obtain ⟨n, hn⟩ := exists_tauN_of_silentHead h
    exact ⟨tauN n (now q), finite_tauN_now n q, by rw [flatten_tauN_now]; exact hn.symm⟩

/-- A delay of one step out of a `tau` closes to the tree behind it. -/
theorem silentHead_of_tauHead {p q : OTree} (h : TauHead p q) : SilentHead p q :=
  tauHead_iff_silentHead.mp h

/-- The same trees, the same silent closure, witnessed by a delay. -/
theorem tauHead_of_silentHead {p q : OTree} (h : SilentHead p q) : TauHead p q :=
  tauHead_iff_silentHead.mpr h

/-! #### Infinite delay is silent divergence -/

/-- A silently diverging tree is the tree of infinitely many silent steps: its
only silent steps are `tau`s, so an infinite chain of them is `infTau`. -/
theorem eq_infTau_of_silentDiverges {p : OTree} (h : SilentDiverges p) : p = infTau := by
  refine PFunctor.M.bisim (fun x y => SilentDiverges x ∧ y = infTau) ?_ _ _ ⟨h, rfl⟩
  rintro x y ⟨hdiv, rfl⟩
  have hF : DivF SilentDiverges x := (congrFun SilentDiverges.eq_1 x).mp hdiv
  cases hF with
  | step hstep hx' =>
      obtain ⟨t, hx, ht⟩ := SilentStep_inv hstep
      refine ⟨Shape.tau, fin1Const t, fin1Const infTau, ?_, ?_, ?_⟩
      · rw [hx, dest_tau]
        rfl
      · conv_lhs => rw [infTau_eq]
        exact dest_tau
      · intro i
        match i with
        | .up (.ofNat' 0) => exact ⟨ht ▸ hx', rfl⟩

theorem silentDiverges_of_tauDiverges {p : OTree} (h : TauDiverges p) : SilentDiverges p := by
  obtain ⟨d, hinf, hfl⟩ := h
  subst hfl
  apply SilentDiverges.coind (fun p => ∃ d : TauClosure OTree, Infinite d ∧ flatten d = p)
  · rintro p ⟨d, hinf, rfl⟩
    obtain ⟨d', hd, hd'⟩ := (Infinite.unfold d).mp hinf
    rw [hd, flatten_later]
    exact DivF.step (SilentStep.step _) ⟨d', hd', rfl⟩
  · exact ⟨d, hinf, rfl⟩

theorem tauDiverges_of_silentDiverges {p : OTree} (h : SilentDiverges p) : TauDiverges p :=
  ⟨forever, infinite_forever, by rw [flatten_forever, eq_infTau_of_silentDiverges h]⟩

theorem tauDiverges_iff_silentDiverges {p : OTree} :
    TauDiverges p ↔ SilentDiverges p :=
  ⟨silentDiverges_of_tauDiverges, tauDiverges_of_silentDiverges⟩

/-! #### Terminal reachability -/

theorem tauReachesUb_iff {p : OTree} : TauReachesUb p ↔ ReachesUb p := by
  constructor
  · rintro ⟨q, hhead, hterm⟩
    exact ReachesUb.of_silentHead (silentHead_of_tauHead hhead) (reachesUb_of_terminal hterm)
  · intro h
    cases h with
    | retLeaf h' => exact ⟨_, tauHead_of_silentHead h', UbTerminal.retLeaf⟩
    | ubNode h' => exact ⟨_, tauHead_of_silentHead h', UbTerminal.ubNode _⟩

theorem tauTimeoutReachable_iff {p : OTree} :
    TauTimeoutReachable p ↔ TimeoutReachable p := by
  constructor
  · rintro ⟨q, hhead, k, hk⟩
    exact ⟨q, silentHead_of_tauHead hhead, k, hk⟩
  · rintro ⟨q, hhead, k, hk⟩
    exact ⟨q, tauHead_of_silentHead hhead, k, hk⟩

/-! ### The delay-indexed one-step functional -/

/-- One unfolding of the relation with every silent-closure witness given by a
delay: the same nine classes, in the same direction. -/
inductive TauSimttF (post : Outcome → Outcome → Prop) (sim : OTree → OTree → Prop) :
    OTree → OTree → Prop where
  | ret_ret {p q : OTree} {v₁ v₂ : Option Value} {mem₁ mem₂ : Mem}
      (h1 : TauHead p (ret (Outcome.ret v₁ mem₁)))
      (h2 : TauHead q (ret (Outcome.ret v₂ mem₂)))
      (hp : post (Outcome.ret v₁ mem₁) (Outcome.ret v₂ mem₂)) : TauSimttF post sim p q
  | right_ub_ret {p q : OTree} {o : Outcome}
      (h1 : TauHead p (ret o)) (h2 : TauReachesUb q) : TauSimttF post sim p q
  | ub {p q : OTree} (h1 : TauReachesUb p) (h2 : TauReachesUb q) : TauSimttF post sim p q
  | timeout {p q : OTree} (k1 k2 : Empty → OTree)
      (h1 : TauHead p (vis ObsEv.timeout k1))
      (h2 : TauHead q (vis ObsEv.timeout k2)) : TauSimttF post sim p q
  | left_diverges {p q : OTree} (hdiv : TauDiverges p)
      (hnt : ¬ TauTimeoutReachable q) : TauSimttF post sim p q
  | right_diverges {p q : OTree} (hdiv2 : TauDiverges q)
      (hdiv1 : TauDiverges p) : TauSimttF post sim p q
  | vis_load {p q : OTree} (addr : Nat) (ty : Ty) (r : Option Value)
      (k1 k2 : Unit → OTree)
      (h1 : TauHead p (vis (ObsEv.load addr ty r) k1))
      (h2 : TauHead q (vis (ObsEv.load addr ty r) k2))
      (hs : sim (k1 ()) (k2 ())) : TauSimttF post sim p q
  | vis_store {p q : OTree} (addr : Nat) (ty : Ty) (v : Value)
      (k1 k2 : Unit → OTree)
      (h1 : TauHead p (vis (ObsEv.store addr ty v) k1))
      (h2 : TauHead q (vis (ObsEv.store addr ty v) k2))
      (hs : sim (k1 ()) (k2 ())) : TauSimttF post sim p q
  | vis_call {p q : OTree} (callee : String) (args : List Value)
      (k1 k2 : Option Value → OTree)
      (h1 : TauHead p (vis (ObsEv.call callee args) k1))
      (h2 : TauHead q (vis (ObsEv.call callee args) k2))
      (hs : ∀ r, sim (k1 r) (k2 r)) : TauSimttF post sim p q

/-- The delay-indexed functional is the existing one, clause by clause. -/
theorem tauSimttF_iff (post : Outcome → Outcome → Prop) (sim : OTree → OTree → Prop)
    (p q : OTree) : TauSimttF post sim p q ↔ SimttF post sim p q := by
  constructor
  · intro h
    cases h with
    | ret_ret h1 h2 hp =>
        exact SimttF.ret_ret (silentHead_of_tauHead h1) (silentHead_of_tauHead h2) hp
    | right_ub_ret h1 h2 =>
        exact SimttF.right_ub_ret (silentHead_of_tauHead h1) (tauReachesUb_iff.mp h2)
    | ub h1 h2 => exact SimttF.ub (tauReachesUb_iff.mp h1) (tauReachesUb_iff.mp h2)
    | timeout k1 k2 h1 h2 =>
        exact SimttF.timeout k1 k2 (silentHead_of_tauHead h1) (silentHead_of_tauHead h2)
    | left_diverges hdiv hnt =>
        exact SimttF.left_diverges (silentDiverges_of_tauDiverges hdiv)
          (fun ht => hnt (tauTimeoutReachable_iff.mpr ht))
    | right_diverges hdiv2 hdiv1 =>
        exact SimttF.right_diverges (silentDiverges_of_tauDiverges hdiv2)
          (silentDiverges_of_tauDiverges hdiv1)
    | vis_load addr ty r k1 k2 h1 h2 hs =>
        exact SimttF.vis_load addr ty r k1 k2 (silentHead_of_tauHead h1)
          (silentHead_of_tauHead h2) hs
    | vis_store addr ty v k1 k2 h1 h2 hs =>
        exact SimttF.vis_store addr ty v k1 k2 (silentHead_of_tauHead h1)
          (silentHead_of_tauHead h2) hs
    | vis_call callee args k1 k2 h1 h2 hs =>
        exact SimttF.vis_call callee args k1 k2 (silentHead_of_tauHead h1)
          (silentHead_of_tauHead h2) hs
  · intro h
    cases h with
    | ret_ret h1 h2 hp =>
        exact TauSimttF.ret_ret (tauHead_of_silentHead h1) (tauHead_of_silentHead h2) hp
    | right_ub_ret h1 h2 =>
        exact TauSimttF.right_ub_ret (tauHead_of_silentHead h1) (tauReachesUb_iff.mpr h2)
    | ub h1 h2 => exact TauSimttF.ub (tauReachesUb_iff.mpr h1) (tauReachesUb_iff.mpr h2)
    | timeout k1 k2 h1 h2 =>
        exact TauSimttF.timeout k1 k2 (tauHead_of_silentHead h1) (tauHead_of_silentHead h2)
    | left_diverges hdiv hnt =>
        exact TauSimttF.left_diverges (tauDiverges_of_silentDiverges hdiv)
          (fun ht => hnt (tauTimeoutReachable_iff.mp ht))
    | right_diverges hdiv2 hdiv1 =>
        exact TauSimttF.right_diverges (tauDiverges_of_silentDiverges hdiv2)
          (tauDiverges_of_silentDiverges hdiv1)
    | vis_load addr ty r k1 k2 h1 h2 hs =>
        exact TauSimttF.vis_load addr ty r k1 k2 (tauHead_of_silentHead h1)
          (tauHead_of_silentHead h2) hs
    | vis_store addr ty v k1 k2 h1 h2 hs =>
        exact TauSimttF.vis_store addr ty v k1 k2 (tauHead_of_silentHead h1)
          (tauHead_of_silentHead h2) hs
    | vis_call callee args k1 k2 h1 h2 hs =>
        exact TauSimttF.vis_call callee args k1 k2 (tauHead_of_silentHead h1)
          (tauHead_of_silentHead h2) hs

theorem TauSimttF_monotone {post} {sim sim' : OTree → OTree → Prop}
    (h : ∀ p q, sim p q → sim' p q) :
    ∀ p q, TauSimttF post sim p q → TauSimttF post sim' p q := by
  intro p q hpq
  cases hpq with
  | ret_ret h1 h2 hp => exact TauSimttF.ret_ret h1 h2 hp
  | right_ub_ret h1 h2 => exact TauSimttF.right_ub_ret h1 h2
  | ub h1 h2 => exact TauSimttF.ub h1 h2
  | timeout k1 k2 h1 h2 => exact TauSimttF.timeout k1 k2 h1 h2
  | left_diverges hdiv hnt => exact TauSimttF.left_diverges hdiv hnt
  | right_diverges h2 h1 => exact TauSimttF.right_diverges h2 h1
  | vis_load addr ty r k1 k2 h1 h2 hs =>
      exact TauSimttF.vis_load addr ty r k1 k2 h1 h2 (h _ _ hs)
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact TauSimttF.vis_store addr ty v k1 k2 h1 h2 (h _ _ hs)
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact TauSimttF.vis_call callee args k1 k2 h1 h2 (fun r => h _ _ (hs r))

private instance instTauSimttPartialOrder : Lean.Order.PartialOrder (OTree → OTree → Prop) :=
  inferInstanceAs (Lean.Order.PartialOrder (OTree → OTree → ReverseImplicationOrder))

private instance instTauSimttLattice : Lean.Order.CompleteLattice (OTree → OTree → Prop) :=
  inferInstanceAs (Lean.Order.CompleteLattice (OTree → OTree → ReverseImplicationOrder))

theorem TauSimttF_monotone_order (post) : monotone (TauSimttF post) := by
  intro x y hxy
  exact TauSimttF_monotone hxy

/-- The directed simulation, as the greatest fixed point of the delay-indexed
functional.  It is not a second relation: `simtt_eq_tau_plfp` identifies it with
`Simtt.lean`'s. -/
private def tauSimtt (post : Outcome → Outcome → Prop) : OTree → OTree → Prop :=
  plfp (TauSimttF post) (hm := TauSimttF_monotone_order post)
    (Lean.Order.top : OTree → OTree → Prop)

theorem tauSimttF_eq (post) : TauSimttF post = SimttF post := by
  funext sim p q
  exact propext (tauSimttF_iff post sim p q)

/-- Two `plfp`s of equal functionals, with whatever monotonicity proofs. -/
private theorem plfp_congr {f g : (OTree → OTree → Prop) → OTree → OTree → Prop}
    (h : f = g) (hmf : monotone f) (hmg : monotone g) (r : OTree → OTree → Prop) :
    plfp f (hm := hmf) r = plfp g (hm := hmg) r := by
  subst h
  rfl

/-- The existing directed simulation is exactly the greatest fixed point of the
delay-indexed functional. -/
theorem simtt_eq_tau_plfp (post : Outcome → Outcome → Prop) :
    simtt post = plfp (TauSimttF post) (hm := TauSimttF_monotone_order post)
      (Lean.Order.top : OTree → OTree → Prop) := by
  unfold simtt
  exact plfp_congr (tauSimttF_eq post).symm _ _ _

private theorem tauSimtt_unfold (post) : tauSimtt post = TauSimttF post (tauSimtt post) := by
  unfold tauSimtt
  conv_lhs => rw [plfp_unfold (hm := TauSimttF_monotone_order post)]
  congr 1
  simp only [uplfp]
  rw [CompleteLattice.meet_comm, CompleteLattice.meet_top]

/-- Unfolding of `simtt` through the delay-indexed functional. -/
theorem simtt_iff_tau (post) (p q : OTree) :
    simtt post p q ↔ TauSimttF post (simtt post) p q := by
  rw [simtt_eq_tau_plfp]
  change tauSimtt post p q ↔ TauSimttF post (tauSimtt post) p q
  conv_lhs => rw [tauSimtt_unfold]

/-- Coinduction for the delay-indexed functional: a relation contained in its
own one-step unfolding is contained in `simtt`. -/
theorem tauSimtt_coind (post) (pred : OTree → OTree → Prop)
    (h : ∀ p q, pred p q → TauSimttF post pred p q) :
    ∀ p q, pred p q → simtt post p q := by
  intro p q hpq
  rw [simtt_eq_tau_plfp]
  rw [← plfp_init (hm := TauSimttF_monotone_order post)]
  exact lfp_le_of_le_monotone (TauSimttF post)
    (hm := TauSimttF_monotone_order post) pred h p q hpq

end LeanLLVM.ITree
