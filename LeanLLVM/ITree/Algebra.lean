/-
Conditioned transport of the directed relation.

Two things live here:

* **exact transport.**  `IEq` is exact equality (`ieq_iff_eq`), so a related pair
  can be replaced by a related pair on either side and the relation is unchanged.
  `simtt_ieq` states that once, with the target on the left.
* **congruence under `bind` and under a same-signature interpreter.**  Both need
  real hypotheses, and both are false without them:
  * `simtt_bind` needs the continuations to be related at `post`-related returns,
    the left continuation to silently complete at a return or reach UB (a left
    side that ends at a visible node has no clause to match), the `.ub`
    continuations to reach UB (`bind (ret .ub) f` is the leaf `f .ub`, not the
    stuck `vis ObsEv.ub`), and the right continuations never to reach a timeout.
    The last two are what the refused examples below show: `simtt Eq (ret o)
    (vis ObsEv.ub Empty.elim)` holds, but binding the left to a timeout gives a
    pair the relation refuses, and a left `infTau` against a right return stops
    being related once the right continuation can reach a timeout;
  * `simtt_interp` needs the handler to re-emit the *identical* event with the
    identical responses, optionally behind a finite silent delay
    (`h e = tauN n (trigger e)`).  A same-signature handler that maps `ObsEv.ub`
    to `ObsEv.timeout` breaks the relation even though its signature matches,
    which is why the event/terminal preservation is a hypothesis and not a
    consequence of the type.

Both proofs are stated over the delay-indexed witnesses the host relation now
exposes: a silent prefix is a `TauHead` with a finite delay, divergence is a
`TauDiverges`, and UB/timeout reachability are `TauReachesUb` and
`TauTimeoutReachable`.  The clause functional is `TauSimttF`, and `simtt` is its
greatest fixed point (`simtt_iff_tau`), so the coinduction is Tau-indexed and the
old `SimttF` characterization is only used where an accepted hypothesis or
statement is phrased in its predicates.
-/
import LeanLLVM.ITree.TauClosure
import ITree.EffectAlgebra

namespace LeanLLVM.ITree

open LeanLLVM
open _root_.ITree
open _root_.ITree.Internal
open _root_.ITree.TauClosure

/-! ### Prepending a finite delay -/

/-- The empty delay: a tree is behind no silent steps of itself. -/
theorem tauHead_refl (p : OTree) : TauHead p p :=
  ⟨now p, finite_now p, flatten_now p⟩

/-- One silent step in front of a delay is still a delay to the same result. -/
theorem tauHead_step {p q : OTree} (h : TauHead p q) : TauHead (tau p) q := by
  obtain ⟨d, hf, hfl⟩ := h
  exact ⟨later d, Finite.later hf, by rw [flatten_later, hfl]⟩

/-- Two finite delays compose: a finite prefix in front of a finite prefix is
one finite prefix.  The composed delay is the first delay's tower of `later`s in
front of the second delay, which is why the composition stays inside
`TauClosure`. -/
theorem tauHead_trans {p q r : OTree} (h1 : TauHead p q) (h2 : TauHead q r) :
    TauHead p r := by
  obtain ⟨d1, hf1, hfl1⟩ := h1
  obtain ⟨d2, hf2, hfl2⟩ := h2
  obtain ⟨n, hn⟩ := flatten_finite_tauN hf1
  refine ⟨tauN n d2, finite_tauN n hf2, ?_⟩
  rw [flatten_tauN, hfl2, ← hn, hfl1]

/-- A delay that reaches a tree through a tower of `tau`s, indexed by the
tower's height. -/
theorem tauHead_tauN (n : Nat) (p : OTree) : TauHead (tauN n p) p :=
  ⟨tauN n (now p), finite_tauN n (finite_now p),
    by rw [flatten_tauN, flatten_now]⟩

/-- Binding keeps a finite delay: the delay's leaf is mapped to the binding, so
its steps are unchanged. -/
theorem tauHead_bind {p p' : OTree} (h : TauHead p p') (f : Outcome → OTree) :
    TauHead (ITree.bind p f) (ITree.bind p' f) := by
  obtain ⟨d, hf, hfl⟩ := h
  exact ⟨ITree.map (fun t => ITree.bind t f) d, finite_map_delay _ hf,
    by rw [flatten_map_bind, hfl]⟩

/-- Binding keeps an infinite delay: the delay's leaf is mapped to the binding,
so its steps are unchanged. -/
theorem tauDiverges_bind {p : OTree} (h : TauDiverges p) (f : Outcome → OTree) :
    TauDiverges (ITree.bind p f) := by
  obtain ⟨d, hinf, hfl⟩ := h
  exact ⟨ITree.map (fun t => ITree.bind t f) d, infinite_map_delay _ hinf,
    by rw [flatten_map_bind, hfl]⟩

/-- A finite prefix in front of an infinite delay is an infinite delay. -/
theorem tauDiverges_of_tauHead {p q : OTree} (h1 : TauHead p q)
    (h2 : TauDiverges q) : TauDiverges p := by
  obtain ⟨d1, hf1, hfl1⟩ := h1
  obtain ⟨d2, hinf2, hfl2⟩ := h2
  obtain ⟨n, hn⟩ := flatten_finite_tauN hf1
  refine ⟨tauN n d2, infinite_tauN n hinf2, ?_⟩
  rw [flatten_tauN, hfl2, ← hn, hfl1]

/-- A finite prefix in front of a tree that reaches UB still reaches UB. -/
theorem tauReachesUb_of_tauHead {p q : OTree} (h1 : TauHead p q)
    (h2 : TauReachesUb q) : TauReachesUb p := by
  obtain ⟨r, hh, ht⟩ := h2
  exact ⟨r, tauHead_trans h1 hh, ht⟩

/-- A finite prefix in front of a tree that reaches a timeout still reaches
one. -/
theorem tauTimeoutReachable_of_tauHead {p q : OTree} (h1 : TauHead p q)
    (h2 : TauTimeoutReachable q) : TauTimeoutReachable p := by
  obtain ⟨r, hh, k, hr⟩ := h2
  exact ⟨r, tauHead_trans h1 hh, k, hr⟩

/-- A finite prefix whose target reaches no timeout reaches none itself: the
prefix consists of silent steps, so a timeout behind it is a timeout of the
target. -/
theorem not_tauTimeoutReachable_of_tauHead {p q : OTree} (h : TauHead p q)
    (hnt : ¬ TauTimeoutReachable q) : ¬ TauTimeoutReachable p := by
  intro hp
  exact (not_timeoutReachable_of_silentHead (silentHead_of_tauHead h))
    (fun hq => hnt (tauTimeoutReachable_iff.mpr hq)) (tauTimeoutReachable_iff.mp hp)

/-! ### Terminal classes are exclusive

A finite silent closure to a step-free tree is the same closure whichever
step-free tree it ends at, so a tree cannot both reach UB and reach a timeout.
The bridge is the `tauN` normal form of a finite closure. -/

theorem tauN_terminal_inj {q r : OTree} {n m : Nat}
    (h : tauN n q = tauN m r) (hq : ∀ s, ¬ SilentStep q s) (hr : ∀ s, ¬ SilentStep r s) :
    q = r := by
  induction n generalizing m with
  | zero =>
      cases m with
      | zero => exact h
      | succ m =>
          change q = tau (tauN m r) at h
          exact absurd (h.symm ▸ SilentStep.step (tauN m r)) (hq _)
  | succ n ih =>
      change tau (tauN n q) = tauN m r at h
      cases m with
      | zero =>
          change tau (tauN n q) = r at h
          exact absurd (h ▸ SilentStep.step (tauN n q)) (hr _)
      | succ m =>
          exact ih (tau_inj h)

/-- A tree that reaches a timeout does not reach UB. -/
theorem not_reachesUb_of_timeoutReachable {p : OTree} (hto : TimeoutReachable p) :
    ¬ ReachesUb p := by
  intro hub
  obtain ⟨q, hq, k, hqk⟩ := hto
  subst hqk
  obtain ⟨n, hn⟩ := exists_tauN_of_silentHead hq
  cases hub with
  | retLeaf h' =>
      obtain ⟨m, hm⟩ := exists_tauN_of_silentHead h'
      have he : tauN n (vis ObsEv.timeout k) = tauN m (ret Outcome.ub) := hn.symm.trans hm
      have := tauN_terminal_inj he (vis_no_step ObsEv.timeout k) (ret_no_step (o := Outcome.ub))
      exact ret_ne_vis ObsEv.timeout k this.symm
  | ubNode h' =>
      obtain ⟨m, hm⟩ := exists_tauN_of_silentHead h'
      have he : tauN n (vis ObsEv.timeout k) = tauN m (vis ObsEv.ub _) := hn.symm.trans hm
      have := tauN_terminal_inj he (vis_no_step ObsEv.timeout k) (vis_no_step ObsEv.ub _)
      exact vis_ub_ne_timeout _ _ this.symm

/-! ### A finite delay in front of a binding

The delay's target is the binding's result, so a finite prefix either stays
inside the binding (the bound tree takes the steps) or enters the continuation
at a return the bound tree reaches.  The inversion is over the finite witness
itself: the delay is put in `tauN` normal form and the binding is unfolded one
constructor at a time, so no `SilentHead` inversion is involved. -/

/-- The inversion at a tower of `tau`s: if `bind q f` is `n` silent steps in
front of `r`, then either it is already `r`, or `q` silently reaches a return and
the continuation does the rest. -/
theorem tauHead_bind_of_tauN {r : OTree} {f : Outcome → OTree} :
    ∀ (n : Nat) (q : OTree), ITree.bind q f = tauN n r →
      (∃ q' : OTree, TauHead q q' ∧ r = ITree.bind q' f) ∨
        (∃ o : Outcome, TauHead q (ret o) ∧ TauHead (f o) r) := by
  intro n
  induction n with
  | zero =>
      intro q hq
      exact Or.inl ⟨q, tauHead_refl q, hq.symm⟩
  | succ n ih =>
      intro q hq
      refine dMatchOn (motive := fun x => ITree.bind x f = tauN (n + 1) r →
        (∃ q' : OTree, TauHead x q' ∧ r = ITree.bind q' f) ∨
          (∃ o : Outcome, TauHead x (ret o) ∧ TauHead (f o) r)) q ?_ ?_ ?_ hq
      · intro o heq hb
        rw [heq, ITree.bind_ret] at hb
        subst heq
        refine Or.inr ⟨o, tauHead_refl _, ⟨tauN (n + 1) (now r),
          finite_tauN (n + 1) (finite_now r), ?_⟩⟩
        rw [flatten_tauN, flatten_now]
        exact hb.symm
      · intro c heq hb
        rw [heq, ITree.bind_tau] at hb
        have hc : ITree.bind c f = tauN n r := tau_inj hb
        subst heq
        rcases ih c hc with ⟨q', hq', hr⟩ | ⟨o, hq, hf⟩
        · exact Or.inl ⟨q', tauHead_step hq', hr⟩
        · exact Or.inr ⟨o, tauHead_step hq, hf⟩
      · intro β e k heq hb
        rw [heq, ITree.bind_vis] at hb
        exact absurd hb.symm (tau_ne_vis e (fun a => ITree.bind (k a) f))

/-- A finite delay entering a binding either stays inside the binding or enters
the continuation at a return the bound tree reaches. -/
theorem tauHead_bind_inv {q r : OTree} {f : Outcome → OTree}
    (h : TauHead (ITree.bind q f) r) :
    (∃ q' : OTree, TauHead q q' ∧ r = ITree.bind q' f) ∨
      (∃ o : Outcome, TauHead q (ret o) ∧ TauHead (f o) r) := by
  obtain ⟨d, hfin, hfl⟩ := h
  obtain ⟨n, hn⟩ := flatten_finite_tauN hfin
  exact tauHead_bind_of_tauN n q (hfl.symm.trans hn)

/-- A timeout in a bound tree is a timeout of the bound tree, or of a
continuation at a return it silently reaches.  The inversion consumes the
finite delay witness directly. -/
theorem tauTimeoutReachable_bind {q : OTree} {f : Outcome → OTree}
    (h : TauTimeoutReachable (ITree.bind q f)) :
    TauTimeoutReachable q ∨
      ∃ o : Outcome, TauHead q (ret o) ∧ TauTimeoutReachable (f o) := by
  obtain ⟨r, hhead, k, hk⟩ := h
  subst hk
  rcases tauHead_bind_inv hhead with ⟨q', hq', hb⟩ | ⟨o, hq, hfo⟩
  · refine dMatchOn (motive := fun x => ITree.bind x f = vis ObsEv.timeout k →
      TauTimeoutReachable q ∨ ∃ o, TauHead q (ret o) ∧ TauTimeoutReachable (f o))
      q' ?_ ?_ ?_ hb.symm
    · intro o heq hb'
      rw [heq, ITree.bind_ret] at hb'
      exact Or.inr ⟨o, heq ▸ hq', ⟨f o, tauHead_refl _, k, hb'⟩⟩
    · intro c heq hb'
      rw [heq, ITree.bind_tau] at hb'
      exact absurd hb' (tau_ne_vis ObsEv.timeout k)
    · intro β e k' heq hb'
      rw [heq, ITree.bind_vis] at hb'
      cases e with
      | load addr ty r' => exact absurd (vis_inj_α hb').symm empty_ne_unit
      | store addr ty v => exact absurd (vis_inj_α hb').symm empty_ne_unit
      | call callee args => exact absurd (vis_inj_α hb').symm empty_ne_option_value
      | ub => exact absurd hb' (vis_ub_ne_timeout _ _)
      | timeout => exact Or.inl ⟨q', hq', k', heq⟩
  · exact Or.inr ⟨o, hq, ⟨vis ObsEv.timeout k, hfo, k, rfl⟩⟩

/-- A silent closure that reaches a UB terminal keeps reaching one after
binding, provided the `.ub` continuation does. -/
theorem tauReachesUb_bind {p : OTree} (h : TauReachesUb p) (f : Outcome → OTree)
    (hub : TauReachesUb (f Outcome.ub)) : TauReachesUb (ITree.bind p f) := by
  obtain ⟨q, hhead, hterm⟩ := h
  have hb : TauHead (ITree.bind p f) (ITree.bind q f) := tauHead_bind hhead f
  cases hterm with
  | retLeaf =>
      rw [ITree.bind_ret] at hb
      exact tauReachesUb_of_tauHead hb hub
  | ubNode k =>
      rw [ITree.bind_vis] at hb
      exact ⟨_, hb, UbTerminal.ubNode _⟩

/-! ### Prepending a finite delay to a one-step clause

The two sides of a `TauSimttF` clause are reached through delay witnesses, so a
finite prefix in front of either side can be absorbed by composing it with that
side's witness.  A left divergence stays a left divergence, and an unreachable
right timeout stays unreachable. -/

/-- A finite silent closure in front of the left tree keeps the one-step clause. -/
theorem tauSimttF_of_tauHead_left {post : Outcome → Outcome → Prop}
    {sim : OTree → OTree → Prop} {a a' b : OTree}
    (hab : TauSimttF post sim a b) (h : TauHead a' a) : TauSimttF post sim a' b := by
  cases hab with
  | ret_ret h1 h2 hp => exact TauSimttF.ret_ret (tauHead_trans h h1) h2 hp
  | right_ub_ret h1 h2 => exact TauSimttF.right_ub_ret (tauHead_trans h h1) h2
  | ub h1 h2 => exact TauSimttF.ub (tauReachesUb_of_tauHead h h1) h2
  | timeout k1 k2 h1 h2 => exact TauSimttF.timeout k1 k2 (tauHead_trans h h1) h2
  | left_diverges hdiv hnt =>
      exact TauSimttF.left_diverges (tauDiverges_of_tauHead h hdiv) hnt
  | right_diverges hdiv2 hdiv1 =>
      exact TauSimttF.right_diverges hdiv2 (tauDiverges_of_tauHead h hdiv1)
  | vis_load addr ty r k1 k2 h1 h2 hs =>
      exact TauSimttF.vis_load addr ty r k1 k2 (tauHead_trans h h1) h2 hs
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact TauSimttF.vis_store addr ty v k1 k2 (tauHead_trans h h1) h2 hs
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact TauSimttF.vis_call callee args k1 k2 (tauHead_trans h h1) h2 hs

/-- A finite silent closure in front of the right tree keeps the one-step
clause.  A left divergence additionally needs the right timeout to stay
unreachable, which is what the prefix's own reachability gives. -/
theorem tauSimttF_of_tauHead_right {post : Outcome → Outcome → Prop}
    {sim : OTree → OTree → Prop} {a b b' : OTree}
    (hab : TauSimttF post sim a b) (h : TauHead b' b) : TauSimttF post sim a b' := by
  cases hab with
  | ret_ret h1 h2 hp => exact TauSimttF.ret_ret h1 (tauHead_trans h h2) hp
  | right_ub_ret h1 h2 => exact TauSimttF.right_ub_ret h1 (tauReachesUb_of_tauHead h h2)
  | ub h1 h2 => exact TauSimttF.ub h1 (tauReachesUb_of_tauHead h h2)
  | timeout k1 k2 h1 h2 => exact TauSimttF.timeout k1 k2 h1 (tauHead_trans h h2)
  | left_diverges hdiv hnt =>
      exact TauSimttF.left_diverges hdiv (not_tauTimeoutReachable_of_tauHead h hnt)
  | right_diverges hdiv2 hdiv1 =>
      exact TauSimttF.right_diverges (tauDiverges_of_tauHead h hdiv2) hdiv1
  | vis_load addr ty r k1 k2 h1 h2 hs =>
      exact TauSimttF.vis_load addr ty r k1 k2 h1 (tauHead_trans h h2) hs
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact TauSimttF.vis_store addr ty v k1 k2 h1 (tauHead_trans h h2) hs
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact TauSimttF.vis_call callee args k1 k2 h1 (tauHead_trans h h2) hs

/-! ### Congruence under `bind` -/

/-- The relation bind congruence closes over: a pair already related at `post'`,
or a pair of bindings related at `post`. -/
def BindR (post post' : Outcome → Outcome → Prop) (f g : Outcome → OTree)
    (a b : OTree) : Prop :=
  simtt post' a b ∨
    ∃ p q : OTree, simtt post p q ∧ a = ITree.bind p f ∧ b = ITree.bind q g

/-- The `ret`/`ret` clause, lifted to the two bindings. -/
theorem tauSimttF_ret_ret_bind {post post' : Outcome → Outcome → Prop}
    {f g : Outcome → OTree}
    (hi : ∀ (v : Option Value) (mem : Mem) (v' : Option Value) (mem' : Mem),
      post (.ret v mem) (.ret v' mem') →
        simtt post' (f (.ret v mem)) (g (.ret v' mem')))
    {p q : OTree} {v₁ v₂ : Option Value} {mem₁ mem₂ : Mem}
    (h1 : TauHead p (ret (Outcome.ret v₁ mem₁)))
    (h2 : TauHead q (ret (Outcome.ret v₂ mem₂)))
    (hp : post (Outcome.ret v₁ mem₁) (Outcome.ret v₂ mem₂)) :
    TauSimttF post' (BindR post post' f g) (ITree.bind p f) (ITree.bind q g) := by
  have hres : TauSimttF post' (BindR post post' f g)
      (f (Outcome.ret v₁ mem₁)) (g (Outcome.ret v₂ mem₂)) :=
    TauSimttF_monotone (fun x y hxy => Or.inl hxy) _ _
      ((simtt_iff_tau post' _ _).mp (hi v₁ mem₁ v₂ mem₂ hp))
  have hL : TauHead (ITree.bind p f) (f (Outcome.ret v₁ mem₁)) := by
    have := tauHead_bind h1 f
    rwa [ITree.bind_ret] at this
  have hR : TauHead (ITree.bind q g) (g (Outcome.ret v₂ mem₂)) := by
    have := tauHead_bind h2 g
    rwa [ITree.bind_ret] at this
  exact tauSimttF_of_tauHead_right (tauSimttF_of_tauHead_left hres hL) hR

/-- The right-UB clause, lifted to the two bindings. -/
theorem tauSimttF_right_ub_ret_bind {post post' : Outcome → Outcome → Prop}
    {f g : Outcome → OTree}
    (hii : ∀ o : Outcome,
      (∃ o' : Outcome, SilentHead (f o) (ret o')) ∨ ReachesUb (f o))
    (hiii_g : ReachesUb (g Outcome.ub))
    {p q : OTree} {o : Outcome} (h1 : TauHead p (ret o)) (h2 : TauReachesUb q) :
    TauSimttF post' (BindR post post' f g) (ITree.bind p f) (ITree.bind q g) := by
  have hL : TauHead (ITree.bind p f) (f o) := by
    have := tauHead_bind h1 f
    rwa [ITree.bind_ret] at this
  have hR : TauReachesUb (ITree.bind q g) :=
    tauReachesUb_bind h2 g (tauReachesUb_iff.mpr hiii_g)
  rcases hii o with ⟨o', hret⟩ | hub
  · exact TauSimttF.right_ub_ret (tauHead_trans hL (tauHead_of_silentHead hret)) hR
  · exact TauSimttF.ub (tauReachesUb_of_tauHead hL (tauReachesUb_iff.mpr hub)) hR

/-- One clause for the two bindings, from the clause of the two bound trees. -/
theorem tauSimttF_bind_lift {post post' : Outcome → Outcome → Prop}
    {f g : Outcome → OTree}
    (hi : ∀ (v : Option Value) (mem : Mem) (v' : Option Value) (mem' : Mem),
      post (.ret v mem) (.ret v' mem') →
        simtt post' (f (.ret v mem)) (g (.ret v' mem')))
    (hii : ∀ o : Outcome,
      (∃ o' : Outcome, SilentHead (f o) (ret o')) ∨ ReachesUb (f o))
    (hiii_f : ReachesUb (f Outcome.ub)) (hiii_g : ReachesUb (g Outcome.ub))
    (hiv : ∀ (v : Option Value) (mem : Mem), ¬ TimeoutReachable (g (.ret v mem)))
    {p q : OTree} (hcl : TauSimttF post (simtt post) p q) :
    TauSimttF post' (BindR post post' f g) (ITree.bind p f) (ITree.bind q g) := by
  cases hcl with
  | ret_ret h1 h2 hp => exact tauSimttF_ret_ret_bind hi h1 h2 hp
  | right_ub_ret h1 h2 => exact tauSimttF_right_ub_ret_bind hii hiii_g h1 h2
  | ub h1 h2 =>
      exact TauSimttF.ub (tauReachesUb_bind h1 f (tauReachesUb_iff.mpr hiii_f))
        (tauReachesUb_bind h2 g (tauReachesUb_iff.mpr hiii_g))
  | timeout k1 k2 h1 h2 =>
      have hL : TauHead (ITree.bind p f) (vis ObsEv.timeout fun a => ITree.bind (k1 a) f) := by
        have := tauHead_bind h1 f
        rwa [ITree.bind_vis] at this
      have hR : TauHead (ITree.bind q g) (vis ObsEv.timeout fun a => ITree.bind (k2 a) g) := by
        have := tauHead_bind h2 g
        rwa [ITree.bind_vis] at this
      exact TauSimttF.timeout _ _ hL hR
  | left_diverges hdiv hnt =>
      refine TauSimttF.left_diverges (tauDiverges_bind hdiv f) ?_
      intro hto
      rcases tauTimeoutReachable_bind hto with hq | ⟨o, hq, hgo⟩
      · exact hnt hq
      · cases o with
        | ret v mem => exact hiv v mem (tauTimeoutReachable_iff.mp hgo)
        | ub => exact not_reachesUb_of_timeoutReachable (tauTimeoutReachable_iff.mp hgo) hiii_g
  | right_diverges hdiv2 hdiv1 =>
      exact TauSimttF.right_diverges (tauDiverges_bind hdiv2 g) (tauDiverges_bind hdiv1 f)
  | vis_load addr ty r k1 k2 h1 h2 hs =>
      have hL : TauHead (ITree.bind p f)
          (vis (ObsEv.load addr ty r) fun () => ITree.bind (k1 ()) f) := by
        have := tauHead_bind h1 f
        rwa [ITree.bind_vis] at this
      have hR : TauHead (ITree.bind q g)
          (vis (ObsEv.load addr ty r) fun () => ITree.bind (k2 ()) g) := by
        have := tauHead_bind h2 g
        rwa [ITree.bind_vis] at this
      exact TauSimttF.vis_load addr ty r _ _ hL hR
        (Or.inr ⟨k1 (), k2 (), hs, rfl, rfl⟩)
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      have hL : TauHead (ITree.bind p f)
          (vis (ObsEv.store addr ty v) fun () => ITree.bind (k1 ()) f) := by
        have := tauHead_bind h1 f
        rwa [ITree.bind_vis] at this
      have hR : TauHead (ITree.bind q g)
          (vis (ObsEv.store addr ty v) fun () => ITree.bind (k2 ()) g) := by
        have := tauHead_bind h2 g
        rwa [ITree.bind_vis] at this
      exact TauSimttF.vis_store addr ty v _ _ hL hR
        (Or.inr ⟨k1 (), k2 (), hs, rfl, rfl⟩)
  | vis_call callee args k1 k2 h1 h2 hs =>
      have hL : TauHead (ITree.bind p f)
          (vis (ObsEv.call callee args) fun r => ITree.bind (k1 r) f) := by
        have := tauHead_bind h1 f
        rwa [ITree.bind_vis] at this
      have hR : TauHead (ITree.bind q g)
          (vis (ObsEv.call callee args) fun r => ITree.bind (k2 r) g) := by
        have := tauHead_bind h2 g
        rwa [ITree.bind_vis] at this
      exact TauSimttF.vis_call callee args _ _ hL hR
        (fun r => Or.inr ⟨k1 r, k2 r, hs r, rfl, rfl⟩)

/-- Binding congruence for the directed relation, with the four compatibility
hypotheses it needs: `post`-related returns give related continuations, the left
continuation silently completes at a return or reaches UB, both `.ub`
continuations reach UB, and no right continuation reaches a timeout. -/
theorem simtt_bind {post post' : Outcome → Outcome → Prop}
    {p q : OTree} {f g : Outcome → OTree} (h : simtt post p q)
    (hi : ∀ (v : Option Value) (mem : Mem) (v' : Option Value) (mem' : Mem),
      post (.ret v mem) (.ret v' mem') →
        simtt post' (f (.ret v mem)) (g (.ret v' mem')))
    (hii : ∀ o : Outcome,
      (∃ o' : Outcome, SilentHead (f o) (ret o')) ∨ ReachesUb (f o))
    (hiii_f : ReachesUb (f Outcome.ub)) (hiii_g : ReachesUb (g Outcome.ub))
    (hiv : ∀ (v : Option Value) (mem : Mem), ¬ TimeoutReachable (g (.ret v mem))) :
    simtt post' (ITree.bind p f) (ITree.bind q g) := by
  apply tauSimtt_coind post' (BindR post post' f g)
  · intro a b hab
    rcases hab with hab | ⟨p', q', hpq, rfl, rfl⟩
    · exact TauSimttF_monotone (fun x y hxy => Or.inl hxy) _ _
        ((simtt_iff_tau post' a b).mp hab)
    · exact tauSimttF_bind_lift hi hii hiii_f hiii_g hiv
        ((simtt_iff_tau post p' q').mp hpq)
  · exact Or.inr ⟨p, q, h, rfl, rfl⟩

/-! ### Exact transport

`IEq` is exact equality, so a related pair can be replaced by an `IEq`-related
pair on either side without changing the relation.  The target stays on the
left. -/

theorem simtt_ieq {post : Outcome → Outcome → Prop} {p p' q q' : OTree}
    (hp : IEq p p') (h : simtt post p' q') (hq : IEq q' q) : simtt post p q := by
  rw [ieq_iff_eq] at hp hq
  subst hp hq
  exact h

/-! ### Congruence under a tree-valued interpreter

The handler here is the generic tree-valued one (`EffectAlgebra.interp`), not the
host's computable one-step fold, which keeps its own statements.  It must re-emit
the *same* event with the *same* response type, optionally behind a finite silent
delay, so that the terminal classes and the return postcondition survive. -/

section InterpCongruence

open _root_.ITree.EffectAlgebra

/-- The handler premise: every event is re-emitted identically, behind a finite
silent delay. -/
def Reemits (h : Handler ObsEv ObsEv) : Prop :=
  ∀ {α : Type} (e : ObsEv α), ∃ n : Nat, h e = tauN n (trigger e)

/-- Binding a finite tower of silent steps in front of a tree is a finite tower
of silent steps in front of the binding. -/
theorem bind_tauN {α : Type} (n : Nat) (t : ITree ObsEv α) (f : α → OTree) :
    ITree.bind (tauN n t) f = tauN n (ITree.bind t f) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [tauN, bind_tau, ih, tauN]

/-- The interpretation of a visible event: the same event, behind the handler's
delay and with one completion `tau` in front of each resumed source tree. -/
theorem interp_vis_tauN {h : Handler ObsEv ObsEv} (hh : Reemits h) {α : Type}
    (e : ObsEv α) (k : α → OTree) :
    ∃ n : Nat, interp h (vis e k) = tauN n (vis e (fun a => tau (interp h (k a)))) := by
  obtain ⟨n, hn⟩ := hh e
  have hn' : h e = tauN n (trigger e) := by simpa using hn
  refine ⟨n, ?_⟩
  have hb : ITree.bind (tauN n (trigger e)) (fun a => tau (interp h (k a)))
      = tauN n (vis e (fun a => tau (interp h (k a)))) := by
    rw [bind_tauN, trigger, bind_vis]
    simp only [bind_ret]
  rw [interp_vis, hn']
  exact hb

/-- A source tower of `tau`s is preserved by the interpretation, tower and
all. -/
theorem interp_tauN {h : Handler ObsEv ObsEv} (n : Nat) (t : OTree) :
    interp h (tauN n t) = tauN n (interp h t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change interp h (tau (tauN n t)) = tauN (n + 1) (interp h t)
      rw [interp_tau, ih]
      rfl

/-- The interpreter maps the divergent tree to itself: it adds no step in front
of an endless tower of `tau`s and removes none. -/
theorem interp_infTau {h : Handler ObsEv ObsEv} :
    interp h (infTau : OTree) = infTau := by
  have hself : interp h (infTau : OTree) = tau (interp h infTau) := by
    conv_lhs => rw [infTau_eq]
    exact interp_tau h infTau
  refine PFunctor.M.bisim
    (fun x y => x = interp h (infTau : OTree) ∧ y = (infTau : OTree)) ?_ _ _
    ⟨rfl, rfl⟩
  rintro x y ⟨rfl, rfl⟩
  refine ⟨Shape.tau, fin1Const (interp h (infTau : OTree)), fin1Const infTau, ?_, ?_, ?_⟩
  · conv_lhs => rw [hself]
    exact dest_tau
  · conv_lhs => rw [infTau_eq]
    exact dest_tau
  · intro i
    match i with
    | .up (.ofNat' 0) => exact ⟨rfl, rfl⟩

/-- A finite delay lifts through the interpretation: the source delay's tower is
a target delay of the same height. -/
theorem tauHead_interp {h : Handler ObsEv ObsEv} {p r : OTree}
    (hp : TauHead p r) : TauHead (interp h p) (interp h r) := by
  obtain ⟨d, hfin, hfl⟩ := hp
  obtain ⟨n, hn⟩ := flatten_finite_tauN hfin
  refine ⟨tauN n (now (interp h r)), finite_tauN n (finite_now _), ?_⟩
  rw [flatten_tauN, flatten_now]
  calc tauN n (interp h r) = interp h (tauN n r) := (interp_tauN n r).symm
    _ = interp h p := by rw [← hfl, hn]

/-- A UB terminal still reaches one after interpretation. -/
theorem tauReachesUb_interp {h : Handler ObsEv ObsEv} (hh : Reemits h) {p : OTree}
    (hub : TauReachesUb p) : TauReachesUb (interp h p) := by
  obtain ⟨q, hhead, hterm⟩ := hub
  cases hterm with
  | retLeaf =>
      have hl := tauHead_interp (h := h) hhead
      rw [interp_ret] at hl
      exact ⟨_, hl, UbTerminal.retLeaf⟩
  | ubNode k =>
      obtain ⟨n, hn⟩ := interp_vis_tauN hh ObsEv.ub k
      refine ⟨vis ObsEv.ub (fun a => tau (interp h (k a))), ?_, UbTerminal.ubNode _⟩
      refine tauHead_trans (tauHead_interp (h := h) hhead) ?_
      rw [hn]
      exact tauHead_tauN n _

/-- A timeout still reaches one after interpretation. -/
theorem tauTimeoutReachable_interp {h : Handler ObsEv ObsEv} (hh : Reemits h)
    {p : OTree} (hto : TauTimeoutReachable p) : TauTimeoutReachable (interp h p) := by
  obtain ⟨q, hhead, k, hk⟩ := hto
  subst hk
  obtain ⟨n, hn⟩ := interp_vis_tauN hh ObsEv.timeout k
  refine ⟨vis ObsEv.timeout (fun a => tau (interp h (k a))), ?_, _, rfl⟩
  refine tauHead_trans (tauHead_interp (h := h) hhead) ?_
  rw [hn]
  exact tauHead_tauN n _

/-- Silent divergence lifts through the interpretation: an infinite delay is the
divergent tree, and the interpreter leaves that tree alone. -/
theorem tauDiverges_interp {h : Handler ObsEv ObsEv} {p : OTree}
    (hdiv : TauDiverges p) : TauDiverges (interp h p) := by
  obtain ⟨d, hinf, hfl⟩ := hdiv
  have hp : p = infTau := by rw [← hfl, flatten_infinite hinf]
  refine ⟨forever, infinite_forever, ?_⟩
  rw [flatten_forever, hp, interp_infTau]

end InterpCongruence

/-! ### Reflecting a timeout back through the interpreter -/

section InterpReflect

open _root_.ITree.EffectAlgebra

/-- A point of the interpreter's output reachable from `p`: the interpretation of
a tree silently reachable from `p`, or an intermediate point of a visible
event's delay. -/
def InterpPoint (h : Handler ObsEv ObsEv) (p r : OTree) : Prop :=
  (∃ X : OTree, SilentHead p X ∧ r = interp h X) ∨
    ∃ (β : Type) (e : ObsEv β) (k : β → OTree) (m : Nat),
      SilentHead p (vis e k) ∧ r = tauN m (vis e (fun a => tau (interp h (k a))))

/-- One silent step from the interpretation of a reachable tree stays inside the
interpreter's reachable points. -/
theorem interpStep_interpPoint {h : Handler ObsEv ObsEv} (hh : Reemits h) {p X c : OTree}
    (hX : SilentHead p X) (hstep : SilentStep (interp h X) c) :
    InterpPoint h p c := by
  refine dMatchOn (motive := fun x => SilentHead p x → SilentStep (interp h x) c →
    InterpPoint h p c) X ?_ ?_ ?_ hX hstep
  · intro o heq hX' hs'
    rw [heq, interp_ret] at hs'
    exact absurd hs' (ret_no_step (o := o) c)
  · intro t heq hX' hs'
    rw [heq, interp_tau] at hs'
    obtain ⟨t', hmid, hr⟩ := SilentStep_inv hs'
    refine Or.inl ⟨t, ?_, ?_⟩
    · rw [heq] at hX'
      exact SilentHead.trans hX' (SilentHead.step (SilentStep.step t) (SilentHead.refl t))
    · rw [hr]
      exact (tau_inj hmid).symm
  · intro β e k heq hX' hs'
    obtain ⟨n, hn⟩ := interp_vis_tauN hh e k
    have hn' : interp h (vis e k) = tauN n (vis e (fun a => tau (interp h (k a)))) := hn
    rw [heq, hn'] at hs'
    cases n with
    | zero =>
        rw [tauN] at hs'
        exact absurd hs' (vis_no_step e (fun a => tau (interp h (k a))) c)
    | succ n =>
        rw [tauN] at hs'
        obtain ⟨t', hmid, hr⟩ := SilentStep_inv hs'
        refine Or.inr ⟨β, e, k, n, ?_, ?_⟩
        · rw [heq] at hX'
          exact hX'
        · rw [hr]
          exact (tau_inj hmid).symm

/-- A silent step out of an intermediate delay point stays inside them. -/
theorem interpDelayStep_interpPoint {h : Handler ObsEv ObsEv} {p : OTree} {β : Type}
    {e : ObsEv β} {k : β → OTree} {m : Nat} {c : OTree}
    (hX : SilentHead p (vis e k))
    (hstep : SilentStep (tauN m (vis e (fun a => tau (interp h (k a))))) c) :
    InterpPoint h p c := by
  cases m with
  | zero =>
      rw [tauN] at hstep
      exact absurd hstep (vis_no_step e (fun a => tau (interp h (k a))) c)
  | succ m =>
      rw [tauN] at hstep
      obtain ⟨t', hmid, hr⟩ := SilentStep_inv hstep
      refine Or.inr ⟨β, e, k, m, hX, ?_⟩
      rw [hr]
      exact (tau_inj hmid).symm

/-- Every tree silently reachable from the interpretation of `p` is such a
point. -/
theorem interpPoint_of_silentHead {h : Handler ObsEv ObsEv} (hh : Reemits h) {p r : OTree}
    (hs : SilentHead (interp h p) r) : InterpPoint h p r := by
  induction hs with
  | refl => exact Or.inl ⟨p, SilentHead.refl p, rfl⟩
  | tail _ hstep ih =>
      rcases ih with ⟨X, hX, hmid⟩ | ⟨β, e, k, m, hX, hmid⟩
      · rw [hmid] at hstep
        exact interpStep_interpPoint hh hX hstep
      · rw [hmid] at hstep
        exact interpDelayStep_interpPoint hX hstep

/-- The interpretation of a tree is a budget timeout only if the tree is a budget
timeout: the handler re-emits the identical terminal. -/
theorem interp_vis_timeout_shape {h : Handler ObsEv ObsEv} (hh : Reemits h) {X : OTree}
    {K : Empty → OTree} (hX : interp h X = vis ObsEv.timeout K) :
    ∃ k' : Empty → OTree, X = vis ObsEv.timeout k' := by
  refine dMatchOn (motive := fun x => interp h x = vis ObsEv.timeout K →
    ∃ k' : Empty → OTree, x = vis ObsEv.timeout k') X ?_ ?_ ?_ hX
  · intro o heq hc
    rw [heq, interp_ret] at hc
    exact absurd hc (ret_ne_vis ObsEv.timeout K)
  · intro c heq hc
    rw [heq, interp_tau] at hc
    exact absurd hc (tau_ne_vis ObsEv.timeout K)
  · intro β' e' k' heq hc
    obtain ⟨n, hn⟩ := interp_vis_tauN hh e' k'
    have hn' : interp h (vis e' k') = tauN n (vis e' (fun a => tau (interp h (k' a)))) := hn
    rw [heq, hn'] at hc
    cases n with
    | zero =>
        rw [tauN] at hc
        cases e' with
        | load addr ty r => exact absurd (vis_inj_α hc).symm empty_ne_unit
        | store addr ty v => exact absurd (vis_inj_α hc).symm empty_ne_unit
        | call callee args => exact absurd (vis_inj_α hc).symm empty_ne_option_value
        | ub => exact absurd (vis_inj hc).1 ub_ne_timeout
        | timeout => exact ⟨k', by rw [heq]⟩
    | succ n =>
        rw [tauN] at hc
        exact absurd hc (tau_ne_vis ObsEv.timeout K)

/-- A timeout in the interpretation comes from a timeout in the source. -/
theorem timeoutReachable_interp_reflect {h : Handler ObsEv ObsEv} (hh : Reemits h)
    {p : OTree} (hto : TimeoutReachable (interp h p)) : TimeoutReachable p := by
  obtain ⟨r, hs, k, hr⟩ := hto
  subst hr
  rcases interpPoint_of_silentHead hh hs with ⟨X, hX, hIX⟩ | ⟨β, e, k', m, hX, hm⟩
  · have hun : interp h X = vis ObsEv.timeout k := hIX.symm
    obtain ⟨kk, hXk⟩ := interp_vis_timeout_shape hh hun
    exact ⟨X, hX, kk, hXk⟩
  · cases m with
    | zero =>
        rw [tauN] at hm
        cases e with
        | load addr ty r => exact (empty_ne_unit (vis_inj_α hm)).elim
        | store addr ty v => exact (empty_ne_unit (vis_inj_α hm)).elim
        | call callee args => exact (empty_ne_option_value (vis_inj_α hm)).elim
        | ub => exact (ub_ne_timeout (vis_inj hm).1.symm).elim
        | timeout => exact ⟨_, hX, k', rfl⟩
    | succ m =>
        rw [tauN] at hm
        exact absurd hm.symm (tau_ne_vis ObsEv.timeout k)

/-- The same reflection, stated for the delay-indexed timeout predicate. -/
theorem tauTimeoutReachable_interp_reflect {h : Handler ObsEv ObsEv} (hh : Reemits h)
    {p : OTree} (hto : TauTimeoutReachable (interp h p)) : TauTimeoutReachable p :=
  tauTimeoutReachable_iff.mpr
    (timeoutReachable_interp_reflect hh (tauTimeoutReachable_iff.mp hto))

end InterpReflect

/-! ### Congruence under the interpreter -/

section InterpCongruenceMain

open _root_.ITree.EffectAlgebra

/-- Stuttering both sides with one silent step keeps the relation: every clause
is reached one step later. -/
theorem simtt_tau_tau {post : Outcome → Outcome → Prop} {p q : OTree}
    (h : simtt post p q) : simtt post (tau p) (tau q) := by
  apply tauSimtt_coind post (fun a b =>
    simtt post a b ∨ ∃ p q : OTree, simtt post p q ∧ a = tau p ∧ b = tau q)
  · intro a b hab
    rcases hab with hab | ⟨p, q, hpq, rfl, rfl⟩
    · exact TauSimttF_monotone (fun x y hxy => Or.inl hxy) _ _
        ((simtt_iff_tau post a b).mp hab)
    · have hcl : TauSimttF post (simtt post) p q := (simtt_iff_tau post p q).mp hpq
      exact tauSimttF_of_tauHead_right (tauSimttF_of_tauHead_left
        (TauSimttF_monotone (fun x y hxy => Or.inl hxy) _ _ hcl)
        (tauHead_step (tauHead_refl p))) (tauHead_step (tauHead_refl q))
  · exact Or.inr ⟨p, q, h, rfl, rfl⟩

/-- Congruence under a re-emitting tree-valued interpreter: a same-signature
handler that re-emits the identical event with the identical responses behind a
finite silent delay preserves the directed relation. -/
theorem simtt_interp {h : Handler ObsEv ObsEv} (hh : Reemits h)
    {post : Outcome → Outcome → Prop} {p q : OTree} (hs : simtt post p q) :
    simtt post (interp h p) (interp h q) := by
  apply tauSimtt_coind post (fun a b =>
    ∃ p q : OTree, simtt post p q ∧ a = interp h p ∧ b = interp h q)
  · rintro a b ⟨p, q, hpq, rfl, rfl⟩
    have hcl : TauSimttF post (simtt post) p q := (simtt_iff_tau post p q).mp hpq
    cases hcl with
    | ret_ret h1 h2 hp =>
        have hL := tauHead_interp (h := h) h1
        rw [interp_ret] at hL
        have hR := tauHead_interp (h := h) h2
        rw [interp_ret] at hR
        exact TauSimttF.ret_ret hL hR hp
    | right_ub_ret h1 h2 =>
        have hL := tauHead_interp (h := h) h1
        rw [interp_ret] at hL
        exact TauSimttF.right_ub_ret hL (tauReachesUb_interp hh h2)
    | ub h1 h2 =>
        exact TauSimttF.ub (tauReachesUb_interp hh h1) (tauReachesUb_interp hh h2)
    | timeout k1 k2 h1 h2 =>
        obtain ⟨n1, hn1⟩ := interp_vis_tauN hh ObsEv.timeout k1
        obtain ⟨n2, hn2⟩ := interp_vis_tauN hh ObsEv.timeout k2
        refine TauSimttF.timeout (k1 := fun a => tau (interp h (k1 a)))
          (k2 := fun a => tau (interp h (k2 a))) ?_ ?_
        · have hl := tauHead_interp (h := h) h1
          rw [hn1] at hl
          exact tauHead_trans hl (tauHead_tauN n1 _)
        · have hl := tauHead_interp (h := h) h2
          rw [hn2] at hl
          exact tauHead_trans hl (tauHead_tauN n2 _)
    | left_diverges hdiv hnt =>
        exact TauSimttF.left_diverges (tauDiverges_interp hdiv)
          (fun hto => hnt (tauTimeoutReachable_interp_reflect hh hto))
    | right_diverges hdiv2 hdiv1 =>
        exact TauSimttF.right_diverges (tauDiverges_interp hdiv2)
          (tauDiverges_interp hdiv1)
    | vis_load addr ty r k1 k2 h1 h2 hrel =>
        obtain ⟨n1, hn1⟩ := interp_vis_tauN hh (ObsEv.load addr ty r) k1
        obtain ⟨n2, hn2⟩ := interp_vis_tauN hh (ObsEv.load addr ty r) k2
        refine TauSimttF.vis_load (k1 := fun () => tau (interp h (k1 ())))
          (k2 := fun () => tau (interp h (k2 ()))) addr ty r ?_ ?_ ?_
        · have hl := tauHead_interp (h := h) h1
          rw [hn1] at hl
          exact tauHead_trans hl (tauHead_tauN n1 _)
        · have hl := tauHead_interp (h := h) h2
          rw [hn2] at hl
          exact tauHead_trans hl (tauHead_tauN n2 _)
        · exact ⟨tau (k1 ()), tau (k2 ()), simtt_tau_tau hrel,
            by rw [interp_tau], by rw [interp_tau]⟩
    | vis_store addr ty v k1 k2 h1 h2 hrel =>
        obtain ⟨n1, hn1⟩ := interp_vis_tauN hh (ObsEv.store addr ty v) k1
        obtain ⟨n2, hn2⟩ := interp_vis_tauN hh (ObsEv.store addr ty v) k2
        refine TauSimttF.vis_store (k1 := fun () => tau (interp h (k1 ())))
          (k2 := fun () => tau (interp h (k2 ()))) addr ty v ?_ ?_ ?_
        · have hl := tauHead_interp (h := h) h1
          rw [hn1] at hl
          exact tauHead_trans hl (tauHead_tauN n1 _)
        · have hl := tauHead_interp (h := h) h2
          rw [hn2] at hl
          exact tauHead_trans hl (tauHead_tauN n2 _)
        · exact ⟨tau (k1 ()), tau (k2 ()), simtt_tau_tau hrel,
            by rw [interp_tau], by rw [interp_tau]⟩
    | vis_call callee args k1 k2 h1 h2 hrel =>
        obtain ⟨n1, hn1⟩ := interp_vis_tauN hh (ObsEv.call callee args) k1
        obtain ⟨n2, hn2⟩ := interp_vis_tauN hh (ObsEv.call callee args) k2
        refine TauSimttF.vis_call (k1 := fun r => tau (interp h (k1 r)))
          (k2 := fun r => tau (interp h (k2 r))) callee args ?_ ?_ ?_
        · have hl := tauHead_interp (h := h) h1
          rw [hn1] at hl
          exact tauHead_trans hl (tauHead_tauN n1 _)
        · have hl := tauHead_interp (h := h) h2
          rw [hn2] at hl
          exact tauHead_trans hl (tauHead_tauN n2 _)
        · intro r
          exact ⟨tau (k1 r), tau (k2 r), simtt_tau_tau (hrel r),
            by rw [interp_tau], by rw [interp_tau]⟩
  · exact ⟨p, q, hs, rfl, rfl⟩

end InterpCongruenceMain

end LeanLLVM.ITree
