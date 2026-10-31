/-
The general loop rule for the directed tree relation.

`simtt post` relates bare handled trees: a target on the left and a source on
the right.  A loop proof cannot walk both machines step by step, because the
two sides have different state spaces, different budgets and different amounts
of silent work per iteration.  `simtt_loop` is the rule that replaces the walk:

* an invariant `Inv s t` over the two families' states,
* a one-step obligation `TauSimttF` at the framed, postcondition-indexed return
  relation `fun oT oS => post oT oS ∧ oT.AgreesOutside frame oS`, whose
  continuation position is the same invariant lifted through a finite silent
  delay on each side,

entail `simtt` at that framed relation for every invariant pair.  The rule does
not assert that any two loops satisfy its premise, and it does not demand a
positive guard of the trees: `mfix`/`runT` callers establish their own
productivity or their own finite derivation, which is what the measure lemma
below does for the fixed-budget fixture.

`simtt_post_mono` is the weakening corollary: a stronger postcondition
transports to a weaker one.  It is what recovers the fixture's original
`simtt (Outcome.AgreesOutside frame)` statement from the rule's `True ∧ _`
return relation, without pretending the two propositions are the same
expression.

`handle_tau_guard` and `rawSilentHead_of_measure` are the two obligations a
host client discharges its premise with: the handler's own positive jump delay,
and the strictly decreasing-measure induction that turns per-block raw private
steps into a finite silent closure ending at a stated value and memory.
-/
import LeanLLVM.ITree.Algebra
import LeanLLVM.Frames
import ITree.MonadIter

namespace LeanLLVM.ITree

open LeanLLVM
open _root_.ITree
open _root_.ITree.TauClosure
open Lean.Order

/-! ### Postcondition weakening

The nine clauses at a stronger `post` imply the same clauses at a weaker one:
only the defined-return clause consults `post`, and it is transported by the
weakening hypothesis.  Every terminal and event clause is left as it is, so an
absent return cannot satisfy a fabricated post. -/

/-- The delay-indexed one-step functional is monotone in the postcondition. -/
theorem tauSimttF_post_mono {post post' : Outcome → Outcome → Prop}
    {sim : OTree → OTree → Prop} (h : ∀ oT oS, post oT oS → post' oT oS)
    {p q : OTree} (hF : TauSimttF post sim p q) : TauSimttF post' sim p q := by
  cases hF with
  | ret_ret h1 h2 hp => exact TauSimttF.ret_ret h1 h2 (h _ _ hp)
  | right_ub_ret h1 h2 => exact TauSimttF.right_ub_ret h1 h2
  | ub h1 h2 => exact TauSimttF.ub h1 h2
  | timeout k1 k2 h1 h2 => exact TauSimttF.timeout k1 k2 h1 h2
  | left_diverges hdiv hnt => exact TauSimttF.left_diverges hdiv hnt
  | right_diverges hdiv2 hdiv1 => exact TauSimttF.right_diverges hdiv2 hdiv1
  | vis_load addr ty r k1 k2 h1 h2 hs =>
      exact TauSimttF.vis_load addr ty r k1 k2 h1 h2 hs
  | vis_store addr ty v k1 k2 h1 h2 hs =>
      exact TauSimttF.vis_store addr ty v k1 k2 h1 h2 hs
  | vis_call callee args k1 k2 h1 h2 hs =>
      exact TauSimttF.vis_call callee args k1 k2 h1 h2 hs

/-- Postcondition weakening for the relation. -/
theorem simtt_post_mono {post post' : Outcome → Outcome → Prop}
    (h : ∀ oT oS, post oT oS → post' oT oS)
    {p q : OTree} (hsim : simtt post p q) : simtt post' p q :=
  tauSimtt_coind post' (simtt post)
    (fun p q hp => tauSimttF_post_mono h ((simtt_iff_tau post p q).mp hp)) p q hsim

/-! ### The rule

The premise's continuation relation and the coinduction predicate are the *same*
proposition, including both `TauHead` operands: `hstep` is stated at the relation
`simtt_loop` closes over, so a client cannot satisfy one and bypass the other.
The two sides of that relation are reached by a finite silent delay from the
families' trees, which is why the finite-prefix transport lemmas of `Algebra`
discharge the coinduction. -/

/-- The general framed, postcondition-indexed loop rule.  Left is the target and
right the source; the two state spaces, and the amount of silent work either
side does, are unrelated. -/
theorem simtt_loop {σ τ : Type} (frame : Nat → Prop)
    (post : Outcome → Outcome → Prop)
    (left : σ → OTree) (right : τ → OTree) (Inv : σ → τ → Prop)
    (hstep : ∀ s t, Inv s t →
      TauSimttF (fun oT oS => post oT oS ∧ oT.AgreesOutside frame oS)
        (fun p q => ∃ s' t', Inv s' t' ∧ TauHead p (left s') ∧
          TauHead q (right t')) (left s) (right t)) :
    ∀ s t, Inv s t →
      simtt (fun oT oS => post oT oS ∧ oT.AgreesOutside frame oS)
        (left s) (right t) := by
  intro s t hst
  refine tauSimtt_coind (fun oT oS => post oT oS ∧ oT.AgreesOutside frame oS)
    (fun p q => ∃ s' t', Inv s' t' ∧ TauHead p (left s') ∧ TauHead q (right t'))
    ?_ (left s) (right t) ⟨s, t, hst, tauHead_refl _, tauHead_refl _⟩
  rintro p q ⟨s', t', hst', hp, hq⟩
  exact tauSimttF_of_tauHead_right
    (tauSimttF_of_tauHead_left (hstep s' t' hst') hp) hq

/-! ### The handler's positive jump delay

A source `tau` is one `tau` in the handled tree (`handle_tau`), so the handler's
completion of a jump is itself a positive finite delay of the continuation.  The
statement is the generic delay constructors applied at that equation. -/

/-- A handled silent step is one positive finite delay of the handled
continuation, whose flattening is the handled `tau`. -/
theorem handle_tau_guard (frame : Nat → Prop) (m : Mem) (t : Tree Ev Outcome) :
    FiniteLater (TauClosure.later (TauClosure.now (handle frame m t)))
      (handle frame m t) ∧
    TauClosure.flatten (TauClosure.later (TauClosure.now (handle frame m t))) =
      handle frame m (tau t) :=
  ⟨finiteLater_later_now _, by rw [flatten_later, flatten_now, handle_tau]⟩

/-! ### The decreasing-measure derivation

The fixture's loop is bounded by a counter, so its raw private steps form a
finite closure after all.  This lemma is the general shape of that argument: an
invariant with a strictly decreasing natural measure over a family of raw
sources, a step obligation at positive measure, and an exit obligation at zero
measure, give a finite raw closure ending at a terminal satisfying the caller's
property.  The property `P` names the returned tree *and* its recorded memory,
so a derivation cannot claim a token `ret` whose memory differs from the leaf's.
-/

/-- Finitely many raw private steps reach a terminal of `P`, by strong induction
on a strictly decreasing measure. -/
theorem rawSilentHead_of_measure {frame : Nat → Prop} {σ : Type}
    (toRaw : σ → RawTS) (Inv : σ → Prop) (μ : σ → Nat)
    (P : RawTS → Prop)
    (hstep : ∀ s, Inv s → 0 < μ s →
      ∃ s', Inv s' ∧ μ s' < μ s ∧
        RawSilentHead frame (toRaw s) (toRaw s'))
    (hexit : ∀ s, Inv s → μ s = 0 →
      ∃ terminal, P terminal ∧ RawSilentHead frame (toRaw s) terminal)
    {s₀ : σ} (h₀ : Inv s₀) :
    ∃ terminal, P terminal ∧ RawSilentHead frame (toRaw s₀) terminal := by
  suffices h : ∀ n s, Inv s → μ s ≤ n →
      ∃ terminal, P terminal ∧ RawSilentHead frame (toRaw s) terminal by
    exact h (μ s₀) s₀ h₀ (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
      intro s hs hle
      exact hexit s hs (Nat.le_zero.mp hle)
  | succ n ih =>
      intro s hs hle
      rcases Nat.eq_zero_or_pos (μ s) with hzero | hpos
      · exact hexit s hs hzero
      · obtain ⟨s', hs', hlt, hhead⟩ := hstep s hs hpos
        obtain ⟨terminal, hP, hrest⟩ := ih s' hs' (by omega)
        exact ⟨terminal, hP, hhead.trans hrest⟩

end LeanLLVM.ITree
