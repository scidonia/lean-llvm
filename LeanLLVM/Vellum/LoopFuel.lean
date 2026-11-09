/-
The fuel layer for a loop whose exit test reads its own carried word.

`runFuel` inducts on the control steps left, so a loop whose trip count is
decided by the data it carries needs a measure that is a **function of the
caller's arguments**, not of the run: `Satisfies` states a record's completion at
`Γ.budget args mem`, and a budget that needed the run to know its own trip count
would make the record circular.

`CarriedLoop` is that layer.  A loop is a head block, an exit block, a word the
head carries, and a map the head computes from it; the head leaves the loop
exactly when `map w = w`, the `icmp eq %next, %carried` exit an optimised scan or
escape body emits.  `Inv i s w` is the invariant at the head after `i`
iterations, `N` is the iteration bound the caller derives from its arguments (for
a lane loop, the lane width's thirty-two), and the induction is on `N - i`:
`run_from` walks the loop to the exit block, and the only things it consumes are
the invariant and the head's one-step facts.

**Nothing here identifies the exit word with a specification.**  That
identification is a statement about the map, not about the run, and a loop's
proof applies it once — to the fixed word the induction hands back.  It must not
appear inside the step: the exit test compares the carried word with its *next*
iterate, so a step that had to know the next iterate could only learn it from the
very fixed-point lemma the loop's proof is about, and the induction would prove
nothing.  The step's successor invariant is the definition of the iterate and
nothing more.

The loop's exit is stated as a **prefix of the run**, not as a `ret`: the block a
data-dependent loop leaves for is usually the next stage of the body, so
`run_from` concludes that the run from the head equals the run from the exit
state, and the caller composes that with the exit block's own trace at its own
fuel.  That is what makes the loop's contribution to a record's budget the bound
`N + 1` rather than the trip count.
-/
import LeanLLVM.Semantics

namespace LeanLLVM.Vellum

open LeanLLVM

/-- The `n`-th iterate of a word map. -/
def iter (g : BitVec 64 → BitVec 64) : Nat → BitVec 64 → BitVec 64
  | 0, x => x
  | n + 1, x => g (iter g n x)

@[simp] theorem iter_zero (g : BitVec 64 → BitVec 64) (x : BitVec 64) : iter g 0 x = x := rfl

@[simp] theorem iter_succ (g : BitVec 64 → BitVec 64) (n : Nat) (x : BitVec 64) :
    iter g (n + 1) x = g (iter g n x) := rfl

/-- A loop whose exit test reads its own carried word.

The fields are the loop and the two facts a body supplies per head block:

* `head`/`exitBlock` name the blocks the head's terminator chooses between;
* `map` is the word the head computes from the carried word, and `seed` the word
  the loop is entered with at iteration zero;
* `N` is the iteration bound — a term of the caller's arguments and memory, never
  the number of iterations a particular run took;
* `Inv i s w` is the invariant at the head after `i` iterations: the state is at
  the head and carries `w`;
* `ExitWord e w` is what the head's exit arm leaves behind: the word the exit
  block's `phi` will read, and — in an instance that needs it — the loop's frame,
  the cells the exit block and whatever follows it read and the head does not
  write;
* `step_exit` and `step_loop` are the head's one control step in its two arms,
  and are the only place the block's instructions are consumed;
* `word_iterate`, `bound` and `fixed` tie the invariant to the map: the carried
  word is the `i`-th iterate of `seed`, the invariant is inhabited only up to
  `N`, and at `N` the map is already fixed, so the loop cannot stay in it. -/
structure CarriedLoop (calls : Calls) (f : Function) where
  /-- The block the loop re-enters. -/
  head : String
  /-- The block the loop leaves for. -/
  exitBlock : String
  /-- The word map the head block computes. -/
  map : BitVec 64 → BitVec 64
  /-- The word the loop is entered with. -/
  seed : BitVec 64
  /-- The iteration bound: a term of the caller's arguments and memory. -/
  N : Nat
  /-- The invariant at the head: after `i` iterations the state carries `w`. -/
  Inv : Nat → State → BitVec 64 → Prop
  /-- What the state the loop leaves carries. -/
  ExitWord : State → BitVec 64 → Prop
  /-- The exit arm: the head's test holds and the terminator takes `exitBlock`. -/
  step_exit : ∀ (i : Nat) (s : State) (w : BitVec 64), Inv i s w → map w = w →
    ∃ e : State, step calls f s = .jump e ∧ e.pc = exitBlock ∧ ExitWord e w
  /-- The back edge: the test fails, the terminator re-enters `head`, and the
  next iterate is carried. -/
  step_loop : ∀ (i : Nat) (s : State) (w : BitVec 64), Inv i s w → map w ≠ w →
    ∃ e : State, step calls f s = .jump e ∧ e.pc = head ∧ Inv (i + 1) e (map w)
  /-- The carried word is the `i`-th iterate of the map from the seed. -/
  word_iterate : ∀ (i : Nat) (s : State) (w : BitVec 64), Inv i s w → w = iter map i seed
  /-- The invariant is inhabited only inside the bound. -/
  bound : ∀ (i : Nat) (s : State) (w : BitVec 64), Inv i s w → i ≤ N
  /-- At the bound the map is already fixed, so the loop cannot stay in it. -/
  fixed : ∀ (s : State) (w : BitVec 64), Inv N s w → map w = w

/-- **The induction.**  From an invariant state with `N - i = n` iterations left,
the run reaches the exit block within `n + 1` control steps and leaves a word
that is a fixed iterate of the seed.  The recursion consumes `Inv` and the head's
two arms only; the exit word stays a fixed iterate of the map, identified by the
caller's own map lemma rather than here.

The remaining-step count is the measure: the back edge spends one step and
decrements it, so the fuel is the bound on the loop's *cost*, not on its trip
count. -/
theorem CarriedLoop.run_from (L : CarriedLoop calls f) :
    ∀ (n i : Nat) (s : State) (w : BitVec 64), L.Inv i s w → L.N - i = n →
      ∃ (e : State) (j d : Nat),
        j ≤ n + 1 ∧ d ≤ L.N ∧ e.pc = L.exitBlock ∧
        L.ExitWord e (iter L.map d L.seed) ∧
        L.map (iter L.map d L.seed) = iter L.map d L.seed ∧
        ∀ k, runFuel calls (j + k) f s = runFuel calls k f e
  | 0, i, s, w, h, hn => by
      have hiN : i = L.N := by have := L.bound i s w h; omega
      have hN : L.Inv L.N s w := by rw [← hiN]; exact h
      obtain ⟨e, hstep, hpc, hexit⟩ := L.step_exit i s w h (L.fixed s w hN)
      have hw : w = iter L.map i L.seed := L.word_iterate i s w h
      refine ⟨e, 1, i, by omega, L.bound i s w h, hpc, ?_, ?_, ?_⟩
      · rw [← hw]; exact hexit
      · rw [← hw]; exact L.fixed s w hN
      · intro k
        rw [show 1 + k = k + 1 from by omega]
        simp only [runFuel, hstep]
  | n + 1, i, s, w, h, hn => by
      have hi : i ≤ L.N := L.bound i s w h
      by_cases hfix : L.map w = w
      · obtain ⟨e, hstep, hpc, hexit⟩ := L.step_exit i s w h hfix
        have hw : w = iter L.map i L.seed := L.word_iterate i s w h
        refine ⟨e, 1, i, by omega, hi, hpc, ?_, ?_, ?_⟩
        · rw [← hw]; exact hexit
        · rw [← hw]; exact hfix
        · intro k
          rw [show 1 + k = k + 1 from by omega]
          simp only [runFuel, hstep]
      · obtain ⟨e, hstep, hpc, hinv⟩ := L.step_loop i s w h hfix
        obtain ⟨e', j, d, hj, hd, hpc', hexit, hfix', hrun⟩ :=
          L.run_from n (i + 1) e (L.map w) hinv (by omega)
        refine ⟨e', j + 1, d, by omega, hd, hpc', hexit, hfix', fun k => ?_⟩
        rw [show j + 1 + k = (j + k) + 1 from by omega]
        simp only [runFuel, hstep]
        exact hrun k

/-- **The loop from its head.**  `run_from` at the entry iteration: the run
reaches the exit block within `N + 1` control steps, leaving a word that is a
fixed iterate of the seed.

`N + 1` is the loop's whole cost and it is a term of the caller's arguments: one
step per iteration up to the bound plus the exit test's own step.  Everything the
caller adds on top — the entry blocks and the exit block's continuation — is its
own, so a record's budget over this loop is a function of `(args, mem)` and not of
the trip count the run happened to take. -/
theorem CarriedLoop.run (L : CarriedLoop calls f) (s : State) (w : BitVec 64)
    (h : L.Inv 0 s w) (k : Nat) :
    ∃ (e : State) (j d : Nat),
      j ≤ L.N + 1 ∧ d ≤ L.N ∧ e.pc = L.exitBlock ∧
      L.ExitWord e (iter L.map d L.seed) ∧
      L.map (iter L.map d L.seed) = iter L.map d L.seed ∧
      runFuel calls (j + k) f s = runFuel calls k f e := by
  obtain ⟨e, j, d, hj, hd, hpc, hexit, hfix, hrun⟩ :=
    L.run_from L.N 0 s w h (by omega)
  exact ⟨e, j, d, hj, hd, hpc, hexit, hfix, hrun k⟩

/-- **A budget at the bound, not at the trip count.**  The induction hands back the
run's *exact* exit count `j`, and `j ≤ N + 1`.  A caller that has a completed
outcome from the exit state therefore has one from the head at `N + 1 + k`: the
count is replaced by the bound, which is what lets a record state its completion at
`Γ.budget args mem` — a term of the arguments — instead of at a number only the run
knows.  The lift is `runFuel_mono_le`; what is new here is that the loop's
contribution to the fuel is the bound.

`hcont` is the exit block's trace: the caller's completion from the state the loop
leaves, at its own fuel.  The fuel cannot simply be raised on the prefix — the exit
is a jump, so `runFuel` past it executes the next block — so only a *completed*
continuation can be lifted. -/
theorem CarriedLoop.run_at (L : CarriedLoop calls f) (s : State) (w : BitVec 64)
    (h : L.Inv 0 s w) (k : Nat) {o : Outcome}
    (hcont : ∀ (e : State) (_j d : Nat), e.pc = L.exitBlock →
        L.ExitWord e (iter L.map d L.seed) →
        L.map (iter L.map d L.seed) = iter L.map d L.seed →
        runFuel calls k f e = some o) :
    runFuel calls (L.N + 1 + k) f s = some o := by
  obtain ⟨e, j, d, hj, _hd, hpc, hexit, hfix, hrun⟩ := L.run s w h k
  have hone : runFuel calls (j + k) f s = some o := by
    rw [hrun]
    exact hcont e j d hpc hexit hfix
  exact runFuel_mono_le (by omega) hone

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.iter' does not depend on any axioms -/
#guard_msgs in
#print axioms iter

/-- info: 'LeanLLVM.Vellum.CarriedLoop.run_from' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CarriedLoop.run_from

/-- info: 'LeanLLVM.Vellum.CarriedLoop.run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CarriedLoop.run

/-- info: 'LeanLLVM.Vellum.CarriedLoop.run_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CarriedLoop.run_at

end LeanLLVM.Vellum
