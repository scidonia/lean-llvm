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

**The second shape is the bound exit.**  A scan or a copy loop does not exit on a
fixed point: it carries a counter and compares it with a bound — `k < nps`, `i + 1
= nblk`, `clearLow w 8 = 0` — so the measure is the distance to that bound and the
loop's trip count is the counter's progress.  `BoundLoop` is that induction, with
the bound, the per-iteration step and the invariant as parameters.  One iteration
there is the run between successive visits to the head rather than one block's
step, because the head is the loop's test block and the body between two visits is
several blocks; `cost` is the per-iteration step bound, and the loop's contribution
to a record's budget is `(N + 1) * cost`.
-/
import LeanLLVM.Semantics

namespace LeanLLVM.Refinement

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

/-! ### The bound exit

`CarriedLoop` above is the loop that leaves when its map is fixed.  A scan or a
copy loop leaves on a different test: it carries a counter and compares that
counter with a bound — `k < nps` for the decoder's position walk, `i + 1 = nblk`
for the block scan, `clearLow w 8 = 0` for the eight-at-a-time writer.  The trip
count is the distance to the bound, so the measure is `N - c`, and none of the
iteration's own words is a fixed point to identify.

`BoundLoop` is that induction as vocabulary.  The four things a body supplies are
the bound, the head's exit test, the per-iteration step, and the invariant:

* `N` is the bound and `cost` the per-iteration control-step bound, both terms of
  the caller's arguments;
* `Inv r s c` is the invariant at the head: the state is at `head` carrying the
  counter `c`, and `r` is the iteration budget the caller has accounted for;
* `atBound s c` is the head's exit test — the branch value its terminator reads,
  at the state and the carried counter.  It is a test rather than `c = N`
  because a body may leave **before** the bound: the decoder leaves when the
  position has passed the body's end, the writer when its residual lanes fit the
  final batch, and a refusal leaves at the position that refused;
* `Exit e` is the predicate on the states the loop may leave in, and it **names
  every exit the body takes**.  Its default is the one block `exitBlock` names; a
  loop that also refuses — the decoder leaves at `while.end35` on success and at
  `cleanup41` on a refusal — sets `Exit` to the disjunction of the targets and
  makes `atBound` the disjunction of their tests.  One instance then covers both
  exits and `step_exit` is proved once, at the disjunctive test, rather than a
  second instance whose boundary at budget zero has to be argued separately;
* `step_exit` and `step_loop` are one iteration in its two arms.

One iteration is the **run** between successive visits to the head, not a single
block's step: the bound exit's head is the loop's test block, and the body between
two visits is several blocks (a position scan's copy, an eight-at-a-time batch).
`step_exit` and `step_loop` therefore state `runFuel` prefixes at an exact count
bounded by `cost`; that is what makes the loop's whole fuel `(N + 1) * cost`
rather than a number only the run knows.

`budget` is the arithmetic that ties the two: the budget covers the distance to
the bound, and every iteration spends one unit of it.  A step's counter advance
may overshoot by more than one (a surrogate pair advances the position index by
two, a writer batch claims up to eight entries), which is why the measure is the
budget and not `N - c` itself. -/
structure BoundLoop (calls : Calls) (f : Function) where
  /-- The block the loop's iteration is entered at: the loop's test block. -/
  head : String
  /-- The block a one-exit loop leaves for.  `Exit` below defaults to the states at
  this block; an instance with several exit targets leaves this as the success
  target and overrides `Exit` with their disjunction. -/
  exitBlock : String
  /-- The bound the carried counter is compared against: a term of the caller's
  arguments. -/
  N : Nat
  /-- The per-iteration control-step bound: a term of the caller's arguments. -/
  cost : Nat
  /-- The invariant at the head: after `r` iterations' budget the state is at
  `head` carrying the counter `c`. -/
  Inv : Nat → State → Nat → Prop
  /-- The head's exit test: the branch value its terminator reads, at the state
  and the carried counter.  An instance that leaves in several ways makes this
  the disjunction of their tests, so one `step_exit` covers all of them. -/
  atBound : State → Nat → Bool
  /-- The states the loop may leave in.  The default is the one block `exitBlock`
  names; an instance with a success target and a refusal target sets it to their
  disjunction.  Making the exit a predicate rather than a block name is what lets
  `atBound`'s disjunctive test and `Exit` together name every way out. -/
  Exit : State → Prop := fun e => e.pc = exitBlock
  /-- What the state the loop leaves satisfies. -/
  ExitWord : State → Prop
  /-- The exit arm: the head's test holds, and the iteration reaches a state that
  `Exit` admits within `cost` control steps. -/
  step_exit : ∀ (r : Nat) (s : State) (c : Nat), Inv r s c → atBound s c = true →
    ∃ (e : State) (j : Nat), j ≤ cost ∧ Exit e ∧ ExitWord e ∧
      ∀ k, runFuel calls (j + k) f s = runFuel calls k f e
  /-- The back edge: the test fails, the iteration re-enters `head` within `cost`
  control steps carrying a strictly larger counter, and spends one unit of the
  budget. -/
  step_loop : ∀ (r : Nat) (s : State) (c : Nat), Inv (r + 1) s c → atBound s c = false →
    ∃ (e : State) (c' : Nat) (j : Nat), j ≤ cost ∧ e.pc = head ∧ c < c' ∧
      Inv r e c' ∧ ∀ k, runFuel calls (j + k) f s = runFuel calls k f e
  /-- At the end of the budget the head's test holds, so the loop cannot stay in
  it: this is where the bound is consumed. -/
  exit_at_zero : ∀ (s : State) (c : Nat), Inv 0 s c → atBound s c = true
  /-- The invariant's budget accounts for the distance to the bound. -/
  budget : ∀ (r : Nat) (s : State) (c : Nat), Inv r s c → c ≤ N ∧ N ≤ c + r

/-- **The induction.**  From an invariant state with `r` iterations of budget, the
run reaches an exit state — one `Exit` admits — within `(r + 1) * cost` control
steps.  The recursion consumes the two arms only; the bound appears as the budget,
and the counter's strict advance is what lets the budget fall by one per iteration
however far the counter jumps.  The exit stays a predicate rather than a block
name, so a loop with a success target and a refusal target is one induction. -/
theorem BoundLoop.run_from (L : BoundLoop calls f) :
    ∀ (r : Nat) (s : State) (c : Nat), L.Inv r s c →
      ∃ (e : State) (j : Nat), j ≤ (r + 1) * L.cost ∧ L.Exit e ∧
        L.ExitWord e ∧
        ∀ k, runFuel calls (j + k) f s = runFuel calls k f e
  | 0, s, c, h => by
      obtain ⟨e, j, hj, hpc, hexit, hrun⟩ :=
        L.step_exit 0 s c h (L.exit_at_zero s c h)
      exact ⟨e, j, by simpa using hj, hpc, hexit, hrun⟩
  | r + 1, s, c, h => by
      cases hb : L.atBound s c
      · obtain ⟨e, c', j, hj, hpc, hlt, hinv, hrun⟩ := L.step_loop r s c h hb
        obtain ⟨e', j', hj', hpc', hexit', hrun'⟩ := L.run_from r e c' hinv
        refine ⟨e', j + j', ?_, hpc', hexit', fun k => ?_⟩
        · rw [Nat.succ_mul]
          omega
        · rw [show j + j' + k = j + (j' + k) from by omega, hrun (j' + k)]
          exact hrun' k
      · obtain ⟨e, j, hj, hpc, hexit, hrun⟩ := L.step_exit (r + 1) s c h hb
        have hj' : j ≤ (r + 1 + 1) * L.cost := by
          rw [Nat.succ_mul]
          omega
        exact ⟨e, j, hj', hpc, hexit, hrun⟩

/-- **The loop from its head.**  At the whole bound as its budget — `Inv N s c`,
which every instance inhabits, since the budget covers any distance up to `N` —
the run reaches the exit block within `(N + 1) * cost` control steps.

That is the loop's whole cost and it is a term of the caller's arguments: one
iteration's cost per unit of the bound, plus the exit iteration.  Everything the
caller adds — the entry blocks and the exit block's continuation — is its own, so
a record's budget over this loop is a function of `(args, mem)` and not of the trip
count the run happened to take. -/
theorem BoundLoop.run (L : BoundLoop calls f) (s : State) (c : Nat)
    (h : L.Inv L.N s c) (k : Nat) :
    ∃ (e : State) (j : Nat), j ≤ (L.N + 1) * L.cost ∧ L.Exit e ∧
      L.ExitWord e ∧
      runFuel calls (j + k) f s = runFuel calls k f e := by
  obtain ⟨e, j, hj, hpc, hexit, hrun⟩ := L.run_from L.N s c h
  exact ⟨e, j, hj, hpc, hexit, hrun k⟩

/-- **A budget at the bound, not at the trip count.**  The induction hands back the
run's exact exit count `j`, and `j ≤ (N + 1) * cost`.  A caller that has a
completed outcome from the exit state therefore has one from the head at
`(N + 1) * cost + k`: the count is replaced by the bound, which is what lets a
record state its completion at `Γ.budget args mem` — a term of the arguments —
instead of at a number only the run knows.

`hcont` is the exit state's trace: the caller's completion from any state `Exit`
admits, at its own fuel.  Only a *completed* continuation can be lifted, because
the exit is a jump and `runFuel` past it executes the next block.  An instance
with several exits states this continuation once and case-splits at `Exit`, and
that is the whole of the case split — the induction above does not see it. -/
theorem BoundLoop.run_at (L : BoundLoop calls f) (s : State) (c : Nat)
    (h : L.Inv L.N s c) (k : Nat) {o : Outcome}
    (hcont : ∀ (e : State), L.Exit e → L.ExitWord e →
        runFuel calls k f e = some o) :
    runFuel calls ((L.N + 1) * L.cost + k) f s = some o := by
  obtain ⟨e, j, hj, hpc, hexit, hrun⟩ := L.run s c h k
  have hone : runFuel calls (j + k) f s = some o := by
    rw [hrun]
    exact hcont e hpc hexit
  exact runFuel_mono_le (by omega) hone

/-- **One step's prefix.**  A `jump` is the iteration fact `BoundLoop` consumes at
`cost = 1`: from the state the step leaves, the run continues identically.  Named
here so an instance whose head block is a self-loop states its arms without
unfolding `runFuel`. -/
theorem runFuel_jump_prefix {calls : Calls} {f : Function} {s s' : State}
    (h : step calls f s = .jump s') (k : Nat) :
    runFuel calls (1 + k) f s = runFuel calls k f s' := by
  rw [show 1 + k = k + 1 from by omega]
  simp only [runFuel, h]

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.iter' does not depend on any axioms -/
#guard_msgs in
#print axioms iter

/-- info: 'LeanLLVM.Refinement.CarriedLoop.run_from' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CarriedLoop.run_from

/-- info: 'LeanLLVM.Refinement.CarriedLoop.run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CarriedLoop.run

/-- info: 'LeanLLVM.Refinement.CarriedLoop.run_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CarriedLoop.run_at

/-- info: 'LeanLLVM.Refinement.BoundLoop.run_from' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BoundLoop.run_from

/-- info: 'LeanLLVM.Refinement.BoundLoop.run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BoundLoop.run

/-- info: 'LeanLLVM.Refinement.BoundLoop.run_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BoundLoop.run_at

/-- info: 'LeanLLVM.Refinement.runFuel_jump_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms runFuel_jump_prefix

end LeanLLVM.Refinement
