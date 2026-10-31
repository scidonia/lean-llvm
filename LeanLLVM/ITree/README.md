# `LeanLLVM.ITree`: memory as an effect, and a directed simulation of handled trees

This directory is the LLVM instantiation of the generic interaction-tree
library (`ITree/`).  It interprets the fuel semantics as a tree, folds the
memory protocol into a handler so that a tree no longer needs a memory index,
and relates the resulting **bare handled trees** with a directed,
postcondition-indexed relation.

## Modules

| Module | Contents |
| --- | --- |
| `Interpret.lean` | `Ev` (`load`, `store`, `call`, `ub`, `timeout`), `runT` (the fuel-indexed tree of a function), `Exec` and `exec_runT` (the canonical resolution of an unhandled tree) |
| `MemoryEffect.lean` | `ObsEv`, `InFrame`, `memoryHandler`, `handle`, `runHandled`, the handler's equations, and the raw private step used only to transport the loop derivation |
| `Simtt.lean` | `SilentStep`/`SilentHead`/`SilentDiverges`, the one-step functional `SimttF` and its greatest fixed point `simtt post` on bare `ObsEv` trees, the positive rules, the terminal refusals and the event-payload refusals; the **unchanged** accepted definition |
| `TauClosure.lean` | the delay-indexed restatement: `TauHead`/`TauDiverges`/`TauReachesUb`/`TauTimeoutReachable`, each proved equivalent in both directions to the existing predicate on the same trees, the nine-clause functional `TauSimttF` with `TauSimttF post sim p q ↔ SimttF post sim p q`, and `simtt_eq_tau_plfp` |
| `Algebra.lean` | exact-`IEq` transport (`simtt_ieq`), conditioned congruence under `bind` (`simtt_bind`) and under a re-emitting tree-valued interpreter (`simtt_interp`), proved by `TauSimttF` coinduction with `TauHead`/`TauDiverges` transport through `bind` and the finite-witness timeout inversion |
| `LoopRule.lean` | the general loop rule `simtt_loop` (framed, postcondition-indexed, with the invariant also in the continuation position), postcondition weakening `simtt_post_mono`, the handler's positive jump delay `handle_tau_guard`, and the decreasing-measure derivation `rawSilentHead_of_measure` |
| `Bridge.lean` | `HandledExec`, the correspondence `handled_runFuel`, the elimination `simtt_exec_some`, and the budget-, behaviour- and refinement-level corollaries |
| `LoopInstance.lean` | the repository's concrete instances of the rule: a visibly recurring call tree, and the comma-mask loop's seed family against its unrolled candidate — with the fixed-budget instance, the address-0 counterexample and the behaviour corollary |

## Memory as an effect

`Ev` is the source protocol.  `memoryHandler frame` decides each event once, and
`handle frame m t` is the generic fold of that decision over `t`:

* a **defined in-frame load** and **any in-frame store** are answered privately;
  the fold performs them as `tau` and advances the handler's own memory
  (`loadValue` for the read, `storeMem` for the write);
* every other access stays **visible**: a load at another address, or an
  undefined one, emits `ObsEv.load addr ty (loadValue m ty addr)` — the response
  the handler itself computed — and a store outside the frame emits
  `ObsEv.store addr ty v`.  Nothing observable is discarded;
* a **call** is re-emitted with its own callee and arguments and its response
  type intact; the memory is untouched and no environment is consulted;
* `ub` and `timeout` remain distinct stuck nodes, `ObsEv.ub` and
  `ObsEv.timeout`, each with the empty response type.

A leaf's recorded memory is replaced by the handler's final state
(`finishOutcome`).  For an arbitrary synthetic source tree that is a deliberate
change; for the trees `runT` produces it is the same memory, which is the
correspondence in `Bridge.lean`: at every reachable continuation the handler's
memory equals the `State.mem` the semantics uses, because a store advances both
by `storeMem` (`storeValue_mem`) and every other instruction and terminator
leaves the memory alone.  So `handled_runFuel` states exactly

```lean
HandledExec calls (runHandled calls frame n f s) (runFuel calls n f s)
```

**The host handler is proof-facing and noncomputable.**  `frame` is an arbitrary
`Nat → Prop` predicate, and the existing API gives it no decider, so the
handler's branch is decided with `Classical.propDecidable`.  This is not a new
executable route: `runFuel`, `runT`, `Beh`, the driver and the installer are
untouched.  A computable handler would need a decidable frame representation or
an explicit `DecidablePred` contract for `frame`; that is a separate change, and
it must not silently narrow today's frame API.

The axiom budget reflects that: the simulation, the correspondence, the fixed
loop proofs and the new delay/congruence theorems stay within
`[propext, Classical.choice, Quot.sound]`.  `Classical.choice` reaches that
footprint from **two separate sources**, and neither one accounts for the other:

* the **generic tree carrier** inherits it from mathlib's `PFunctor.M`: its
  `dest`/`children` already depend on `[propext, Classical.choice, Quot.sound]`
  at the pinned revision, so every statement that mentions the destructor — even
  the generic library's `rfl` lemma `ITree.dest_ret` — carries that axiom before
  any host proof adds a line;
* the **host handler** adds its own decision: `Classical.propDecidable` on the
  arbitrary `Nat → Prop` frame, the same axiom the framed refinement layer
  already pays.

So the ceiling here is not evidence that a host proof decided a proposition; it
is the carrier's floor plus the frame decision.  The pins in
`LeanLLVMTest/Vellum.lean` and `tests/itree-import.lean` record both.

## The relation

`simtt post` relates two bare `ObsEv` trees.  Its silent step is exactly `tau` —
a private access is silent because the handler inserted the `tau`, never because
the relation inspects a memory — and it is the greatest fixed point of a
one-step functional, built on the generic `plfp`.

* a `ret` leaf on both sides is related when `post` holds of the two outcomes;
  `post` never sees `ub`;
* `timeout` matches only `timeout`;
* a UB terminal is a `ret` leaf carrying `Outcome.ub` or a `vis ObsEv.ub` node;
  a left UB terminal requires a right one, and a right one admits any completed
  left return without consulting `post`;
* left silent divergence is the bottom against a right side that cannot silently
  reach `timeout`; right silent divergence requires left silent divergence;
* a visible event matches only the same event: the same load annotation, the
  same store address/type/value, the same callee and arguments — and then its
  continuations are related (for a call, for every response).

The frame is therefore not a parameter of the relation at all.  It is chosen by
the caller's postcondition (`simtt (Outcome.AgreesOutside frame)`) and it is what
selected each producer's private effects.

`Bridge.lean` eliminates the relation against a completed target run
(`simtt_exec_some`), specialises that to `runFuel` and `Beh` with a separate
budget on each side, and derives `refinesWithin_of_simtt`/`refines_of_simtt` as
corollaries at the framed and exact posts.  Those theorems take the relation
between the two `runHandled` trees as a hypothesis: they define neither
`Refines` nor `RefinesWithin`, and no pass or route reasons through the tree
layer.

## The delay closure and the characterization

`TauClosure.lean` does not install a second relation.  `TauHead p q` says `p` is
`q` behind finitely many silent steps, witnessed by a first-class delay whose
`flatten` is `p`; `TauDiverges p` says `p` is an infinite delay.  Both are
*equivalent* to the existing `SilentHead`/`SilentDiverges` on the same trees, and
`TauReachesUb`/`TauTimeoutReachable` likewise.  `TauSimttF` repeats the nine
terminal/event clauses with those witnesses, `TauSimttF post sim p q ↔
SimttF post sim p q` for every `post`, `sim` and pair of trees, and therefore
`simtt post = plfp (TauSimttF post) top` — the greatest fixed point of the
delay-indexed functional.  `simtt_iff_tau` is the unfolding, and coinduction
over that same functional yields `simtt` again.  The classification, direction
and refusal classes are `Simtt.lean`'s, clause for clause.

## Conditioned congruence

Two theorems relate the relation to the tree algebra, and both are false without
their hypotheses:

* `simtt_bind`: from `simtt post p q`, `bind p f` simulates `bind q g` when
  (i) `post`-related returns give related continuations, (ii) each `f o`
  silently completes at a return or reaches UB, (iii) `f .ub` and `g .ub` reach
  UB, and (iv) `g` reaches no timeout at a defined return — the quantifier is
  only over `g (.ret v mem)`.  `LeanLLVMTest/Vellum.lean` checks the positive
  theorem and two refusals whose source pair is related, and the refusals break
  different hypotheses:
  * the UB→timeout refusal binds `simtt checkPostTrue (ret o) ubNode` with a
    left continuation that always reaches a timeout: the right side stays the
    bound `ubNode`, so the bound pair is a timeout against a UB terminal, which
    the detector refuses.  The hypothesis that fails is (ii), not (iv): the
    left `f o` is a timeout node, neither a silent complete at a return nor a
    UB reach, while the right continuation `bindCont` returns on every defined
    return, so (iv) still holds;
  * the (iv) refusal instead keeps the left continuation completing at a
    return and gives the right a continuation that reaches a timeout at a
    defined return (`fun _ => timeoutNode`).  The bound pair is a left return
    against a timeout, refused by the same detector, and `TimeoutReachable` of
    `g (.ret v mem)` is the hypothesis that fails;
* `simtt_interp`: a tree-valued handler that re-emits the *identical* event with
  the *identical* responses, optionally behind a finite silent delay
  (`h e = tauN n (trigger e)`), preserves the relation.  A same-signature
  handler that maps `ObsEv.ub` to `ObsEv.timeout` does not, and that pair is
  refused by the same detector — the event/terminal preservation is a real
  precondition, not a consequence of the handler's type.

Both proofs are carried out on the delay-indexed witnesses rather than by
returning to `SimttF`: they coinduct on `TauSimttF` and transport the delay
witnesses directly.  Binding maps a delay's result through `fun t => bind t f`,
so a `TauHead` stays a `TauHead` and a `TauDiverges` stays a `TauDiverges`
(`tauHead_bind`, `tauDiverges_bind`); the generic layer supplies the finite and
infinite result transport and the flattening law those use.  A timeout in a bound
tree is inverted over the finite witness itself — the delay is put in `tauN`
normal form and the binding is unfolded constructor by constructor
(`tauTimeoutReachable_bind`) — so the clause construction never calls the
`SilentHead` inversion.  The interpreter transports a delay tower to a target
tower of the same height (`tauHead_interp`), and a divergent source reaches
`infTau`, which the interpreter leaves alone (`tauDiverges_interp`,
`interp_infTau`).  The old predicates appear only where an accepted statement
still uses them: the hypotheses of `simtt_bind`, and the terminal-exclusivity
and timeout-reflection lemmas behind the divergence clauses.

Neither theorem is about the host's one-step `Effect.interp`, which keeps its own
equations; the interpreter here is the generic, tree-valued
`ITree.EffectAlgebra.interp`.

## The general rule and its instances

`simtt_loop` is the rule the instances use.  For a frame, a `post`, two families
of bare handled trees over possibly unrelated state spaces, and an invariant
`Inv s t`, it concludes

```lean
simtt (fun oT oS => post oT oS ∧ oT.AgreesOutside frame oS) (left s) (right t)
```

for every invariant pair, from a one-step `TauSimttF` obligation at exactly that
framed return relation, whose continuation position is the same invariant lifted
through a finite silent delay on each side.  The frame is expressed at the
return, not as a third index, because `simtt` observes bare trees; the rule does
not assert that any two loops satisfy its premise, and it demands no positive
guard of the caller's trees.  `simtt_post_mono` weakens the postcondition, which
is how the original `simtt (Outcome.AgreesOutside frame)` statement is recovered
from the rule's `True ∧ _` return relation.  `handle_tau_guard` is the handler's
own positive jump delay, and `rawSilentHead_of_measure` turns an invariant with a
strictly decreasing natural measure into a finite raw private closure ending at a
stated value and memory.

The first instance is a genuinely recurring tree.  `tickStep` visibly emits
`call "tick" []` and returns `.recur ()` at every response, so the loop's only
way forward is the rule's continuation position; `tick_loop_simtt` relates it to
itself at the framed `True` postcondition.  Its backedge is guarded at the
internal position (`mfix_bindStep_recur_guard`), and a differing `"tock"` call is
refused by the existing event detector.

`loop_candidate_simtt` is the second instance.  It relates, for every
`x : BitVec 64`,

```lean
simtt (Outcome.AgreesOutside (loopFrame x))
  (runHandled noCalls (loopFrame x) 19     loopFunction      (initState loopFunction      [.int 64 x]))
  (runHandled noCalls (loopFrame x) 10000  candidateFunction (initState candidateFunction [.int 64 x]))
```

The loop's state family is a `LoopSeed`: a budget, a machine state, the symbolic
`%m` register, the accumulator and the counter.  The family's two kinds of seed
are the run's entry state at its own 19-step budget and the condition seeds,
each carrying the loop invariant, a counter of at most eight, the budget
`2 * (8 - k) + 2` its remaining iterations cost, the lane prefix as the
accumulator, and the run's own symbolic memory.  Every seed's return obligation
is discharged by the loop's finite derivation of private accesses, obtained from
`rawSilentHead_of_measure` at the measure `8 - k` from the per-block facts, and
transported through the handler into the `tau` closure of the handled tree; the
candidate has no memory events at all.  The postcondition compares the two
handler-produced returns, and a returned memory that differs at address `0`,
outside the allocator-derived band, is rejected.
`loop_candidate_beh_bridge` is the one behaviour statement derived from the
bridge for that pair.

This is a tree-level conditional rule, two instances, fixed budgets for the
fixture and one allocator-derived frame.  It is not a refinement rule: there is
no rule for loops at `Refines`/`RefinesWithin`, no automatic discharge of the
rule's premise, no `runT = mfix` correspondence for the fixed-budget trees, no
memory-effectful call environment, and no memory-aware module theorem; those are
open obligations of the programme.  No pass, route or installer reasons through
the tree layer.
