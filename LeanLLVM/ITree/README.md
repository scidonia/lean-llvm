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
| `Simtt.lean` | `SilentStep`/`SilentHead`/`SilentDiverges`, the one-step functional `SimttF` and its greatest fixed point `simtt post` on bare `ObsEv` trees, the positive rules, the terminal refusals and the event-payload refusals |
| `Bridge.lean` | `HandledExec`, the correspondence `handled_runFuel`, the elimination `simtt_exec_some`, and the budget-, behaviour- and refinement-level corollaries |
| `LoopInstance.lean` | the comma-mask loop and its unrolled candidate: the fixed-budget instance, the address-0 counterexample, and the behaviour corollary |

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

The axiom budget reflects that: the simulation, the correspondence and the fixed
loop proofs stay within `[propext, Classical.choice, Quot.sound]`, and
`Classical.choice` is there for the arbitrary-`Prop` frame decision, exactly as
the framed refinement layer already pays it.  The pins in
`LeanLLVMTest/Vellum.lean` record it.

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

## The instance

`loop_candidate_simtt` relates, for every `x : BitVec 64`,

```lean
simtt (Outcome.AgreesOutside (loopFrame x))
  (runHandled noCalls (loopFrame x) 19     loopFunction      (initState loopFunction      [.int 64 x]))
  (runHandled noCalls (loopFrame x) 10000  candidateFunction (initState candidateFunction [.int 64 x]))
```

The loop's finite derivation of private accesses is stated on raw `(tree,
memory)` states (`RawSilentHead`, local to `MemoryEffect`) and transported
through the handler into the `tau` closure of the handled tree; the candidate has
no memory events at all.  The postcondition compares the two handler-produced
returns, and a returned memory that differs at address `0`, outside the
allocator-derived band, is rejected.  `loop_candidate_beh_bridge` is the one
behaviour statement derived from the bridge for that pair.

This is one fixture at fixed budgets and one allocator-derived frame.  There is
no general loop or recursion rule, no automatic discharge of the relation
hypothesis, no memory-effectful call environment, and no memory-aware module
theorem; both are open obligations of the programme.
