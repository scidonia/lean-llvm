# Design

## Goal

Insert a certified optimiser between the production of textual LLVM IR and the
LLVM back end, so that late transformations are proved correct with respect to a
formal semantics rather than trusted.  VeLLVM supplies the architectural model:
a syntax, an interpretation of memory and events, and a refinement relation
under which transformations are justified.  This repository restates that model
in Lean 4 and grows it pass by pass.

## Refinement

`Beh f args o` holds when some finite run of `f` on `args` produces outcome
`o`, or when a run reaches `ub`.  The first disjunct does not depend on `o`, so
reaching `ub` admits every outcome; a run that never terminates contributes no
outcome at all.

```lean
def Refines (target source : Function) : Prop :=
  ∀ args o, Beh target args o → Beh source args o
```

Consequences that drive the proof style:

- **Replacing a source `ub` by anything is sound.**  The source admits every
  outcome, so the target's outcomes are already included.  This is what lets an
  optimiser delete a trapping `load` whose result is unused.
- **Introducing `ub` is unsound.**  A target `ub` is an outcome the defined
  source cannot produce, so `ub`-introducing rewrites fail the obligation.
- **Turning divergence into a result is unsound.**  A divergent source admits no
  outcome, so the target must diverge too.
- **Equivalence is the easy special case.**  All passes in this slice preserve
  `Beh` exactly; their theorems are `↔`, which yields `Refines` by
  `Refines.of_iff`.

The fuel-indexed `runFuel` makes the modelling explicit: `none` is "no outcome
within the budget", and `Beh` existentially quantifies the budget.  Proofs lift
a per-step equality to `runFuel` by induction and then to `Beh`.

## Modelling choices

The model is deliberately conservative: it may permit fewer rewrites than LLVM's
own semantics, never more.

| Construct | Choice | Consequence |
| --- | --- | --- |
| `undef` / `poison` | reading one is `ub` | no nondeterminism or poison-aware rewrites yet |
| division/remainder by zero | `ub` | a fold is skipped rather than proved under a side condition |
| shifts | a count of at least the width saturates: all zeroes for `shl`/`lshr`, the sign bit for `ashr` | defined where LLVM has poison, so fewer rewrites than LLVM's semantics would allow |
| memory | finite map from byte address to byte; `alloca` bumps a monotone pointer | no provenance, aliasing or deallocation model yet |
| uninitialised load | `ub` | store-to-load forwarding needs the memory model next |
| integer values | width carried with a `BitVec`; operations read operands at `Nat` width | representation-agnostic folds, no dependent casts in proofs |
| control flow | one flat register environment across blocks | `phi` and dominance are not modelled; passes stay block-local |

## Pass framework

```lean
structure Pass where
  name : String
  run  : Function → Function

def Pass.Sound (p : Pass) : Prop := ∀ f, Refines (p.run f) f
```

`Pass.comp` runs two passes in order; `Pass.pipeline` folds a list;
`Pass.pipeline_sound` composes the proofs.  A new pass therefore costs:

1. the transformation on `Function`;
2. a local lemma that each rewritten instruction or terminator has the same
   `evalInstr`/`execTerm` effect;
3. a lift over `runFuel` (induction on fuel, using the step lemma);
4. `Refines` from behavioural equivalence, and a `Pass.Sound` instance.

The constant folder illustrates the pattern where a rewrite is not local: a
substitution is carried through the block, and an environment invariant
(`EnvEmbeds`) states that every substituted name is bound to exactly the literal
being substituted.  A separate invariant lemma maintains it across instructions,
including instructions that rebind a name.

## Toolchain position

```
source -> clang -S -emit-llvm -> .ll -> leanllvm -> .ll -> opt/llc -> object
```

The driver rejects any construct the semantics does not model, so the invariant
"every function that reaches the pipeline has a defined meaning" holds by
construction.  The emitted text is canonical IR, checked with `llvm-as` in the
verification runs.

## Next milestones

1. **Dead-code elimination.**  Needs the `ub`-aware direction of refinement:
   deleting a pure unused instruction is an equivalence when its operands are
   bound, and a refinement when they are not.  This is the first pass whose
   proof is naturally one-directional.
2. **Unreachable-block elimination.**  Branch folding creates unreachable
   blocks; removing them is an equivalence over reachable states.
3. **Wider syntax.**  `getelementptr`, `phi`, then calls and globals, with a
   dominance check for cross-block constant propagation.
4. **Memory.**  Provenance and a store-to-load forwarding pass; the current
   byte map is the starting point, not the destination.
5. **Validation seam.**  An Alive2-style driver that checks a candidate rewrite
   against the semantics when a proof is not yet available, so unproved passes
   can still be gated in the toolchain.
