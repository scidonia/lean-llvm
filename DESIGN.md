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

## Pure seam refinement

`LeanLLVM/Vellum/` carries the first boundary contract at the type the seam
uses.  A contract fixes the admitted inputs and the observable guarantee:

```lean
structure Contract where
  pre  : BitVec 64 → Prop
  post : BitVec 64 → BitVec 64 → Prop

def Refines (Γ : Contract) (target source : BitVec 64 → BitVec 64) : Prop :=
  ∀ x, Γ.pre x → target x = source x
```

`SemRefines` is the option-valued form for partiality or undefined behaviour;
`semRefines_total` relates it to the pure equality above.  `Correct Γ f` is
`∀ x, Γ.pre x → Γ.post x (f x)`, and `Correct.of_refines` transfers it from the
source to the target.  `Context` and `Context.refines` are the pure-slice
counterpart of the contextual replacement theorem: a caller that only calls the
seam at admissible arguments keeps its result.

The first instance is the comma mask.  `swar` (the baseline body) and
`byteLoop` (the candidate body) are both proved equal to the lane-wise `spec`,
so `commaContract ⊢ byteLoop ⊑ swar`; a two-call context is preserved as well.
The 64-bit identities are kernel-checked in `CommaMaskKernel.lean` by a
byte-lane argument: the packed addition is shown to have no lane carries, each
8-bit lane is discharged by `decide`, and the lanes are glued back by a
base-256 decomposition.  `LeanLLVMTest/Vellum.lean` pins the standard axiom
footprint; no native bit-blast axioms remain.

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

The strength-reduction pass (`mul x, 2` → `shl x, 1`) is the smallest shape: one
`BitVec` identity (`x * 2 = x <<< 1`), one instruction-equivalence lemma, the
same lift over `runFuel`.

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
