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
def Refines (calls : Calls) (target source : Function) : Prop :=
  ∀ args o, Beh calls target args o → Beh calls source args o
```

`Calls` is the environment a call resolves in: a symbol and its argument values
give the result, or nothing for an unresolved (undefined) call.  Threading it
explicitly keeps one semantics for a function in every environment, and lets a
theorem say what it assumes about the callee rather than inlining it.  The
environment is deterministic, but an unresolved call is `ub`, which admits
every outcome, so the environments still have a non-trivial order:
`CallRefines calls' calls sym` holds when on every argument list the source is
`ub` or the two agree.  A target that defines a call the source leaves
undefined refines it; the reverse does not.  `LeanLLVM/CallRefinement.lean`
lifts that order to `Beh`, so a caller's behaviour under the candidate
environment is included in its behaviour under the baseline environment.

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

## Framed refinement

`Refines` compares whole outcomes, so the returned memories must be equal.  A
replacement that allocates privately does not satisfy that: its locals are not
caller-visible, so demanding their equality rejects a sound replacement.  The
finer relation is in `LeanLLVM/Frames.lean`:

```lean
def AgreesOutsideMem (m n : Mem) (frame : Nat → Prop) : Prop :=
  ∀ a, ¬ frame a → readByte m a = readByte n a

def Outcome.AgreesOutside (frame : Nat → Prop) : Outcome → Outcome → Prop
  | .ub, .ub => True
  | .ret v m, .ret w n => v = w ∧ AgreesOutsideMem m n frame
  | _, _ => False

def BehsWithin (target source : List Value → Outcome → Prop) (frame : Nat → Prop) : Prop :=
  ∀ args o, target args o → ∃ o', source args o' ∧ o.AgreesOutside frame o'

def RefinesWithin (calls : Calls) (target source : Function)
    (frame : Nat → Prop) : Prop :=
  BehsWithin (Beh calls target) (Beh calls source) frame
```

Four points make it usable rather than vacuous:

- The footprint is a parameter, and the one used here is read off the execution:
  `AllocFrame s₀ s₁` is the band from the allocator state before the run to the
  state after it, so a unit that allocates nothing covers no address and a unit
  that allocates two `i64` locals covers exactly their sixteen bytes.
  `MemPrivate frame m` says the memory has nothing outside the frame, and
  `AgreesOutsideMem.of_private` turns two such memories into agreement outside
  the union of the two footprints.  A footprint chosen existentially could be
  the universal predicate and the relation would say nothing, which is why the
  band comes from the allocator states instead.
- Memory is compared byte by byte rather than as an association list: `readByte`
  equality is the observation, list equality would be stronger than a caller can
  see.
- The `ub` direction is kept.  A target that reaches `ub` admits every outcome,
  including every defined one, so `RefinesWithin` forces the source to be `ub`
  too, and a private allocation cannot hide undefined behaviour.  The
  one-sided write law only covers stores inside the frame, so a byte written
  outside it cannot be forgotten.
- Exact refinement is the special case: `refinesWithin_of_refines` derives a
  framed refinement from any `Refines`, so every existing theorem keeps its
  meaning and none is weakened.

`LeanLLVM/Vellum/CommaMaskLoop.lean` is the instance: the loop's two `alloca`s
give the band, the invariant carries the proof that both stores stay inside it,
and `loop_refines_candidate_within` states the same returned value with byte
agreement outside the band.  `LeanLLVMTest/Vellum.lean` also exercises the
negative direction: a unit that writes one byte outside the frame, for which the
framed relation is proved to fail.

The relation is a statement about memory, not a module theorem.  Calls still
have no memory effects, and there is no simulation rule for an arbitrary loop;
the loop's induction is proved for that fixture.  Both are open obligations of
the programme rather than consequences of this relation.

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

`LeanLLVM/Vellum/CommaMaskIR.lean` carries the same statement to emitted IR:
it parses the probe's two fixtures, pins the ASTs, proves each body returns the
corresponding `CommaMask` function, and concludes
`Refines candidateFunction baselineFunction` for every call environment.  The
fixtures are what the installation probe compiles and installs, so the proved
code is the installed code.  `LeanLLVM/Vellum/SeamContext.lean` adds a caller
whose body is a call to the seam and proves that swapping the environment entry
leaves its behaviour unchanged, so the replacement goes through the call
instruction rather than an inlined body.
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
3. **Wider syntax.**  `getelementptr`, `phi` and globals, with a dominance
   check for cross-block constant propagation.  Calls are modelled
   (`Instr.call` resolved through `Calls`) and refinement through them is
   one-directional (`CallRefinement`); memory effects across calls are the next
   step after that.
4. **Memory.**  Provenance and a store-to-load forwarding pass; the current
   byte map is the starting point, not the destination.  The same-address
   store/load round trip, the little-endian round trip and write-below framing
   are in `LeanLLVM/Memory.lean`; the footprint-parameterized relation and the
   allocator-derived band are in `LeanLLVM/Frames.lean`.  A Lean-produced,
   memory-using loop, a memory-aware call environment and a module theorem
   remain open.
5. **Validation seam.**  An Alive2-style driver that checks a candidate rewrite
   against the semantics when a proof is not yet available, so unproved passes
   can still be gated in the toolchain.
