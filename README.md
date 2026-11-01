# lean-llvm

A certified transformation and refinement framework for LLVM IR, written in
Lean 4.  The intended use is late optimisation: accept textual LLVM IR produced
by `clang`/`llc`-style front ends, apply transformations whose soundness is a
Lean theorem, and emit textual IR that the rest of the LLVM toolchain consumes
unchanged.

The design is cribbed from [VeLLVM](https://github.com/vellvm/vellvm) — its
separation of syntax, event-based semantics, memory model and refinement — but
the Lean development is original.  A copy of the VeLLVM sources is vendored
under `reference/vellvm/` for study; see `reference/README.md` for provenance.

## Status

This repository is an initial vertical slice, not a port of VeLLVM:

| Area | What is here | What is not |
| --- | --- | --- |
| Syntax | Integer scalars, `ptr`, `void`; arithmetic, `icmp`, `select`, `trunc`/`zext`/`sext`, `alloca`, `load`, `store`; `br`, `condbr`, `ret`, `unreachable` | aggregates, floating point, vectors, `phi`, `call`, `getelementptr`, globals |
| Front end | A line-oriented parser and a canonical printer for the modelled subset | bitcode, metadata, attributes, declarations with bodies |
| Semantics | Executable step semantics over basic blocks, byte-addressed memory, fuel-indexed divergence, `ub` as a distinguished outcome | poison, provenance, concurrency, calls |
| Refinement | `Refines target source` = every outcome of the target is an outcome of the source; `ub` in the source admits everything, divergence admits nothing. A framed relation (`RefinesWithin`, `LeanLLVM/Frames.lean`) compares the returned value and the bytes outside a footprint read off the allocator state | relational/log relations; memory-aware contextual replacement; a simulation rule for arbitrary loops |
| Tree relation | A generic interaction-tree library (`ITree/`) with a one-step event handler and its computable interpreter, a seeded guarded recursion `mfix` with its unfolding equations and positive-delay witnesses, and an LLVM instantiation (`LeanLLVM/ITree/`) that folds memory into the tree as an effect: `simtt` is a postcondition-indexed, directed simulation over those bare handled trees, `timeout` matches only `timeout`, undefined behaviour and silent divergence are one-sided, a framed rule proves it for the remaining pairs of an invariant, and the comma-mask loop is related to its unrolled candidate at the loop's allocator-derived frame | adoption by `Refines`/`RefinesWithin`; a refinement- or behaviour-level loop rule; a `runT`/`mfix` correspondence; a memory-aware module theorem; a computable host handler (`frame` has no decider today) |
| Passes | Certified constant propagation, certified branch folding, certified strength reduction, composition, pipeline | dead-code elimination, unreachable-block elimination, algebraic simplification, loop transforms |
| Pure seam refinement | `Γ ⊢ candidate ⊑ baseline` for the comma-mask seam, with a contextual replacement theorem (`LeanLLVM/Vellum/`) | no theorem relates Lean's compiled code or machine instructions to the model; installation is gated by a kernel-derived certificate over the proved fixture (hash and byte-for-byte reproduction), not by a compiler-equivalence theorem, and each installed unit — baseline, candidate and the memory-backed loop — has its own certificate and its own covering statement |
| Toolchain | `leanllvm` reads `.ll`, applies the pipeline, writes `.ll`; output is checked with `llvm-as` | bitcode I/O, pass-manager integration inside `opt` |

Every pass is a theorem, not a test: the build fails if the refinement proof
fails.  The executable checks in `LeanLLVMTest/` exercise the parser, the
semantics, the pipeline on a concrete program, and the axiom footprint of the
soundness theorems.

The memory-backed loop is the current boundary of that claim.  Its fixture is
printed from the Lean AST in `LeanLLVM/Vellum/CommaMaskLoopBody.lean` by
`lake exe leanllvm-loop-emit`, through the framework's own printer, so the text
the correctness and framed-memory statements are proved about is what that AST
renders to.  It is not Lean's native compiler output: no `lean -c` emission and
no clang lowering is related to the AST, and that provenance chain is open. The
loop is installed through its own certificate, gated by
`loop_refines_candidate_within` (a framed-memory refinement within the loop's
own allocations); the certificate is a hash-and-rebuild bridge like the
candidate's and baseline's, not a compiled-code theorem.  There is no benchmark,
and calls still have no memory effects, so no memory-aware module theorem is
claimed.

The interaction-tree layer asks a different question of the same fuel
semantics: whether two executions agree as trees under a postcondition on their
leaves.  It comes in two libraries.

`ITree/` is the **generic** interaction tree: the coinductive carrier, exact
tree equality with lawful `Functor`/`Monad` instances, a first-class finite/
infinite silent-delay object, the ported monadic iterator, a tree-valued handler
with its directly guarded interpreter, *and* a one-step event handler with a
computable interpreter.  It imports no `LeanLLVM` module; its only direct mathlib
importer is `ITree/Internal/PFunctor.lean`.  `ITree/README.md` records the public
surface, the two interpreters, the import boundary and the upstream provenance.

`LeanLLVM/ITree/` is the instantiation.  Memory is an **effect** there: a handler
folds the `load`/`store` protocol into the tree, private accesses becoming silent
steps and everything else staying visible with the response the handler computed.
The directed relation then compares those bare handled trees; its finite and
infinite silent closures are restated through the generic delay object and proved
equivalent to them, and it is congruent under `bind` and under a re-emitting
tree-valued interpreter under explicit hypotheses.  The bridge shows that the
handled tree of a budgeted run resolves exactly as `runFuel` does.
The relation has a framed, postcondition-indexed rule: from an invariant over two
tree families and one `TauSimttF` step obligation at the relation's framed return
clause, it concludes `simtt` for every invariant pair, and postcondition weakening
recovers the plain framed post.  Two instances are proved.  A tree that visibly
emits the same call and recurs at every response is related to itself, which
exercises an actual recursive backedge; and the comma-mask loop is related to its
unrolled candidate, for every 64-bit argument, at fixed fuel budgets (19 for the
loop, 10000 for the candidate) and the loop's allocator-derived frame, with a
returned memory that differs at address zero rejected by the same postcondition.
That is a rule for bare handled trees with two instances.  It is not a refinement
rule: there is no rule for `Refines`/`RefinesWithin` loops, no `runT`/`mfix`
correspondence, and it installs nothing; neither the pass proofs nor the
executable relation use it.  The handler is proof-facing and noncomputable,
because the frame is an arbitrary proposition; the routes above are untouched.

## Build

The toolchain is Lean `v4.35.0` from the flake.  Run every command through
the shell so the environment comes from this checkout:

```bash
nix develop -c lake build            # default targets: leanllvm and the ITree library
nix develop -c lake build ITree      # the generic tree library alone
nix develop -c lake build LeanLLVMTest
nix develop -c lake exe leanllvm tests/constfold.ll
```

The flake also provides `llvm-as`, `llvm-dis`, `opt`, `llc` and `clang` for
checking emitted IR.  A cold build also resolves
`leanprover-community/mathlib4` at the revision pinned in `lakefile.toml` into
`.lake/packages`, which the `ITree` library depends on; mathlib's oleans have to
be present before the tree modules build, so expect a mathlib build unless its
prebuilt cache is already there.  That pin, `lean-toolchain` and the flake's
Lean source are upgraded together.

## Use

```bash
nix develop -c lake exe leanllvm input.ll -o output.ll

# choose passes (default: constprop,foldbr,strength)
nix develop -c lake exe leanllvm input.ll --passes foldbr

# print to stdout instead of a file
nix develop -c lake exe leanllvm input.ll
```

A sample input and the resulting output:

```llvm
; tests/constfold.ll
define i32 @main(i32 %x) {
entry:
  %a = add i32 1, 2
  %c = icmp eq i32 %a, 3
  br i1 %c, label %yes, label %no
yes:
  ret i32 %a
no:
  ret i32 %x
}
```

```llvm
define i32 @main(i32 %x) {
entry:
  %a = add i32 1, 2
  %c = icmp eq i32 3, 3
  br label %yes

yes:
  ret i32 %a

no:
  ret i32 %x
}
```

The folded instructions remain until dead-code elimination is implemented; the
conditional edge is gone, which is what the certified branch folder proves.

## Architecture

| Module | Contents |
| --- | --- |
| `LeanLLVM/Basic.lean` | types, literals, values, environments, byte memory |
| `LeanLLVM/Syntax.lean` | instructions, terminators, blocks, functions, cheap well-formedness |
| `LeanLLVM/Semantics.lean` | executable step semantics, `Outcome`, `Beh`, `Refines` |
| `LeanLLVM/Memory.lean` | byte-access and round-trip facts |
| `LeanLLVM/Frames.lean` | framed refinement: byte agreement outside an allocation-derived footprint |
| `ITree.lean`, `ITree/` | the generic interaction tree: public tree API, one-step event handler and interpreter, coinduction layer; the single mathlib import boundary |
| `LeanLLVM/ITree.lean`, `LeanLLVM/ITree/` | the LLVM instantiation: memory as an effect, the directed relation on bare handled trees, the correspondence with `runFuel`, the loop/candidate instance |
| `LeanLLVM/Parser.lean` | textual-IR parser for the modelled subset |
| `LeanLLVM/Printer.lean` | canonical textual-IR printer |
| `LeanLLVM/Transform/Basic.lean` | `Pass`, soundness, composition, pipeline |
| `LeanLLVM/Transform/ConstantFold.lean` | certified constant propagation |
| `LeanLLVM/Transform/FoldBranches.lean` | certified conditional-branch folding |
| `LeanLLVM/Transform/StrengthReduce.lean` | certified strength reduction (`mul x, 2` → `shl x, 1`) |
| `LeanLLVM/Pipeline.lean` | the shipped pipeline and its soundness theorem |
| `Main.lean` | the `leanllvm` driver |

`DESIGN.md` records the refinement definition, the modelling choices that bound
what the framework can claim, and the next milestones.  The pure seam contract
and its proof are in `LeanLLVM/Vellum/`: `commaContract ⊢ byteLoop ⊑ swar`,
with `Correct` transferred to the candidate and a two-call contextual theorem.

## Refinement discipline

A pass is `Function → Function` plus `Pass.Sound`: for every input, the output
refines the input.  `Beh` collects an outcome whenever some finite run produces
it; a `ub` reached on any prefix makes every outcome possible, and a run that
never finishes contributes none.  Consequently a pass may remove behaviours but
never add one: introducing `ub` where the source was defined is rejected by the
proof obligation.

Each pass is proved in two steps: a local lemma that a rewritten instruction or
terminator has the same effect, and a lift over `runFuel` by induction on the
fuel.  Composition is sound by transitivity, so the pipeline theorem is
`constantPropagation_sound`, `branchFolding_sound` and
`strengthReduction_sound` combined.

`LeanLLVM/ITree/` asks a separate question: whether two executions agree as
handled trees under a leaf postcondition, with private memory already folded into
the tree by the handler and a caller-chosen frame.  It is directed — left is the
target, right the source — and `ub`, budget timeout and silent divergence are
distinct terminals there.  No pass is proved with it, so the obligations above
are unchanged.

## Design notes

- [`docs/simd-recogniser-options.md`](docs/simd-recogniser-options.md) — where a
  faster SIMD recogniser can be inserted into a verified parser, the proof
  obligation at each insertion point, and the trust boundary each option adds.
- [`docs/lean-vellum-development-programme.md`](docs/lean-vellum-development-programme.md)
  — the proposed programme for certified replacement in a Lean compilation
  chain, with milestones and acceptance gates.
- [`docs/m0-runtime-noise-report.md`](docs/m0-runtime-noise-report.md) — M0
  evidence: what Lean-generated IR contains at a replacement boundary, the
  inline/opaque-call behaviour, and the corrected exact-mask contract.
  Reproduce with `nix develop -c bash probes/m0/check.sh`.
- [`docs/m0-runtime-noise-review-handoff.md`](docs/m0-runtime-noise-review-handoff.md)
  — the review of that report and the corrected first work package.
- [`ITree/README.md`](ITree/README.md) — the generic tree library: its public
  API, the import boundary, the one-step handler limit and the upstream
  provenance.
- [`LeanLLVM/ITree/README.md`](LeanLLVM/ITree/README.md) — the instantiation:
  memory as an effect, the handler's equations and noncomputability, the
  relation's clauses, the correspondence with `runFuel` and the open work.

## Reference materials

`reference/vellvm/src/rocq/` contains the VeLLVM Coq sources (MIT) at revision
`de5b3249`; `reference/vellvm/src/ml/libvellvm/` contains its OCaml parser.  They
are read-only study material and are not part of the Lean build.
