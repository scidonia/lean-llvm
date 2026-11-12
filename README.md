# lean-llvm

A certified transformation and refinement framework for LLVM IR, written in
Lean 4.  The intended use is late optimisation: accept textual LLVM IR produced
by `clang`/`llc`-style front ends, apply transformations whose soundness is a
Lean theorem, and emit textual IR that the rest of the LLVM toolchain consumes
unchanged.

The design is cribbed from [Vellvm](https://github.com/vellvm/vellvm) — its
separation of syntax, event-based semantics, memory model and refinement — but
the Lean development is original.  A copy of the Vellvm sources is vendored
under `reference/vellvm/` for study; see `reference/README.md` for provenance.

## Status

This repository is an initial vertical slice, not a port of Vellvm:

| Area | What is here | What is not |
| --- | --- | --- |
| Syntax | Integer scalars, `ptr`, `void` and integer-lane vectors `<n x iW>`; arithmetic, `icmp`, `select`, `trunc`/`zext`/`sext`, `alloca`, `load`, `store`, plus a vector `load` and a vector `store` at a whole-byte total width, both literal vector forms (a `splat` and a lane list, with `zeroinitializer`), lane-wise `icmp` and integer binops, the mask `bitcast`, and the lane accesses `extractelement`/`insertelement`; `br`, `condbr`, `ret`, `unreachable`, `call`, `phi`, and a `getelementptr` whose element type is an admitted integer width (`i1`, `i7`, `i8`, `i16`, `i32`, `i64`, `i128`) or a vector of integer lanes whose lane width is whole bytes and whose packed size is a power of two | aggregates, floating point, globals, a `getelementptr` scaled by an aggregate or pointer element type, a vector `store` whose total width is not a whole number of bytes |
| Front end | A line-oriented parser and a canonical printer for the modelled subset, including `declare` lines (held in `Module.decls`) | bitcode, metadata, attributes |
| Semantics | Executable step semantics over basic blocks, byte-addressed memory, fuel-indexed divergence, `ub` as a distinguished outcome | poison, provenance, concurrency |
| Refinement | `Refines target source` = every outcome of the target is an outcome of the source; `ub` in the source admits everything, divergence admits nothing. A framed relation (`RefinesWithin`, `LeanLLVM/Frames.lean`) compares the returned value and the bytes outside a footprint read off the allocator state. A call environment returns the value, the memory and the allocator state the callee leaves (`CallOutcome`), and the caller adopts them | relational/log relations; a contextual replacement whose frame is load-bearing; a simulation rule for arbitrary loops |
| Tree relation | A generic interaction-tree library (`ITree/`) with a one-step event handler and its computable interpreter, a seeded guarded recursion `mfix` with its unfolding equations and positive-delay witnesses, and an LLVM instantiation (`LeanLLVM/ITree/`) that folds memory into the tree as an effect: `simtt` is a postcondition-indexed, directed simulation over those bare handled trees, `timeout` matches only `timeout`, undefined behaviour and silent divergence are one-sided, a framed rule proves it for the remaining pairs of an invariant, and the comma-mask loop is related to its unrolled candidate at the loop's allocator-derived frame | adoption by `Refines`/`RefinesWithin`; a refinement- or behaviour-level loop rule; a `runT`/`mfix` correspondence; a memory-aware module theorem; a computable host handler (`frame` has no decider today) |
| Passes | Certified constant propagation, certified branch folding, certified strength reduction, composition, pipeline | dead-code elimination, unreachable-block elimination, algebraic simplification, loop transforms |
| Pure seam refinement | `Γ ⊢ candidate ⊑ baseline` for the comma-mask seam, with a contextual replacement theorem (`LeanLLVM/Refinement/`) | no theorem relates Lean's compiled code or machine instructions to the model; installation is gated by a kernel-derived certificate over the proved fixture (hash and byte-for-byte reproduction), not by a compiler-equivalence theorem, and each installed unit — baseline, candidate and the memory-backed loop — has its own certificate and its own covering statement |
| Toolchain | `leanllvm` reads `.ll`, applies the pipeline, writes `.ll`; output is checked with `llvm-as` | bitcode I/O, pass-manager integration inside `opt` |

Every pass is a theorem, not a test: the build fails if the refinement proof
fails.  The executable checks in `LeanLLVMTest/` exercise the parser, the
semantics, the pipeline on a concrete program, and the axiom footprint of the
soundness theorems.

The memory-backed loop is the current boundary of that claim.  Its fixture is
printed from the Lean AST in `LeanLLVM/Refinement/CommaMaskLoopBody.lean` by
`lake exe leanllvm-loop-emit`, through the framework's own printer, so the text
the correctness and framed-memory statements are proved about is what that AST
renders to.  It is not Lean's native compiler output: no `lean -c` emission and
no clang lowering is related to the AST, and that provenance chain is open. The
loop is installed through its own certificate, gated by
`loop_refines_candidate_within` (a framed-memory refinement within the loop's
own allocations); the certificate is a hash-and-rebuild bridge like the
candidate's and baseline's, not a compiled-code theorem.  The seam units have a
benchmark (`probes/bench/bench.sh`, with a recorded run at `b29716c`) that
reports how fast each installed unit ran and presents no ratio as proof, while
the parser has no timing and no native-reference comparison (J5 and J6 are
open), so no parser performance is claimed.
Calls carry a memory channel: an environment returns the value, the memory and
the allocator state the callee leaves, and the caller adopts them.  The
module-level replacement theorem is stated over `CallRefines`, which demands
complete agreement of the two outcomes, so its frame stays inert; a contextual
replacement that permits the callee's footprint to differ is not claimed, and
the tree layer describes only environments that leave memory and allocator
untouched (`PureEnv`).

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

## The JSON demonstration

The framework's subject is LLVM IR.  Everything above concerns the syntax, the
semantics, the refinement relation and the passes over it.

There is also a worked demonstration under `LeanLLVM/JSON/`, `LeanLLVM/Refinement/`
and `kernel/json/`: a real SIMD parser for a subset of JSON, taken from C
through its emitted IR into the framework, with each translation unit carrying
its own record, its own `Satisfies` theorem, and a certified composition for the
assembled pipeline.  It exists to exercise the framework end to end on a
program large enough to be interesting — a unit that is thousands of
instructions long, a loop whose exit is a refusal rather than a fixpoint, and
memory regions that alias — and it is measured against `simdjson` on the
documents that parser is usually benchmarked on.

**It is a proof of concept, not the subject of the repository.**  A defect in the
demonstration is a defect in the demonstration; the framework's claims are the
ones in `DESIGN.md`.  Two things it established that the framework itself now
relies on are general and live outside it: that an invariant must carry every
consequence of a precondition its own proof uses — including a region's
presence across a reserve, not merely the bytes written — and that a claim
quantified across stages different stages own is a scope error.

The demonstration is also the honest illustration of the framework's boundary.
Its units are proved against their emitted IR, and its assembled pipeline is
proved from those units' records; that chain begins at a textual emission and
ends at the model, and no theorem relates Lean's compiled code to either end.

**Nothing in this repository is a theorem about time**, so the numbers below are
of two kinds and are labelled as such. The ratios are measurements of the
native pipeline against `simdjson` On-Demand, taken on one host in a scratch
tree, medians of 11–15 rounds, both binaries pinned to one core with the same
alignment flags; they are a record of observed runs and are not reproducible
from this tree (`docs/json-pipeline-performance.md` gives the harness's shape
so a rebuild can repeat the comparisons). The throughput is a measurement of
the Lean model in this tree, from `probes/bench/json-bench.sh`.

Ratios to On-Demand under the two contracts that mean most; **below 1.0 is
faster**, `E` and `P` are the host's two core classes.

| file | entries/block | P2 E | P2 P | P0 E | P0 P |
|---|---:|---:|---:|---:|---:|
| `canonical` | 6.8 | 1.044 | **0.922** | 0.945 | **0.814** |
| `citm` | 7.9 | 0.843 | **0.555** | 0.746 | **0.452** |
| `twitter` | 7.9 | 0.847 | **0.611** | 0.704 | **0.528** |
| `canada` | 9.9 | 1.023 | **0.946** | 0.910 | **0.849** |
| `dense` | 26.4 | 1.027 | 1.037 | 0.829 | **0.873** |
| `longstr` | 1.3 | 0.721 | **0.586** | 0.296 | **0.236** |
| `escdense` | 7.4 | 0.816 | **0.759** | 0.648 | **0.719** |

`P2` — full extraction, exact error offset, every string validated — is faster on
six of seven on the faster core, by 4–45%, with `dense` the single loss at 3.7%;
`P0` is faster on all seven on both classes. The margin is core-specific and the
*decisions* are not: the stage-1 advantage over the alternative arm is 1.7–3.9
ns/block on the slower class and 0.2–0.9 on the faster one.

The Lean parser's own model, parsed by `parseDocument` in this tree, costs
**35.5 ns/byte at 64 KiB** and 48.0 at 4–16 KiB, with a 4 µs floor on a
one-byte document — that is, about 21–28 MB/s, and the cost per byte falls
with size. The benchmark's documents are `{"a":1234,"b":"hello"}` repeated, so
that figure describes the parser on tier-1 numbers and says nothing about the
conversion's fallback path.

What none of this establishes: that the numbers generalise past one host, one
governor setting and AVX2 code paths; that a different reference parser or
corpus would rank the same way; or that any timing follows from the proofs.

## Build

The toolchain is Lean `v4.35.0` from the flake.  Run every command through
the shell so the environment comes from this checkout:

```bash
nix develop -c lake build            # default targets: leanllvm, ITree and LeanLLVMTest
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
and its proof are in `LeanLLVM/Refinement/`: `commaContract ⊢ byteLoop ⊑ swar`,
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

`reference/vellvm/src/rocq/` contains the Vellvm Rocq sources (MIT) at revision
`de5b3249`; `reference/vellvm/src/ml/libvellvm/` contains its OCaml parser.  They
are read-only study material and are not part of the Lean build.

## Licence

Apache License 2.0 — see `LICENSE`.  The Vellvm sources vendored under
`reference/vellvm/` for study are not covered by it and are not built; see
`reference/README.md` for their provenance and terms.
