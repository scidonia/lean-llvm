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
| Tree relation | A postcondition-indexed, directed simulation `simtt` over interaction trees (`LeanLLVM/ITree/`): the one-step functional takes a leaf postcondition, `timeout` matches only `timeout`, undefined behaviour and silent divergence are one-sided, and the comma-mask loop is related to its unrolled candidate at the loop's allocator-derived frame | adoption by `Refines`/`RefinesWithin`; a general loop or recursion rule; a memory-aware module theorem |
| Passes | Certified constant propagation, certified branch folding, certified strength reduction, composition, pipeline | dead-code elimination, unreachable-block elimination, algebraic simplification, loop transforms |
| Pure seam refinement | `Γ ⊢ candidate ⊑ baseline` for the comma-mask seam, with a contextual replacement theorem (`LeanLLVM/Vellum/`) | the same at the emitted-LLVM level; the object connection is a runtime differential transcript, not a proof, and the memory-backed loop is refused by the selector |
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
no clang lowering is related to the AST, and that provenance chain is open.  The
installer refuses the loop, because no checked theorem binds the loop object to
the seam's contract.  There is no benchmark, and calls still have no memory
effects, so no memory-aware module theorem is claimed.

The interaction-tree layer in `LeanLLVM/ITree/` asks a different question of the
same fuel semantics: whether two executions agree as trees under a postcondition
on their leaves, with each side's private memory abstracted by a frame.  It is
proved for the comma-mask loop against its unrolled candidate, for every 64-bit
argument, at fixed fuel budgets (19 for the loop, 10000 for the candidate) and
the loop's allocator-derived frame; a returned memory that differs at address
zero is rejected by the same postcondition.  That is one fixture.  It is not a
general loop rule, it installs nothing, and neither the pass proofs nor the
executable relation (`Refines`, `RefinesWithin`) use it yet.  The layer is a
second Lake library whose only direct mathlib importer is
`LeanLLVM/ITree/Internal/PFunctor.lean`; `LeanLLVM/ITree/README.md` records the
API, the dependency and the upstream provenance.

## Build

The toolchain is Lean `v4.36.0-rc1` from the flake.  Run every command through
the shell so the environment comes from this checkout:

```bash
nix develop -c lake build            # library, tree library and leanllvm executable
nix develop -c lake build LeanLLVMTest
nix develop -c lake exe leanllvm tests/constfold.ll
```

The flake also provides `llvm-as`, `llvm-dis`, `opt`, `llc` and `clang` for
checking emitted IR.  A cold build also resolves
`leanprover-community/mathlib4` at the revision pinned in `lakefile.toml` into
`.lake/packages`, which `LeanLLVM.ITree` depends on; mathlib's oleans have to be
present before the tree modules build, so expect a mathlib build unless its
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
| `LeanLLVM/ITree.lean`, `LeanLLVM/ITree/` | interaction trees, the directed postcondition-indexed relation, the loop/candidate instance; the single mathlib import boundary |
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
trees under a leaf postcondition, with private memory hidden by a frame.  It is
directed — left is the target, right the source — and `ub`, budget timeout and
silent divergence are distinct terminals there.  No pass is proved with it, so
the obligations above are unchanged.

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
- [`LeanLLVM/ITree/README.md`](LeanLLVM/ITree/README.md) — the tree library:
  its public API, the single mathlib dependency, the relation's clauses and the
  upstream provenance.

## Reference materials

`reference/vellvm/src/rocq/` contains the VeLLVM Coq sources (MIT) at revision
`de5b3249`; `reference/vellvm/src/ml/libvellvm/` contains its OCaml parser.  They
are read-only study material and are not part of the Lean build.
