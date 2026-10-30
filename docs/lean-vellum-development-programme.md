# LeanVellum: development programme

**Status:** proposed programme, not an implementation report  
**Date:** 28 October 2026  
**Objective:** certified replacement of LLVM code in a real Lean compilation chain, including implementations independently synthesised by an LLM.

## 1. Decision and intended outcome

Build a Lean-native LLVM semantic refinement framework and integrate it into the compilation path:

**Lean → generated C → LLVM IR → certified replacement → LLVM backend → executable.**

This is Option D in `simd-recogniser-options.md`. Its purpose is broader than speeding up the recogniser: it establishes a reusable replacement window for memory-using computations. Source-level SWAR and compiler auto-vectorisation remain useful baselines, but do not deliver this capability.

Use Vellvm's semantic architecture and refinement theory as the starting point for adaptation into Lean. Do not make a complete line-for-line port a prerequisite for a working compilation example. Implement a coherent supported fragment, with explicit rejection of unsupported features, and extend it around representative replacements.

The intended product accepts a baseline implementation, an independently constructed candidate and a checked refinement certificate. It installs the candidate only when the certificate applies to the exact artifacts and assumptions used by the build.

## 2. Fundamental design requirements

1. **Production-chain integration.** Baseline code must come from an actual Lean build, not solely from hand-written toy LLVM examples.
2. **Independent synthesis.** The candidate need not be derived from the baseline by a known sequence of transformations. Different algorithms, control-flow graphs and internal representations are permitted.
3. **Lean-checked certification.** Accepted certificates are proof terms checked by Lean's kernel under an explicit axiom policy. LLMs, proof search and candidate generators are untrusted.
4. **Memory-relational reasoning.** Proofs may relate different allocations, layouts and intermediate states while preserving the boundary contract.
5. **Contextual validity.** A local certificate must justify replacement inside an admissible calling environment.
6. **Artifact fidelity.** The certified program and the program handed to the backend must agree, including semantically relevant attributes and target configuration.
7. **Conservative failure.** Unsupported syntax, missing contracts, failed proofs and stale certificates retain the original implementation. A strict CI mode may instead fail the build.
8. **Separate correctness from performance.** Refinement is mandatory; speedup is measured separately. A correct candidate can still be rejected as an optimisation.

## 3. Certification model

Write the local obligation schematically as:

```text
Γ ⊢ Fnew ⊑ Fold
```

The direction means that the candidate refines the original. The environment `Γ` records interface requirements, admissible incoming states, ownership and aliasing assumptions, external-call contracts and target configuration.

The relation must account for returned values, observable memory effects, interactions, termination, divergence, poison, underdefined values and undefined behaviour. Equality of results when both sides terminate is insufficient. A terminating defined baseline must not be replaced by an implementation that diverges or invokes undefined behaviour on the same admissible input.

The exact behavioural model and treatment of nondeterminism must be fixed in the semantics milestone. Behaviour inclusion is a useful intuition, not a substitute for the formal definition.

The required composition theorem has the schematic form:

```text
LocalRefinement Γ Fnew Fold
AdmissibleContext Γ C
-----------------------------------------
ModuleRefinement (C[Fnew]) (C[Fold])
```

For stateful replacement, the context theorem must support a relation between source and target heaps and preservation of unrelated memory. An arbitrary single-function input/output theorem does not automatically supply this result.

Conditional assumptions must be discharged at the boundary: by caller proofs, established interface invariants, or a verified runtime guard and fallback. They cannot merely be recorded in a manifest.

### Proof strategies

Support direct relational simulation with loop invariants and heap relations. Also support proofs through an intermediate abstract specification when the resulting theorems actually imply candidate-to-baseline refinement. Two implementations satisfying the same loose specification does not, by itself, establish that one refines the other.

The framework must not require matching instruction sequences or matching loop iterations. Proof rules should accommodate stuttering and different traversal orders where the observable semantics permits them.

## 4. Initial scope and replacement boundary

Start with sequential, whole-function replacements that preserve the externally visible ABI. Candidate implementations may change their private representation and scratch allocations.

Choose the first function from real Lean-generated code and inspect its emitted LLVM before committing to a feature subset. Prefer a byte-buffer or array computation with a loop and observable output, with few external calls. Preserve or create an identifiable function boundary and verify that it survives Lean lowering and Clang preprocessing.

The initial LLVM subset should cover what that example actually emits: integer arithmetic, comparisons, branches, SSA joins, loads and stores, pointer arithmetic, calls and returns, plus required types and attributes. Allocation, vectors, globals and intrinsics enter as required by milestones, not as unmodelled shortcuts.

Initially exclude concurrency, inline assembly, exceptions, unsupported intrinsics and unsupported semantic annotations. Do not silently erase features to make an input parse. Any normalisation that changes semantics belongs in the proof or the declared trusted base.

If a representation change crosses the function boundary, either prove adapters correct or enlarge the certified unit to include all affected functions. Unchanged callers must continue to see the representation their contract requires.

## 5. Build architecture

| Component | Responsibility | Acceptance output |
|---|---|---|
| Capture driver | Invoke the pinned Lean/C/LLVM path and identify the replacement unit | Baseline IR and build manifest |
| Importer and well-formedness checker | Represent the supported LLVM fragment faithfully | Formal AST and checked structural conditions |
| Semantic core | Define values, execution, memory and interactions | Versioned semantics |
| Refinement library | Support local proofs, heap relations and composition | Kernel-checked theorems |
| Candidate producer | Generate LLVM, or compile candidate C/Rust to LLVM | Candidate IR; optional proposed proof |
| Certificate checker | Check the precise refinement statement and allowed dependencies | Accepted or rejected certificate |
| Installer | Bind the certificate to the artifacts and perform replacement | Patched module and audit record |
| Backend driver | Resume compilation and link against the required runtime | Executable and reproducible build record |

If an LLM writes C or Rust, certify the LLVM produced from that source. A proof about a separate abstract model does not certify the compiled candidate without an additional connection theorem.

Initially interpose before aggressive inlining or whole-program optimisation destroys the boundary. Determine the exact position experimentally. Resume ordinary LLVM optimisation after installation, subject to the existing downstream compiler trust assumption.

The manifest should bind baseline and candidate content, semantic version, toolchain versions, target triple, data layout, CPU/features, function signatures, calling conventions, semantic attributes, linked contracts and proof dependencies. Hashes detect stale or substituted artifacts; they do not establish that parsing or serialization preserves semantics.

## 6. Development milestones

### M0 — Reproducible compilation window

**Work:** pin Lean, Clang/LLVM and target; compile a small real Lean application to C and LLVM; identify a memory-using function and all relevant dependencies; prototype capture and reinsertion.

**Deliverables:** reproducible build script, baseline artifacts, toolchain manifest, IR feature inventory, explicit trust ledger.

**Acceptance:** an identity replacement passes through the build and produces a working executable. Inspection confirms that the selected body is the one installed and compiled. This is integration evidence, not a semantic certification claim.

### M1 — Executable and propositional semantics for the supported fragment

**Work:** adapt the relevant Vellvm structure into Lean; define types, values, control flow, calls, memory operations and observable behaviour; settle undefined behaviour, poison and underdefined values. Provide well-formedness checks and useful execution diagnostics.

**Deliverables:** semantic definitions, support matrix, importer, interpreter where practical, fixtures extracted from M0, documented relation to the pinned LLVM language specification.

**Acceptance:** the M0 baseline and a structurally different candidate are represented without silently dropping semantics. Focused differential tests against LLVM cover supported operations and memory edge cases. Such tests detect modelling errors but do not prove agreement with LLVM.

### M2 — Open-function and module refinement

**Work:** define refinement, external-call environments and admissible contexts; develop loop and recursion rules, framing, heap relations and contextual replacement. Include mutually dependent calls when required by the selected unit.

**Deliverables:** precise refinement definition, reflexivity/transitivity where appropriate, proof rules, `replaceFunction_sound` or a corresponding module theorem.

**Acceptance:** prove replacement in a module containing a real caller and callee, including memory effects. Prove at least one nontrivial loop replacement without bounded unrolling as the justification. Examples must exercise the context theorem rather than bypass it.

### M3 — Certificate-bound installation

**Work:** connect formal artifacts to the build; audit proof dependencies; reject missing assumptions, unsupported features and stale certificates; record the exact installed module. Decide which import/export components remain trusted and which receive verified checks.

**Deliverables:** certificate format, checking driver, installer, audit report and strict CI mode.

**Acceptance:** a valid proof permits the corresponding replacement. Mutating the candidate, baseline, relevant attributes, data layout or contracts invalidates the certificate. An invalid proof and an unsupported module cannot produce an accepted replacement. The build falls back or fails according to policy.

### M4 — First end-to-end semantic replacement

**Work:** connect M0–M3 for a Lean-produced memory-using loop. Use a candidate with genuinely different control flow, rather than only an arithmetic peephole change.

**Deliverables:** original and candidate IR, complete refinement proof, contextual installation proof, rebuilt executable, correctness tests and benchmark record.

**Acceptance:** a clean build compiles Lean, checks the certificate, installs the candidate and executes the result. The local proof and module theorem are checked without `sorry`, project-specific correctness axioms or unchecked solver verdicts. Runtime tests complement the proof and are not presented as certification.

### M5 — Physical representation change

**Work:** replace an implementation using one private layout with another, for example an intermediate array of records with packed or separated arrays. Account for allocation, lifetime, bounds, alignment, aliasing and unchanged surrounding memory.

**Deliverables:** reusable heap-relation lemmas, a layout-changing candidate, proof and build example.

**Acceptance:** source and target demonstrably use different physical representations; their correspondence is expressed in the refinement proof. The external ABI and ownership contract remain satisfied, or the certified unit includes verified adapters and affected callers.

### M6 — SIMD and LLM candidate generation

**Work:** add vector operations and required intrinsic semantics; handle tails and target features; integrate an LLM candidate-and-proof proposal loop. Reuse scalar and layout proofs as library material.

**Deliverables:** supported vector fragment, scalar-to-vector example, bounded-resource synthesis driver and reproducible performance corpus.

**Acceptance:** an independently generated candidate is certified and installed. Its proof covers all admissible lengths, including empty input and tails, without unproved padding assumptions. Wrong candidates are rejected. Report proof success rate, proof-checking cost and execution performance separately.

M0 and semantic exploration should inform one another. M2 depends on a coherent M1 semantics; M3 can be prototyped during M2. M4 is the first integrated release gate. M5 establishes the representation-changing objective; M6 expands implementation freedom and candidate throughput.

## 7. Trust and assurance

The initial certified claim is:

> Under the checked environment assumptions and the chosen LLVM semantics, the installed module refines the captured original module.

Connecting this claim to the original Lean specification and the final machine executable additionally relies on Lean lowering, Clang, the downstream LLVM compiler, linking and runtime contracts. The selected semantic model's agreement with actual LLVM is also an explicit assurance obligation.

| Item | Initial treatment |
|---|---|
| Lean kernel and approved logical axioms | Trusted proof-checking foundation |
| Semantic definitions | Audited statement of intended LLVM behaviour |
| Refinement and replacement theorems | Proved in Lean |
| LLM, optimiser and proof search | Untrusted; proposals require checking |
| SMT or other automation | Proof reconstruction or checked certificates required for acceptance |
| Import/export and installation | Minimise, audit and explicitly list trusted portions until verified |
| External/runtime calls | Model through explicit contracts; justify their use at boundaries |
| Lean lowering, Clang and LLVM backend | Trusted in the initial programme |

A proved source specification does not erase these compiler assumptions. Conversely, the project need not first verify the entire Lean compiler to deliver certified LLVM replacement.

## 8. Validation and release policy

Maintain a corpus combining small semantic cases, real compiler output and adversarial replacement attempts. Cover overflow flags, poison propagation, invalid accesses, aliasing, alignment, lifetime, zero-length inputs, loop divergence, external effects and target mismatches as the supported fragment grows.

Use negative tests to ensure the installation gate cannot accept stale or unrelated proofs. Include candidates that return the right value while corrupting memory, omit a tail case, or strengthen preconditions without justification.

For performance, record toolchain, hardware, flags, corpus and repeated measurements. Compare baseline, ordinary compiler optimisation and certified candidate. Correctness acceptance must not depend on whether the candidate is faster; installation as an optimisation may additionally require a chosen performance threshold.

A release requires documented feature coverage, a clean reproducible example, audited proof dependencies, an explicit trust ledger and a regression run. Unsupported inputs must have a clear diagnostic and conservative outcome.

## 9. Main risks and responses

| Risk | Response |
|---|---|
| Real compiler output exceeds the semantics | Inventory actual output first; extend deliberately; reject unsupported features |
| A full Vellvm port delays integration indefinitely | Port a coherent vertical slice; keep M4 as the first release gate |
| Local refinement does not compose | Make the contextual theorem a prerequisite for certified installation |
| Memory proofs become bespoke and expensive | Invest in framing, ownership and reusable representation relations at M2/M5 |
| Runtime calls dominate proof effort | Begin with a narrow boundary, then expand contracts and certified units |
| LLM candidates are correct but difficult to prove | Supply invariant and heap-relation templates; permit proof guidance; retain baseline on failure |
| LLVM versions or attributes drift | Pin versions and configurations; require a compatibility review for upgrades |
| Correct proof refers to different installed bytes | Bind artifacts and semantic configuration; audit import/export and installation |
| Refinement is vacuous because baseline assumptions imply UB | Check contract satisfiability and definedness on the intended domain; review specifications explicitly |

## 10. Delivery discipline and first work package

Organise work around three responsibilities: semantics/refinement, compiler integration/artifact fidelity, and examples/proof automation. These are responsibilities, not fixed staffing estimates. Estimate schedule and effort after M0 and a small M1/M2 proof spike reveal actual IR coverage and the cost of the memory model.

The first work package is:

1. Select one Lean application and a memory-using function boundary.
2. Capture its emitted LLVM and enumerate the required semantics.
3. Choose a structurally different replacement and write its boundary contract.
4. Identify which Vellvm definitions and theorems support that pair and where new theory is needed.
5. Specify the local and contextual theorem statements before building extensive proof automation.
6. Implement the identity installation path and versioned manifest.
7. Use the evidence to fix the M1–M4 scope and estimate delivery.

The programme succeeds when independently authored implementations can enter a normal Lean build only through a checked semantic refinement gate. A faster parser, an LLVM interpreter or a collection of peephole theorems can support that outcome, but none alone constitutes it.

## 11. Milestone status

This section records where the repository stands against the gates above.  It
does not change them: an item listed as open is unmet, and no milestone is
accepted on the strength of a narrower result.

- **M0 — met as integration evidence.** The probes build, select, install and
  run, and inspection shows the selected body is the installed one
  (`probes/install/`, `probes/app/`).
- **M1 — partly met.** The modelled fragment has a step semantics, a parser that
  refuses the constructs it knows it does not model (instructions, block
  structure and function-definition headers), and differential tests against the
  pinned toolchain.  Poison, provenance and underdefined values are not modelled,
  the semantics' agreement with LLVM remains an explicit obligation, and
  declaration headers are not attribute-checked yet.
- **M2 — open.** Refinement is exact (`Refines`) plus a framed relation
  (`RefinesWithin`, `AgreesOutsideMem`, `AllocFrame` in
  `LeanLLVM/Frames.lean`) that compares the returned value and the bytes outside
  a footprint read off the allocator state.  Open: a general loop or recursion
  rule — the loop's induction is a proof about its own fixture — memory-effectful
  call environments, and a `replaceFunction_sound`-style module theorem for a
  memory-using callee.  The contextual theorem covers one pure caller
  (`LeanLLVM/Vellum/SeamContext.lean`).
- **M3 — partly met; certificate-bound installation open.** The selector
  (`probes/install/select.sh`) verifies hashes, fixture rebuilds and target
  configuration, and accepts a unit only when the manifest's theorem covers that
  unit.  The memory-backed loop is refused on exactly that ground: no checked
  theorem covers it, and a differential transcript ending `RESULT: PASS` is
  never treated as proof.  Open: a serialized proof artifact generated from
  kernel checking, rejection tests that mutate that artifact, and a semantic
  attribute policy richer than `attributes=reject` over attribute-free fixtures.
- **M4 — open.** The loop fixture (`probes/install/ir/loop.ll`) is printed from
  the Lean AST (`LeanLLVM/Vellum/CommaMaskLoopBody.lean`) by
  `lake exe leanllvm-loop-emit` through `LeanLLVM.Function.render`, and
  `capture.sh` regenerates it; the correctness and framed-memory theorems are
  pinned to that AST by a parsed `#guard`, so the text they are about is what
  the AST renders to.  That emission is the framework's own printer, not Lean's
  native compiler: a memory-using loop produced by `lean -c`, lowered by clang
  and related to a Lean AST is still unproved.  The repository also has no
  memory-aware module theorem and no benchmark record.  The M4 acceptance
  conditions — a loop certified from the Lean compilation chain, a contextual
  installation proof including memory effects, a checked certificate and
  benchmark measurements — are therefore unmet.

## References and provenance

- [Vellvm development structure](https://vellvm.github.io/vellvm/structure/) — semantics, refinement layers and open-control-flow reasoning; consulted in the preceding design discussion.
- [Vellvm compatibility and limitations](https://vellvm.github.io/vellvm/faq/) — scope and known unsupported features; consulted in the preceding design discussion.
- [LLVM language reference](https://llvm.org/docs/LangRef.html) — resolve to the pinned toolchain version during M0.
- `simd-recogniser-options.md` — supplied design note defining Options A–E. Its repository observations are input claims, not independently reproduced by this programme document.

The architecture, milestones and acceptance gates above are proposed engineering decisions. They do not assert that the framework or its required theorems already exist.
