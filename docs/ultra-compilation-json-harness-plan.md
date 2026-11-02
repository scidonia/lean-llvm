# Ultra-Compilation: certified SIMD JSON parsing from Lean

**Date:** 2 November 2026  
**Audience:** implementation and proof harness  
**Status:** executable development plan; repository capabilities must be audited before assigning completion status.

## 1. Mission and success condition

Build a fully validating JSON parser specified and verified in Lean, then replace selected compiled critical sections with independently produced SIMD implementations certified by low-level semantic refinement.

The intended compilation path is:

**Verified Lean implementation → generated C → baseline LLVM → checked replacement → LLVM optimisation/backend → executable.**

The candidate may change algorithms, control flow, private layout and vectorisation. It need not be derived from a fixed rewrite sequence. The harness may use proved transformations, manual implementation, synthesis or an LLM to find candidates and proofs. Acceptance depends on the certificate for the installed artifact, independently of its origin.

The first decisive result is a complete parser with a certified SIMD scanner and measured end-to-end improvement. The subsequent performance target is competitiveness with a mature native parser on equivalent work. No speedup or parity with simdjson is assumed in advance.

The central claim is that verified Lean source can retain its guarantee while selected sections execute as aggressively optimised low-level code, under explicitly stated compiler and runtime trust assumptions.

## 2. Operating instructions for the harness

1. Read the destination repositories' `AGENTS.md` and existing plans. Inspect actual definitions, tests, build commands and proof dependencies before implementing replacements.
2. Keep JSON application work separate from reusable lean-llvm semantics and certificate infrastructure. Pin their dependency commits. Do not import unrelated ownership or LeanIn results as evidence that lean-llvm already supports a feature.
3. Create a capability ledger with four statuses: **implemented and checked**, **implemented but unverified**, **missing**, **out of scope**. Record evidence, commit and command for each implemented claim.
4. Execute milestones in dependency order. Continue independent work when an integration gate is blocked, but report the exact missing theorem or feature rather than replacing it with an assumption.
5. Preserve fixed specifications and theorem statements during candidate/proof search. A candidate agent must not weaken preconditions, alter the baseline or replace a failed theorem with an axiom.
6. Keep all completed work, proofs, fixtures and reproducibility scripts in the repositories. Temporary benchmark binaries and candidate scratch space need not be committed.
7. Use existing test/build conventions. The command names proposed below are interfaces to implement or map to existing commands, not claims about current tools.

### First execution session

- Identify the JSON project location and lean-llvm checkout/dependency.
- Record toolchain, target and repository commits.
- Build both unchanged and record outcomes.
- Locate `Beh`, `Refines`, call/module semantics, memory semantics, vector semantics, any replacement theorem and installer.
- Select the first pure block operation and the subsequent memory-using scanner boundary.
- Write `docs/capabilities.md`, `docs/contract.md` and a task ledger before extending the optimiser.

If repository access is unavailable, complete the contract and task design, mark implementation audit blocked, and request the exact missing checkout or access. Do not report inferred repository state as inspected fact.

## 3. Fixed scope and contract

### Initial public API

Parse one complete UTF-8 JSON document supplied as bytes. Accept the four JSON whitespace characters before and after it; reject trailing non-whitespace and multiple top-level documents. NDJSON, incremental network input and concurrent parsing are later extensions.

Produce a compact token tape with source spans, plus a verified decoding/view operation. Preserve array order and object member order, including duplicate keys. Preserve number lexemes and validate their grammar; conversion to binary floating point is a separate optional API and proof obligation.

The logical JSON value model should distinguish null, booleans, strings, exact number lexemes, arrays and ordered object members. Use an explicit inductive or equivalent semantic relation over bytes. Avoid defining validity solely as whatever the reference parser happens to accept.

### Policy decisions to settle in `docs/contract.md`

Default choices for the first implementation:

| Concern | Initial decision |
| --- | --- |
| Input encoding | Strict UTF-8; no malformed byte sequences or overlong encodings |
| Byte-order mark | Reject; document this API policy |
| String escapes | Validate standard escapes and four-hex-digit Unicode escapes |
| Unicode surrogates | Require well-formed pairs; reject unpaired escaped surrogates; identify this as the chosen Unicode policy |
| Numbers | Validate JSON number syntax and preserve the exact source lexeme; no NaN/Infinity extension |
| Duplicate object keys | Preserve, without implicit last-wins conversion to a map |
| Output | Tape with checked spans and a unique decoded logical value |
| Diagnostics | Syntax rejection required; diagnostic text and exact earliest-error location are not part of the first equivalence contract |
| Limits | Explicit input, depth and output-capacity limits; distinguish limit exhaustion from invalid JSON |
| Parser reuse | Supported through explicitly owned reusable buffers; benchmark fresh and reused modes separately |

Check these policies against the chosen JSON reference standard and record deliberate restrictions. In particular, do not claim that rejecting unpaired surrogate escapes recognises every grammar-legal JSON text without qualification.

The ideal recogniser theorem concerns arbitrary finite inputs. A bounded executable API has completeness only inside its documented resource limits. `OutOfCapacity`, `DepthLimit` and allocation failure must not be conflated with a proof that the input is invalid.

## 4. Architecture and proof decomposition

### Reference implementation

Write a clear scalar Lean implementation over bytes, with separate scanner, grammar parser and tape builder. Keep its specification simple enough to reason about. Do not require it to be fast or structurally identical to the SIMD candidate.

### Optimised implementation

Use block scanning to produce structural information, then parse that information and the original bytes into a tape. Stage 1 does not by itself establish JSON validity: grammar checks, escape decoding and number syntax remain accounted for in the complete parser.

The scanner contract must specify exactly which indexes are emitted. Punctuation alone is insufficient: define how quotes and starts of scalar tokens are represented, as required by the consumer.

Candidate layouts may use masks, packed indexes and explicit output buffers internally. At the first installation boundary, preserve the public ABI and ownership contract. If a layout change crosses that boundary, certify adapters or enlarge the replacement unit to include affected callers.

### Required theorem families

The names below are proposed names; adapt them to existing conventions without changing their intended strength.

1. **Reference correctness:** `parseRef_sound` and `parseRef_complete` connect acceptance/decoding to the independent byte-level JSON semantics, subject to policy and limits.
2. **Tape interpretation:** `tape_valid` and `decodeTape_correct` establish well-formed spans, nesting, values and the decoded meaning. Source-backed tapes retain the input for the required lifetime.
3. **Block correctness:** `scanBlock_correct` relates the candidate block operation to a scalar transition, including next state and error information.
4. **Whole-scan correctness:** `scan_simd_refines_scalar` composes blocks, tails and end-of-input finalisation.
5. **Actual LLVM refinement:** `scannerLLVM_refines` concerns the imported baseline/candidate bodies, not only separate Lean algorithm models.
6. **Contextual replacement:** `replaceScanner_sound` transports the local theorem through the parser caller and linking environment.
7. **Build acceptance:** the installation gate binds those theorems and assumptions to the artifacts compiled into the executable.

State the local relation schematically as `Γ ⊢ candidate ⊑ baseline`. The environment includes bounds, ownership, external calls, target configuration and admissible initial states. Cover observable results, memory effects, definedness and termination/divergence. Matching return values only when both executions terminate is too weak.

For the current deterministic scalar reference, exclude introducing undefined behaviour or divergence on an admissible input where the reference terminates normally.

## 5. The first substantial replacement: stateful scanning

Use a transition contract of the conceptual form:

```text
scanBlock(state, block, validByteCount)
  → (nextState, structuralInformation, validationStatus)
```

The state must capture cross-block dependencies, including:

- whether the current position is inside a string;
- whether a trailing backslash run affects escaping of the next byte;
- UTF-8 continuation requirements and restrictions on pending sequences;
- any additional predecessor information required to identify token starts.

Specify the invariant that makes each state admissible. Arbitrary bit patterns in a state record need not represent reachable scanner states. If local refinement assumes admissibility, prove initialisation and preservation so the caller discharges the assumption.

Prove block composition and an explicit finalisation rule. A block scanner may defer errors across a boundary; end-of-input must reject incomplete strings, escape sequences and UTF-8 sequences appropriately. The grammar stage handles unmatched JSON containers.

Do not require the block scanner to fully decode `\uXXXX` escapes if the grammar/string stage handles them. Record exactly which stage validates each rule and prove no rule is lost between stages.

### Lane-mask regression

Do not reuse the subtraction-based zero-byte idiom as an exact per-byte mask without a proof. For comma classification, the expression

```text
m = x XOR 0x2C2C2C2C2C2C2C2C
(m - 0x0101010101010101) AND NOT m AND 0x8080808080808080
```

can set an adjacent nonmatching lane because of borrowing. With input `0x0000000000002D2C`, it returns `0x8080`, whereas the exact high-bit comma mask is `0x0080`. Include this regression and prove the actual mask contract.

## 6. SIMD and memory contract

Use one backend initially: **x86-64, little-endian, AVX2**, unless the capability audit finds a concrete incompatibility. Record any additional required features separately. AVX2 does not imply every optional instruction a candidate might use. If the available machine lacks the backend, run correctness work where possible and report target performance as unmeasured.

Prefer portable LLVM vector operations where practical, adding precisely modelled target intrinsics only when required. Inventory the actual emitted IR before committing to a semantics subset.

Required features may include integer vectors, comparisons, bitwise operations, shifts, casts, element operations, shuffles, vector loads/stores, mask extraction, pointer arithmetic, control-flow joins and loops. Reject unsupported instructions, flags, intrinsics and semantic attributes until they have a justified treatment.

Prove three layers separately:

| Layer | Obligation |
| --- | --- |
| Vector algorithm | Per-lane operations, masks and carried state implement the scalar transition |
| Low-level memory | Accesses are valid; output capacity is sufficient; input and unrelated memory are preserved |
| Instruction connection | The actual imported LLVM instructions implement the proved transition under the chosen semantics |

### Buffers and tails

The external API accepts ordinary unpadded input. Initially use complete vector loads only when enough readable bytes remain, and a scalar or safely copied tail. An internal padded-buffer path may follow, with its allocation, initialisation and length contract proved and any copy cost measured.

For every memory-using replacement specify:

- input logical length and readable extent;
- output capacity and maximum produced indexes/tokens;
- read/write footprint, alias restrictions and ownership;
- permitted alignment and actual load alignment;
- input/output lifetime and pointer provenance;
- fixed-width index overflow constraints;
- behaviour on insufficient output capacity and resource exhaustion.

Masking the result of an out-of-bounds vector load does not make the load valid. Proofs quantify over every allowed alignment and tail length, not only padded benchmark buffers.

## 7. Compilation seam and artifact fidelity

Use the previously investigated opaque external seam as the initial installation mechanism:

1. Compile a verified scalar Lean definition into a separate baseline implementation unit.
2. Have the caller reference a compatible external declaration so its optimiser cannot inline the baseline before replacement.
3. Capture baseline and candidate LLVM and certify them under the same boundary contract.
4. Install the accepted candidate; otherwise link the baseline or fail in strict certification mode.
5. Resume normal LLVM optimisation, linking and execution.

An opaque declaration alone does not connect execution to the logical Lean function. Audit and document that bridge: prove it where the framework permits, or identify the compiler/FFI correspondence as an explicit initial trust assumption. No hidden source-to-extern axiom may be counted as a proved end-to-end result.

Check actual calling conventions, unboxed versus boxed arguments, return conventions, buffer representation and any generated wrappers. Never assume a Lean `ByteArray` has a raw pointer/length ABI. An adapter can remain outside the first local certificate, but its correctness assumptions and performance cost remain visible.

Install before cross-unit inlining or LTO can consume the baseline body. Inlining after certified installation is allowed under the downstream compiler assumption.

The certification record binds content, theorem, semantic version, source commits, toolchains, target triple, data layout, feature set, semantic attributes, declarations, call-site assumptions and external contracts. Hashes prevent stale pairing; they do not prove importer/exporter correctness.

Attributes such as `range`, `noundef` and `noalias` require a sound policy. Do not silently ignore them or merely remove them from the candidate after callers have already used them. Preserve their obligations, rebuild under justified weaker assumptions, or reject the artifact. Distinguish semantic metadata from optimisation hints.

Report semantic acceptance and replacement coverage separately. Residual execution of the correct baseline is a performance-coverage issue unless it exposes another correctness fault. Establish intended call-site routing by construction and inspection, rather than searching binaries for every baseline-shaped instruction sequence.

## 8. Milestones and release gates

| ID | Work package | Exit gate |
| --- | --- | --- |
| J0 | Audit repositories/toolchain, freeze contract, identify seam | Reproducible unchanged builds; capability ledger; actual IR inventory; written trust ledger |
| J1 | Independent semantics, scalar scanner/parser and tape view | Soundness/completeness under policy/limits; tape meaning established; scalar executable runs fixtures |
| J2 | Pure block candidate and restricted contextual integration | Structurally different pure candidate certified at actual LLVM level and called from the application through a checked restricted context theorem |
| J3 | Stateful SIMD scanner model | Classification, quote/escape logic, UTF-8 state, block composition and tails proved against scalar transitions |
| J4 | Memory-using LLVM scanner and installation | Required memory/vector semantics, actual LLVM refinement, caller theorem and artifact-bound installation pass all checks |
| J5 | Complete parser demonstration | Parser theorem composes with installed scanner; complete executable passes adversarial and differential corpus; measured full-parser improvement |
| J6 | Performance refinement and synthesis | Additional bottlenecks addressed through certificates; fixed-budget synthesis/transform comparisons; reproducible results against native reference |

J2 is an integration checkpoint, not completion of the memory-refinement objective. J1 and early block-model work can progress independently after interface decisions; J4 requires the relevant semantic foundations rather than a whole Vellvm port.

### J0 tasks

- Record current supported LLVM subset, theorem statements and axiom dependencies.
- Inventory unsupported output constructs and separate application runtime noise from operations inside the selected unit.
- Capture baseline C/LLVM and show the intended call survives caller optimisation.
- Establish a repeatable benchmark driver before changing performance-sensitive code.

### J1 tasks

- Implement grammar, byte/string semantics, number grammar and explicit resource outcomes.
- Prove scalar scanning and parsing; define and verify tape interpretation.
- Reuse existing verified components only after checking their exact Unicode, number and duplicate-key policies.

### J2–J4 tasks

- Start with exact byte classification, then add string masks and carried state, then UTF-8 validation and index emission.
- Reuse existing certificate/context machinery where it meets the contract; add missing calls, memory, vectors or proof rules explicitly.
- Certify unbounded iteration through invariants/induction or suitable simulation, not finite test coverage or bounded loop unrolling.
- Produce proofs concerning the captured IR. Candidate C, Rust or intrinsics source is permitted, but certify its resulting LLVM.

### J5–J6 tasks

- Verify every stage's validation responsibilities compose into complete acceptance/rejection.
- Profile remaining costs, including adapters, indexing, string decoding, tape allocation and number work.
- Optimise measured bottlenecks; do not assume scanner speed determines parser speed.
- Retain rejected and unresolved candidates with failure reasons for later evaluation.

## 9. Harness tasks, outputs and proposed commands

Use existing repository layout when suitable. Otherwise introduce modules with these responsibilities:

```text
JsonSpec/           independent semantics and policies
JsonRef/            scalar implementation and correctness
JsonTape/           tape representation and decoded view
JsonScan/           scalar/vector block models and composition
JsonCertificates/   actual LLVM pair proofs and caller instantiations
bench/              corpus manifests and equivalent-work benchmark drivers
scripts/            capture, certify, install, build and audit commands
docs/               capabilities, contracts, trust and task status
```

Reusable compiler semantics and general contextual theorems belong in lean-llvm, pinned by the application dependency. The names above are proposed modules, not assertions about existing paths.

Expose a small command interface, mapped to native build tooling:

| Proposed command | Responsibility |
| --- | --- |
| `audit` | Build, inspect dependencies, report capabilities and trust assumptions |
| `capture-baseline` | Emit baseline artifacts and semantic configuration |
| `check-certificates` | Kernel-check fixed statements and audit permitted dependencies |
| `build-certified --strict` | Reject stale, unsupported or uncertified replacements |
| `test-correctness` | Run corpus, malformed inputs and boundary/negative tests |
| `bench` | Produce raw repeated measurements and configuration records |

These commands must be implemented or mapped during J0; do not invoke imaginary binaries and report them as existing.

For every task record: ID, dependency, fixed goal, changed files, command, outcome, proof dependencies, evidence and next blocker. At each milestone produce a short status report that distinguishes completed theorems, runtime tests, assumptions and unresolved cases.

## 10. Candidate search and proof acceptance

Use a fixed-budget loop:

1. Freeze baseline, contract, target and theorem statement.
2. Propose a candidate through proved transformations, independent synthesis or both.
3. Reject malformed or unsupported IR before proof work.
4. Run cheap differential checks to discard obvious mistakes; these are filters, not certificates.
5. Generate invariants, heap relations and proof terms for the fixed obligation.
6. Check using Lean and audit transitive axiom dependencies.
7. Benchmark only candidates eligible for installation, or label uncertified exploration separately.
8. Install an accepted performant candidate; retain baseline on timeout or failure.

No `sorry`, `admit`, candidate-specific correctness axioms or unchecked solver verdicts may justify acceptance. Use a documented approved axiom policy. Proof-producing or certificate-checking automation is allowed; an external tool reporting success without a checked semantic connection is not.

Resource-limited proof search is allowed. Unknown is not valid, and failed proof search does not establish that a candidate is incorrect. Keep invalid and unresolved outcomes separate.

Proved simplification and supercompilation steps can be interleaved with independently synthesised replacements. An `eutt` proof counts only at the semantic layer where it is stated and after the required interpretation/context transport. It does not itself establish lower execution cost.

## 11. Correctness and rejection tests

Maintain a versioned corpus and policy annotations. Expected tests include:

- empty input, whitespace-only input, scalar documents and trailing data;
- punctuation inside strings, escaped quotes and backslash runs crossing every block boundary;
- valid and malformed UTF-8, continuation bytes and truncation at every position;
- Unicode escape pairs, unpaired surrogates, invalid hex digits and unescaped control bytes;
- numeric leading zeros, missing fraction/exponent digits and very long lexemes;
- duplicate keys, deep nesting and explicit capacity/depth exhaustion;
- lengths around every vector/block boundary, every supported alignment and tails near inaccessible guard pages;
- output-capacity limits, index overflow boundaries and forbidden input/output aliasing;
- the exact-mask subtraction counterexample in §5.

Add negative installation tests: mutate the baseline, candidate, target, call-site contract, feature flags or relevant attributes after certification and require rejection. Include candidate mutations that omit tails, fail cross-block escaping, return plausible indexes while corrupting memory, or introduce extra preconditions.

Use the JSONTestSuite corpus where suitable, pin its revision and classify policy-sensitive cases. Differential comparison is informative only where semantics agree. Boundary tests and sanitizers complement formal proofs; they do not replace them.

## 12. Performance evaluation

Measure both scanner throughput and complete parsing. Use a pinned simdjson release as the native performance reference, not as the normative correctness oracle.

Compare:

1. Scalar verified Lean baseline compiled normally.
2. Equivalent baseline with ordinary toolchain optimisation/auto-vectorisation.
3. Certified SIMD implementation.
4. simdjson doing equivalent validation and output work where an equivalent mode exists.

Separate validation-only, tape construction and materialised-value measurements. A lexeme-preserving parser must not claim a direct parsing speed win against a baseline doing additional floating-point conversion or object construction. For API differences that cannot be aligned, report separate measurements and the exact work performed.

Use small-message and large-document workloads, string-heavy, escape-heavy, UTF-8-heavy, numeric and mixed data. Keep invalid-input performance separate. Consume outputs to prevent dead-code elimination; include adapters and input preparation; report fresh and reused-buffer modes.

Record hardware, CPU features, frequency policy where controlled, compiler options, source/corpus hashes, warmup, repetitions and raw results. Report cycles/byte, throughput, latency distributions for small documents, allocations/peak memory, and compile/proof-check time. Do not select a backend from assumed instruction count alone.

For the hybrid optimisation claim, compare proved transforms only, synthesis only and the combination under equal search budgets. Report attempted candidates, valid certificates, invalid/unresolved cases, certification cost and achieved performance. Never hide failed cases from the denominator.

## 13. Trust ledger and final acceptance

The initial executable guarantee relies on Lean's kernel/approved axioms, the formal model, source lowering, Clang/LLVM, runtime and ABI correspondence, linking and hardware. Importer/exporter/installer trust must be explicit until verified. A successful Lean proof does not automatically establish that the formal LLVM semantics matches every behaviour of the real toolchain.

The final release gate requires:

- independent JSON semantics and verified scalar implementation;
- defined Unicode, number, duplicate-key and resource policies;
- proved tape interpretation and stateful SIMD scanning;
- memory safety and state/frame preservation under the documented boundary;
- refinement of actual baseline/candidate LLVM, with relevant semantic attributes;
- contextual transport to the parser and discharged caller assumptions;
- certificate-bound installation in a real Lean build;
- clean proof-dependency audit and reproducible correctness suite;
- full-parser benchmark evidence with equivalent-work qualifications;
- a precise list of remaining trusted components and unsupported features.

If SIMD classification alone is complete, report that milestone. If only a Lean model is proved, report model correctness. Reserve “certified compiled SIMD parser” for the completed artifact and context connection.

## 14. References and provenance

These are starting references, not imported correctness assumptions. Pin versions during J0.

- [RFC 8259: JSON](https://www.rfc-editor.org/rfc/rfc8259)
- [Parsing Gigabytes of JSON per Second](https://arxiv.org/abs/1902.08318)
- [simdjson repository](https://github.com/simdjson/simdjson)
- [simdjson performance notes](https://simdjson.org/api/4.6.4/md_doc_2performance.html)
- [JSONTestSuite](https://github.com/nst/JSONTestSuite)
- [LLVM language reference](https://llvm.org/docs/LangRef.html)
- [Vellvm development structure](https://vellvm.github.io/vellvm/structure/)
- [Trivet: LLVM Translation Validation Automated with Large Language Models and Lean](https://arxiv.org/abs/2609.19583)

Related project documents: `lean-vellum-development-programme.md`, `m0-runtime-noise-report.md` and `m0-runtime-noise-review-handoff.md`. Reconcile their milestones with the actual repositories; their existence does not imply the implementation gates above have passed.
