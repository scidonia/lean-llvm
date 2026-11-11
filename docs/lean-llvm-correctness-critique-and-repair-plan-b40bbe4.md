# lean-llvm: correctness critique and repair plan

Reviewed revision: `b40bbe4919678557df61284c86e11bf90b598ca4`  
Review date: 11 November 2026  
Repository: <https://github.com/scidonia/lean-llvm>

## 1. Assessment

The repository contains substantial formal work: an independently specified scalar JSON parser, proofs relating parsing and tape decoding to that specification, executable LLVM semantics, certified optimisation passes, and proofs for several emitted SIMD kernels. In particular, the escape expander has an unconditional `Satisfies` theorem; it should not be described as still depending on the earlier open assembly bundle.

It does **not yet establish an end-to-end certified SIMD replacement for the Lean JSON parser**. The remaining obstacles include unfinished stage-2 and pipeline proofs, an unusable semantic premise in the final parser theorem, and mismatches between the framework's LLVM model/exporter and real LLVM.

The appropriate near-term goal is a precisely scoped replacement theorem and one working application route. Completing a few foundational obligations is more valuable than adding further kernel examples before those obligations are settled.

This review distinguishes four kinds of evidence:

- **Observed:** a command was run on the reviewed checkout and its result recorded.
- **Source finding:** a defect or limitation follows from inspection of the definitions; a corresponding Lean or LLVM regression was not executed here.
- **Implemented proof:** a theorem and proof are present in source; this review did not independently rebuild them.
- **Open obligation:** a statement, record or conditional composition exists, but its required instance is absent.

No Nix, Lean/Lake or Clang toolchain was available in the review environment. Full proof builds and native JSON differential routes were therefore not rerun. The checkout was not modified.

## 2. Prioritised findings

| ID | Priority | Finding | Evidence | Consequence |
|---|---|---|---|---|
| F1 | P1 | Final parser theorem assumes mutually contradictory verdict facts | Source finding | Its premise cannot be discharged, even if the implementation is correct |
| F2 | P1 | `phi` instructions read sequentially updated environments | Source finding | The LLVM model disagrees with real LLVM on valid loop programs |
| F3 | P1 | Printer adds `inbounds`; index widths and alignment information are lost | Source finding | A model-preserving transformation or identity round trip can change real LLVM semantics or produce invalid IR |
| F4 | P1 | Stage-2 correctness, pipeline tail and parser/event correspondence remain open | Open obligations | Individual kernel proofs do not establish complete JSON correctness |
| F5 | P2 | JSON scanner selection route is unsupported | Observed; documented scaffolding | No working certified installation route for this JSON scanner |
| F6 | P2 | Generic refinement permits a divergent target vacuously | Source finding; deliberate relation definition | Behaviour inclusion alone is insufficient for the intended replacement guarantee |
| F7 | P2 | Artifact binding and semantic conformance exceed the theorem axiom ledger | Source finding | A clean axiom footprint does not imply a kernel-only end-to-end trust surface |

P1 means resolve before claiming general certified LLVM replacement or complete certified JSON replacement. P2 means resolve or explicitly scope the public guarantee. An open obligation is not evidence that the native implementation necessarily gives a wrong answer.

## 3. F1: the final semantic premise is impossible

Source: [JsonPipelineRefine.lean, `pipeline_satisfies_of_parser`](https://github.com/scidonia/lean-llvm/blob/b40bbe4/LeanLLVM/Vellum/JsonPipelineRefine.lean#L1081).

The theorem takes, schematically:

```text
hsem : ∀ mem bs verdict returnedMemory dst ev err,
  readBytes mem base bs.length = some bs →
  ParserHalf eventRel bs verdict returnedMemory dst ev err
```

`ParserHalf` includes:

```text
verdict = 1 ↔ ∃ tape, parseBytes default bs = ok tape
```

Nothing in the premise connects `verdict` or `returnedMemory` to an execution. For the same input, instantiate it once at verdict `1` and once at verdict `0`. The first instance requires acceptance; the second requires non-acceptance.

The buffer-read premises inside `ParserHalf` do not block this argument: select zero-length arena and event reads, which succeed in every memory. In the universal premise of `pipeline_satisfies_of_parser`, even the input-read premise can be instantiated with empty input and empty memory. The contradiction does not require computing the parser's answer.

`pipeline_units_finalisation` has the same underlying problem: its semantic premise ranges over arbitrary verdicts and output memories for an input that can be read. Given its staged input, it similarly asks for incompatible facts.

This is a valid implication from an impossible assumption, rather than an inconsistency in Lean. A standard axiom footprint will not detect it.

### Suggested repair

1. State the parser correspondence at the **actual input, arguments and outcome** of the pipeline run.
2. Bind document, destination, event buffer and error slot to the fields in that argument list.
3. Require the relevant staging and parser-domain conditions.
4. Derive the correspondence from the stage-1 stream invariant, UTF-8 result and stage-2 semantic postcondition.
5. Keep the remaining missing proof visible as an explicit obligation until it is discharged.

A useful factoring is an outcome-indexed predicate, conceptually:

```text
ParserHalfForOutcome eventRel base args inputMemory outcome
```

It extracts the document, verdict and output memory from that particular call. Its producer must take an execution or reachability hypothesis. It must not assert the parser's answer for unrelated outputs.

### Acceptance checks

- Prove a small negative lemma showing that the old universally quantified `hsem` implies `False`.
- Replace both affected semantic premises.
- Instantiate the repaired correspondence on an actual accepting and an actual refusing execution.
- Require a final theorem for the concrete pipeline environment and body, with no residual assumption equivalent to the desired parser correctness result.

## 4. F2: `phi` evaluation needs an incoming-environment snapshot

Sources: [Semantics.lean, `evalInstr`'s `phi` case](https://github.com/scidonia/lean-llvm/blob/b40bbe4/LeanLLVM/Semantics.lean#L586) and [`denoteCode`](https://github.com/scidonia/lean-llvm/blob/b40bbe4/LeanLLVM/Semantics.lean#L825).

`evalInstr` selects an incoming operand from the current environment and immediately binds its destination. `denoteCode` passes that updated environment to the next instruction, including the next `phi`.

LLVM's incoming uses occur on the predecessor edge. Every leading `phi` therefore needs to read the environment arriving on that edge, before the current block's new destinations are installed. See the [LLVM language reference](https://llvm.org/docs/LangRef.html#phi-instruction).

### Minimal source-level counterexample

```llvm
define i32 @main() {
entry:
  br label %loop
loop:
  %a = phi i32 [ 1, %entry ], [ %b, %loop ]
  %b = phi i32 [ 2, %entry ], [ %a, %loop ]
  %i = phi i32 [ 0, %entry ], [ %j, %loop ]
  %j = add i32 %i, 1
  %again = icmp ult i32 %j, 2
  br i1 %again, label %loop, label %done
done:
  ret i32 %b
}
```

By the respective definitions, LLVM returns `1`: the second iteration swaps `(a, b)` from `(1, 2)` to `(2, 1)`. The current model returns `2`: it updates `a` to `2` and then reads that new value for `b`. These expected results are derived by inspection; the differential test was not executed in this review.

### Suggested repair

- Split the leading `phi` prefix from the rest of a basic block.
- Evaluate every selected incoming operand against one snapshot of the incoming state.
- Install all computed destination bindings only after evaluation of the group.
- Execute the remaining instructions using the resulting environment.
- Preserve the existing missing-predecessor and malformed-input policy, while distinguishing malformed LLVM from a disagreement on valid LLVM.

### Acceptance checks

- Add the swap program to both the model and native differential routes.
- Add a three-register cycle, self-carried values and a loop whose backedge comes from a different block.
- Establish that permuting independent leading `phi` instructions does not change the result.
- Rebuild existing loop and pipeline proofs against the corrected block semantics.

This is a general-model defect. It does not by itself establish that a particular JSON fixture encounters a cyclic `phi` dependency.

## 5. F3: preserve real LLVM meaning through parsing and printing

Source: [Printer.lean](https://github.com/scidonia/lean-llvm/blob/b40bbe4/LeanLLVM/Printer.lean#L124).

The parser drops whether a GEP was `inbounds`, while the printer emits every GEP with `inbounds`. That flag is a semantic promise. Adding it requires proof; a parser/printer round trip inside the simplified AST cannot justify it.

### Minimal source-level counterexample

```llvm
define i8 @roundtrip_gep() {
entry:
  %p = alloca i8
  store i8 7, ptr %p
  %q = getelementptr i8, ptr %p, i64 2
  %r = getelementptr i8, ptr %q, i64 -2
  %v = load i8, ptr %r
  ret i8 %v
}
```

Without `inbounds`, the address calculation can leave the one-byte allocation and return before dereferencing; the load reads `7`. Printing the first GEP as `inbounds` makes its out-of-object result poison, which propagates into the dereference. See [LLVM's GEP explanation](https://llvm.org/docs/GetElementPtr.html#what-happens-if-an-array-index-is-out-of-bounds).

This can occur with `--passes none`. It is an exporter correctness issue independent of pass proofs. Native execution is not guaranteed to expose it: an undefined transformed program may still appear to return `7`.

Two further losses require the same discipline:

- `gepIndexTy` prints register indices as `i64` regardless of their actual definition width. `laneIndexTy` similarly prints register lane indices as `i32`. The source documents assembler failures for such mismatches.
- Loads and stores do not retain explicit alignment. In LLVM, omitting alignment selects a default rather than meaning arbitrary byte alignment. Capture scripts acknowledge the distinction. A proof about an unaligned load under the model does not automatically justify recompiling its printed form.

### Suggested repair

Preserve operand types and semantic flags in the AST. Until `inbounds` has a model and a proof, emit an ordinary GEP; for a strict unsupported fragment, rejection is another defensible choice. Preserve load/store alignment or emit a justified weaker alignment. Audit accepted-and-dropped calling conventions, linkage and declaration attributes for equivalent exporter problems.

### Acceptance checks

- Add the GEP example as a definedness regression, not just an observed-return test.
- Assemble identity-round-tripped inputs with `i32` GEP indices and `i64` lane indices.
- Exercise deliberately misaligned buffers with explicit `align 1` vector accesses.
- Check both parsing and exporting against real LLVM validation.
- Treat text-to-AST-to-text preservation as a separate obligation from an AST pass's `Sound` theorem.

## 6. F4 and F5: what the JSON example currently establishes

| Component | Status at the reviewed revision | Remaining qualification |
|---|---|---|
| Scalar parser and tape semantics | Correctness proofs implemented | Against the repository's specification and policy, with explicit limits |
| SIMD mask unit | Emitted-body proofs implemented | Under the custom semantics, intrinsic environment and staging preconditions |
| Entry emitters | Emitted-body proofs implemented | Same semantic and staging boundary |
| UTF-8 stage | Emitted-body proofs implemented | A staged-window/prefix result; document finalisation remains a composition obligation |
| Escape list and expansion | Substantial proofs; unconditional expander theorem implemented | Does not supply the missing stage-2 grammar/value proof |
| Pipeline loop | Concrete loop and seed work implemented | Tail target remains a supplied premise |
| Stage 2 | C implementation and `Γ_stage2` record present | No proved emitted-body `stage2_satisfies` instance |
| Reference-parser correspondence | `Sigma_pipeline`, `ParserHalf`, conditional finalisation | Semantic producer absent; final theorem premise needs F1 repair |
| Lean JSON call using the native replacement | Not demonstrated by the public scalar entry point | `parseDocument` calls `parseBytes` directly |
| JSON scanner installation | Scaffold scenario fails | Selector does not recognise `json_scan` |

Relevant sources:

- [JsonUnitContracts.lean](https://github.com/scidonia/lean-llvm/blob/b40bbe4/LeanLLVM/Vellum/JsonUnitContracts.lean)
- [JsonEscapeExpandAssembly.lean](https://github.com/scidonia/lean-llvm/blob/b40bbe4/LeanLLVM/Vellum/JsonEscapeExpandAssembly.lean#L8254)
- [PipelineDischarge.lean](https://github.com/scidonia/lean-llvm/blob/b40bbe4/LeanLLVM/Vellum/PipelineDischarge.lean)
- [JsonStage2Contract.lean](https://github.com/scidonia/lean-llvm/blob/b40bbe4/LeanLLVM/Vellum/JsonStage2Contract.lean)
- [JsonPipelineSpec.lean](https://github.com/scidonia/lean-llvm/blob/b40bbe4/LeanLLVM/Vellum/JsonPipelineSpec.lean)
- [Parse.lean, public entry point](https://github.com/scidonia/lean-llvm/blob/b40bbe4/LeanLLVM/JSON/Parse.lean#L407)

### Keep the number representation decision explicit

The reference number value preserves a source lexeme; the native event contains eight binary64 bytes. Those are different observables. Number-conversion specification and modelling work exists, including the tier-3 rounding walk, but it must not be confused with an emitted-body proof for the complete stage-2 conversion path.

Choose one concrete correspondence:

1. **Lexeme-preserving replacement:** retain the number's source span/lexeme in the native output, leaving conversion outside the first replacement contract.
2. **Binary64 correspondence:** define the output abstraction explicitly through `strtodSpec` and prove the emitted conversion's complete selected path against it.

The first is a smaller proof target and matches the original lexeme-preserving API. The second is appropriate if binary64 output is a product requirement, but it cannot be presented as equality with a lexeme-valued result. A binary64 result also cannot reconstruct which lexeme was supplied.

### Respect the actual domain

The scalar defaults are 1 MiB input, 128 levels and 1 Mi tokens. The pipeline specification has additional staging requirements, excludes empty input, and excludes reference depth/token exhaustion. It also requires padded readable memory, three prefix bytes for UTF-8 staging, separate scratch/output regions and sufficient capacity.

Keep these as explicit preconditions until the wrapper discharges them. A public ByteArray API must prepare the required storage or handle inputs outside that domain separately, including empty input and resource-limit outcomes. It must not assume that a caller's ByteArray has readable bytes before or after its logical extent.

### Installation result: acknowledged scaffolding

Both JSON selection scenarios failed:

```text
bash tests/json-scan-select-gate.sh --strict
  exit 1; five assertion failures
  selector: unknown unit json_scan

bash tests/json-scan-select-gate.sh --fallback
  exit 1; one assertion failure
  fallback selected baseline for unknown-unit reason
```

The [scenario contract](https://github.com/scidonia/lean-llvm/blob/b40bbe4/tests/json-scan-select-gate.contract.md) explicitly says the selector does not yet know the unit and that its fixtures are scaffolding. This is an acknowledged incomplete integration, not evidence of a regression or of unsafe acceptance. The selector fails closed.

Finish it with real fixture, theorem, contract and ABI bindings. A successful mocked selector scenario will establish routing behaviour, not that a native JSON body has been proved or installed correctly.

## 7. F6: preserve termination in the replacement guarantee

`Beh` observes finite outcomes and gives an indefinitely divergent function no outcomes. `Refines target source` asks only for inclusion of target outcomes in source outcomes. Thus an always-diverging target refines a terminating source vacuously.

This is a relation-design limitation for the intended product, not evidence that the existing three shipped passes introduce divergence. Those passes have stronger preservation arguments in their implementation.

For a total reference function under precondition `P`, require the candidate to complete, avoid undefined behaviour, produce a related result, and respect the memory frame. The existing `Satisfies` relation is useful here: it requires a defined return at its declared budget and constrains every behaviour. Keep that completion requirement in the terminal theorem and installation acceptance criteria.

A mathematical step-count budget is a completion witness, not a wall-clock performance bound.

Acceptance checks: reject a candidate that loops forever and one that returns a correct result on some paths but introduces undefined behaviour on an admissible input.

## 8. F7: trust ledger and how to reduce it

| Layer | Current basis | Recommended treatment |
|---|---|---|
| Proof logic | Lean kernel and standard axiom footprint | Retain; audit final theorem dependencies |
| Specification | Hand-written JSON relations, policy and output interpretation | Review for intended behaviour; keep semantic correspondence concrete |
| LLVM semantics | Original Lean model inspired by VeLLVM | Treat conformance as an explicit assumption until justified on the supported domain |
| Intrinsics | Hand-written models in call environments | Check lane order, signedness, flags, poison and target features; prove the facts used by each kernel |
| Fixture normalisation | Capture scripts, stripped attributes and rewrites | Record every modification; preserve semantics or prove admissibility under the call-site contract |
| Fixture-to-AST identity | `include_str`, parser and executable `#guard` pins | Include parser and executable guard evaluation in artifact assurance; consider a checked parsing certificate |
| Printer | Canonical rendering | Repair F3; validate exported types, flags, alignment, symbols and ABI |
| Native compilation | Clang/LLVM backend, assembler and linker | Reasonable declared initial trust; proof of the backend is not a prerequisite for a useful scoped result |
| Lean execution bridge | Lowering/runtime, FFI adapter and buffer staging | Make an actual call route; state the bridge assumption and prove wrapper obligations where feasible |
| Installation | Certificate producer, hashes, rebuilds, shell manifest and local integrity | Extend per-unit checks; hashes bind bytes but do not prove their semantics |

### Why the axiom list is insufficient

The fixture pins use executable `#guard` checks because the parser's string operations do not reduce as needed for a reflexivity proof. See [JsonS1MasksIR.lean](https://github.com/scidonia/lean-llvm/blob/b40bbe4/LeanLLVM/Vellum/JsonS1MasksIR.lean#L12).

The kernel checks the theorem about the literal AST. Associating that AST with the source text additionally relies on the parser and the successful executable pin. This does not introduce a new logical axiom into the theorem, but it does add trusted machinery to the claim about the installed bytes. The same distinction applies to capture scripts, hashing and compilation.

Tactics and imported mathematical proofs need not be independent semantic trust assumptions when their produced proof terms are kernel checked. The important additions are unchecked artifact associations and the intended meaning of the definitions.

### Avoid the blanket “conservative model” claim

Over-approximating both source and target behaviours does not automatically transport a refinement to real LLVM. From:

```text
RealBeh(target) ⊆ ModelBeh(target)
ModelBeh(target) ⊆ ModelBeh(source)
RealBeh(source) ⊆ ModelBeh(source)
```

one cannot conclude `RealBeh(target) ⊆ RealBeh(source)`.

For example, treating an unused poison-producing instruction as immediate UB can make the model's source admit every outcome even though real LLVM still returns a specific defined result. Conversely, some poison-producing operations are given ordinary values by this model. These choices need domain-specific justification, not one global adjective.

A practical first target is exact semantic agreement for the concrete kernels under their staging invariants: accesses are valid, arithmetic stays in the required domains, and any poison-producing corner is either excluded or shown unobservable by an adequate semantics. The alternative is an explicitly directional adequacy argument sufficient to transfer the desired refinement.

Do not make a full port of LLVM semantics the prerequisite for the JSON milestone. Restrict the claim to a supported fragment and prove or audit the conformance facts it actually needs.

## 9. Suggested implementation sequence

### Step A — repair foundational semantics and export

Implement grouped `phi` evaluation; preserve types, flags and alignment; stop inventing `inbounds`. Add the counterexamples above and rebuild the existing proof graph.

**Done when:** the valid LLVM counterexamples agree with the corrected model, identity export preserves the relevant semantics, and existing proofs still check.

### Step B — repair the final theorem interface

Prove the old universal semantic premise contradictory, replace it with a reachable-outcome correspondence, and state the final JSON guarantee with concrete functions and concrete output abstraction.

**Done when:** no final theorem assumes parser correctness for arbitrary outputs, and positive instances exist at actual executions.

### Step C — choose and close the complete JSON proof target

Resolve the number-output decision. Supply stage-2 emitted-body correctness, the pipeline tail proof, structural and string-policy correspondence, and the event-stream relation. Relate the UTF-8 staged-window result to document acceptance/refusal, including boundaries and truncation.

**Done when:** the concrete pipeline satisfies the chosen semantic contract under its explicit precondition, without residual stage-2, tail or `ParserHalf` assumptions.

### Step D — connect one Lean application call

Build a real external seam and wrapper. Discharge padding, capacities, separation, lifetime and limit obligations. Either adapt the output to the public API or publish the narrower API and its relation explicitly. Handle inputs outside the native proof domain through a proved case split or an explicit supported-domain API.

**Done when:** an actual Lean caller executes the optimised native JSON body, and its observable result is covered by the stated replacement theorem and declared compiler/FFI assumptions.

### Step E — finish installation and measure that route

Bind the selected JSON unit to its actual fixture, covering theorem, contract, intrinsic/callee assumptions, target and artifact hashes. Run strict rejection and fallback controls with a real producer as well as shell shims. Benchmark the same wrapper and body used by the correctness demonstration.

**Done when:** a valid replacement installs, wrong theorem/contract/fixture combinations are refused, fallback uses a genuinely compatible baseline, and reported timing includes the relevant wrapper costs.

Do not reuse the comma-mask baseline as evidence of JSON fallback correctness: a fallback must implement the same call boundary and observable contract.

## 10. Required validation and reporting

Follow the repository's toolchain and memory-ceiling instructions. In an environment with a working user systemd scope, the intended form is:

```bash
systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c bash probes/install/lake-locked.sh build

systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c bash probes/install/lake-locked.sh build LeanLLVMTest
```

If that scope facility is unavailable, establish an equivalent enforced memory ceiling before building. Preserve the source-elaboration lock discipline. Re-elaborate proof modules that consume fixtures after fixture changes; an `include_str` pin is not sufficient protection if a stale compiled module is reused.

Run the relevant JSON corpus and emitted-body/native differential routes under the pinned toolchain, including invalid JSON, escapes, Unicode policy, truncated UTF-8, block boundaries, misalignment, capacities and limits. Include an end-to-end test through the actual Lean wrapper; component agreement is not a substitute for that route.

Add these proof-specific checks:

- Old finalisation premise is contradictory; repaired premise has concrete execution instances.
- Final theorem's stage-2 selection and event relation are concrete.
- No residual tail or parser semantic assumption remains in the claimed complete result.
- Relevant preconditions have valid witnesses and are established by the wrapper.
- Divergence and UB candidates cannot satisfy replacement acceptance.
- Artifact pins fail on controlled fixture changes and are rechecked from source.

### Evidence obtained during this review

| Check | Result | Scope |
|---|---|---|
| `bash tests/json-import-boundary.sh` | Passed | Import separation |
| `bash tests/itree-boundary.sh` | Passed | Generic/mathlib adapter boundary |
| `bash tests/m4-loop-gate.sh --strict` | Passed | Mocked selector refuses a loop with missing proof certificate |
| `bash tests/m4-loop-install-gate.sh --strict` | Passed | Mocked selector accepts matching loop metadata |
| `bash tests/m4-depth-install-gate.sh --strict` | Passed | Mocked selector accepts matching depth-unit metadata |
| `bash tests/m3-certificate-gate.sh --strict theorem` | Passed | Mocked selector refuses a changed theorem field |
| `bash tests/json-scan-select-gate.sh --strict` | Failed | Unsupported `json_scan`; five assertions fail |
| `bash tests/json-scan-select-gate.sh --fallback` | Failed | Baseline fallback occurs for the unknown-unit reason; one assertion fails |
| Lexical scan of 129 Lean files in `LeanLLVM`, `ITree`, `LeanLLVMTest` | No `sorry`, `admit`, `sorryAx`, `native_decide`, custom `axiom` or `implemented_by` tokens found outside comments/strings | Source hygiene only; not a kernel check or full dependency audit |
| Lean builds and native JSON differential tests | Not run | Required tools unavailable |

### Recommended claim after the work

The useful deliverable is: **a specified Lean JSON operation replaced by a particular SIMD implementation, proved equivalent under explicit input and staging conditions in an audited LLVM fragment, with compiler, runtime and artifact-binding assumptions listed separately**.

That is a strong result without claiming a verified Lean compiler or a verified machine-code backend. At the reviewed revision, the individual kernel proofs are significant progress toward it; the complete replacement claim remains unestablished.
