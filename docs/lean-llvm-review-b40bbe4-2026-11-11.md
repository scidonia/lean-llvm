# lean-llvm: certification status and development handoff

**Review date:** 11 November 2026  
**Repository:** [scidonia/lean-llvm](https://github.com/scidonia/lean-llvm)  
**Reviewed commit:** [`b40bbe4919678557df61284c86e11bf90b598ca4`](https://github.com/scidonia/lean-llvm/tree/b40bbe4919678557df61284c86e11bf90b598ca4)  
**Comparison baseline:** [`9c29e11866a7da2648a19f636ad57f7df7a16929`](https://github.com/scidonia/lean-llvm/tree/9c29e11866a7da2648a19f636ad57f7df7a16929)  
**Purpose:** Technical review and implementation handoff for certified replacement of performance-critical Lean code with independently authored SIMD implementations.

## 1. Assessment

The latest work substantially strengthens the mathematical certification of decimal-to-binary64 conversion. The tier-2 guard now has a correctness theorem; the fallback has proofs for its retained window, sticky comparisons, rounding intervals and an eventually terminating walk; and a concrete decimal reader removes the arbitrary reader hypothesis at the model level. These are material results. The previous assessment that numeric correctness was largely an obligation still to be proved is now outdated.

The project has not yet established certification of the complete native JSON parser as a replacement for the Lean reference parser. Pipeline composition remains conditional on the tail and concrete stage-2 implementation. The final parser bridge also retains an impossible semantic premise. That statement must be repaired before its proof can become a usable part of the replacement chain.

The recommended next milestone is **one complete, artifact-bound replacement theorem**, using the existing optimised implementation. Further performance work can follow once the actual output, memory and termination guarantees compose through the parser boundary.

### Decision for LeanIn

The proved kernels provide a credible basis for a certified-kernel integration path. The complete native parser should remain experimental until the obligations below are closed. An integration may still be useful earlier, but its documentation must identify which properties are proved and which depend on unverified code or trusted toolchain boundaries.

This review does not require verification of the entire Lean compiler as a prerequisite for useful deployment. A practical first result can state its compiler, ABI and runtime assumptions explicitly. The immediate mathematical gaps are within the claimed parser certification itself.

## 2. Evidence and limits

The review compared source snapshots at the two commits above and inspected the statements and implementations of the relevant definitions and proofs. All source links in this report are pinned to the reviewed commit.

Two independent source-boundary checks were rerun successfully:

| Check | Result | What it establishes |
| --- | --- | --- |
| `tests/json-import-boundary.sh` | Passed | The checked reference-parser and scanner-model import boundaries remain intact, including the detector controls. |
| `tests/itree-boundary.sh` | Passed | The checked generic-tree dependency boundary and direct mathlib adapter inventory remain intact. |

The required Nix/Lean toolchain was unavailable in the review environment. Lean elaboration, native fixture regeneration, object differential tests and benchmarks were not rerun. Consequently, this is a source review with independently executed boundary checks, not a fresh verification of the complete proof build or the reported timings.

“Proved” below describes the theorem present in the inspected source. It must not be read as a claim that the reviewer independently re-elaborated that theorem.

## 3. Current status

| Component | Status at the reviewed commit | Remaining boundary |
| --- | --- | --- |
| Stage-1 masks and carry | Existing pinned-body proof against the mask/carry specification. | Intrinsic interpretations and the declared LLVM modelling boundary. |
| Position emitters | Existing proofs for the POS8 and B8 bodies, cursors and memory effects. | Composition with the enclosing caller and its staging. |
| UTF-8 unit | Existing pinned-body proof against the staged-window valid-prefix specification. | Whole-document finalisation and caller composition. |
| Escape expansion | Existing unconditional `Satisfies` theorem, relative to its contract precondition and call model. | Use within the complete parser proof. |
| Tier-1 numeric path | New exact-operand and exact-value arguments, with a correctly rounded operation model. | Concrete floating-point instruction semantics and implementation correspondence. |
| Tier-2 numeric path | New proof that a successful guard decision agrees with `roundMag`, under the explicit 64-bit mantissa bound. | Connection of the model to the concrete emitted path and the enclosing conversion. |
| Tier-3 numeric fallback | New window/sticky/clamp arguments and termination/correctness of the walk using exact comparisons. | Reachable comparison hypotheses, concrete implementation correspondence and a usable execution bound. |
| Decimal reader | New concrete reader, round trip, grammar properties and agreement with the existing recogniser. | Correspondence with the C/LLVM loops and bounded accumulators. |
| Pipeline body | Four of five body-fact fields assembled at the staging. | `PipelineTailTarget` remains an input. |
| Stage 2 | A boundary contract and C implementation exist. | Concrete body certification and parser semantics. |
| Final parser replacement | A conditional bridge theorem exists. | Its semantic hypothesis is impossible as currently quantified. |
| Performance evidence | Native scratch measurements, Lean-reference throughput and conversion costs are distinguished. | Reproducible measurement of the exact artifact covered by the completed proof. |

## 4. What has advanced

### 4.1 Tier-2 arithmetic is substantially closed at the model

[`ElGuardRefine.elGuardRefinesOn`](https://github.com/scidonia/lean-llvm/blob/b40bbe4919678557df61284c86e11bf90b598ca4/LeanLLVM/ElGuardRefine.lean#L2667) proves `ElGuardRefinesOn`: for a positive mantissa below `2^64`, whenever `elTier2Code` returns a code, that code is the magnitude selected by `roundMag` for the exact decimal value.

This resolves the previously identified arithmetic obstacle around the guard, discarded product words, midpoint cases and exponent carry. The word bound is explicit, and the unbounded reading is separately refuted. That is a stronger and more useful result than a theorem whose unstated machine-word assumptions are hidden in its definitions.

The remaining task is to connect this arithmetic model to the concrete call path. The theorem is not itself a `runFuel` result for an imported LLVM conversion body.

### 4.2 The fallback now has a real walk theorem

[`StrtodTier3.walkLoop_computes`](https://github.com/scidonia/lean-llvm/blob/b40bbe4919678557df61284c86e11bf90b598ca4/LeanLLVM/StrtodTier3.lean#L4170) establishes that, from any finite starting pattern, some execution of the model walk stops at the pattern encoding `roundMag`'s answer. The associated arguments identify the lattice, rounding intervals, tie behaviour, movement toward the target and the overflow endpoint.

This is substantive algorithm verification. It should be credited separately from the simpler `tier3Mag_eq_roundMag` result: the latter's non-clamped branch invokes `roundMag` directly, whereas the walk theorem establishes that an iterative selection procedure reaches that answer.

However, the walk uses `cmpWalk`, an exact rational comparison. Its correctness does not automatically establish that every implemented `stk_cmp` call provides that comparison. Section 5.4 identifies the remaining premise.

### 4.3 The reader parameter is discharged at a concrete model

[`StrtodReader`](https://github.com/scidonia/lean-llvm/blob/b40bbe4919678557df61284c86e11bf90b598ca4/LeanLLVM/StrtodReader.lean) supplies `reader_lexeme`, accepted-input grammar properties, completeness, and `reader_isSome_eq_numLexB`. It instantiates the tier-1 and tier-3 statements as `tier1_no_reader` and `tier3_no_reader`.

The result removes an arbitrary reader from those model statements. It does not yet prove that the concrete C locals hold precisely the corresponding model fields. The source explicitly distinguishes segmentation and counts from bounded accumulators, exponent saturation and the sticky window.

### 4.4 Pipeline facts are better carried and assembled

[`PipelineDischarge`](https://github.com/scidonia/lean-llvm/blob/b40bbe4919678557df61284c86e11bf90b598ca4/LeanLLVM/Vellum/PipelineDischarge.lean) assembles the loop instance, iteration-count equality, cost bound and seed. The exit predicate now receives the document-relative entry bound, escape-count slot contents and escape-count growth through the actual loop producers.

This reduces the composition problem to a more explicit tail target. It does not discharge that target: `pipeline_satisfies_at_stage2_of_exitStage2` still accepts both a stage-2 selection satisfying its contract and a proof of `PipelineTailTarget`.

## 5. Blocking findings and required changes

### 5.1 P0 — Repair the impossible final parser premise

**Location:** [`JsonPipelineRefine.pipeline_satisfies_of_parser`](https://github.com/scidonia/lean-llvm/blob/b40bbe4919678557df61284c86e11bf90b598ca4/LeanLLVM/Vellum/JsonPipelineRefine.lean#L1081), together with `pipeline_units_finalisation` and `ParserHalf`.

The `hsem` premise quantifies over arbitrary input memory, readable document, verdict, output memory and output addresses. Its only input restriction is a read of the document from the initial memory. No execution or unit postcondition restricts the chosen verdict or output memory.

The contradiction can be seen without executing the parser:

1. Fix the empty input memory and empty document. Reading zero bytes at `base` succeeds.
2. Choose an empty output memory and zero output-prefix lengths. Both output reads succeed.
3. Instantiate `hsem` with verdict `1`. The acceptance equivalence requires the reference parser to accept that document.
4. Instantiate it again with verdict `0`. The same equivalence requires the same document not to be accepted.

The contradiction does not depend on whether the empty document is actually accepted. The same fixed acceptance proposition is forced both true and false.

Lean is not made unsound by a theorem with this hypothesis. The theorem instead has an uninhabitable premise and cannot serve as the intended certification bridge.

There is a second issue: `ParserHalf` ranges over every readable output prefix, including empty prefixes. A real event/arena relation should describe the actual reported output extents, not every prefix of those outputs.

**Required change:** State the parser property at the actual returned outcome and actual cursor values. Its proof must have access to the input staging, the relevant execution or reachable-state evidence, and the unit postcondition. State the event and arena relation at those particular extents.

**Acceptance criteria:**

- The semantic bridge cannot be instantiated with an arbitrary verdict unrelated to execution.
- The bridge names the actual output extents and their byte reads.
- Add a regression theorem demonstrating that the retired universal hypothesis implies `False`.
- Establish the replacement bridge for the concrete implementation, rather than introducing another unconstrained semantic hypothesis.

### 5.2 P1 — Prove the pipeline tail target

**Location:** [`PipelineDischarge`](https://github.com/scidonia/lean-llvm/blob/b40bbe4919678557df61284c86e11bf90b598ca4/LeanLLVM/Vellum/PipelineDischarge.lean).

The loop, bounds and seed are now assembled. The final theorem still requires `PipelineTailTarget`, whose conclusion includes both the three-step returning execution and the unit-level postcondition.

**Required change:** Derive the tail's call preconditions, call resolution and final postcondition from the exit state actually produced by the loop, the caller's staging and the relevant unit contracts. Complete the frame argument back to the original caller memory.

**Acceptance criteria:**

- A theorem constructs the tail proof from the staging, reachable exit facts and certified callees.
- The top-level unit-composition result no longer takes an externally supplied `PipelineTailTarget` or equivalent body-fact premise.
- Refusal, successful parsing and the required cursor/frame properties all compose through the same declared contract.

### 5.3 P1 — Certify concrete stage 2 and its observable output

**Locations:** [`JsonStage2Contract`](https://github.com/scidonia/lean-llvm/blob/b40bbe4919678557df61284c86e11bf90b598ca4/LeanLLVM/Vellum/JsonStage2Contract.lean) and [`kernel/json/stage2.c`](https://github.com/scidonia/lean-llvm/blob/b40bbe4919678557df61284c86e11bf90b598ca4/kernel/json/stage2.c).

The C implementation exists. What remains absent is a concrete body theorem providing the stage-2 selection required by pipeline composition and the semantic result needed by the repaired parser bridge.

**Required change:** Pin and model the concrete stage-2 body, or explicitly choose and document another justified implementation semantics. Relate its locals and memory to the reader, conversion and parsing models. Define the actual relation between emitted arena/event bytes and the reference parser's tokens or decoded values.

The observation relation must address the different representations of numbers. If one side retains a decimal lexeme while the other emits binary64, define exactly what equivalence means, including rounding, signed zero and any admitted overflow behaviour.

**Acceptance criteria:**

- The stage-2 `CallSatisfies` premise is supplied by a theorem about the concrete implementation.
- The event/arena relation is concrete and instantiated in the final theorem.
- Accepted values, rejection behaviour, error offsets and permitted resource limits are stated consistently on both sides.
- Reader and numeric-model results are connected to the actual implementation, not merely imported beside it.

### 5.4 P1 — Connect fallback comparisons and termination to execution

**Location:** [`StrtodTier3`](https://github.com/scidonia/lean-llvm/blob/b40bbe4919678557df61284c86e11bf90b598ca4/LeanLLVM/StrtodTier3.lean), particularly `stkCmp_sticky_spec'`, `walkStep` and `walkLoop_computes`.

The sticky comparison theorem requires a boundary exponent bound and a proximity condition: the compared boundary must be at least half the input value. The source explicitly leaves the argument from the floating-point starting approximation to these reachable comparison conditions open.

The exact-comparison walk can terminate from any finite pattern. That is stronger about the abstract walk's starting state, but it does not remove the proximity requirement of the implemented sticky comparison. These statements have different premises and must be composed explicitly.

The walk theorem also supplies existential fuel. A concrete `Satisfies` result requires returning execution at the contract's stated budget. This review has not established that the current stage-2 allowance is sufficient for the concrete numeric implementation; that bound must be proved or adjusted with justification.

**Required change:** Establish an initial-approximation bound and preserve the conditions needed by each implemented comparison. Prove agreement between the implemented walk and the exact-comparison walk on reachable states. Derive a bound usable by the execution contract.

**Acceptance criteria:**

- Every reachable sticky comparison satisfies its exponent, scale and proximity hypotheses.
- Concrete comparison results agree with the exact model at every walk step.
- The concrete walk returns the correctly rounded encoding within a stated bound that the enclosing contract covers.

### 5.5 P1 — State the floating-point instruction boundary precisely

**Location:** [`StrtodTier1`](https://github.com/scidonia/lean-llvm/blob/b40bbe4919678557df61284c86e11bf90b598ca4/LeanLLVM/StrtodTier1.lean).

Tier 1 proves exactness of the operands and agreement of their exact product or quotient with the decimal value. Its single rounded operation is represented using `roundMag`. The source explicitly does not establish correctness of the concrete hardware operation.

**Required change:** Give floating-point operations a declared semantics and connect the concrete instructions to it, or list their correctly rounded behaviour as an explicit trusted boundary for the first deployment result. Include relevant rounding-mode and compilation assumptions. The fallback's initial approximation requires a corresponding treatment.

**Acceptance criterion:** A reader can distinguish the proved exact-value argument, the rounding model and the assumption or proof connecting actual execution to that model.

## 6. Performance evidence

The latest documentation makes a useful distinction between three kinds of evidence:

| Evidence | Current report | Interpretation |
| --- | --- | --- |
| Native pipeline versus simdjson | Scratch measurements; P2 faster on six of seven P-core documents. | Promising implementation evidence; not a reproducible benchmark of the completed certified artifact. |
| Lean reference parser | Approximately 21–28 MB/s on the stated repeated-document benchmark. | Reference-parser throughput for that workload, which uses tier-1 numbers. |
| Replacement numeric conversion | 116 to 137 ns/call on the mixed corpus; 1,035 to 2,917 ns on the 1,002-digit case. | Approximately 18% and 2.82× increases respectively, measured for the stated before/after revisions. |

The [performance record](https://github.com/scidonia/lean-llvm/blob/b40bbe4919678557df61284c86e11bf90b598ca4/docs/json-pipeline-performance.md) reports the conversion slowdown directly. This is useful engineering evidence, and the bounded, allocation-free fallback removes behaviours that throughput alone does not capture.

The old scratch ratios must not be transferred to the current staged implementation or current conversion without measurement. Inlining, translation-unit structure and numeric-path changes can affect the result. A proof about semantic correctness also does not establish a timing result; the practical requirement is that the measured executable be traceably the implementation covered by the certification claim.

### Required benchmark closure

1. Commit a harness that rebuilds both the candidate and a pinned reference release.
2. Identify the proved fixture, source revision, emitted object, compiler flags and selected CPU path.
3. Compare matching contracts for extraction, string validation, errors and numeric conversion.
4. Measure through the intended Lean calling boundary, including staging/copying where the application pays for it.
5. Include numeric-heavy and fallback-heavy workloads alongside the existing corpus.

## 7. Documentation and paper claims

The README describes each translation unit as carrying a `Satisfies` theorem and the assembled pipeline as having a certified composition. At the reviewed commit, the concrete stage-2 and tail premises remain open. The wording should distinguish established unit proofs from conditional composition.

A defensible description today is:

> A Lean LLVM refinement framework with pinned-body SIMD kernel proofs, substantial decimal-to-binary64 algorithm verification, and a partially discharged composition toward a native JSON parser replacement.

A stronger description becomes justified after the blocking work:

> A certified native JSON implementation satisfying a concrete Lean parser contract, with an explicit compiler/runtime trust boundary and reproducible performance measurements of the covered artifact.

For the proposed **Lean Mean Speed Machine** paper, the current work has a much stronger technical core than before this update. The clearest practical contribution would be a complete example in which independently authored low-level code is accepted through a proved contract and then called from Lean. A single closed demonstration would make that claim easier to assess than a larger set of conditional top-level results.

Avoid claiming a verified Lean-to-machine-code compiler chain unless the corresponding compiler-preservation results are actually part of the contribution. Artifact identity checks and differential execution evidence should be reported for what they establish.

## 8. Recommended implementation order

| Order | Work item | Deliverable |
| --- | --- | --- |
| 1 | Repair the final parser bridge and actual output extents. | An inhabitable statement, with a regression proof refuting the retired premise. |
| 2 | Discharge the pipeline tail. | Unit composition with no external tail/body-fact hypothesis. |
| 3 | Close the fallback comparison and approximation premises. | Reachable-state agreement with the exact walk and a concrete bound. |
| 4 | Certify concrete stage 2 and instantiate the event/value relation. | The complete parser-replacement theorem at the chosen implementation semantics. |
| 5 | Bind and exercise the Lean call boundary. | A documented replacement route with explicit ABI, memory and toolchain assumptions. |
| 6 | Reproduce performance on the covered artifact. | A pinned harness and results for the actual deployment path. |

Items 2–4 can be developed alongside one another, but the corrected semantic interface should be settled first so subsequent proofs target the final statement.

## 9. Completion checklist for the next review

- [ ] `pipeline_satisfies_of_parser` refers to actual execution outcomes.
- [ ] `ParserHalf` or its replacement uses actual output extents.
- [ ] The old universal semantic premise is formally refuted in a regression check.
- [ ] Pipeline tail obligations are constructed from the real loop exit.
- [ ] Concrete stage 2 supplies the required call contract.
- [ ] The event/arena relation to reference values is defined and instantiated.
- [ ] Implemented fallback comparisons satisfy all reachable-state hypotheses.
- [ ] The concrete numeric execution fits its declared budget.
- [ ] Floating-point and compiler/runtime assumptions are explicit.
- [ ] The final theorem is source-elaborated with its fixtures and axiom checks.
- [ ] Benchmarks measure the exact covered artifact through the intended Lean boundary.
- [ ] README and paper claims agree with the completed theorem and evidence.

The key development objective is to make the existing component proofs compose into a theorem that a real caller can use. The latest numeric work removes a substantial part of that burden; the remaining interface and execution obligations are now the priority.
