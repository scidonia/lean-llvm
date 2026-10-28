# LeanVellum M0 runtime-noise report: review and implementation handoff

**Date:** 28 October 2026  
**Reviewed input:** `m0-runtime-noise-report.md`  
**Programme:** `lean-vellum-development-programme.md`  
**Disposition:** adopt the opaque external seam for the first integration slice, subject to the corrections and acceptance checks below.

## 1. Review scope and decision

The supplied report provides useful evidence that ordinary Lean byte-array loops bring significant runtime machinery into their emitted LLVM, and that exporting a function does not preserve a call boundary through Clang optimisation. Its probes support an opaque `@[extern]` declaration as a practical first seam for the reported toolchain.

The toolchain probes have not been independently reproduced in this review. The SWAR counterexample in §4 was independently checked with fixed-width arithmetic. Repository counts, emitted IR and `@[noinline]` observations remain evidence supplied by the report and should be reproduced by the implementation owner.

Proceed with this sequence:

**Opaque seam → pure contextual replacement → memory-using loop → layout change → SIMD.**

The pure slice is an early integration checkpoint. The memory-using replacement remains the first demonstration of the programme's central capability: installing independently synthesised code under a semantic refinement certificate.

## 2. Preserve the boundary until installation

### Required correction

Replace “the seam must be an opaque `@[extern]` symbol” with:

> The first implementation will use an opaque external declaration. The build must preserve the intended replacement boundary until certification and installation have completed.

The report demonstrates that `@[export]` alone is insufficient in its same-translation-unit `-O3` probe. It does not establish that `@[extern]` is the only possible mechanism. Replacement before inlining and controlled separate compilation remain alternatives.

Treat the reported absence of emitted `noinline` as specific to the probed toolchain. Do not depend on Lean's `@[noinline]` as a Clang boundary without inspecting its actual output.

### Implementation requirements

- Keep the baseline definition unavailable to caller optimisation before installation, or run installation before it becomes available.
- Initially disable LTO across that boundary unless installation is explicitly placed before LTO.
- Inspect the actual application caller, not only the standalone probe.
- After installation, ordinary downstream optimisation and inlining may resume under the declared compiler trust assumptions.

**Acceptance:** at the installation point, the intended caller still invokes the identified seam; the build record identifies the exact body and interface supplied at that seam.

## 3. Supply a concrete baseline behind the opaque declaration

### Required correction

An opaque declaration supplies an interface, not an implementation to refine. The first work package must identify the baseline body and explain how it connects to the original Lean computation.

Use the following arrangement:

| Artifact | Responsibility |
| --- | --- |
| Lean caller containing the opaque external declaration | Preserve a stable call boundary |
| Separately compiled baseline definition | Supply the original LLVM implementation |
| Candidate definition | Supply the replacement LLVM implementation |
| Checked refinement theorem | Relate the actual candidate and baseline artifacts |
| Contextual replacement/linking theorem | Justify substitution at the caller boundary |
| Installation record | Bind the proof, artifacts, contracts and target configuration |

Prefer generating the baseline definition from the original Lean function, exporting it under the seam's symbol in a separate compilation unit. Verify the actual signature, calling convention, symbol resolution and any generated wrappers; matching names alone is insufficient.

If the baseline is authored independently in C or another language, explicitly discharge or declare the additional connection to the Lean specification. An opaque Lean function does not acquire its intended semantics merely through its name or external binding.

**Acceptance:** the handoff identifies one concrete baseline definition, its provenance, the caller-side declaration and the guarantee connecting the baseline to the intended source computation.

## 4. Correct the SWAR specification before proving parity

### Finding

The report's expression is a zero-byte detection idiom applied after XOR with repeated comma bytes:

```text
m = x XOR 0x2C2C2C2C2C2C2C2C
result = (m - 0x0101010101010101) AND NOT m AND 0x8080808080808080
```

Subtraction is modulo 2^64. Borrowing can cross byte boundaries, so the result is not always an exact per-byte comma mask.

For the report's function:

```text
Input word:             0x0000000000002D2C
Computed high-bit mask: 0x0000000000008080
Exact comma-byte mask:  0x0000000000000080
```

The low byte is a comma (`0x2C`); the adjacent byte is `0x2D`. The computed result marks both lanes.

### Required action

Choose and document the intended contract before using this baseline in a parity proof:

- If the result is an exact lane mask, replace the implementation with an exact classifier and prove it correct.
- If the result is only an existence predicate, state that predicate and prove the relevant detection property.
- If mask bits are compacted into another format, specify both the high-bit representation and the compaction mapping.

Include the counterexample as a regression case. Define lane numbering, bit order, fixed-width overflow and, when memory loads enter the example, byte order.

A candidate refining this baseline would preserve its behaviour; that alone would not establish exact classification. Keep baseline-to-specification correctness separate from candidate-to-baseline refinement.

**Acceptance:** the chosen baseline satisfies the intended specification for all inputs. The proof does not assert exact-mask parity for the expression above.

## 5. Separate semantic acceptance from replacement coverage

### Required correction

An inlined copy of the correct baseline elsewhere in the application is not inherently a semantic failure. It can mean that a desired optimisation does not reach every intended path.

Define two independent checks:

| Check | Question |
| --- | --- |
| Semantic acceptance | Is every installed candidate covered by a valid certificate and contextual theorem? |
| Replacement coverage | Do the application paths targeted for optimisation execute the candidate? |

A global requirement that no baseline-shaped instructions remain anywhere in the binary is unnecessary for semantic correctness and difficult to establish by pattern matching. Equivalent computations can have different syntax; unrelated code can share the same syntax.

### Implementation requirements

- Preserve the boundary before installation so coverage can be established from construction and call-site inspection.
- Record the intended callers and their symbol resolution.
- Use inspection or a dedicated diagnostic build to establish that representative executions reach the seam.
- Apply semantic certification to the release artifacts. Instrumented diagnostics are supporting evidence, not a substitute for that connection.
- Distinguish an identity-installation smoke test from evidence of candidate selection: byte-identical bodies cannot reveal which implementation ran through their outputs alone.

**Acceptance:** report semantic acceptance and optimisation coverage separately. Any residual baseline execution is described as a coverage limitation unless it exposes a distinct correctness issue.

## 6. Retain a contextual theorem for the pure slice

### Required correction

Beginning with `UInt64 → UInt64` avoids heap relations in the first local proof, but does not remove the obligation to justify LLVM substitution into a caller.

The first slice needs, schematically:

```text
CandidateRefinesBaseline(candidateIR, baselineIR, boundaryContract)
AdmissibleCaller(callerIR, boundaryContract)
---------------------------------------------------------------
ModuleRefines(link(callerIR, candidateIR), link(callerIR, baselineIR))
```

Instantiate a small theorem for the pure supported subset if necessary. Do not claim general memory-aware contextual refinement from that theorem.

A Lean arithmetic equality can supply an important lemma, but it must connect to the semantics of the actual LLVM bodies, including relevant attributes, poison and definedness. Acceptance must concern the installed LLVM pair.

Runtime operations found outside the certified unit belong in the application inventory and trust ledger. Model their detailed semantics when they enter the certified unit or become necessary to justify its boundary assumptions. Their presence elsewhere does not force the first pure certificate to formalise all Lean reference counting.

**Acceptance:** a caller/callee example exercises the local LLVM refinement and contextual replacement theorem, not just a bit-vector equality or an executable comparison.

## 7. Preserve semantic attributes and caller assumptions

### Required correction

Do not adopt a blanket “drop unsupported attributes” policy. The LLVM language reference specifies that an integer result outside a declared `range` becomes poison. Relevant assumptions may also appear on declarations and call sites or have already influenced caller optimisation.

Removing an attribute from a candidate definition does not undo assumptions already used in a compiled caller. Handle the established boundary contract as a whole.

For each supported attribute or metadata kind, choose a documented treatment:

1. Model it and establish the required obligations.
2. Remove or weaken it at a controlled earlier stage, then rebuild affected callers, with the semantic justification or trust assumption stated.
3. Reject the artifact until supported.

Distinguish semantic information such as aliasing constraints from optimisation hints such as ordinary branch weights. Do not treat `!tbaa`, `!prof`, `range`, `noundef` and `noalias` as one interchangeable category.

Bind target triple, data layout, relevant target features, signatures, declarations, call-site assumptions and linked contracts into the certification record. Hashes bind artifacts but do not prove that an attribute policy is sound.

**Acceptance:** no unsupported semantic claim is silently ignored. The candidate satisfies every boundary assumption retained by the caller. The implementation checks its policy against the pinned LLVM 21 language reference rather than assuming current documentation is version-identical.

## 8. Revised milestone handoff

| Milestone | Required outcome |
| --- | --- |
| M0: capture and boundary | Reproduce the probes, capture the real application caller, supply the separate baseline and demonstrate boundary survival through the chosen optimisation path |
| Early pure integration slice | Correct specification, structurally different candidate, actual LLVM refinement, restricted contextual theorem and certificate-bound installation |
| Memory-using loop | Add the necessary memory semantics, external-call contracts, framing and loop reasoning; certify a real loop from the Lean compilation chain |
| Representation change | Relate different private layouts or allocations while preserving the externally observed contract |
| SIMD and synthesis | Extend supported vector semantics, prove tails and target assumptions, and accept independently generated candidates through the same gate |

Keep the memory-using loop as the programme's substantive M4 acceptance target. Label the pure slice as an earlier integration gate so it cannot be mistaken for completion of the memory-refinement objective.

## 9. Immediate implementation checklist

- [ ] Reproduce and preserve the report's probe sources, commands and relevant IR as durable test fixtures.
- [ ] Specify exact-mask versus existence semantics; fix the SWAR example accordingly.
- [ ] Identify the caller declaration and separately compiled baseline body in a real application.
- [ ] Define the installation point relative to Clang optimisation, linking and LTO.
- [ ] Inventory semantic attributes on definitions, declarations and call sites.
- [ ] Write the first local LLVM refinement statement and restricted contextual theorem before extending proof automation.
- [ ] Implement artifact-bound checking, conservative fallback and strict CI behaviour.
- [ ] Demonstrate identity installation, then candidate selection with a structurally different certified body.
- [ ] Record semantic acceptance and replacement coverage separately.
- [ ] Retain an explicit next milestone for the memory-using loop and its runtime contracts.

## 10. Reference and assurance note

[LLVM Language Reference: parameter and return attributes](https://llvm.org/docs/LangRef.html#parameter-attributes) was consulted for the review's `range` semantics. Pin and verify the corresponding LLVM 21 documentation during implementation.

This review proposes corrections and acceptance criteria. It does not assert that the replacement infrastructure, contextual theorem or source-to-external-baseline connection has already been implemented or proved.
