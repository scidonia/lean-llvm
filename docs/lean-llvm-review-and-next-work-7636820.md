# lean-llvm correctness review and next work

**Reviewed revision:** [`763682060836c5822da435dc20511b07928c4137`](https://github.com/scidonia/lean-llvm/commit/763682060836c5822da435dc20511b07928c4137)  
**Comparison revision:** `94d607cad93d40d6f4c4c7463c5ab009b12654de`  
**Review date:** 13 November 2026  
**Scope:** JSON replacement, completion and fuel accounting, helper correspondence, admission, and the resulting trust surface.

## Assessment

The repository has made meaningful progress towards a completed stage-2 proof. It now contains a conditional traversal theorem, a model-level correctness argument for the native policy algorithm, and LLVM constructs that remove several previous representation barriers. These are useful developments.

The complete native JSON replacement is still unverified. In particular, `Stage2WalkCompletes` is not inhabited. The new traversal theorem assumes `WalkLoopStep`, which includes the existence, invariant preservation and bounded cost of a complete dispatch revolution or exit. That premise contains the main operational work still to be proved.

Two findings should be addressed before continuing the assembly:

1. The new potential adds bytes already accounted for to the remaining budget. This gives the byte term the opposite direction from the intended amortised accounting and makes the revolution premise unsuitable for long-string iterations.
2. The certified admission predicate and executable admission still differ. The README describes a nesting-based native check, but the adapter still counts opener bytes and the test still expects the old fallback behaviour.

The next milestone should be an instantiated completion theorem under a named helper environment, with a complete long-string traversal and admission agreement exercised. Further local block proofs alone are insufficient evidence of approaching completion.

## 1. What has improved

| Area | Evidence at this revision | What remains |
| --- | --- | --- |
| Traversal structure | `WalkSegment` composes counted runs; `walkLoopFinishes` performs induction on the remaining entry count; completion is transported to the stage-2 budget. | Prove `WalkLoopStep` for the actual dispatch, connect the actual entry state, and discharge the exit allowance. |
| Initial invariant | The existing seed development produces the invariant from staged memory and the entry run. | Instantiate and compose those results at the ABI entry state in the final completion theorem. |
| Container-stack contents | The carry contains maps of stack bytes, and the value-position result can be derived from them. | Preserve and use these facts across the complete traversal. |
| Character policy | `policyStep_spec`, `policyWalk_spec`, `policyClass_refClass`, `policyClass_backward` and `refClass_scanCharsEnd` relate the algorithm model to the reference scanner. | Relate the C body, its backward-fill storage, screening and wrapper to that model. |
| LLVM representation | Pointer conversions, global-symbol operands, binary64 operations and aggregate allocation are represented. The captured string helper parses. | Prove helper-body contracts and validate the extended semantics against the admitted LLVM fragment. |
| Local stage-2 proofs | The source census reports 157 of 165 blocks as links, with additional finalisation steps handled separately. | Establish applicability on reachable states and assemble the complete control flow. The count is not a percentage of end-to-end correctness. |

Relevant sources: [traversal](https://github.com/scidonia/lean-llvm/blob/7636820/LeanLLVM/Refinement/JsonStage2WalkTraverse.lean), [seed](https://github.com/scidonia/lean-llvm/blob/7636820/LeanLLVM/Refinement/JsonStage2WalkSeedRun.lean), [policy model](https://github.com/scidonia/lean-llvm/blob/7636820/LeanLLVM/Refinement/JsonPolicyModel.lean), [helper status](https://github.com/scidonia/lean-llvm/blob/7636820/LeanLLVM/Refinement/JsonStage2HelperIR.lean).

## 2. Finding: the potential charges newly processed bytes in the wrong direction

**Priority: high. This obstructs the intended completion proof; it is not evidence that Lean accepted a false unconditional theorem.**

In [the potential definition](https://github.com/scidonia/lean-llvm/blob/7636820/LeanLLVM/Refinement/JsonStage2WalkTraverse.lean#L242), write:

```text
E = number of entries
k = consumed entry index
D = sum of the lengths in C.spans

Φ(C) = 32 × (E − k) + 8 × D
```

The revolution branch of `WalkLoopStep` requires:

```text
p + Φ(C′) ≤ Φ(C)
```

where `p` is the number of model control steps. The spans are accumulated as decoding proceeds, so a revolution that adds a long span increases `D`.

Consider the arithmetic of a revolution consuming one entry and adding a 100-byte span:

```text
Φ(C′) − Φ(C) = −32 + 8 × 100 = 768
```

Even `p = 0` cannot satisfy the required inequality. For example, ten remaining entries and no previous spans give `Φ(C) = 320`; nine remaining entries and 100 accounted bytes give `Φ(C′) = 1088`.

This calculation is an algebraic diagnostic of the proposed charging rule, not a separately constructed concrete LLVM-state counterexample. Its relevance is that ordinary string bodies can be long while their entry-index advance is small. The proof must cover precisely those executions.

The hypothesis of `walkPotential_of_allowances` makes the issue explicit:

```text
p + 8 × D′ ≤ 32 + 8 × D
```

For `D′ = D + added`, it asks for:

```text
p + 8 × added ≤ 32
```

The intended allowance is instead:

```text
p ≤ 32 + 8 × added
```

The conditional arithmetic theorem can be valid while its premise cannot be established for the required executions. This is the same logical concern as vacuous refinement: the critical question is whether the premise has a producer at the actual states.

### Suggested repair

Use remaining work as credit. A candidate is:

```text
Φ(C) = 32 × (E − k) + 8 × (n − A(C))
```

Here `A(C)` is a monotone amount of byte work already charged, bounded by document length `n`. If the existing span sum is suitable for `A`, prove that suitability explicitly. Do not assume it pays for every scan merely because it bounds arena output.

For `Δk = k′ − k` and `ΔA = A(C′) − A(C)`, the desired local accounting becomes:

```text
p ≤ 32 × Δk + 8 × ΔA
```

This then yields `p + Φ(C′) ≤ Φ(C)`. At the seed, the available credit includes `8 × n`; the current seed theorem's disappearance of the byte allowance should therefore change too.

There are two obligations to resolve before selecting the exact definition:

- Whitespace, quote discovery, escape-position traversal and other byte-dependent loops must each have a charging source. If some are not covered by the span sum, use additional monotone progress counters or explicitly spend the existing position allowance.
- Successful processing, refusal and early exit need consistent accounting. The exit branch currently has a constant allowance, so any unbounded byte-dependent work on that branch must be paid before finalisation or included in its cost relation.

**Acceptance criteria:** prove one complete revolution containing a long string, including its actual counted run and corrected credit inequality. Then cover escaped strings, whitespace-heavy input, malformed input encountered late, and the last entry's exit. A regression should exercise actual dispatch execution, not only the numeric identity above.

## 3. Finding: native admission still implements the previous domain

**Priority: high. The current implementation and documentation disagree about fast-path selection.**

[Lean admission](https://github.com/scidonia/lean-llvm/blob/7636820/LeanLLVM/JsonKernelDomain.lean#L482) checks `docDepth`, which reads maximum structural nesting and skips string bodies. [The native adapter](https://github.com/scidonia/lean-llvm/blob/7636820/probes/json/route/shim.c#L410) still computes:

```c
uint64_t clause = openers > maxDepth ? ADMIT_DEPTH : ADMIT_NONE;
```

It calls `admit_scan` with depth collection disabled. Neither this adapter nor the route test changed between the comparison revision and `7636820`.

An explicit witness is a JSON string containing 129 `[` characters. Its structural nesting is zero, and it has no character-policy refusal. Lean admission accepts it; the native opener-count check sends it to fallback. The script still constructs this input and expects fallback acceptance, while its separate agreement check also requires native admission to equal Lean admission.

The new README text says opener-rich documents are admitted on the fast path. That describes the desired behaviour, not the current adapter.

This witness demonstrates a conservative selection mismatch. It does not by itself demonstrate a wrong parse result or unsafe native call: the fallback can still return the correct value. It does invalidate the claimed equality of admission decisions and means earlier passing transcripts do not establish that equality for this revision.

### Suggested repair

Implement the certified nesting predicate on the native route and update the boundary expectations together. Across blocks, carry the relevant nesting state and compute the maximum prefix nesting, rather than using total opens or final balance as substitutes.

The existing depth unit reports final depth and the sum of prefix depths. Those outputs alone do not give maximum prefix depth. Specify whether a new maximum statistic, an additional traversal, or another proved construction supplies the native maximum. Establish agreement with the library's measurement, including its treatment of strings and malformed documents.

If the native implementation deliberately retains a narrower predicate temporarily, name it separately and prove the implication from native acceptance to certified admission. That supports a conservative route, but it does not justify an equality claim.

**Acceptance criteria:** rerun the agreement gate after rebuilding, covering the opener-rich string, many shallow sibling containers, the depth boundary, escaped quotes, block boundaries and malformed delimiter sequences. Preserve a negative control that restores the old opener-count rule and causes an agreement failure. Compare refusal reason and position where applicable, as well as the verdict.

## 4. Completion remains conditional on the substantive traversal

The new induction is useful. `walkLoopFinishes` states exactly how bounded revolutions yield a completed run. However, `WalkLoopStep` is not a small administrative premise: it quantifies over loop-head states satisfying `WalkInv` and requires either a complete progressing revolution with its cost bound or a bounded exit to return.

The final `walkCompletes_of_seed_loop` also retains hypotheses for the actual seed run, the invariant at its target, and the exit allowance. The module explicitly leaves construction of the geometry and staging from the ABI preconditions unwritten.

The proposition to close remains [Stage2WalkCompletes](https://github.com/scidonia/lean-llvm/blob/7636820/LeanLLVM/Refinement/JsonStage2Body.lean#L1673): from the actual precondition and staged arguments, the pinned body returns at `stage2Budget` under the selected helper environment.

### Suggested repair

Organise the remaining work around producers of the endpoint theorem's hypotheses:

1. Construct `WalkGeom` and `WalkStage` from the actual preconditions, proving any additional watermark or width facts needed.
2. Instantiate the entry, preheader and first-header runs at that same initial state; handle zero entries as well as the positive-entry seed.
3. Prove a dispatch-progress theorem from the carried invariant. Derive the branch-local register, read and callee facts instead of passing them indefinitely between conditional lemmas.
4. Compose the dispatch, merge, back edge and header, carrying the predecessor and phi bindings needed by the next state.
5. Exclude the trap arms and handle acceptance and refusal exits with actual counted runs.
6. Instantiate the corrected induction and budget argument to produce `Stage2WalkCompletes` without a traversal or completion premise.

A theorem named as completion should have only the intended preconditions and explicitly declared external assumptions. It should not take `WalkLoopStep`, `Stage2WalkCompletes`, a completed chain, or an equivalent bounded-run premise as an argument.

## 5. Helper correspondence: representation is improving, proofs remain

| Helper | Standing at this revision | Suggested next action |
| --- | --- | --- |
| `s2_init` | Actual emitted body run and contract proved. | Preserve the fixture and axiom-footprint checks. |
| `s2_value_pos` | Body captured and pinned; body-to-model proof open. | Prove the small branching body, including predecessor-selected phi and byte-value conversion. |
| `s2_after_value` | Body captured and pinned; body-to-model proof open. | Prove the root flag and stack-byte cases, with the positive-depth arithmetic bound. |
| `s2_string_body` | Pointer conversions and symbol operands now allow parsing; body proof open. | Instantiate bounded addresses and the symbol assignment, then prove the scan and writes against the helper contract. |
| `od_scalar_value` | Captured transformed body is representable; proof open. | Resolve number-helper correspondence, error writes and event/hash output correspondence. |
| `num_fast_el1` | Aggregate and binary64 forms are represented, but the inventory still records a literal-parsing refusal. | Fix signed floating-literal handling, recapture the body and inventory its remaining constructs before attempting the full trace proof. |

The parser's `parseDoubleLit` detects a leading negative sign but passes the signed text into the mantissa parser, whose accepted forms do not include that sign. Exponent syntax has some support already, so describe the negative-zero issue precisely rather than treating all exponent notation as absent. Preserve the negative-zero bit pattern when fixing the reader. Successfully parsing that literal would not establish that the entire number helper is otherwise accepted or correct.

The error-footprint mismatch remains explicit in the source: modelled helper refusal effects cover `[e, e + 16)`, while the emitted body also writes the message pointer at `e + 16`. The actual error object is 24 bytes. Widen and model the effect, or define a justified abstraction that hides the message field while still accounting for the physical write in framing. The present 16-byte unchanged-outside statement cannot certify that native store.

## 6. Trust surface and scope of the eventual claim

| Layer | What is supported | What remains trusted or to be established |
| --- | --- | --- |
| Lean proofs | Proof terms and standard-axiom footprints are recorded. | The Lean kernel and the intended interpretation of each statement. This review did not independently elaborate the new modules. |
| LLVM model | The syntax and executable semantics now cover more of the captured bodies. | Conformance to the admitted target LLVM fragment, including address bounds, aggregate layout, globals and floating-point behaviour. |
| Helper calls | Model helper contracts exist; `s2_init` has body correspondence. | Remaining emitted bodies implementing the models, with the correct physical footprints. |
| Policy admission | The algorithm model is related to the reference scanner. | The actual C transition, screening, class-array fill, refusal selection and wrapper implementing that model. |
| Stage-2 and pipeline | Local links, seed results, tail proofs and conditional assembly exist. | The actual bounded traversal and concrete semantic correspondence from produced events and arena bytes to the Lean parser's result. |
| Artifact binding | Capture records, fixture checks and installation infrastructure provide useful evidence. | The exact relationship between transformed proof fixtures and the native bodies compiled and linked for this route. |
| Native execution | The route stages buffers, invokes the kernel and exposes observations. | Compiler/backend/linker, ABI, wrapper implementation and platform assumptions within the stated deployment scope. |

Extending the semantics removes representation barriers; it also adds definitions whose intended LLVM meaning must be justified. Use the new binary64 rounding theory as evidence, while separately checking the exact operation and bit-pattern behaviour needed by the number helper. A verified compiler is not required to reach a useful milestone: a clearly scoped compiler and runtime assumption is acceptable. An undisclosed body-to-model assumption is not a completed body proof.

For the replacement criterion, completed-behaviour inclusion alone still permits an implementation with no completed behaviour. A concrete completion theorem closes that particular hole under this executable model. It does not by itself prove that the returned value is the specified parse result. Completion and result correspondence must both reach the installed route.

## 7. Recommended order and milestone gates

### Milestone A — repair the immediate inconsistencies

- Correct the potential and its allowance lemma; update the seed budget.
- Align native admission and tests with the chosen certified predicate.
- Correct documentation and regenerate evidence after the implementation changes.
- Add the long-string counted traversal and admission-disagreement controls.

**Gate:** the credit argument handles a complete long-string iteration, and freshly rebuilt admission checks agree on all declared boundary cases.

### Milestone B — complete stage 2 under named helper models

- Produce the dispatch-progress and revolution theorem from reachable invariant states.
- Complete the ABI-to-geometry construction and actual seed composition.
- Prove all exits and the total fuel bound.
- Instantiate `Stage2WalkCompletes` and then the full `Stage2WalkObligation`, explicitly naming the helper-model assumption.

**Gate:** a theorem about the pinned stage-2 body at its actual arguments, with no assumed traversal, completion or equivalent run witness.

### Milestone C — discharge helper and policy implementation assumptions

- Close the two small helper-body proofs first.
- Resolve the physical error footprint.
- Prove string and number helper correspondence, then scalar-value composition.
- Prove or explicitly retain a scoped assumption for native policy-body correspondence.

**Gate:** each helper assumption is replaced by a body theorem or remains clearly enumerated in the public claim.

### Milestone D — establish the native replacement claim

- Instantiate the parser-result correspondence for actual event and arena outputs.
- Bind the proof-facing bodies to the exact deployed native artifacts and wrapper configuration.
- Run fresh build, corpus, negative-control and artifact-correspondence checks at one recorded revision.
- Report consumer-level performance with admission, staging and copying included; distinguish it from kernel-only time and debug-output cost.

**Gate:** one reviewable claim stating the admitted input domain, result correspondence, completion guarantee, artifact identity and remaining trusted components.

## 8. Validation and limits of this review

This was a source review of the pinned revision and its changes from `94d607c`. During the review, the parser import-boundary check passed. The potential arithmetic above was independently evaluated: the example rises from 320 to 1088, contradicting the required decrease even at zero cost.

The native route check stopped at setup because its executable was absent. Nix, Lean, Lake and Clang were unavailable on the review host. No fresh Lean elaboration, helper capture, native corpus run or benchmark was performed here. Source-level findings should not be presented as independently reproduced compiler or runtime failures.

For implementation validation, use the repository's pinned Nix toolchain, source-build lock and memory ceiling. For example:

```bash
systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c bash probes/install/lake-locked.sh build \
  LeanLLVM.Refinement.JsonStage2WalkTraverse \
  LeanLLVM.Refinement.JsonPolicyModel LeanLLVMTest

systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c bash probes/install/lake-locked.sh env lean tests/core-extension.lean

systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c bash probes/json/route/build.sh

nix develop -c bash probes/json/route/check.sh
nix develop -c bash probes/json/route/correspondence.sh
```

Record which proof declarations were actually elaborated and which executable and artifact hashes were tested. The most valuable next result is a concrete stage-2 completion theorem whose operational premise has been discharged, followed by the remaining implementation correspondence proofs.
