# lean-llvm: closure handoff at 27bd727

**Date:** 17 November 2026  
**Repository:** [scidonia/lean-llvm](https://github.com/scidonia/lean-llvm)  
**Reviewed snapshot:** [`27bd727ae90882dc129bdd206702fef65dba7e7c`](https://github.com/scidonia/lean-llvm/tree/27bd727ae90882dc129bdd206702fef65dba7e7c)  
**Previous review:** [`f7d122f44dd3335400e6de6538e30976ca2ad43b`](https://github.com/scidonia/lean-llvm/tree/f7d122f44dd3335400e6de6538e30976ca2ad43b)

## 1. Objective and decision

The objective remains a usable replacement theorem: a real Lean caller establishes a declared precondition, invokes the low-level implementation, and receives the specified output and memory guarantees with returning execution. The replacement may be independently authored or synthesised; correctness must follow from the certification boundary, not its transformation history.

There is material progress at this snapshot. The arena-cursor mismatch is repaired, terminal log-word facts are derived from the invariant, and dispatch coverage has expanded. The next work is terminal pricing and the complete production of the remaining per-state payloads.

**Do not reopen the repaired arena equality as an outstanding defect. Do not treat the remaining conditional composition theorems as completed parser certification.**

`27bd727` itself is a documentation commit. The snapshot includes the preceding implementation repairs; the assessment concerns that complete snapshot.

## 2. Preserve the corrected boundary

The authoritative definitions are [`stage2Boundary`](https://github.com/scidonia/lean-llvm/blob/27bd727ae90882dc129bdd206702fef65dba7e7c/LeanLLVM/Refinement/JsonStage2Contract.lean#L1135) and [trust ledger §7.7](https://github.com/scidonia/lean-llvm/blob/27bd727ae90882dc129bdd206702fef65dba7e7c/docs/contract.md#77-the-stage-2-report-at-its-boundary).

### Two arena extents

| Quantity | Meaning | Required uses |
| --- | --- | --- |
| `ndstU` | Used extent: the cursor word actually reported by the run. | Caller-visible output length and interpretation of decoded output. |
| `ndst'` | Reserved extent represented by the walk's carried arena bound. | Presence, the reserved arena read, capacity and the touched-memory frame. |

The boundary carries:

```text
ndst0 ≤ ndstU ≤ ndst' ≤ ndst0 + n
```

The report writes `ndstU` to the caller's cursor slot. An escaping string can have a used extent strictly smaller than the reserved extent. Preserve that distinction through every adapter, output decoder and semantic relation.

The decoder's reserve/slack belongs to the touched-memory bound. In particular, the arena frame remains at the reserved extent plus the declared slack; reducing it to the used prefix would lose coverage of permitted decoder writes.

### Terminal words are now derived

`WalkMergeWords` and `WalkRefuseWords` now name the actual log word existentially, bounded by the carried cursor. [`walkMergeWords_of_inv`](https://github.com/scidonia/lean-llvm/blob/27bd727ae90882dc129bdd206702fef65dba7e7c/LeanLLVM/Refinement/JsonStage2WalkTargetPost.lean#L1647) and its refusal twin obtain those facts from `WalkInv.log_alen`.

The old requirement that the stored cursor equal the reservation bound was false for escaping inputs. Its specific source of vacuity is closed. The current `WalkLoopEnd` supplies the last-entry arm, not those retired log-word equations.

### Other results to retain

- The execution-indexed parser bridge and actual output extents.
- The repaired watermark, indexed by the actual carried state.
- The caller's proof that staged objects lie below its allocator cursor.
- The string-body execution theorem and discharged string residue.
- The whitespace execution and cost producers.
- The expanded dispatch: nineteen continuing-arm constructors and sixteen last-entry constructors, including the added depth and nested-string cases.

An enumeration and conditional arm proofs are not themselves a producer of an applicable arm at every reachable state. Keep those two claims distinct.

## 3. Current completion boundary

The [staging theorem](https://github.com/scidonia/lean-llvm/blob/27bd727ae90882dc129bdd206702fef65dba7e7c/LeanLLVM/Refinement/JsonStage2WalkFlushPost.lean#L864) still takes:

```text
hcont : for each geometry, WalkContinueFacts
hend  : for each geometry, WalkLoopEnd
```

Those are substantial execution-producer obligations. The lower-level [`stage2WalkObligation_of_premises`](https://github.com/scidonia/lean-llvm/blob/27bd727ae90882dc129bdd206702fef65dba7e7c/LeanLLVM/Refinement/JsonStage2WalkAssembly.lean#L3130) takes both `WalkPremises` and a rule asserting the record's postcondition at every behaviour.

Both theorem forms are useful composition interfaces. Completion requires constructing their arguments from the advertised precondition, invariant/reachability facts and justified helper contracts. Repackaging the same obligations under a payload or row name does not discharge them.

Separate the finish lines:

1. **Execution closure:** returning execution within budget and the stage-2 memory contract, under the explicitly named helper environment.
2. **Semantic replacement:** actual output and refusal behaviour related to the reference parser.
3. **Native Lean route:** the installed artifact and real caller meet that certification boundary, with the remaining toolchain assumptions explicit.

## 4. P0 — repair terminal pricing

### Finding

`RunLastFacts.hbudget` still requires:

```text
whitespace-run cost + extra-scan cost ≤ 6
```

`runLastFacts_of_staging` still takes `terminalPriceFits` as a premise. The document property names the restriction but does not prove it for the admitted input domain. The existing terminal-price module contains a computed counterexample to the entry-only allowance and arithmetic showing how document-byte credit can cover the work.

### Files

- `JsonStage2WalkTraverse.lean`
- `JsonStage2WalkDispatchThreeOfRun.lean`
- `JsonStage2WalkDispatchRun.lean`
- `JsonStage2WalkDispatchRunOfStaging.lean`
- `JsonStage2WalkTerminalPrice.lean`
- The loop induction and finalisation consumers of those prices.

All paths above are under `LeanLLVM/Refinement/`.

### Required implementation

1. Inspect `mergeLast` and the path by which its price is consumed by the loop induction. Identify every use of the entry-only terminal allowance.
2. State the terminal price using the same potential as the induction. The established potential already reads the document length through `boundary` at the exhausted index.
3. Prefer an additive spending statement of this conceptual shape, accounting for the actual control-step overhead:

   ```text
   segment cost + control overhead + potential(after) ≤ potential(before)
   ```

   This avoids accidental loss of credit through saturating subtraction. At a terminal index the remaining document-byte credit must still pay for the bytes scanned to reach that index.
4. Apply `runLast_price_with_credit` and the path's actual index, count and document-bound equalities. Prove those equalities from the execution state and entry stream.
5. Rewire the terminal arm, dispatch result and loop induction to consume that price.
6. Remove the constant-six condition and `terminalPriceFits` as external restrictions on otherwise admitted inputs. Preserve the old short-path result as a corollary if useful.

The existing total budget may already have sufficient byte credit. Establish that by proof; do not add an input-length restriction merely to satisfy the old local interface.

### Acceptance

- A formerly excluded terminal-price example is covered by the actual dispatch proof.
- Valid input with substantial trailing whitespace returns within the declared total budget.
- The general terminal producer does not assume the discarded entry-only restriction.
- Every affected terminal and induction price composes under one documented cost convention.

## 5. P1 — close per-class payloads and helper calls

### Scope

The current separation between class, document, ABI and traversal evidence is useful. Use it to close the evidence, not merely inventory it.

Read these modules together:

- `JsonStage2WalkDispatchSupply.lean`
- `JsonStage2WalkDispatchClassRows.lean`
- `JsonStage2WalkDispatchResidual.lean`
- `JsonStage2WalkDispatchDefaultLane.lean`
- `JsonStage2WalkDispatchSegments.lean`
- `JsonStage2WalkDispatchSeams.lean`
- `JsonStage2WalkHcontSeamInv.lean`
- The corresponding arm producer and its consumer.

### Required implementation

For each remaining row, maintain a compact ledger:

| Item | Required content |
| --- | --- |
| Statement | Exact state, memory, cursor, class and index to which the row applies. |
| Producer | Named theorem from staging, the predecessor's post or reachable-state facts. |
| Consumer | The proof that actually uses the result. |
| Remaining assumption | Precisely identified input fact or declared helper contract. |

Then close the groups:

**Document/lane rows.** Read the actual entry lane and document byte through the proved preservation steps. Case-split on the byte or depth when necessary. A fixed geometry does not give a predetermined byte value; it can still provide the read from which an exhaustive case split proceeds.

**Helper ABI rows.** Establish each helper's precondition at the actual call memory and allocator cursor. Use its returning-execution/contract theorem to obtain its answer and postcondition. Carry those results into the next call. Preserve call ordering and do not substitute a head-state answer for a later call's answer without a correspondence proof.

**Seam rows.** Use the existing seam-invariant transports. Audit presence, log words, stack bytes, cursor placement and block-keyed event bounds at the seam's own state. The head invariant alone is not automatically the seam invariant.

**Traversal rows.** Derive round, guard, byte-read and preservation obligations from the scan step and bounded input window. Preserve the needed endpoint registers and memory facts through the induction.

**Arm-specific segments.** Connect the existing head, span and tail producers. A wrapper that still takes `hHead`, `hTail` or a route segment has not closed that execution dependency; name and compose the missing producer.

Audit quantifiers as part of this work. A row for one class should be guarded by that class and the corresponding reachable state. Requiring a scan-free row at every head can recreate the earlier incompatible-bundle problem.

### Acceptance

- Every continuing and last-entry arm is constructible from the declared domain and reachable-state evidence.
- The string opener is handled at both zero and positive depth, including the implemented key/merge/refusal routes.
- Closing delimiters at zero depth and openers at the depth cap use their actual refusal paths.
- No arm producer assumes the execution segment it is meant to establish.
- Every remaining trusted helper boundary is explicitly listed, not hidden in an unexplained payload.

## 6. P1 — close stage 2 from staging

### Required implementation

After pricing and payload closure:

1. Construct `WalkContinueFacts` by exhaustive dispatch at every relevant continuing head.
2. Construct `WalkLoopEnd` by terminal dispatch. Reuse `walkMergeWords_of_inv` and `walkRefuseWords_of_inv`; those log equations are no longer supplied obligations.
3. Build the loop-step premise and then `WalkPremises` from the actual ABI/staging conditions.
4. Derive the actual postcondition from the terminal runs at their returned memories.
5. Instantiate `stage2WalkObligation_of_premises` with those proofs, or provide a direct theorem with the same final guarantees.

If `WalkInv` admits states that violate a fact needed by the dispatch, either strengthen it with a preserved clause or use a reachable-state predicate through the induction. Do not require a false property of every state admitted by the weaker invariant.

### Acceptance

The final stage-2 theorem has no externally supplied:

- `WalkContinueFacts` or `WalkLoopEnd`;
- equivalent payload/row family concealing an unproved run;
- arbitrary correctness rule for the postcondition;
- terminal input restriction introduced solely to satisfy the old budget.

It establishes returning execution at the contract's budget and the postcondition of the actual outcome. A caller can instantiate it from the stated input/staging conditions and the explicitly identified implementation environment.

## 7. P1 — close the pipeline adapter and count-slot frame

`pipeline_satisfies_at_stage2_of_exitStage2` still needs the concrete stage-2 call contract and `Stage2SlotKeeps`.

### Required implementation

- Supply the actual stage-2 selection using the closed stage-2 theorem and the staged-to-native ABI adapter.
- Derive preservation of the caller's `%nk` and `%nxp` slots from separation and the concrete touched regions.
- Include the arena reserve/slack, event writes, report slots, appended scratch objects and fresh allocation interval in that argument.
- Use the existing allocator watermark and model caller cursor proofs; preserve their connection when altering staging.
- Ensure used versus reserved extents survive through `pipelineUnitsPost`, `pipelineOutputExtents`, `SigmaFrame` and the caller's output extraction.

Separation in the precondition must be combined with a write/frame theorem to conclude preservation. If the generic stage-2 ABI cannot name the caller's count slots, prove an adapter-specific framed contract for the actual call.

### Acceptance

- Pipeline composition receives the concrete stage-2 instance internally.
- Count-slot preservation is proved, not passed as an external global assertion.
- The caller reads the used cursor and interprets only that used prefix as decoded output.
- Frame and capacity obligations retain the reserved extent and slack.

## 8. Semantic replacement and native use

Execution closure is the next proof milestone, not the end of the intended claim.

### Reference-parser correspondence

Instantiate the execution-indexed parser bridge with a concrete arena/event relation. Prove accepted values, strings, containers and binary64 numeric observations. State the selected refusal/error-offset policy and resource-limit behaviour consistently on both sides.

Where the post supplies a reserved arena read, derive the used-prefix read using `ndstU ≤ ndst'`. State semantic output correspondence at the used prefix and the actual event cursor. Keep the larger extent for memory reasoning.

### Helper and artifact boundaries

For each forwarded helper, identify whether its correctness theorem covers the actual emitted body or a model of its behaviour. Close or explicitly declare the remaining implementation correspondence, numeric-operation and approximation assumptions.

Document fixture capture rewrites, the staged ABI, helper call boundaries and differences from an inlined native build. Identify the exact implementation covered by the theorem and the object installed by the caller. Hash/rebuild checks establish identity evidence; they are not compiler-preservation theorems.

### Lean caller and performance

The real Lean wrapper must establish presence, capacities, padding, separation, lifetimes and cursor bounds, and decode the output according to the proved relation. Benchmark this route, including staging/copying costs the application pays for.

A first useful deployment may trust named compiler/backend/ABI components. State that trust boundary. Verification of the entire Lean compiler is not a prerequisite for closing the immediate parser proof, and must not be implied by completion of that proof.

## 9. Concrete applications and regression cases

Use the reference specification for the exact expected values, rejection policies and offsets.

| Case | Required evidence |
| --- | --- |
| `0`, `null`, `true`, `false` | Ordinary scalar/literal dispatch and terminal execution. |
| `""`, `"abc"`, `"\u0041"` | String execution, decoded output and used/reserved distinction. |
| `0 ` and `null` followed by substantial whitespace | Valid terminal execution covered by document-byte credit. |
| `["a"]`, `{"a":"b"}` | Positive-depth string/key paths and finalisation. |
| `[]`, `{}`, `[0]`, `{"a":1}` | Container transitions and closing delimiters. |
| Empty or whitespace-only input, `}`, lone quote, malformed numeric lexemes | The implemented refusal paths and their actual report memory. |
| Inputs near the nesting cap | The depth split and reserve/refusal behaviour. |
| 32/64-byte boundaries, escaped and multibyte tails | SIMD carry, UTF-8 completion and padded reads. |

At least the escaped-string, long-trailing-whitespace and nested-string cases should instantiate a complete returning run and postcondition through the real seed/dispatch route. Branch examples supplement universal producers; they do not replace them.

## 10. Build and review evidence

Follow the current checkout's `AGENTS.md`. At this snapshot the memory ceiling is **12 GiB RAM plus 4 GiB swap**, and builds must use the lock wrapper:

```bash
systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=4G --quiet \
  nix develop -c bash probes/install/lake-locked.sh build
```

Record the actual command status, not a trailing log-filter's exit code. Ensure all cited proof modules are imported by the intended target, pin stable soundness axiom footprints, and re-elaborate source modules when their `include_str` fixtures change.

Both source-boundary checks passed during this review:

```bash
nix develop -c bash tests/json-import-boundary.sh
nix develop -c bash tests/itree-boundary.sh
```

**Verification limit:** the reviewer ran those scripts directly as source checks. Nix/Lean was unavailable, so Lean elaboration, native fixture regeneration, object differential tests and performance measurements were not independently rerun. Treat the repository's reported full-build result separately from this review evidence.

## 11. Completion checklist

- [ ] The terminal price uses the same document-byte potential as the loop induction.
- [ ] General terminal execution does not assume the constant-six price restriction.
- [ ] Per-class payloads are produced at actual reachable states and call memories.
- [ ] `WalkPremises` and the postcondition rule are constructed from declared assumptions.
- [ ] The stage-2 theorem no longer requires externally supplied execution bundles.
- [ ] Pipeline count-slot preservation is derived from the actual frame.
- [ ] Used-length output semantics and reserved-extent memory semantics remain distinct throughout.
- [ ] Complete escaped-string, trailing-whitespace, nested-string and refusal applications are checked.
- [ ] The reference-parser relation is concrete and instantiated at actual outcomes.
- [ ] The native Lean route, artifact identity and remaining trust assumptions are documented and tested.

The arena-boundary repair is complete enough to build upon. The next review should assess which top-level assumptions have disappeared and which complete caller-to-return results can be instantiated, with terminal pricing the first remaining repair.
