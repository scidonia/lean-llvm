# lean-llvm: progress review and development handoff

**Date:** 15 November 2026  
**Reviewed commit:** [`4ca52e7c9ad7089942556ef6530f89d74401c08a`](https://github.com/scidonia/lean-llvm/tree/4ca52e7c9ad7089942556ef6530f89d74401c08a)  
**Immediate comparison:** [`10c523aad7b0d742508e2c7b06cbe9c3cf0b9b6d`](https://github.com/scidonia/lean-llvm/tree/10c523aad7b0d742508e2c7b06cbe9c3cf0b9b6d)  
**Earlier review baseline:** [`b40bbe4919678557df61284c86e11bf90b598ca4`](https://github.com/scidonia/lean-llvm/tree/b40bbe4919678557df61284c86e11bf90b598ca4)  
**Purpose:** Assess whether recent work advances usable certification, and identify the next proof closures needed for a real Lean replacement chain.

## 1. Assessment

**There is real progress. The latest change removes supplied execution evidence from a consuming proof.** The whitespace path now constructs its run, cost guarantee and endpoint facts from a classification of the input and relevant bounds. The enclosing composition actually invokes the new producer.

This is a meaningful local closure. It does not yet establish a complete certified native JSON replacement. The pipeline watermark defect identified in the previous review remains unchanged, and the stage-2 obligation still takes three substantial bundles of facts whose complete producers remain outstanding.

The most useful next milestone is a top-level result that can be instantiated from declared input staging and justified runtime assumptions. More helper proofs contribute to that goal only when their hypotheses can be produced from the states the program actually reaches.

## 2. Scope and verification limits

This report is pinned to `4ca52e7`; it does not claim to describe commits made after that snapshot. The immediate review examined the two commits following `10c523a`, their source changes and their use in the enclosing proof.

The changes affect the continuing-entry and whitespace proof modules and a draft probe. `PipelineDischarge.lean` and the top-level stage-2 obligation were unchanged in that comparison.

The Nix/Lean toolchain was unavailable in the review environment. The new proofs were inspected but not independently elaborated. No fresh native benchmark, fixture regeneration or object differential test was run for this snapshot. The source-boundary checks passed during the immediately preceding review at `10c523a`; that result should not be presented as a fresh proof build at `4ca52e7`.

## 3. What the latest update closes

### 3.1 The whitespace execution is derived

Previously, `HcontFacts` required the caller to supply a whitespace execution segment, its cost guarantee, a separate endpoint register fact and additional endpoint data.

The current version replaces those with a named endpoint function and an input classification:

| Former obligation or data | Current producer |
| --- | --- |
| `hRun`: execution of the whitespace skip | `contWsRunF` constructs the `WalkSegment`. |
| `hnRun`: the skip fits its share of the budget | `contWsPriceF` derives the required inequality. |
| `hcond_sl`: the stop state's `%cond350.i` register | Returned by `contWsRunF`. |
| `sl`: separately supplied endpoint state | `wsSlS` defines the endpoint from the path's parameters. |
| `n`: separately supplied run length | Obtained existentially from the execution theorem. |
| `b8`: separately supplied endpoint byte | The revised path uses the bundle's corresponding byte. |

[`contWsRunF`](https://github.com/scidonia/lean-llvm/blob/4ca52e7c9ad7089942556ef6530f89d74401c08a/LeanLLVM/Refinement/JsonStage2WalkRevolution.lean#L3185) returns an execution segment, the bound

```text
N ≤ 5 · (k − ix) + 10
```

and the endpoint's bound-register fact. [`contWsPriceF`](https://github.com/scidonia/lean-llvm/blob/4ca52e7c9ad7089942556ef6530f89d74401c08a/LeanLLVM/Refinement/JsonStage2WalkRevolution.lean#L3295) connects that count to the enclosing entry/byte allowance.

The [consuming composition](https://github.com/scidonia/lean-llvm/blob/4ca52e7c9ad7089942556ef6530f89d74401c08a/LeanLLVM/Refinement/JsonStage2WalkRevolutionSeg.lean#L820) calls `contWsRunF` and subsequently uses `contWsPriceF`. The result is integrated rather than merely available as an unused lemma.

### 3.2 What `hClass` still assumes

The new [`hClass`](https://github.com/scidonia/lean-llvm/blob/4ca52e7c9ad7089942556ef6530f89d74401c08a/LeanLLVM/Refinement/JsonStage2WalkRevolution.lean#L2314) is more than a statement that the first byte is whitespace. It includes:

- the source byte's whitespace dispatch class;
- the continuing-byte predicate over the relevant interval;
- the stopping predicate at `k`;
- strict advancement from the starting index to `k`;
- the initial inner-budget bound;
- the relationship between the entry position and the starting index.

These are logical facts about the input and state, rather than an assumed execution of the code being verified. Proving that these facts imply execution is genuine progress. However, a producer must still derive this complete classification from reachable parser states and the entry-stream specification.

Reducing the bundle from 64 to 59 fields is not itself a correctness metric: one conjunctive field can contain many obligations. The important change is that the run and its cost are now conclusions of a proof.

## 4. Broader progress since the earlier review

Several earlier concerns have been addressed and should not be reported as still open in their original form:

| Earlier gap | Current position |
| --- | --- |
| Parser bridge demanded semantics for arbitrary verdicts and output memories. | The bridge is now indexed by actual behaviour and actual output extents. Counterexample theorems refute the retired universal premise. |
| Concrete stage-2 execution reasoning was largely absent. | A pinned LLVM stage-2 body and extensive path reasoning now exist. |
| String helper needed an execution theorem. | `s2StringBodyBody_contract` establishes returning execution within its budget, its postcondition and frame. |
| The loop postcondition was supplied as `hpost`. | The staging-level obligation now derives the post from its terminal routes, relative to its remaining bundles. |
| Two-entry string-path composition was missing. | `stringPath_seg` composes fifteen links, conditional on its remaining residue. |
| Whitespace execution was supplied in the continuing bundle. | The current update derives it from `hClass`. |

Relevant evidence includes the [execution-indexed parser bridge](https://github.com/scidonia/lean-llvm/blob/4ca52e7c9ad7089942556ef6530f89d74401c08a/LeanLLVM/Refinement/JsonPipelineRefine.lean#L1218), the [string-body contract](https://github.com/scidonia/lean-llvm/blob/4ca52e7c9ad7089942556ef6530f89d74401c08a/LeanLLVM/Refinement/JsonStage2StringBody.lean#L6517), and the [composed string path](https://github.com/scidonia/lean-llvm/blob/4ca52e7c9ad7089942556ef6530f89d74401c08a/LeanLLVM/Refinement/JsonStage2WalkDispatchWitnessString.lean#L1954).

This is substantial movement toward implementation-level certification. The remaining concern is how quickly the component results become a usable top-level theorem.

## 5. P0: repair the pipeline watermark

### 5.1 The defect remains

[`Stage2Watermark`](https://github.com/scidonia/lean-llvm/blob/4ca52e7c9ad7089942556ef6530f89d74401c08a/LeanLLVM/Refinement/PipelineDischarge.lean#L1399) currently has the following shape:

```text
∀ S e,
  pipelineLoopExit mem args e →
  ∀ r ∈ stage2ExitRegions S, end(r) ≤ e.next
```

`pipelineLoopExit` internally supplies a carried-state witness, but the independently quantified `S` above is not constrained to be that witness. As a result, the premise ranges over unrelated memory regions.

For any admitted exit state `e`, choose an arbitrary carried record with `S.ndst = e.next`. `stage2ExitRegions S` includes `(S.ndst, 8)`. The watermark then requires:

```text
e.next + 8 ≤ e.next
```

This is impossible. The precise conclusion is that the current watermark is incompatible with an inhabited exit predicate. No claim about Lean's logical soundness follows; the conditional pipeline result instead has an unusable premise on the intended executions.

### 5.2 Required repair

Tie the regions to the actual carried state and establish the allocator bound along the real execution. Suitable designs include:

1. Index the exit predicate by its carried state, and state the watermark for that same state.
2. Include the required allocator bound in the carried invariant and return it with the exit witness.

Whichever design is selected, its initial bound must follow from justified staging assumptions, and the relevant steps and calls must preserve it. Merely replacing the free `S` with another global preservation hypothesis will leave the composition problem open.

The neighbouring `Stage2SlotKeeps` premise also quantifies over a carried state separately from the exit witness. Audit and repair that relationship while changing the interface; this report establishes the explicit contradiction for `Stage2Watermark`, not a separate counterexample for `Stage2SlotKeeps`.

### 5.3 Acceptance criteria

- Prove a regression result that the retired watermark, together with an admitted exit, implies `False`.
- State the replacement at the carried witness actually produced by the loop.
- Derive the allocator bound from staging and preserved execution facts.
- Instantiate the repaired tail on an inhabited execution case.
- Ensure the top-level pipeline result no longer requires the impossible universal watermark.

## 6. P1: produce the remaining stage-2 bundles

[`stage2WalkObligation_of_staging`](https://github.com/scidonia/lean-llvm/blob/4ca52e7c9ad7089942556ef6530f89d74401c08a/LeanLLVM/Refinement/JsonStage2WalkFlushPost.lean#L801) still takes:

| Premise | Required closure |
| --- | --- |
| `WalkContinueFacts` | Classify continuing entries from reachable states and construct each applicable branch's facts. The new whitespace run theorem belongs inside this producer. |
| `WalkLoopEnd` | Produce the last-entry facts and terminal memory/register facts at the states the dispatch actually reaches. |
| `WalkStringResidue` | Derive the remaining string-path helper results, lengths, address bounds and log/cursor relationships from staging and the certified callees. |

The immediate whitespace change improves the contents of the first bundle. It does not supply that bundle for all relevant reachable states, nor eliminate the other two.

### Acceptance criteria

- Each producer starts from the declared staging, invariant and justified reachability facts.
- No producer assumes the execution segment it is intended to establish.
- Classification is exhaustive for the claimed input domain, including refusal paths.
- Helper postconditions are applied at the actual call memory and allocator cursor.
- The stage-2 theorem obtains these bundles internally rather than taking them as unexplained external arguments.

If the current invariant admits states for which a required fact is false, strengthen the invariant or use an explicit reachable-state predicate. Do not silently narrow the advertised input domain to make the proof close.

## 7. Development discipline to reduce rework

The project is making progress, but repeated late discoveries of incompatible premises show that conditional pieces are being composed too late. The appropriate correction is to validate the source of each premise as part of developing its consumer.

For every substantial bundle or theorem, record:

| Item | Required evidence |
| --- | --- |
| Input assumptions | Exact state, memory, cursor and input facts. |
| Producer | A named theorem deriving them from staging or reachable states. |
| Consumer | The proof that actually uses the result. |
| Non-vacuity | An inhabited application case; this supplements rather than replaces the general producer. |
| Execution connection | The concrete body, call environment and returned outcome covered. |
| Build coverage | The module is imported by the intended target and its proof is elaborated. |

A useful progress measure is the set of externally supplied execution and semantic assumptions remaining at the chosen top-level theorem. Field counts, file counts and build success alone do not measure closure.

Retain the current distinction between path composition and premise production. For example, `stringPath_seg` is a completed composition theorem with an open residue producer; reporting either the whole path as absent or the entire string branch as unconditionally closed would obscure the real state.

## 8. Recommended order of work

1. **Repair and regression-test the watermark.** This is a known statement defect at the pipeline boundary.
2. **Derive `hClass` and its related continuation facts from reachable states.** Finish integrating the new whitespace execution producer into the general continuing-entry producer.
3. **Complete terminal and string-residue producers.** Remove the three unexplained bundle arguments from the staging-level stage-2 obligation.
4. **Close the caller-to-return theorem for a precisely stated domain.** Include returning execution, output relation, rejection behaviour and frame guarantees. Any restricted domain must be explicit and justified by the intended application.
5. **Exercise the certified implementation through Lean's intended call boundary.** State the remaining ABI, compiler and runtime assumptions and bind the proof to the installed artifact.

The final milestones require semantic correspondence to the reference parser as well as execution and memory correctness. A closed execution contract alone is not the complete JSON replacement claim.

## 9. Definition of the next successful milestone

The next milestone should be reviewable as one complete example rather than another collection of conditional helpers:

- [ ] A concrete input domain and justified precondition.
- [ ] A pinned implementation and explicitly identified callees.
- [ ] An inhabitable, correctly indexed pipeline watermark.
- [ ] Continuing, terminal and string-residue facts produced from execution invariants.
- [ ] Returning execution within the declared budget.
- [ ] A concrete relation between the output and the reference specification.
- [ ] Required refusal and memory-frame guarantees.
- [ ] Source elaboration and appropriate axiom checks.
- [ ] A real Lean caller exercising the covered replacement boundary.

**Current decision:** continue the work. The latest update advances the proof dependency chain in a useful way. Prioritise closing the top-level interface and its premise producers so that the substantial implementation proofs become a certification a real caller can use.
