# lean-llvm: correctness review, status report and completion plan

**Reviewed commit:** [`45ce69e9e454c712ba9cd2ebfe929d5358e080c4`](https://github.com/scidonia/lean-llvm/commit/45ce69e9e454c712ba9cd2ebfe929d5358e080c4)  
**Comparison:** `59191bb6d4a0670d6c1e4c7ad01e37db4c7a0725`  
**Review date:** 14 November 2026  
**Repository:** `scidonia/lean-llvm`  
**Scope:** JSON stage-2 execution and completion, helper-body correspondence, caller staging, parser correspondence and the native trust surface.

## 1. Executive assessment

There is substantial implementation progress. The development now includes concrete counted dispatch-refusal witnesses, more composed finish paths, a counted prefix to the extra-token scan, and additional string-arm proofs relating actual instructions to the model's reads and branches. This is more concrete than the earlier collection of isolated block lemmas.

The central correctness milestone has not yet changed: `Stage2WalkCompletes` is not supplied unconditionally from the intended ABI preconditions, and `stage2WalkObligation_of_premises` still takes both `WalkPremises` and an externally supplied `hpost`. The complete string-helper contract is also absent. The numeric body's general conversion proof and the parser-result correspondence remain separate substantive obligations.

The next work should prioritise connecting the available branch proofs to an endpoint, rather than expanding supporting vocabulary without a producer for the endpoint's hypotheses.

Four issues deserve immediate attention:

1. The new three-outcome decomposition is more general, but the completion route still uses the older index-based dispatch/exit assembly.
2. Terminal charging still uses `entryPos` beyond the entry list, where it returns zero.
3. The string-helper precondition has been strengthened to include the previously missing memory facts. Their production by the actual caller remains unproved, especially incoming presence of the private alloca slot.
4. The last-entry bundle and its bridge demonstrate a particular path under substantial assumptions. The bridge still requires a non-empty stack, so it is not general coverage of successful last-entry execution.

**Recommendation:** aim next for a completed staged all-whitespace run and one successful complete string-helper contract. In parallel in the work plan, replace the old loop assembly with a direct outcome-based rule and repair terminal accounting. Do not describe the whole native JSON route as verified until completion, semantic correspondence and artifact binding are connected.

## 2. What changed and what it establishes

The diff from the last reviewed tree changes 25 files, predominantly proof modules. It does not change the native kernel or adapter implementation. The following are the useful proof advances; their presence in source is distinct from an independent fresh Lean build by this review.

| Development | Evidence | Assessment |
| --- | --- | --- |
| Concrete early refusal | `JsonStage2WalkDispatchWitness.lean` and its state-stack companion compose named paths to the refusal copy. | Real branch-level execution evidence, including a closing bracket at depth zero with entries remaining. General dispatch coverage is still open. |
| Finish-tail composition | `JsonStage2WalkFinishPath.lean` composes the normal and refusal routes after the merge. | Useful terminal-run proofs. It correctly distinguishes the walk frame from the larger report-writing frame. |
| Counted head prefix | `JsonStage2WalkPrefixCount.lean` and the head-chain modules expose concrete segment counts. | Improves on a longest-path census. Assumptions about the token class, operands and helper calls still need production. |
| Last-entry construction | `HlastFacts`, `hlast_toMerge`, `hlast_finish`, `hlast_refuse` and `hlastFacts_of_staging`. | Some fields now follow from the invariant or entry values. The bundle remains conditional and path-specific. |
| String model/execution bridge | Model-arm equations, framed callee reads, scan-exit characterisation and form-1 conclusion theorems. | Significant progress towards the whole helper contract. The full decoded/refused conclusion and final assembly remain open. |
| New helper precondition | `s2StringBodyPre` now names output presence, region separation and read/write separation. | Missing facts are visible. This changes the interface and creates caller obligations; it does not discharge them. |
| Scoped flush | The earlier `WalkFlushAt` repair remains in use; more operand and output-state facts are exposed. | The universal-memory defect stays repaired. The staged completion/boundary producer still needs closing. |

Sources: [dispatch witnesses](https://github.com/scidonia/lean-llvm/blob/45ce69e/LeanLLVM/Refinement/JsonStage2WalkDispatchWitness.lean), [finish paths](https://github.com/scidonia/lean-llvm/blob/45ce69e/LeanLLVM/Refinement/JsonStage2WalkFinishPath.lean), [counted prefix](https://github.com/scidonia/lean-llvm/blob/45ce69e/LeanLLVM/Refinement/JsonStage2WalkPrefixCount.lean), [string development](https://github.com/scidonia/lean-llvm/blob/45ce69e/LeanLLVM/Refinement/JsonStage2StringBody.lean).

## 3. Findings and required repairs

### F1 — The outcome decomposition improved, but the endpoint still uses the old assembly

**Priority: high. Status: partially addressed.**

`WalkDispatchThree.ofContinueAndLast` no longer insists that the `C.k + 1 < G.nep` branch continue. Its `hcont` now returns any `WalkDispatchOutcome`. This is a genuine improvement: early refusal and consuming the final two quote entries can be expressed in that branch.

However, `walkLoopStep_of_dispatch_exit` still takes the older `WalkDispatch` and `WalkExit`, splits on `C.k + 1 < G.nep`, and selects a revolution in the first case. It now additionally takes the loop-head arena-word equality. It is not an assembly from the new three outcomes.

The earlier witnesses remain relevant to this old route:

- A standalone string consumes opening and closing quote entries. At `k = 0`, `nep = 2`, the old split chooses continuation even though the actual next index is terminal.
- Malformed input such as `] 0` refuses at the first entry while another entry remains. It does not return to the merge for another revolution.

The new concrete refusal witness addresses one execution of the second case. It must feed a new global assembly, rather than be passed through a predicate that still requires continuation.

**Repair:** prove a loop-step rule directly from a dispatch result that either returns to a valid next loop head or reaches terminal finalisation. Interpret `finish` as entry-stream exhaustion at the merge, not as proof of parser acceptance: finalisation can still reject an unclosed container or an unfinished root.

Use existential terminal verdicts, or another precisely justified result relation, if one fixed verdict for every state satisfying the chosen invariant is too strong. Prove actual result facts rather than assume uniformity.

**Acceptance:** an exported producer covers the real standalone-string and early-refusal runs and supplies the loop rule without the old `WalkDispatch` assumption.

Source: [dispatch and assembly definitions](https://github.com/scidonia/lean-llvm/blob/45ce69e/LeanLLVM/Refinement/JsonStage2WalkAssembly.lean).

### F2 — Terminal credit still loses the remaining byte allowance

**Priority: high. Status: unresolved.**

The normal terminal constructor still requires:

```text
p + 2 ≤ 32 × (k2 − k)
        + 8 × (entryPos k2 − entryPos k)
```

At stream exhaustion, `k2 = nep`. `entryPos` uses `getD ... 0`, and the new `entryPos_nep` theorem explicitly proves that `entryPos nep = 0`.

Consequently, the terminal byte-difference term vanishes. `hlast_finish` currently proves a fixed short witness fits the entry allowance: its counted prefix reaches the merge in 20 steps and the inequality reduces to `22 ≤ 32`. This is valid arithmetic for that witness. It does not establish a general bound for a final scalar whose trailing whitespace requires a long scan.

**Repair:** define a credit boundary on indices through the terminal index:

```text
boundary(k) = entryPos(k)  for k < nep
boundary(nep) = input length
```

Prove its bounds and monotonicity, and use it for terminal charging. Alternatively, charge terminal work directly against the remaining potential. Keep this proof quantity separate from actual entry loads.

**Acceptance:** prove and count a complete run for a final scalar followed by a large whitespace suffix. The proof must derive the count from the scan trace, not insert a hand-selected price row.

Source: [the terminal-index lemma and last-entry price](https://github.com/scidonia/lean-llvm/blob/45ce69e/LeanLLVM/Refinement/JsonStage2WalkDispatchWitnessHlast.lean).

### F3 — Stronger string-helper staging needs an actual caller producer

**Priority: high. Status: declared at the interface; caller correspondence open.**

The previous review identified that the string-memory joins required facts absent from `s2StringBodyPre`. This revision adds them: output-region presence, pairwise separation, private-slot presence at `next`, and separation between the body's reads and writes.

Making assumptions explicit is an improvement. It also narrows the set of calls covered by the helper contract. Updating a precondition is not the same as proving the deployed call satisfies it.

The requirement:

```text
readBytes mem next 8 ≠ none
```

still needs particular care. `%ei` is allocated by the helper. In this executable model, `alloca` advances the cursor and does not populate bytes; its later clear creates or replaces those bytes. The native caller does not normally pre-initialise a callee's private stack slot. A staging watermark establishing separation does not establish incoming readability there.

The stage-2 caller proof must therefore either produce this fact at the exact current allocator cursor, or the helper's proof interface must accommodate a fresh slot. No such derivation from the stage-2 caller was found in this review. The call-site development often takes the helper answer and frame facts as hypotheses instead.

There are two reasonable approaches:

1. **Preserve the incoming helper domain.** Weaken write-order lemmas to handle a fresh private slot crossing already-present caller-owned regions. Supply its separation from allocator freshness, and account for the initial clear. Do not assume private bytes exist before the allocation/clear.
2. **Adopt stronger staging deliberately.** Define the initialisation step that supplies the new region, relate that step to the actual native execution, and propagate the revised contract through every caller and the boundary theorem.

For caller-owned `dst`, `outn` and error objects, derive presence and separation from the existing staged objects. For the private slot, keep freshness and initialisation distinct.

The claim in the precondition commentary that all regions must already be present is stronger than the demonstrated need of the current join lemmas. Those lemmas provide sufficient hypotheses; necessity for native correctness or for every possible exact-memory proof has not been established.

**Acceptance:** a named call-site theorem derives the full new `s2StringBodyPre` from actual reachable caller facts, or a revised helper theorem handles the fresh-slot case. Then prove `s2StringBodyBody_contract` with its own run, post, allocator effect and footprint.

Source: [strengthened helper precondition](https://github.com/scidonia/lean-llvm/blob/45ce69e/LeanLLVM/Refinement/JsonStage2Helpers.lean).

### F4 — The last-entry bridge is still a branch theorem, not universal coverage

**Priority: high. Status: partial execution evidence.**

`HlastFacts` packages a particular default/scalar path, its helper calls, scan landing and merge facts. `hlastFacts_of_staging` derives more fields than before, including the head byte and merge depth from invariant-carried information. That is useful.

It still receives document-class bits, a counted tail segment, scan facts and other inputs. A producer named “of staging” does not make these all consequences of memory layout; token-class choices must be established by case analysis on the actual document byte.

Furthermore, `walkDispatchThree_ofLastFacts` still takes:

```text
hb : ∀ C s f, the merge depth is nonzero
```

and its `hlast` invocation selects the refusal proof. This excludes depth-zero cases that should be allowed to reach normal finalisation. Moving polarity out of the bundle avoids making every bundle inherently nonzero, but the universal bridge still requires that polarity externally.

The source also notes that `finish` at the merge and a later refusal prefix can both describe the same execution. Use that distinction consistently. A merge-reaching witness is not an acceptance theorem, and a refusal-only bridge is not general last-entry coverage.

**Repair:** keep class-specific bundles local to their branch proofs. Produce a dispatch result by a complete case split over actual input classes and actual helper answers. Do not require every last entry to inhabit the same scalar-path bundle or satisfy a non-empty-stack condition.

**Acceptance:** cover depth-zero successful completion, non-empty-stack rejection, terminal strings consuming two entries, and early parse refusal, all through the same exported outcome producer.

Source: [last-entry proofs and bridge](https://github.com/scidonia/lean-llvm/blob/45ce69e/LeanLLVM/Refinement/JsonStage2WalkDispatchWitnessHlast.lean).

### F5 — The loop-head arena equality remains an external producer obligation

**Priority: medium/high. Status: identified but unproved globally.**

The assembly now explicitly takes the equality between the loop-head arena word at `z + 48` and `C.alen`. `WalkInv.log_alen` supplies an inequality because intermediate states may temporarily have a reserved carry ahead of the stored cursor.

This distinction is appropriate. It does not follow that the equality can simply be assumed at all loop heads. The writer census proves which direct stores target `%alen`; it does not, by itself, prove the desired word survives all calls, aliases and paths.

**Repair:** introduce a loop-head predicate containing `WalkInv` plus the properties true specifically at the head, such as the refilled inner allowance and arena-word equality. Establish it at the seed and preserve it across complete revolutions. Keep the weaker mid-block invariant for scan and reservation states.

This also gives the last-entry construction a legitimate source for head-only facts instead of repeatedly adding them to bundle signatures.

**Acceptance:** the loop rule consumes this head predicate, and its seed and successor producers prove every field. No universal head-word premise remains uninhabited outside the reachable-state argument.

## 4. Current proof and trust status

| Claim | Standing at this revision |
| --- | --- |
| `s2_init`, `s2_value_pos`, `s2_after_value` body contracts | Present from earlier work. |
| String helper | More real instruction/model correspondence, including form-1 conclusions. Whole contract absent; decoded/refused drafts are explicitly uncompleted. |
| Number helper | Body captured and pinned; empty-lexeme refusal contract present. General accepting conversion remains open. |
| Scalar-value helper | Complete body-to-model correspondence remains open. |
| Stage-2 completion | Conditional on `WalkPremises`; not instantiated from the intended ABI preconditions. |
| Stage-2 boundary post | Supporting invariant/report and finalisation lemmas exist; endpoint still takes `hpost`. |
| JSON semantic correspondence | Event/arena/verdict relation to the reference parser remains an additional obligation. A memory-boundary contract alone does not prove JSON correctness. |
| Native admission and escape-list guard | Runtime evidence and model reasoning remain useful; general body correspondence is not supplied by this diff. |
| Installed native artifact | Capture rewrites, layouts, erased flags, flattened allocations, wrapper and actual object binding still require their stated correspondence assumptions. |
| Native execution | Compiler/backend/linker, ABI and platform assumptions remain outside kernel checking. |

The repository's draft Markdown files are useful work records, but their unelaborated declarations and remaining goals are not proof coverage. Completion claims should be based on declarations in built Lean modules and on their explicit assumptions.

The non-vacuity question remains central: a subset relation over completed outcomes does not force an implementation to return. A concrete completion theorem at the actual precondition excludes that failure under the deterministic executable model. Result correspondence and artifact correspondence must then connect that returned outcome to the intended parser and installed code.

## 5. Implementation plan

### Phase A — repair the proof interfaces before generalising more paths

1. Adopt a terminal credit boundary, prove its monotonicity, and update the terminal outcome price.
2. Make the outcome-based dispatcher the input to the loop-step theorem. Retire the old forced-continuation route from the endpoint.
3. Separate loop-head facts from intermediate-state facts. Seed and preserve the head predicate.
4. Resolve the private-slot domain decision for the string helper and update every caller producer accordingly.

**Gate:** the main proof interfaces can describe all required executions and have concrete sources for their staging assumptions. No new general traversal should be built on an impossible or artificially restricted premise.

### Phase B — finish two complete cases with their actual posts

**B1: all-whitespace input.** Compose the actual entry-zero run, flush store, refusal copy and return from the ABI staging. Derive the verdict, error offset, cursor results and frame at the returned memory.

**B2: standalone string.** Prove the full string-helper contract and consume it in the walk. Cover a plain string, an escaped decoded string and an invalid escape/refusal. Include the two-entry terminal advance and a fresh private slot.

**Gate:** exported staged-run theorems supply both completion and the boundary post. They do not take a completed chain, traversal or equivalent whole-case run as a hypothesis.

### Phase C — close all dispatch branches and their counted scans

1. Classify the current input byte and dispatch using branch-specific facts produced inside that case.
2. Compose the remaining finite paths with their helper contracts and scan inductions.
3. Return continue, stream-exhausted or early-refusal evidence from the actual result.
4. Prove the actual cost inequalities, including trailing whitespace and terminal work.
5. Account for traps by showing their guards are clear under the intended capacity and stack assumptions.

**Gate:** one general dispatch producer covers all admitted control-flow outcomes. A set of representatives or opcode counts is insufficient.

### Phase D — instantiate the stage-2 endpoint

1. Produce `WalkPremises` from the actual ABI preconditions, or simplify it away once the concrete producers exist.
2. Instantiate `Stage2WalkCompletes ... stage2SubCalls`.
3. Derive the final boundary directly from actual return-memory observations and the appropriate report frame.
4. Instantiate `Stage2WalkObligation` without externally supplied `hpost`.

**Gate:** a downstream Lean module can invoke the endpoint theorem with the documented staging and named external assumptions only. No dispatch, exit, flush or completed-run premise remains hidden in a bundle.

### Phase E — establish the native replacement claim

1. Discharge the remaining numeric and scalar helper-body obligations, or explicitly scope an intermediate claim around those assumptions.
2. Instantiate the parser semantic relation over the produced events, arena bytes, verdict and error information.
3. Connect transformed proof fixtures to the exact native route, including diagnostic-pointer rewrites and erased instruction flags.
4. Record admission/guard correspondence and wrapper obligations.
5. Rebuild and run corpus, boundary, mutation-control and artifact checks at the same pinned revision.

**Gate:** a single public statement identifies the input domain, completion guarantee, parser-result correspondence, artifact identity and remaining trusted components.

## 6. Regression and evidence requirements

| Scenario | What it must establish |
| --- | --- |
| Long standalone string | Two-entry consumption, whole helper result, terminal index and finalisation. |
| Final scalar with substantial trailing whitespace | Actual byte-dependent trace fits the terminal credit. |
| `] 0` or an equivalent early malformed input | Refusal is available before the final entry. |
| All-whitespace non-empty input | Zero-entry staging reaches the specified refusal and post within budget. |
| Escaped string with a fresh `%ei` slot | The helper's private-allocation treatment matches its real caller domain. |
| Decoded and refused string arms | Every strengthened precondition is produced at the call; the output and footprint match. |
| Depth-zero and non-empty-stack finalisation | The outcome assembly handles both without assuming one polarity globally. |
| Duplicate-address memory control | The invalid plain-map equivalence remains rejected. |

Add a small downstream proof-consumption file for each completed milestone. It should state the intended theorem directly and invoke the exported endpoint, with axiom-footprint checks. This makes it harder for a conditional wrapper to be mistaken for a closed result.

Use a hypothesis ledger with four columns: required fact, exact producer, current consumer, and evidence that the producer's premises hold at that use. Stop propagating a fact when its only producer is another hypothesis with a different name.

## 7. Validation performed and limitations

This review fetched and fast-forwarded to the pinned commit, inspected the diff and key endpoint/branch/helper declarations, and performed these independent lightweight checks:

| Check | Result |
| --- | --- |
| `git diff --check 59191bb..45ce69e` | Passed. |
| `bash tests/json-import-boundary.sh` | Passed, including its detector controls. |
| Working-tree status | Clean after the source review; no implementation changes made. |
| Lean/Nix/Lake/Clang availability | Unavailable on the review host. |
| Fresh proof elaboration | Not performed. |
| Fresh native execution, artifact capture or benchmark | Not performed. |

Source-level findings and inspected proof terms should not be presented as independently reproduced Lean or runtime failures. Conversely, the absence of a local build is not evidence that the repository's source proofs fail to elaborate.

Run the required validation in the pinned repository environment, under its memory ceiling and source lock. For example:

```bash
systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c bash probes/install/lake-locked.sh build \
  LeanLLVM.Refinement.JsonStage2StringBody \
  LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessHlast LeanLLVMTest

systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c bash probes/install/lake-locked.sh env lean tests/stage2-walk-credit.lean

systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c bash probes/json/route/build.sh

nix develop -c bash probes/json/route/check.sh
nix develop -c bash probes/json/route/guard.sh
nix develop -c bash probes/json/route/correspondence.sh
```

The next review should begin with the actual exported endpoint types and their premise producers. The strongest evidence of completion will be the disappearance of traversal and postcondition assumptions from those types, supported by fresh elaboration and the corresponding staged execution cases.
