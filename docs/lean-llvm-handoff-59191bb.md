# lean-llvm review and implementation handoff

**Reviewed commit:** [`59191bb6d4a0670d6c1e4c7ad01e37db4c7a0725`](https://github.com/scidonia/lean-llvm/commit/59191bb6d4a0670d6c1e4c7ad01e37db4c7a0725)  
**Compared with:** `a8195c3679a4cad594966717481622ca17e9e1e6`  
**Date:** 13 November 2026  
**Scope:** stage-2 completion, dispatch outcomes, terminal credit, the string-helper body contract, and remaining native-replacement assumptions.

## Assessment

The new tree makes useful progress in two files: `JsonStage2StringBody.lean` and `JsonStage2WalkAssembly.lean`. It adds string-memory absorption and decoded/refused join theorems, relates the scan counter to the model's `takeWhile` result, and develops entry framing and invariant assembly. The invalid plain-map memory proposal is now explicitly refuted by a checked counterexample.

The full correctness endpoint remains conditional. `stage2WalkCompletes_of_premises` still takes `WalkPremises`; `stage2WalkObligation_of_premises` still takes both `WalkPremises` and `hpost`. There is no complete string-helper contract theorem at this revision.

The immediate priorities are:

1. Replace the old index-based dispatch assembly with the actual three-outcome relation.
2. Repair terminal byte credit by using the document end at the terminal index.
3. Establish that the new string-memory join premises follow from the actual helper/caller staging. In particular, their requirement that the private alloca slot already be readable does not follow from the current helper precondition.
4. Finish one complete staged execution and its boundary post, then generalise it to the full endpoint.

This is progress towards a proof, not yet a completed verified native JSON replacement.

## 1. Progress since the previous review

| Area | New source evidence | What it establishes |
| --- | --- | --- |
| Duplicate addresses | `writeByte_not_map_of_duplicate` | The proposed plain `List.map` update does not model first-match writes when duplicate addresses exist. The false route is identified rather than used as a theorem. |
| Write-order reasoning | `writeBytes_absorb_one` | An earlier write can be absorbed across intervening disjoint writes under explicit presence assumptions. |
| String output memory | `s2StringBodyMemory_decoded`, `s2StringBodyMemory_refused`, `s2StringBodyErrRecord_reconciles` | The body/model write sequences agree under the stated presence, separation and arithmetic hypotheses. |
| Scan/model correspondence | `takeWhile_length_of_counter`, `scanCounter_eq_takeWhile` | A counter with the stated visited-prefix and stopping properties equals the model's `takeWhile` index. |
| Entry memory | Narrow write-region and store-list lemmas; `readBytes_frame` | Reads outside the declared writes are preserved, supporting entry-state construction. |
| Initial invariant | `walkInvSeat`, register facts, `walkEntry_inv_at` | Invariant construction and preservation are assembled from named register, memory, frame and staging facts. |

The scoped flush repair from the preceding tree remains in use: `WalkPremises` consumes `WalkFlushAt` at the actual memory and cursor, and the false universal `WalkFlush` definition is absent. Do not reopen that old defect; finish the producer of the scoped branch.

Sources: [string-helper development](https://github.com/scidonia/lean-llvm/blob/59191bb/LeanLLVM/Refinement/JsonStage2StringBody.lean), [walk assembly](https://github.com/scidonia/lean-llvm/blob/59191bb/LeanLLVM/Refinement/JsonStage2WalkAssembly.lean).

## 2. High priority: the dispatch repair is still not integrated

The tree contains `WalkDispatchOutcome` with `cont`, `finish` and `refuse`, and the predicate `WalkDispatchThree`. This is the appropriate vocabulary for actual execution.

However, `WalkDispatchThree.ofContinueAndLast` still takes the old `WalkDispatch` for states where `C.k + 1 < G.nep`. `walkLoopStep_of_dispatch_exit` also still chooses continuation by that condition. The outcome relation has not replaced the problematic assumption in the loop-completion argument.

### Why the old premise cannot cover the required inputs

**Standalone string:** the document `"abc"` contributes opening and closing quote entries. At `k = 0`, `nep = 2`, the old split chooses continuation because `k + 1 < nep`. The string branch consumes both entries and selects `%inc208.i = k + 2` at the merge, so the actual next index equals `nep`. The old premise demands an index strictly below `nep`.

**Early refusal:** the bytes `] 0` can reach the native path because admission is not a syntax checker. The first unmatched closing bracket is refused at depth zero while another entry remains. The pinned body jumps through the error store to refusal finalisation, bypassing the merge. The old non-final-entry premise demands a continuing revolution instead.

Adding constructors that can describe these outcomes does not discharge the old premise. A theorem that embeds the old premise into `cont` preserves its assumptions, including the obstruction.

### Required change

Prove a direct dispatch theorem from the actual loop-head invariant and unconsumed-entry fact. Its result should be one of:

- a counted segment to the merge with an actual next index below the stream;
- a counted segment to normal finalisation after the dispatch consumes the final entry or entries;
- a counted segment to refusal finalisation at any entry index.

Use that result to construct the next loop step. Let terminal outcomes carry the verdict and report facts the return proof needs, or prove separately how those facts are derived. If the existing loop rule's fixed verdict is too restrictive for the chosen invariant, adjust that rule explicitly rather than assuming a uniform result without a producer.

Retire the old continuation premise from the completion path. Keep it only as a restricted lemma for states where continuation has actually been established.

**Acceptance:** complete staged model runs for a standalone string and an early refusal with entries remaining, then a loop-step theorem consuming the direct outcome relation rather than `WalkDispatch`.

## 3. High priority: terminal charging still reads a past-end entry

The `finish` constructor still uses:

```text
p + 2 ≤ 32 × (k2 − C.k)
        + 8 × (entryPos G k2 − entryPos G C.k)
```

At normal completion, the intended `k2` is `G.nep`. But `entryPos` is `G.ent.getD k 0`: past the entry list, it returns zero.

Consequently, the byte term collapses at the terminal index. A single final scalar beginning at zero receives only its entry allowance from this formula, even if scanning its trailing whitespace requires work proportional to the document length.

The existing loop rule allows terminal work to consume the remaining potential. The new terminal outcome must provide a compatible price, not a difference computed from a zero-valued sentinel.

### Required change

Introduce a credit boundary separate from the function used for actual entry loads:

```text
creditBoundary(k) = entryPos G k   when k < G.nep
creditBoundary(G.nep) = G.n
```

Prove its bounds and monotonicity on the closed interval `0 ≤ k ≤ nep`. State and spend the terminal price against that boundary, or directly against the remaining input-length allowance.

Do not change the semantics of an actual stream read just to fix accounting. A terminal credit boundary is a proof quantity; no out-of-range entry needs to be loaded.

**Acceptance:** derive the cost of a complete final scalar followed by a substantial whitespace suffix. Check the actual trace against the ABI budget, rather than only evaluating an assumed formula such as `22 + 6b`.

Sources: [terminal outcome](https://github.com/scidonia/lean-llvm/blob/59191bb/LeanLLVM/Refinement/JsonStage2WalkAssembly.lean#L1146), [entry position and its default](https://github.com/scidonia/lean-llvm/blob/59191bb/LeanLLVM/Refinement/JsonStage2WalkScope.lean#L949).

## 4. New integration finding: string joins require unstated presence facts

The new memory lemmas are useful and have explicit hypotheses. Their applicability is a separate obligation from their proofs.

For example, `s2StringBodyMemory_decoded` requires:

```text
readBytes mem ei 8 ≠ none
readBytes mem dst out.length ≠ none
readBytes mem xj 8 ≠ none
readBytes mem outn 8 ≠ none
```

It also requires several disjointness facts. The refused join similarly requires the private slot, cursor and error-record regions to be present and separated.

The current `s2StringBodyPre` takes `_next` and does not inspect it. It requires the input and cursor reads, escape-list spacing and arithmetic bounds, but does not establish that the body's private slot at `ei = next` is already readable. It also does not state all the output-region presence and separation premises used by the new joins.

The private-slot case is particularly important: the body allocates `%ei` and clears it before calling the expander. `alloca` advances the model's allocator cursor; it does not populate bytes. The later clear establishes presence after the clear, whereas the new join asks for presence in the memory before it.

Because the helper precondition is independent of `next`, existing valid reads do not imply presence at an arbitrary fresh `next`. This is a concrete missing entailment, not a hypothetical concern about native allocation failure.

### Suggested repair

Separate three kinds of assumptions:

| Kind | Treatment |
| --- | --- |
| Caller-owned outputs (`dst`, `outn`, error record) | Derive their presence and separation from caller staging, or strengthen the helper precondition with justified obligations and update every producer. |
| Private alloca slot (`ei`) | Establish freshness/separation and account for the clear that creates its bytes. Do not assume it was initialised in the incoming memory. |
| List-shaped memory equality | Preserve first-match update semantics, including duplicated addresses. Avoid adding duplicate-freedom merely to rescue a convenience representation. |

One promising route is a mixed-presence commutation lemma: disjoint writes can commute when the crossed caller-owned region is already present, even if the private slot is newly inserted. Prove the exact statement needed using the existing first-match primitives, then weaken the join's unnecessary incoming-slot presence hypothesis. Another route is to retain the initialised private slot in the comparison base and prove the final relation from there.

Whichever route is chosen, prove a small premise-supply theorem at `s2StringBodyPre` or the actual call-site staging before describing the memory work as finished.

The comment that only four branch-bit derivations remain is premature until these entailments are established. The lemmas can be correct while still being too strong to instantiate at their intended call.

Sources: [decoded join](https://github.com/scidonia/lean-llvm/blob/59191bb/LeanLLVM/Refinement/JsonStage2StringBody.lean#L3605), [refused join](https://github.com/scidonia/lean-llvm/blob/59191bb/LeanLLVM/Refinement/JsonStage2StringBody.lean#L3709), [helper precondition](https://github.com/scidonia/lean-llvm/blob/59191bb/LeanLLVM/Refinement/JsonStage2Helpers.lean#L340).

## 5. Close the scan/model bridge at its producer

`scanCounter_eq_takeWhile` now proves an important semantic fact: given a visited prefix entirely below the body's start and a stopping entry at or beyond it, the counter equals the model's `takeWhile` index.

It still needs those hypotheses derived from the scan invariant and actual exit. In particular, establish:

1. the initial cursor is at or before the final cursor;
2. every entry traversed between them is below `pos0`;
3. the exit cursor is past the list or names an entry at least `pos0`;
4. the loaded lane and pointer subtraction represent the same natural values used by the model;
5. the inside-window and expander-result bits choose the model's corresponding arm.

Then compose entry, seating, the concrete bounded scan, terminal continuation, memory relation and frame into `s2StringBodyBody_contract`.

The theorem's existence, with a satisfiable precondition whose producers are established, is the milestone. The number of supporting lemmas does not substitute for it.

## 6. Finish the flush branch and the actual endpoint

The earlier universal-memory defect is repaired. `WalkFlushAt.ofRun` composes four supplied step equations, and there is an entry-zero theorem at staging. The current tree adds more of the frame and register facts needed to supply the remaining equations.

Produce a theorem that starts with `Γ_stage2.pre`, `stage2StagedPre` and `nep = 0` and returns the completed flush run plus the boundary post at its actual final memory. A theorem that asks the caller for all four step equations is a composition tool; it is not yet that producer.

Likewise, `walkInvSeat` assembles the initial invariant from named fields. Its remaining hypotheses should be discharged at the exact state produced by the entry/header run, not passed forward as an implicit second specification of that state.

The final required declarations are:

```text
Stage2WalkCompletes ... stage2SubCalls
Stage2WalkObligation ...
```

with no assumed `WalkPremises`, completed dispatch, flush run, or equivalent completion witness. The full obligation must also derive its own postcondition rather than take `hpost`.

At this commit, [the endpoint wrapper](https://github.com/scidonia/lean-llvm/blob/59191bb/LeanLLVM/Refinement/JsonStage2WalkAssembly.lean#L2846) still takes both `WalkPremises` and `hpost`. Its type is the most direct status indicator.

## 7. Recommended sequence and acceptance gates

| Order | Work package | Completion gate |
| --- | --- | --- |
| 1 | Repair the dispatch producer and terminal accounting. | Standalone string, early refusal, and final-scalar-plus-whitespace cases follow the actual control flow and have counted runs. |
| 2 | Supply string-join presence/separation premises and connect the scan counter. | Whole `s2_string_body` contract proved at the intended helper/caller staging, including fresh-slot behaviour. |
| 3 | Finish the scoped flush and initial-state construction. | All-whitespace input runs from the ABI entry state to the specified refusal boundary. |
| 4 | Instantiate stage-2 completion and its post. | No assumed traversal/completion witness or externally supplied `hpost`. |
| 5 | Discharge remaining helper and parser correspondence. | Actual numeric/scalar bodies and produced event/arena results connected to the reference parser. |
| 6 | Bind to the installed native route. | Exact artifacts, capture transformations, wrapper configuration and remaining trusted components recorded together. |

Keep the three main regressions executable under the model, not merely represented by hand-selected price rows. Add a fresh-slot case to the string-helper proof tests, and retain the duplicated-address counterexample to prevent reintroduction of the map shortcut.

## 8. Trust surface and scope

This revision changes proof files only. It does not itself add native admission-body correspondence, prove the escape-list-skipping guard, close the numeric conversion body proof, or instantiate the parser event-stream relation.

The remaining trust/proof boundaries include the custom LLVM semantics, intrinsic and binary64 conformance, helper call models, transformed-fixture/native-artifact correspondence, native admission and guard code, the FFI wrapper, compiler/backend/linker and platform assumptions. A scoped compiler assumption is acceptable; it should remain distinct from unproved correspondence between two program bodies.

The earlier non-vacuity concern is still relevant. Completed-behaviour inclusion needs a concrete completion guarantee for the target. Conditional wrappers establish what follows from completion premises; only their instantiated producers establish that the intended execution actually returns. Result correspondence is then required to show that it returns the specified parser outcome.

## 9. Review evidence and limitations

This is a source review of the pinned commit and its diff from `a8195c3`. The two changed files, endpoint signatures, dispatch branches, helper precondition and new memory lemmas were inspected directly. The repository working tree was clean after the review; no implementation files were modified.

Nix, Lean, Lake and Clang were unavailable in this environment. No fresh Lean elaboration, native corpus run, artifact capture or benchmark is claimed. The control-flow and premise findings are source-level analyses; they should be reproduced as formal or executable regressions in the pinned implementation environment.

Validate with the repository's Nix toolchain, source-build lock and memory ceiling. For example:

```bash
systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c bash probes/install/lake-locked.sh build \
  LeanLLVM.Refinement.JsonStage2StringBody \
  LeanLLVM.Refinement.JsonStage2WalkSteps LeanLLVMTest

systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c bash probes/install/lake-locked.sh env lean tests/stage2-walk-credit.lean

systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c bash probes/json/route/build.sh

nix develop -c bash probes/json/route/check.sh
nix develop -c bash probes/json/route/guard.sh
nix develop -c bash probes/json/route/correspondence.sh
```

Record the instantiated endpoint declarations and their remaining premises alongside fresh test results. The next decisive advance is a completed branch from real staging to a returning outcome with its boundary post, followed by the general stage-2 theorem.
