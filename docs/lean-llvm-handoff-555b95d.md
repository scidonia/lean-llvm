# lean-llvm: stage-2 correctness handoff

**Reviewed commit:** [`555b95dfc8ac77ec1540bc7a4798ffccc900f7fa`](https://github.com/scidonia/lean-llvm/commit/555b95dfc8ac77ec1540bc7a4798ffccc900f7fa)  
**Comparison:** `763682060836c5822da435dc20511b07928c4137`  
**Date:** 13 November 2026  
**Objective:** close the stage-2 completion and boundary theorem under named helper assumptions, then discharge the remaining implementation and parser-correspondence assumptions.

## Assessment

This revision makes substantial progress. The previous potential-direction error, admission mismatch and 16-byte error footprint have been addressed in source. Two more helper bodies now have contract proofs. The number helper is representable and captured, and the string helper has a pinned AST plus several block-run proofs.

The complete verified native JSON replacement remains unfinished. `stage2WalkCompletes_of_premises` still takes `WalkPremises`, which contains the unproved traversal. `stage2WalkObligation_of_premises` additionally takes the postcondition as a hypothesis.

The next work should address two problems in those premises before attempting further assembly:

1. The dispatch/exit split does not accommodate strings that consume the final two entries or malformed input that returns before the last entry.
2. `WalkFlush` requires completion for arbitrary memory and allocator cursors without the staging preconditions that make the entry block runnable.

These are problems with the assumptions a conditional theorem needs to discharge. They are not evidence of a false unconditional theorem accepted by Lean.

## 1. Progress to retain

| Earlier finding | Standing at this revision | Evidence |
| --- | --- | --- |
| Potential increases with already-decoded bytes | Corrected: credit uses remaining document position and unconsumed entries. | `walkPotential`, `walkPotential_spend` in `JsonStage2WalkTraverse.lean`. |
| Native admission counts openers instead of nesting | Changed: the adapter computes maximum structural nesting, with string-body traversal. The opener-rich scenario now expects the fast path. | `depth_measure` in `shim.c`; updated `check.sh`. |
| Refusal footprint omits the message word | Changed: a three-field error model and 24-byte footprint account for the physical third store. | `stage2ErrSetMsg`, `stage2ErrSetMsg_frame`, `stage2ErrorExtent`. |
| Small helper bodies only modelled | Body-level run, post and frame proofs now exist for `s2_value_pos` and `s2_after_value`, alongside the existing `s2_init` proof. | `s2ValuePosBody_contract`, `s2AfterValueBody_contract`. |
| Number body blocked by representation and literals | Signed floating-literal handling is repaired; the transformed number body is captured and pinned with its declared layout. | `Parser.lean`, helper inventory and number fixture. |
| Existing links hide successor states | More step lemmas expose the actual successor environment and memory, enabling composition. | `JsonStage2WalkSteps.lean`, `JsonStage2WalkAssembly.lean`. |

These statuses describe source changes and proof declarations inspected in this review. They do not imply an independent fresh Lean build or native test run on the review host.

## 2. Priority 1: choose continuation or exit from the dispatch result

### Current obstruction

[`WalkDispatch`](https://github.com/scidonia/lean-llvm/blob/555b95d/LeanLLVM/Refinement/JsonStage2WalkAssembly.lean#L767) is required whenever:

```text
WalkInv G C s
C.block = walkLoopHead
C.k + 1 < G.nep
```

Its conclusion requires a segment to `cleanup478.i` whose selected next index `k2` is strictly below `G.nep`. The assembly theorem chooses this branch solely from `C.k + 1 < G.nep`; otherwise it uses `WalkExit`.

That split does not describe all executions.

### Witness A: a standalone JSON string

Consider:

```json
"abc"
```

The string uses two entry positions: the opening quote and the closing quote. At the first dispatch, `C.k = 0` and `G.nep = 2`, so the current split selects continuation because `0 + 1 < 2`.

The string branch consumes the closing entry as well. The source explicitly reads `close = ep[k++]`; the pinned IR computes `%inc208.i = %k.0.i249 + 2`, and the merge selects that value on the string arms. The actual next index is therefore `2`, equal to `nep`, and the loop finishes. It cannot satisfy the required `k2 < G.nep` continuation condition.

The proof vocabulary already allows variable index advances. The assembly's pre-dispatch case split incorrectly treats the advance as if it were always one.

Sources: [string branch](https://github.com/scidonia/lean-llvm/blob/555b95d/kernel/json/stage2.c#L1137), [pinned stage-2 body](https://github.com/scidonia/lean-llvm/blob/555b95d/probes/install/ir/stage2.candidate.ll), [assembly split](https://github.com/scidonia/lean-llvm/blob/555b95d/LeanLLVM/Refinement/JsonStage2WalkAssembly.lean#L992).

### Witness B: refusal before the final entry

Consider these bytes:

```text
] 0
```

Admission is a domain check rather than a JSON syntax check, so malformed documents are intentionally eligible for the native path. This input has no excessive nesting or character-policy refusal. The first closing bracket is rejected at stack depth zero while a later scalar entry remains.

The body takes its refusal path, not a segment back to the loop merge. In the pinned IR, `if.then53.i` tests the zero depth, `if.then56.i` stores the error offset and jumps to `if.then`, and the finalisation returns. The current non-final-entry branch instead demands a continuing revolution.

This is a source-level control-flow witness. A formal regression should instantiate the staged state and reproduce the path under the Lean semantics.

### Suggested repair

Prove a dispatch theorem whose result explicitly distinguishes the possible outcomes. For example, use a proposition or indexed relation with these alternatives:

| Outcome | Required evidence |
| --- | --- |
| Continue | A counted segment to the merge, the selected phi values, actual advanced index below `nep`, target invariant and credit bound. |
| Finish normally | A counted segment to the merge with the actual terminal index, followed by the checked finalisation path. |
| Refuse early | A counted segment to the refusal finalisation, with the error position and bounded cost. This branch must be available at any entry index. |

Select the continuation or finalisation from the actual dispatch outcome and resulting index. Do not decide it from `C.k + 1` before running the dispatch.

Preserve the distinction between a normal loop exit through `cleanup478.i` and direct refusal paths that bypass it. A single terminal-result alternative may package both, provided the proofs cover their different paths and memory effects.

**Acceptance criteria:**

- A standalone string consumes both quote entries and returns without requiring another iteration.
- A string at the end of an array or object also reaches the correct subsequent control flow.
- A malformed first or middle token can refuse while entries remain.
- Every terminal path carries its actual verdict, offset and counted finalisation run.
- The completion theorem no longer assumes a dispatch proposition that excludes these executions.

## 3. Priority 1: scope the empty-stream run to staged memory

### Current obstruction

[`WalkFlush`](https://github.com/scidonia/lean-llvm/blob/555b95d/LeanLLVM/Refinement/JsonStage2WalkAssembly.lean#L858) currently has the form:

```text
nep = 0 →
  ∀ mem next,
    ∃ q m, q ≤ stage2FinalisationAllowance ∧
      runFuel calls q stage2Body
        (EntryState stage2Body args mem next) = some (.ret v0 m)
```

It does not require `Γ_stage2.pre` or `stage2StagedPre` for those universally quantified memories. The outer `WalkPremises` obtains preconditions for one memory and cursor, but asking for `WalkFlush` then demands completion for every memory and cursor.

The entry-state constructor supplies the register bindings; it does not supply readable bytes. The entry block loads `%ndst` and `%nev`, among other reads. Arbitrary memory may omit those words. For disjoint staging addresses, the preceding initialisation writes do not manufacture the missing caller cursor words, so the run cannot return as required.

### Suggested repair

Make `WalkFlush` a property of the particular memory and allocator cursor at which it is used. Schematically:

```text
WalkFlush calls args mem next :=
  ∃ q v m', q ≤ finalisationAllowance ∧
    runFuel calls q stage2Body (EntryState ... args mem next)
      = some (.ret v m')
```

Supply the preconditions and the zero-entry fact when proving that property. Alternatively, retain universal quantification but put the appropriate preconditions under the quantifier and before the completion conclusion.

The result should be about the actual ABI arguments, staged memory, allocator cursor and selected helper environment. Those should remain tied through the entry run and refusal copy.

**Acceptance criteria:** prove the all-whitespace document's complete run from a staging satisfying the actual preconditions. It should return the specified refusal and error position within budget. A memory missing the required cursor bytes must fail the precondition rather than become an obligation to prove completion.

## 4. Priority 2: prove actual counted traversals

The potential now has the intended direction:

```text
Φ(C) = 32 × (nep − C.k) + 8 × (n − entryPos G C.k)
```

`walkPotential_spend` connects this credit to an entry-index advance and an input-position advance. The exit branch has also been widened to allow remaining potential plus finalisation overhead, so byte-dependent work on the last entry is no longer restricted to a constant tail allowance.

What is still missing is the actual trace that establishes the spending hypothesis. The long-string checks in `tests/stage2-walk-credit.lean` use constructed arithmetic rows such as `22 + 6 × 100` and execute a few pivot steps. They explicitly do not run a whole revolution.

Use the explicit successor lemmas to build the finite dispatch paths and the scan-loop inductions. Prove how often each scan can visit a position and where its cost is charged. Then compose their counted segments with the merge, next header or terminal path.

Do not treat a longest-path calculation or an opcode census as a bound on a trace containing loops. Likewise, do not present the 157-link count as a percentage of completed verification.

The first three end-to-end proof cases should be:

1. A long standalone string, exercising both byte credit and a two-entry advance that finishes the stream.
2. An early refusal with entries remaining, exercising the terminal path inside dispatch.
3. An all-whitespace input, exercising the zero-entry branch and memory staging.

After those, cover escaped strings, whitespace gaps, malformed input encountered late, and container nesting.

## 5. Helper proofs: current status and next work

| Helper | Body-level standing | Next work |
| --- | --- | --- |
| `s2_init` | Run and contract proof present. | Preserve artifact and footprint checks. |
| `s2_value_pos` | New body run, post and frame proofs present. | Use the body theorem when discharging the call-model assumption. |
| `s2_after_value` | New body run, post and frame proofs present. | Use the body theorem for both root and container cases. |
| `s2_string_body` | Ten-block AST pinned; entry, several arms and scan-body instruction runs proved. No complete helper contract theorem found. | Prove the scan induction, expander-call composition, phi/return paths and whole-body contract. |
| `num_fast_el1` | Transformed body captured and pinned; layout supplied and literals accepted. | Prove the emitted numeric computation and its helper calls against the number model. |
| `od_scalar_value` | Transformed body captured; whole-body correspondence remains open. | Compose number conversion, literal refusal and event/hash writes. |

The string module's opening description sounds like a completed contract proof. Update it to the actual standing until that theorem exists. Individual block runs are useful progress, but they do not establish the whole helper's totality or postcondition.

The 24-byte refusal footprint repair should be retained. Message-pointer rewriting to `null` remains part of artifact correspondence: hiding a diagnostic value does not remove the obligation to account for its physical store or relate the transformed fixture to the native body.

The number fixture also erases an `ashr exact` flag. A proof over the erased instruction does not establish that the original instruction's additional definedness condition holds. Prove the relevant operand property on reachable executions or retain it explicitly among the artifact-correspondence assumptions.

Sources: [small helper proofs](https://github.com/scidonia/lean-llvm/blob/555b95d/LeanLLVM/Refinement/JsonStage2HelperIRBodies.lean), [string proof development](https://github.com/scidonia/lean-llvm/blob/555b95d/LeanLLVM/Refinement/JsonStage2StringBody.lean), [capture and correspondence inventory](https://github.com/scidonia/lean-llvm/blob/555b95d/probes/install/ir/stage2.helpers.tsv).

## 6. Finish the boundary theorem, then parser correspondence

The ABI-to-geometry and staging construction now exists, and the seed run is proved at the reference helper selection. `Stage2Run.ofInv` projects a report from the invariant. The new uniqueness argument transports a proved postcondition for a completed outcome to every behaviour of that same run.

However, `stage2Post_of_run` requires completion at the particular `stage2Report` memory, and `stage2WalkObligation_of_premises` still accepts `hpost` as an argument. Those are assembly results, not a completed producer of the final postcondition.

Derive the boundary directly from the actual final memory's reads, extents and frame. Do not require equality between differently ordered memory-write lists where pointwise observations suffice. Preserve acceptance's untouched error slot and refusal's correctly reported offset.

The next endpoint should be:

```text
Stage2WalkCompletes ... stage2SubCalls
```

followed by the complete `Stage2WalkObligation`, with no assumed `WalkPremises`, `WalkDispatch`, `WalkExit`, `WalkFlush`, `hpost`, or equivalent completed-run witness. Named helper-model assumptions are acceptable for this intermediate milestone if they remain explicit.

That endpoint establishes the modelled stage-2 execution and boundary. JSON semantic correctness is a further obligation: instantiate the event-stream relation and prove that the actual verdict, events, decoded arena bytes and error information correspond to the Lean parser. The boundary contract deliberately does not assert that semantic correspondence.

## 7. Trust surface and claim boundaries

| Layer | Remaining obligation or assumption |
| --- | --- |
| Lean | Kernel and recorded standard axioms; independent elaboration of the new proof modules. |
| Extended LLVM model | Conformance of admitted pointer, layout, global and binary64 forms to the target fragment. |
| Helper models | Remaining body-to-model proofs and their composition at actual call sites. |
| Native admission | General body correspondence for the C nesting and policy checks; corpus agreement is runtime evidence rather than a universal theorem. |
| Stage-2 result | Actual traversal, termination, fuel bound and boundary at the returned memory. |
| Parser result | Concrete event-stream and value correspondence to the reference parser. |
| Artifact relation | Capture transformations, message rewriting, flag erasure, flattened staging and exact installed-object binding. |
| Execution platform | Compiler/backend/linker, ABI, wrapper and platform assumptions within the stated scope. |

The native admission change addresses the previous concrete mismatch at source level. It does not eliminate admission implementation from the trust surface. The repository records expanded differential evidence, including boundary cases and constructed document classes; those results should be kept tied to their recorded builds.

Completion matters to the user's original replacement question: completed-behaviour inclusion alone can be satisfied by an implementation with no completed outcomes. A proved return at the actual budget excludes that case under this deterministic executable model. It must be combined with result correspondence and the stated native assumptions to support the replacement claim.

## 8. Acceptance checklist for the next handoff

- [ ] Dispatch can continue, finish after consuming two quote entries, or refuse before the final entry.
- [ ] Empty-stream completion is scoped to the staged memory and allocator cursor.
- [ ] Standalone string, early refusal and all-whitespace cases have complete counted model runs.
- [ ] Credit is spent by actual scan traces, including the final dispatch.
- [ ] `Stage2WalkCompletes` is instantiated without a traversal/completion premise.
- [ ] The final boundary post is proved at the actual returned memory.
- [ ] `Stage2WalkObligation` is instantiated without `hpost` as an external assumption.
- [ ] Remaining helper, semantic and artifact assumptions are named accurately.
- [ ] Documentation distinguishes block proofs, conditional assembly, completed body proofs and native evidence.

## 9. Validation and review limits

This handoff is based on source review at the pinned commit. The import-boundary check passed during the review. The native route check stopped at setup because the built executable was absent. Nix, Lean, Lake and Clang were unavailable on the review host, so no fresh Lean elaboration, native corpus run or benchmark is claimed.

The control-flow witnesses above were identified from the source and pinned IR; they should be made executable or proved as regressions in the implementation environment. They are not presented as independently executed Lean counterexamples.

Use the repository's pinned Nix environment, source-build lock and memory ceiling. Build the affected proof modules and test library, then run the core-extension and credit scenarios. After implementation changes, rebuild and run the route's corpus, admission disagreement controls and artifact-correspondence check.

For example:

```bash
systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c bash probes/install/lake-locked.sh build \
  LeanLLVM.Refinement.JsonStage2WalkSteps \
  LeanLLVM.Refinement.JsonStage2StringBody LeanLLVMTest

systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c bash probes/install/lake-locked.sh env lean tests/stage2-walk-credit.lean

systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c bash probes/install/lake-locked.sh env lean tests/core-extension.lean

systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c bash probes/json/route/build.sh

nix develop -c bash probes/json/route/check.sh
nix develop -c bash probes/json/route/correspondence.sh
```

Record the reviewed commit, elaborated endpoint declarations, remaining premises, tested artifact hashes and scenario results together. The next decisive result is an actual stage-2 completion theorem covering all admitted control-flow outcomes.
