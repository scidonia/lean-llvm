# lean-llvm: implementation handoff to close the JSON replacement proof

**Date:** 16 November 2026  
**Reviewed commit:** [`6599293bb6bacac498237072f94170770a62b94b`](https://github.com/scidonia/lean-llvm/tree/6599293bb6bacac498237072f94170770a62b94b)  
**Previous snapshot:** [`4ca52e7c9ad7089942556ef6530f89d74401c08a`](https://github.com/scidonia/lean-llvm/tree/4ca52e7c9ad7089942556ef6530f89d74401c08a)  
**Goal:** A usable certification boundary for replacing performance-critical Lean code with independently authored low-level implementations, demonstrated by SIMD JSON parsing.

## 1. Decision and immediate priorities

Continue the work. The latest changes make real progress: the impossible watermark is repaired, the allocator bound is connected to the caller and loop, and more terminal and continuing-entry facts are derived from invariants.

The next priority is **exhaustive dispatch**, followed by the production of the remaining stage-2 fact bundles. The current last-entry producer covers a specific byte class, while its consumer requests it at every last-entry head. More register-preservation lemmas alone cannot close that mismatch.

Complete the work in this order:

1. Replace the universal use of a branch-specific last-entry bundle with exhaustive terminal dispatch.
2. Construct the continuing-entry and string-residue facts from reachable states and callee contracts.
3. Derive terminal words and finalisation facts at the returned memories.
4. Remove the remaining bundle arguments from the stage-2 obligation.
5. Prove caller count-slot preservation and supply the concrete stage-2 selection.
6. Complete semantic correspondence with the reference parser and exercise the artifact through the Lean calling boundary.

Do not narrow the advertised JSON domain merely to make an existing branch-specific producer applicable. Any deliberately restricted first milestone must state its domain explicitly and include both successful and rejected executions relevant to that domain.

## 2. What is already closed

These results should be preserved and reused rather than reopened as original findings.

| Area | Current position |
| --- | --- |
| Parser-bridge quantification | The bridge is indexed by actual behaviour and actual output extents. The retired arbitrary-verdict premise is refuted by regression theorems. |
| Watermark | `pipelineLoopExitAt` ties the regions to the actual carried state. `stage2Watermark` derives the bound; `retiredStage2Watermark_false` refutes the old form. |
| Initial allocator bound | `Γ_pipeline_units.pre` includes `pipelineStagedBelow`. `routeNext` and `routeStagedBelow` construct and justify a model caller cursor. |
| String helper execution | `s2StringBodyBody_contract` establishes returning execution within its budget, a postcondition and a memory frame. |
| Two-entry string path | `stringPath_seg` composes the path, relative to its remaining residue. |
| Whitespace skip | Its run, cost and endpoint facts are derived from classification and state facts. The consuming composition uses those theorems. |
| Last-entry bookkeeping | More registers and bounds are invariant consequences; the loop-head guard supports the last-index argument. |
| Loop postcondition | The staging-level obligation no longer takes the old unrestricted `hpost` premise. |

Evidence: [watermark and regression](https://github.com/scidonia/lean-llvm/blob/6599293bb6bacac498237072f94170770a62b94b/LeanLLVM/Refinement/PipelineDischarge.lean#L1445), [caller cursor](https://github.com/scidonia/lean-llvm/blob/6599293bb6bacac498237072f94170770a62b94b/LeanLLVM/JsonCallRoute.lean#L807), [string helper](https://github.com/scidonia/lean-llvm/blob/6599293bb6bacac498237072f94170770a62b94b/LeanLLVM/Refinement/JsonStage2StringBody.lean#L6517).

The watermark fix tightens the execution precondition: staged objects must lie below the allocator cursor. That is an explicit operational assumption, and the model caller now proves it. Preserve that connection when changing the caller or layout.

## 3. Define three separate completion gates

| Gate | Required result | What remains outside that gate |
| --- | --- | --- |
| A — Stage-2 execution | The pinned stage-2 body satisfies its execution/memory contract under the named helper environment, without externally supplied execution bundles. | Reference-parser correspondence and any helper implementation assumptions not yet discharged. |
| B — Semantic replacement | Actual accepted output, rejection behaviour and required frames correspond to the declared reference semantics; returning execution is included. | Explicit compiler, ABI, runtime and native-artifact assumptions. |
| C — Native Lean route | The real caller invokes the covered implementation; artifact identity, staging and trust assumptions are documented and exercised; performance is measured on that route. | Any explicitly declared unverified toolchain boundary. |

A useful first deployment result may retain an explicit compiler/runtime trust boundary. Verification of the entire Lean compiler is not a prerequisite for closing the immediate parser obligations. Conversely, a closed Gate A must not be described as a complete JSON semantic replacement.

## 4. Task A: make last-entry dispatch exhaustive

**Priority:** P0 for proof closure.

**Primary files:**

- `LeanLLVM/Refinement/JsonStage2WalkDispatchWitnessHlast.lean`
- `LeanLLVM/Refinement/JsonStage2WalkPremisesOfStaging.lean`
- `LeanLLVM/Refinement/JsonStage2WalkDispatchThreeOfRun.lean`
- `LeanLLVM/Refinement/JsonStage2WalkLoopStepOutcome.lean`
- Relevant head-chain, dispatch, finish and traversal modules.

### A1. Establish the mismatch as a checked regression

[`HlastFacts`](https://github.com/scidonia/lean-llvm/blob/6599293bb6bacac498237072f94170770a62b94b/LeanLLVM/Refinement/JsonStage2WalkDispatchWitnessHlast.lean#L191) and its producer require:

```text
signedLessThan(headByte, 125) = false
equal(headByte, 125) = false
```

These conditions restrict the byte to 126 or 127. The source documents that restriction. This is one dispatch class, not a property of every final entry.

[`WalkLoopEnd.hlast`](https://github.com/scidonia/lean-llvm/blob/6599293bb6bacac498237072f94170770a62b94b/LeanLLVM/Refinement/JsonStage2WalkPremisesOfStaging.lean#L208), however, supplied `HlastResidue` at every invariant head with no next entry. The residue includes those same class restrictions. `WalkLoopEnd.facts` then called the branch-specific producer.

**Landed (`JsonStage2WalkHlastDomain`).** The regression is at the document `0`, not at a hand-built state: `ZeroDocument` is the staging's own two reads (`readBytes` for the byte `0x30`, `readLanes32` for the single lane `0`) and the two counts, `hlastByte_zero` derives the head byte from `WalkGeom.doc`/`entries` through `entryPos`/`entryByte`, `zeroDocument_class_false` shows the bundle's `slt 125` bit is `1` there, and `zeroDocument_residue_false`/`zeroDocument_highByteArm_empty` render `HlastResidue G (walkSeed G S) s` empty. Reachability is `walkSeedInvariant_geometry`'s (`zeroDocument_seededInv`), with the guard from `walkSeed_block` and `walkSeed_guard`. `zeroDocument_domain` states the positive half at the same head: the switch's default-arm pivots and the tag test hold, i.e. the scalar arm is the one this input takes.

### A2. Introduce a complete terminal-dispatch result

Reuse `WalkDispatchResult` and the existing terminal-result vocabulary where possible. The general terminal producer should return the actual result of dispatch, rather than requiring all terminal inputs to fit `HlastFacts`.

A suitable interface has this conceptual shape; the notation is architectural, not a proposed compiled API:

```text
terminalDispatch:
  reachable/invariant head state
  + last-entry guard
  → an actual dispatch result
    with its execution segment, endpoint, price and terminal evidence
```

Give each emitted control-flow branch its own premises. Preserve the existing long default-path proof as one branch, with a name and documentation that state its byte-class restriction.

Build a dispatch census from the pinned IR. Every head branch must lead to a proved successor result or a justified refusal. Include scalar/literal, string, container and closing-delimiter paths as the emitted code actually handles them. Do not assume that the entry stream alone makes all unproved byte classes unreachable.

**Landed (`JsonStage2WalkDispatchArms`).** `HeadArm` is the census as a value (string opener, comma, colon, open bracket, close bracket, open brace, close brace, and the default arm split by its seven sub-routes), and `HeadArm.complete` proves every byte has exactly one — the classification is exhaustive by theorem. `LastEntryArm` is the dispatch's evidence, one constructor per arm class, and `LastEntryArm.dispatch` turns it into the actual `WalkDispatchResult`:

| arm | producer | count |
|---|---|---|
| `.scalar` (default arm, tag test true) | `scalarMerge_at` | 11 + 3 + 1 = 15 |
| `.highByte` (bytes 126/127, the preserved long default path) | `hlastFacts_of_staging` → `ofHlastMerge` | 20 |
| `.stringOpener` (bare opener, no entry left) | `quoteRefuse_at` | 5 |
| `.closingZero` (`]` at depth zero) | `bracketRefuse_at` | 6 |
| `.supplied` (container openers, comma, colon, closing with a container open, the default arm's letter routes) | the arm's own result | the arm's |

`.highByte` is where the byte-class restriction now lives: it is one constructor, documented as the 126/127 arm, and it is not the last entry's shape.

### A3. Preserve prices and returned-state evidence

Each branch must return:

- the executed segment or returning run;
- the actual target state and carried state;
- index advancement or a terminal/refusal result;
- the invariant facts required by its consumer;
- a cost bounded by the remaining entry/byte potential;
- terminal memory/register facts at that same endpoint.

The loop-head guard now helps derive the last-index equality. Preserve that improvement, but keep entry-count exhaustion separate from byte-class selection: being the last entry does not choose the character-dispatch branch.

**Landed.** The scalar arm's fifteen links are stated at named states (`ScalarC₁`…`ScalarC₁₁`, `scalarS₁`…`scalarSeam`), its merge cells are `WalkInv.inc_reg`/`depth_reg`/`regs` at the endpoint the segment reaches, and its price is `17 ≤ 32` computed from the merge's own test on `%k.2.i` against `%nep` — never `C.k + 1` as a synonym for the price. The refusal arms' prices are `refusePrice_of_le`'s, and the high-byte arm's is `ofHlastMerge`'s. Entry-count exhaustion is derived once (`WalkInv.head_lt` with the guard) and byte selection once (`HeadArm`).

### A4. Acceptance criteria

- A regression refutes the old universal residue on the actual `0` seed. **Landed**: `zeroDocument_residue_false`, `zeroDocument_highByteArm_empty`, `zeroDocument_domain`.
- Terminal dispatch is exhaustive over the claimed input domain and malformed inputs that the precondition permits. **Interface and census landed**; the container, comma, colon, closing-with-container and letter arms are `.supplied` — their segments are the remaining work, and no other arm's class is a premise of them.
- No ordinary scalar, string or closing-delimiter case is required to prove that its byte is 126 or 127. **Landed**: the scalar arm's class is `91`/`44`/`58`/`44 ≠` plus the tag bit; the string and closing arms are refusals with their own bytes.
- The loop consumer invokes the complete dispatch producer. **Landed**: `walkLoopStep_of_staging`'s last branch is `hend.dispatch C s hInv hhead hk`.
- Every branch has an endpoint and a price, including refusal branches. **Landed for the proved arms**; `.supplied` carries the endpoint and the price it claims.

Build evidence at this landing: the default target is green at `1931` jobs (`LAKE_EXIT=0`), the two source-boundary checks pass, and the new declarations' footprints are `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`); `stage2WalkObligation_of_staging`'s is unchanged at `[propext, Classical.choice, Quot.sound]`.

## 5. Task B: produce continuing-entry facts

**Priority:** P1, alongside terminal dispatch once its common interface is settled.

**Primary files:**

- `JsonStage2WalkHcontFactsOfStaging.lean`
- `JsonStage2WalkRevolution.lean`
- `JsonStage2WalkRevolutionSeg.lean`
- `JsonStage2WalkDispatchWitnessString.lean`
- `JsonStage2WalkPremisesOfStaging.lean`

The current continuing-entry producer derives more of the head, endpoint and byte facts. It still takes branch-class evidence, a tail segment and traversal obligations. `WalkContinueFacts` needs complete classification and producers at all relevant continuing heads, not just an assembled bundle for one class.

### B1. Classify from the actual input and branch tests

Derive the whitespace, scan-free, two-entry-string and other necessary control-flow cases from the emitted tests and the input bytes. Audit the head-byte restrictions of each existing producer: the current whitespace producer also retains class-specific `hlt125`/`hne125` assumptions.

The dispatch must either produce the applicable branch's evidence or follow an implemented refusal path. A classification hypothesis must not silently exclude the ordinary token classes the outer theorem claims to cover.

### B2. Close the whitespace classification

The new whitespace execution theorem is useful and should remain the execution producer. Its input classification still includes the continuing-byte interval, stop position, advancement and inner-budget bound.

Prove those facts from the entry-stream specification and actual document. Construct the stop position from the bounded scan or state the precise reachable-state relation that identifies it. Prove the scan remains within its admitted read window and reaches a stop or an implemented boundary/refusal.

### B3. Construct the tail and traversal

- Build the tail segment from the actual helper contracts at each call memory and allocator cursor.
- Derive its span budget from the carried entry/byte potential.
- Supply the extra-token traversal's round, guard and read-totality facts by reusable step/preservation lemmas.
- Retire unused premises, such as a round hypothesis that the actual consuming proof does not use, after checking all consumers.

### B4. Acceptance criteria

- A complete producer supplies `WalkContinueFacts` from invariant/reachability and staging.
- Its class split is exhaustive for the emitted dispatch.
- It assumes no execution segment or traversal correctness that it is supposed to prove.
- Each helper call consumes its own precondition and contributes its own postcondition.
- The whitespace and subsequent scan share one justified budget; byte credit is not counted twice.

## 6. Task C: close the string-path residue

**Priority:** P1.

**Primary files:**

- `JsonStage2WalkDispatchWitnessString.lean`
- `JsonStage2StringStageFacts.lean`
- `JsonStage2StringBody.lean`
- `JsonStage2Helpers.lean`
- Relevant staging and invariant modules.

The fifteen-link `stringPath_seg` is a composition theorem. Its remaining `HstringResidue` must be produced at the actual call sites.

For each residue field, record the fact, its source and its consumer. Then discharge the following groups:

| Group | Required derivation |
| --- | --- |
| Arena/log base words | Initialisation establishes them; an invariant or targeted preservation theorem carries them to the call site. A frame outside a writable object does not preserve a field inside that object. |
| String helper answer | Establish the helper precondition at the actual call memory; obtain the answer from its returning-execution theorem. |
| Form and decoded length | Read the form, output-length word and length bound from the helper postcondition at its returned memory. |
| Address and signed-width bounds | Derive them from actual ABI staging and reachable cursor bounds. If a necessary input condition is missing, state and justify it at the caller boundary. |
| Event-count/index relationship | Prove the relationship from the event encoding and control-flow history. Audit whether the required strict inequality holds at the initial/root-string state. |
| Allocator placement and frames | Preserve the actual cursor and fresh-allocation extent through calls; use the already repaired interval-based stack frame. |

The last point about event counts is a proof obligation, not permission to add an arbitrary strict inequality to the input contract. A valid root string must not be excluded because an internal residue was stated too strongly.

### Acceptance criteria

- Every `HstringResidue` field has a producer from the call's staging and predecessor posts.
- The root-string case is inhabited and reaches the helper through the actual seed/dispatch path.
- Helpers are invoked at the memories the preceding links leave.
- The complete stage-2 proof no longer takes `WalkStringResidue` externally.

## 7. Task D: produce terminal words and close Gate A

**Primary files:**

- `JsonStage2WalkTargetPost.lean`
- `JsonStage2WalkPremisesOfStaging.lean`
- `JsonStage2WalkFlushPost.lean`
- `JsonStage2WalkAssembly.lean`
- `JsonStage2WalkScope.lean`

Produce the remaining merge/refusal evidence at the actual endpoint:

- finalisation registers, including the document length and parameter words;
- the root-done word and depth state selecting acceptance versus refusal;
- the log's arena/event cursor words;
- the refusal word written by the predecessor on direct refusal routes;
- the merge's index/count relationship.

Use named endpoint states or segments that retain the needed memory facts. Do not ask for a postcondition about an arbitrary state merely because it shares a block label.

Then construct all remaining arguments to [`stage2WalkObligation_of_staging`](https://github.com/scidonia/lean-llvm/blob/6599293bb6bacac498237072f94170770a62b94b/LeanLLVM/Refinement/JsonStage2WalkFlushPost.lean#L801).

**Gate A acceptance:** the chosen top-level theorem provides `Stage2WalkObligation` from the declared ABI/staging conditions and named helper environment. It takes no external `WalkContinueFacts`, `WalkLoopEnd`, `WalkStringResidue`, equivalent run bundle or unrestricted postcondition premise. It proves returning execution at the declared budget and the postcondition of the actual behaviour.

If a reachable-state predicate is needed because `WalkInv` is too weak, integrate it through the induction. Do not require impossible properties of every state admitted by the weaker invariant.

## 8. Task E: remove `Stage2SlotKeeps` and supply the concrete selection

**Priority:** P1 for pipeline closure.

[`pipeline_satisfies_at_stage2_of_exitStage2`](https://github.com/scidonia/lean-llvm/blob/6599293bb6bacac498237072f94170770a62b94b/LeanLLVM/Refinement/PipelineDischarge.lean#L2178) still takes a stage-2 `CallSatisfies` selection and `Stage2SlotKeeps`.

### E1. Derive count-slot preservation

The stage-2 ABI does not itself name the caller's `%nk` and `%nxp` slots. A generic thirteen-argument postcondition cannot establish arbitrary additional preservation facts without a justified frame or adapter.

Choose an explicit proof boundary:

- expose the actual touched regions and fresh allocation extent in the callee contract, then derive that they are disjoint from the caller's count slots; or
- prove an adapter-specific contract for the actual staged stage-2 call, retaining the caller's separation facts and deriving preservation from the concrete body/callee frames.

The proof must account for the output arena, event stream, report slots, appended scratch objects and dynamically allocated stack interval. Separation in a precondition must be combined with an actual write/frame guarantee; it is not itself a postcondition.

### E2. Close the staged adapter and selection

Connect the fixture's staged argument list to the native ABI through the actual adapter and call environment. Obtain the selection's completion, return value, memory postcondition and allocator monotonicity from Gate A and the certified helpers.

**Acceptance criteria:**

- Count-slot preservation follows from the actual call's write set and separation.
- Pipeline composition takes neither external `Stage2SlotKeeps` nor an unexplained `CallSatisfies` instance for stage 2.
- The model caller proves the allocator precondition through `routeStagedBelow`.
- At least one complete accepted run and one complete rejected run instantiate the composite theorem.

## 9. Task F: establish semantic replacement, native identity and Lean use

### F1. Instantiate the parser relation

The repaired [`pipeline_satisfies_of_parser`](https://github.com/scidonia/lean-llvm/blob/6599293bb6bacac498237072f94170770a62b94b/LeanLLVM/Refinement/JsonPipelineRefine.lean#L1218) has an appropriate execution-indexed interface, but its parser half still needs a producer.

Define the concrete arena/event decoding relation and prove it against the reference parser at the actual output extents. Specify:

- accepted values and token/container structure;
- string decoding, escapes and UTF-8 completion;
- binary64 numeric observations, including the relationship to any reference lexeme representation;
- rejection behaviour and the selected error-offset policy;
- resource-limit outcomes and the exact admitted input domain;
- output cursor and memory-frame guarantees.

Do not identify the native parser's error offset with the reference's without a proof that their policies agree. If the chosen specification permits a relation between offsets instead, state that relation explicitly.

### F2. Audit remaining helper implementation assumptions

For each forwarded helper, distinguish the contract/model proof from the theorem about its emitted body. Numeric model correctness must be connected to the concrete helper and its operations. Recheck any remaining approximation, comparison, word-width and budget obligations rather than assuming that importing the tier theorems discharges them.

### F3. Bind the real artifact and calling boundary

Document and exercise the chain from staged model to installed implementation. Account for the pinned fixture's capture rewrites, ABI adaptation, out-of-line helper boundaries and any inlining differences in the measured build.

The first deployment may trust named compiler/backend/ABI components. Record these as assumptions, alongside the exact proof-covered artifact and identity checks. Do not describe hash/rebuild checks as compiler-correctness theorems.

The Lean wrapper must establish buffer presence, capacities, padding, separation, lifetimes and cursor bounds. Its observation of outputs must match the relation proved in F1.

### F4. Measure that implementation

Benchmark the actual covered artifact through the intended Lean route, including staging/copying that the application pays for. Pin the reference version, compiler flags, corpus and contract. Include scalar-heavy, string-heavy, escape-heavy, malformed, tail-boundary and long-number workloads. Existing scratch ratios remain separate evidence until reproduced for this implementation.

## 10. Regression and application matrix

Use the reference specification to determine expected outcomes and offsets. These examples are a minimum proof/application matrix, not a substitute for universal theorems.

| Input or family | Purpose |
| --- | --- |
| `0`, `-1`, `null`, `true`, `false` | Ordinary scalar dispatch and one-entry terminal coverage. |
| `""`, `"abc"`, escaped and multibyte strings | Two-entry/string helper composition and output decoding. |
| `[]`, `{}`, `[0]`, `{"a":1}` | Container transitions, closing delimiters and terminal state. |
| `0 ` and documents with leading/trailing whitespace | Whitespace classification, stop conditions and finalisation. |
| Empty and whitespace-only input | Empty-stream path and specified refusal behaviour. |
| `01`, `1e`, lone `-`, mismatched delimiters, unterminated string | Actual malformed-input refusal paths. |
| Bytes 126 and 127 in token position | Preserve the existing default-class proof as an application case. |
| Inputs crossing 32/64-byte boundaries | SIMD tails, carries, UTF-8 and staging padding. |
| Numeric ties, subnormals, long lexemes and overflow cases | The declared binary64 policy and concrete numeric path. |

Add negative controls that detect a wrong branch, cursor, decoded byte, report slot or write outside the frame. Relevant fixtures must be re-elaborated from source when changed; `include_str` inputs are not ordinary Lake dependency inputs.

## 11. Build and evidence requirements

Follow the checkout's current `AGENTS.md`. At this snapshot it requires the Nix toolchain, a memory ceiling and the build lock. A full build command is:

```bash
systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c bash probes/install/lake-locked.sh build
```

Capture the actual command status. Do not infer build success from the status of a trailing log-filter process. Ensure claimed modules are imported by the intended default target and stable soundness declarations have checked axiom footprints.

Retain the source-boundary checks:

```bash
nix develop -c bash tests/json-import-boundary.sh
nix develop -c bash tests/itree-boundary.sh
```

Run the relevant Lean applications, fixture pins, native routes and certificate checks for changed components. Record which declarations were elaborated and which objects were tested.

**Review limitation:** both source-boundary checks passed at `6599293`. This handoff is based on source inspection; the reviewer could not rerun Lean elaboration, fixture regeneration or native benchmarks because the required toolchain was unavailable.

## 12. Definition of done for the next handoff

- [ ] The old universal last-entry residue is refuted on an actual ordinary-input seed.
- [ ] Terminal dispatch covers every reachable byte/control-flow class in the claimed domain.
- [ ] Continuing-entry classification and execution facts have complete producers.
- [ ] String-path residue is derived at the actual call memories.
- [ ] Merge/refusal words survive to the states where they are consumed.
- [ ] Gate A has no external execution bundles or arbitrary postcondition premise.
- [ ] Stage-2 count-slot preservation is proved from the actual frame.
- [ ] The pipeline uses a concrete certified stage-2 selection.
- [ ] The parser semantic relation is concrete and instantiated at real outcomes/extents.
- [ ] The intended Lean caller establishes all preconditions.
- [ ] Proof/artifact identity and remaining trust assumptions are explicit.
- [ ] Build, proof applications and relevant native checks are recorded accurately.

Judge progress by which assumptions disappear from the complete caller-to-return theorem. The component proofs are now substantial; the priority is to make them usable through exhaustive dispatch, reachable-state producers and a closed composition boundary.
