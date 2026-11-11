# lean-llvm: completion assessment and recommended next work

Reviewed revision: `dedbf668778e4a2288cb2c25ed2508db8818b117`  
Comparison point: `a706a17894147ab43ff55c2eb0b3a17977508b36`  
Date: 11 November 2026  
Repository: <https://github.com/scidonia/lean-llvm>

## 1. Are we close?

**Closer to a working demonstration; still substantial work from a complete correctness argument.** The latest ten commits add a real Lean-to-native JSON probe, represent the stage-2 scratch objects in the contracts, model the six stage-2 helpers, and derive the scanner lane's instruction chain. These are useful advances beyond the earlier foundational repairs and pipeline-tail proof.

The remaining work is not just packaging. The actual stage-2 walk still lacks its `Satisfies` instance, the final reference-parser correspondence remains assumed, and the caller-visible frame needs a sound account of private scratch memory. This review also identifies two concrete statement problems that should be repaired before extending the large proofs:

1. The walk invariant assumes exactly thirteen event bytes per record, while the implementation emits records of one, nine or thirteen bytes.
2. The final parser theorem's new frame premise ranges over arbitrary arguments and outcomes, repeating the earlier universal-premise problem in a different conjunct.

**Recommendation:** freeze the first completion target and spend the next work on eliminating these statement defects, closing the stage-2 execution proof, and making the executable wrapper implement precisely the domain and observations covered by that proof. Do not estimate completion from line counts or the number of inner-loop lemmas.

This is a source-level assessment. Nix, Lean/Lake and Clang were unavailable in this review environment. The new native route was not rebuilt or independently run. Statements about its recorded corpus results below are attributed to repository evidence, not presented as fresh measurements.

## 2. What has materially improved

| Area | Current evidence | Assessment |
|---|---|---|
| Foundational correctness | Earlier `phi`, printer and parser-premise repairs remain in place | Retain and protect with regressions |
| Termination discipline | `Completes`, `RefinesCompleting`, `Satisfies`, and completion preservation for shipped passes | The framework can express the required non-vacuous replacement claim |
| Pipeline tail | `pipelineTailTarget` supplies the formerly assumed tail bundle | Earlier milestone achieved; it still consumes the stage-2 contract |
| Scratch memory | `JsonStage2Scratch`, `stage2StagedPre`, `stage2WalkFrame`, and carried nesting/log state | The previously omitted workspace is now represented; observer-level framing remains open |
| Stage-2 helpers | `stage2SubCalls` models all six forwarded symbols | Removes unresolved-call scaffolding; does not prove equivalence to their emitted implementations |
| Lean/native execution | `probes/json/route/` builds a Lean caller, C adapter and native pipeline | A real call route now exists, beyond the earlier AST staging caller |
| Wrapper domain | `routeStaging`, `routeSpecPre`, `checkRoute` and refusal lemmas | Substantial library-side staging work; executable probe and library shell still differ |
| Scanner lane | The 120-instruction rule chain is derived, and its pending-UTF-8-requirement bridge is proved | Concrete local proof progress; whole-window theorem still absent |
| Trust accounting | `docs/contract.md` now enumerates the trust boundaries | Useful disclosure; some entries still describe the earlier revision |

Primary sources: [PipelineDischarge.lean](https://github.com/scidonia/lean-llvm/blob/dedbf66/LeanLLVM/Refinement/PipelineDischarge.lean), [JsonStage2WalkScope.lean](https://github.com/scidonia/lean-llvm/blob/dedbf66/LeanLLVM/Refinement/JsonStage2WalkScope.lean), [JsonStage2Body.lean](https://github.com/scidonia/lean-llvm/blob/dedbf66/LeanLLVM/Refinement/JsonStage2Body.lean), [JsonCallRoute.lean](https://github.com/scidonia/lean-llvm/blob/dedbf66/LeanLLVM/JsonCallRoute.lean), [route README](https://github.com/scidonia/lean-llvm/blob/dedbf66/probes/json/route/README.md), [JsonScanLane.lean](https://github.com/scidonia/lean-llvm/blob/dedbf66/LeanLLVM/Refinement/JsonScanLane.lean).

## 3. First repair: event size is a bound, not a constant

Source: [WalkInv.evlen_eq](https://github.com/scidonia/lean-llvm/blob/dedbf66/LeanLLVM/Refinement/JsonStage2WalkScope.lean#L503).

The current invariant requires:

```text
C.evlen = G.nev0 + stage2RecordBytes * C.records
stage2RecordBytes = 13
```

But the implementation's encoding is variable-width:

| Event | Bytes |
|---|---:|
| Container marker or `true` / `false` / `null` | 1 |
| Number: tag plus binary64 payload | 9 |
| Key or string: tag, length and span/arena payload | 13 |

This is visible both in native `stage2.c` (`out_tag`, `out_u64`, and the string record's `len += 13`) and the Lean helper model. In particular, [numberRecord](https://github.com/scidonia/lean-llvm/blob/dedbf66/LeanLLVM/Refinement/JsonStage2Body.lean#L233) explicitly emits nine bytes, and `outTag` emits one.

For a fresh event stream, a successful root `true` leaves an event length of one. No natural-number record count can satisfy `1 = 13 * records`. A numeric event similarly leaves nine. The invariant also ties the actual log length to `C.evlen`, so this is not merely an imprecise comment: a proof that carries the invariant across these emissions cannot establish the current equality.

This is a source finding, not a newly executed Lean counterexample.

### Recommended representation

Carry a ghost sequence of emitted records or event fragments:

```text
events : List EventRecord
evlen = nev0 + sum (events.map encodedSize)
events.length ≤ consumedEntryCount
∀ event ∈ events, encodedSize event ≤ 13
```

Then derive the capacity bound:

```text
evlen ≤ nev0 + 13 * consumedEntryCount ≤ nev0 + 13 * documentLength
```

The exact trace also provides a natural substrate for the eventual token/event correspondence. If only the safety theorem is being completed first, `nev0 ≤ evlen ∧ evlen ≤ nev0 + 13 * records` is sufficient for that bound, but it does not replace the later content invariant.

### Acceptance checks

- Derive event lengths one and nine for `true` and `0` from the actual modelled emitters.
- Exercise an empty container and a mixed document containing strings, numbers, literals and nested containers.
- Prove the repaired invariant after each event-producing arm, including events emitted before a later parse refusal.
- Prove content and length from the same ghost trace rather than maintaining unrelated counters.

## 4. Second repair: scope the frame premise to reachable outcomes

Source: [pipeline_satisfies_of_parser](https://github.com/scidonia/lean-llvm/blob/dedbf66/LeanLLVM/Refinement/JsonPipelineRefine.lean#L1200).

The semantic premise is now correctly gated by staging and execution. The new frame premise is not:

```text
hframe : ∀ args mem outcome, SigmaFrame args outcome mem
```

For a correctly shaped argument list and an integer return, `SigmaFrame` requires `pipelineOutputExtents` and a memory-frame property. Yet this universal premise also includes an arbitrary returned memory with no cursor slots at all. Choose an empty returned memory: the required eight-byte cursor reads cannot succeed. Thus the unrestricted premise cannot be supplied.

This is distinct from the real scratch-frame problem. Even after the model is repaired, correctness can only be required for outcomes produced by an admissible execution; it cannot hold of every invented output memory.

### Immediate repair

Scope `hframe` in the same manner as `hsem`:

```text
∀ args mem next outcome,
  pipelineStaging ... args mem →
  BehFromState calls body (EntryState body args mem next) outcome →
  SigmaFrame args outcome mem
```

Use the final specification's precondition if it is the appropriate narrower domain. Keep the remaining frame proof explicit until it is discharged. The local `pipeline_units_finalisation` taking `SigmaFrame` at its own fixed outcome is a reasonable shape.

Add a negative theorem that the retired universal frame premise implies `False`, analogous to the already-added parser-premise counterexamples. Require positive instances at real returning executions.

### Then repair the observer model

[SigmaFrame's docstring](https://github.com/scidonia/lean-llvm/blob/dedbf66/LeanLLVM/Refinement/JsonPipelineSpec.lean#L324) acknowledges that the model has no fresh frame for a callee. The unit post now permits writes in the seven scratch regions; the narrow public frame does not. That gap cannot be removed merely by citing the broader `Owns` theorem.

Choose one explicit approach:

1. **For the scoped JSON milestone:** allocate/model scratch explicitly, prove separation from all live caller objects, and compare outcomes through a caller-visible memory projection that excludes private scratch.
2. **For a reusable general call model:** introduce fresh callee frames with allocation, non-aliasing and return/projection lemmas, then use those results here.

The first is the smaller immediate task. Do not assume a large semantics redesign is necessary for the first demonstration. Conversely, separation alone does not prove unchanged memory outside a narrow write region over the *entire* memory: scratch bytes really change. The observation relation must hide or project them intentionally.

## 5. Close one actual stage-2 walk proof

`Stage2WalkObligation` is still unproved. `stage2WalkObligation_at_subCalls` assembles it from a completion premise and a postcondition premise; its own documentation correctly says that neither is discharged by that assembly theorem.

After the two statement repairs, implement the remaining trace proof in this order:

1. **Initialisation:** derive all workspace contents, immutable pointer bindings, depth zero, log cursors/capacities and the entry-loop seed from `EntryState`. A seed theorem that assumes those facts is not the initialisation proof.
2. **Dispatch coverage:** give meaningful local facts at every reachable dispatch block. `WalkLocal` currently returns `True` outside the inner-loop blocks it covers; the remaining outer control flow has not thereby been verified.
3. **Container discipline:** relate depth, container types/states, pushes, pops, separators and root completion. Preserve staged stack bounds and connect refusal offsets to the state that produced them.
4. **Event and string updates:** preserve the repaired event trace, cursor bounds, arena spans, scratch frame and decoder-position invariants across helper calls.
5. **All exits:** prove accepting and refusing outcomes, including partially written outputs, reserve preconditions and the frame actually observed by the caller.
6. **Whole-run budget:** compose the local steps with the decreasing measure into `Satisfies` at the declared budget. Prove the cost of paths between back edges as well as descent at the edges.

The completion deliverable is a theorem for the concrete body and concrete selection, not another theorem that takes `Stage2WalkCompletes` or the whole run's postcondition as input.

### Modelled helpers need implementation correspondence

The six helpers now have models. Equations selecting a model and lemmas saying it returns `some` are useful, but they do not prove that compiled helper code implements that model.

Give each helper a contract and either prove its emitted body against it or list its equivalence as an explicit temporary trust assumption. In particular, the number helper model returns success on any readable lexeme and omits the native conversion's refusal exits. Prove the required lexical-validity condition at each such call or model the failure cases. Test malformed numeric tokens such as `1e`, `01` and `-`; classifying a token as numeric is not itself a proof of JSON number grammar.

The binary64 conversion model's agreement with `strtodSpec` should be retained. Its exact connection to the helper's actual scanner locals and control flow must remain visible.

## 6. Make the executable wrapper match its proved domain

The new route is a real integration advance. It copies Lean buffers into native allocations, calls `leanllvm_json_pipeline`, and returns metadata plus arena/event bytes. The repository reports a scenario over 122 default-profile corpus rows, including one excluded empty input, with fourteen policy refusals and eight non-default-profile rows skipped. This is finite evidence, not a complete equivalence theorem.

There are currently two different shells:

| Shell | Behaviour |
|---|---|
| Library `checkRoute` | Uses `parseBytes` to exclude reference depth/token exhaustion and character-policy refusals before the call |
| Standalone `RouteMain` | Checks empty/over-bound input, calls native code, then scans accepted documents for the character-policy class; it does not run the library's depth/token checks |

Neither is yet a complete, proved replacement API. The standalone probe is explicitly an instrument, and the library check's use of the scalar parser is appropriate for a temporary oracle but would retain scalar parsing cost on the supposed fast path.

### Recommended API decision

Choose one first deliverable and state it precisely:

- **Restricted certified kernel:** only admit documents satisfying a proved resource/policy predicate; make unsupported-domain refusal distinct from invalid JSON.
- **Drop-in parser replacement:** preserve the reference parser's input/depth/token outcomes, character policy and declared result abstraction on the full supported API domain.

For the second, implement and prove inexpensive resource/policy checks or incorporate them into the verified parser. Do not permanently reparse every input with the scalar parser and present the native part's speed as the API's speed.

The standalone character scan is a second implementation. Prove its relationship to the reference scanner, reuse verified code, or incorporate policy checking into the verified path. Add depth tests around the reference bound of 128 and the native stack bound, rather than inferring agreement from a corpus that skips custom-limit profiles.

## 7. Compare semantic outputs and make FFI failures explicit

### Expand the native route's checks

[check.sh](https://github.com/scidonia/lean-llvm/blob/dedbf66/probes/json/route/check.sh#L83) compares only the first output line between the Lean route and C driver: verdict, cursors and error offset. The route also prints arena and event bytes, but those lines are not included in that fidelity comparison. Equal lengths and verdicts can conceal wrong values.

Add:

- Byte-for-byte comparison of the returned arena and event streams between callers.
- A decoder/abstraction relating those bytes to the reference tape/value, with a concrete binary64 number relation.
- Controls that alter a payload byte while preserving all metadata and require the scenario to fail.
- Diagnostics distinguishing verdict disagreement, value disagreement and an allowed difference in error offset.

Both callers invoke the same native pipeline. Their agreement checks the adapter path; it is not an independent proof that the parser itself is correct. Reference-level value comparison is a separate requirement.

### Harden the adapter boundary

[shim.c](https://github.com/scidonia/lean-llvm/blob/dedbf66/probes/json/route/shim.c#L79) clamps oversized returned cursors to capacity, and its failure branch returns a 48-byte array without constructing a defined error record. These should not become production API behaviours.

Return a tagged result distinguishing parse refusal, unsupported domain, allocation failure and internal contract violation. Do not mask an oversized cursor by reporting a truncated one; detect it as an internal error before copying output. Validate array sizes and capacity arithmetic before the native call. A check after the call cannot repair an out-of-bounds native store.

Make POS8 table initialisation an explicit effect or include it inside the adapter's controlled initialisation path. Consuming a dummy return to preserve an otherwise pure extern call is a probe workaround, not a durable API design.

Copying buffers is a reasonable first safe adapter. Measure and reduce its cost only after the actual call path and results are covered.

## 8. Keep the two scanner routes distinct

`JsonScanLane` concerns the separate window-scanner development. Its rule chain is now derived, and `ruleBridge_pending` proves the pending-requirement arm. The no-requirement branches, whole lane step, bounded loop induction and footprint theorem remain open. Consequently `scanWindowLLVM_refines` and its installation pin remain absent.

This is not identical to the assembled native pipeline's extracted 64-byte SIMD units. Do not use the missing legacy `json_scan` gate as a substitute for tracking the native pipeline's own theorem and artifact identity.

If the immediate goal is the assembled JSON parser, prioritise that pipeline's stage-2 and final semantic proofs. Finish the separate scanner theorem if it is part of the chosen first replacement or a deliberately separate milestone. Avoid treating completion of both paths as an accidental prerequisite.

## 9. Terminal theorem and artifact acceptance

The final result must instantiate:

- The concrete pipeline and helper environments.
- The actual input domain and wrapper behaviour outside it.
- A concrete event/value abstraction, including the binary64-versus-lexeme decision.
- Completion and defined execution for admissible inputs.
- The caller-visible memory relation after scratch is hidden correctly.

It must not assume an unrestricted `SigmaFrame`, the desired `ParserHalfForOutcome`, stage-2 completion, or stage-2 correctness as residual hypotheses. Standard axioms and explicit compiler/FFI/conformance assumptions may remain, but logical premises equivalent to the target result must not be presented as completed verification.

Bind the proof to the actual installed artifact. The new probe compiles C at `-O2`; the pinned stage-2 fixture is derived from a different `-O3`, helper-separated and scratch-flattened emission. Record the exact correspondence relied on. Prefer one auditable artifact path: compile the proved fixture plus separately covered helpers, or explicitly justify the relation from the normalised/helper-separated body to the shipped build. Do not infer it merely from a shared source filename.

Retain the declared trust in the compiler/backend initially. A verified compiler is not the next prerequisite. Custom-semantics conformance, executable pins, normalisation, ABI assumptions and helper equivalence still need honest accounting.

Update the trust ledger's stale statements: it is labelled at `a706a17` and still says no JSON Lean caller exists, although the new native probe now provides one. Clarify that the caller exists while its semantic correspondence remains open. A source build of an opaque extern is not a kernel proof that the linked implementation has the declared behaviour.

## 10. Work order and completion gates

| Order | Deliverable | Completion criterion |
|---:|---|---|
| 1 | Repair event trace and frame-premise statements | Literal/number event transitions satisfy the invariant; retired universal frame premise has a negative lemma; new frame obligation is execution-indexed |
| 2 | Finalise scratch observation discipline | Workspace separation and writes are derived; caller-visible framing follows without a global false premise |
| 3 | Close concrete stage-2 execution | Initialisation, full dispatch, all exits and declared budget yield `Stage2WalkObligation` at the concrete helper selection |
| 4 | Prove helper correspondence and parser meaning | Every callee is covered or explicitly assumed; concrete event relation and reference acceptance/value correspondence are derived |
| 5 | Unify the executable wrapper and proof contract | Same limits/policy/domain logic; explicit failure outcomes; returned payloads compared and interpreted |
| 6 | Install and benchmark the covered artifact | Real proof producer accepts the exact unit; mismatches fail closed; performance includes checks, allocation, copies and output handling |

For each gate, report the exact theorem type, its residual premises, axiom footprint, fresh build command and result. Source-elaborate modules consuming `include_str` fixtures. Keep the repository's memory ceiling and source-elaboration lock discipline. Ensure the new standalone proof modules are named by the validation target; their presence on disk is not a successful proof build.

Avoid adding more assembly wrappers around unproved completion/postcondition premises. The next useful result is a concrete execution theorem that removes such premises.

## 11. Validation status of this review

- Inspected commit `dedbf668778e4a2288cb2c25ed2508db8818b117`, including the new wrapper, helper models, walk invariant, frame premise and lane bridge status.
- `bash tests/json-import-boundary.sh`: passed.
- `bash probes/json/route/check.sh`: stopped with setup exit 3 because the native executable was not present locally. This is not a failing parser observation.
- Lean/Nix/Clang unavailable: no independent kernel build, helper/native differential run or new route run was performed.
- Event-width and universal-frame findings are derived from source definitions; their proposed Lean counterexamples should be committed and checked under the pinned toolchain.

## 12. Recommended stopping criterion

Call the first milestone complete when one Lean-callable JSON API has a concrete theorem for its actual supported observations and domain, completes without undefined behaviour, preserves the chosen reference semantics, and executes the artifact accepted by its proof-bound installation route.

The project is now closer to that milestone in execution and infrastructure. The proof is still missing central work, and the two statement defects above would obstruct an honest final proof even if more inner-loop lemmas were added. Repair those first, then finish the one selected path end to end.
