# Ultra-compilation contract — certified SIMD JSON parsing

This document fixes the interface and the obligations. It is the contract the
harness and the candidate search are held to; changing it is a decision, not an
edit. It does not claim any capability: the audited state lives in
`docs/capabilities.md`.

## 1. Public API

Parse one complete UTF-8 JSON document supplied as bytes.

```text
parseDocument (limits : Limits) (input : ByteArray) : Result ParseError Tape
```

The limits are explicit arguments because §2 requires input length, nesting
depth and output capacity to be stated; a document that fits no default is
still parseable at a caller's chosen bound.  `Result` distinguishes
`invalid` — a proof obligation that the input is not valid JSON — from
`inputTooLong`, `depthExceeded` and `outOfCapacity`, which are resource
outcomes and prove nothing about validity.

* Accepts the four JSON whitespace characters before and after the document.
* Rejects trailing non-whitespace and any second top-level document.
* NDJSON, incremental/networked input and concurrent parsing are out of scope
  for the first API; they are later extensions, not silent behaviours.

A second, optional API decodes the tape into a logical value
(`decodeTape : Tape → Option Value`): a total function on arbitrary tapes has
no honest `Value` to return, so a malformed tape yields `none` and
`decodeTape_correct` states the produced tapes decode. Numbers keep their source
lexeme; converting a lexeme to binary floating point is a separate obligation
with its own proof and is not part of the first equivalence contract.

### 1.1 Normative references and clause map

The specification is RFC 8259 (STD 90) together with RFC 3629 for the encoding
its §8.1 requires.  RFC 7493 (I-JSON) is the strictness profile adopted for
characters only.  ECMA-404 is the same grammar as RFC 8259 §2, not an alternative
to it.  The section numbers below are citations of clauses, not summaries.

|Clause|Requirement|Our reading|Consequence|
|---|---|---|---|
|8259 §2|`JSON-text = ws value ws`; the six structural-character productions carry `ws` on both sides|implemented as the ABNF reads|whitespace is allowed wherever the ABNF allows it|
|8259 §3, §4, §5|lowercase literals; objects; arrays; names `SHOULD` be unique|the grammar, with duplicates preserved in order|outside RFC 7493 §2.3, and stated so|
|8259 §6|number grammar; `NaN`/`Infinity` not permitted; implementations may limit range and precision|grammar enforced, lexeme preserved, magnitude unconstrained|outside RFC 7493 §2.2, and stated so|
|8259 §7|escape list; `unescaped = %x20-21 / %x23-5B / %x5D-10FFFF`; surrogate-pair rule|the ABNF, with the pair rule as a clause|`"\uD834\uDD1E"` and raw `𝄞` denote the same character|
|8259 §8.1|UTF-8 for interchange; BOM `MUST NOT` be added, parser `MAY` ignore|RFC 3629 as normative base; the `MAY ignore` option is not taken|strict UTF-8 is part of the language, and a BOM is refused as a non-text|
|8259 §8.2|the ABNF admits `"\uDEAD"`|`RfcText` admits it; `Policy` refuses its reading|the two adherence theorems are conditional on `Policy`|
|8259 §9|a parser `MUST` accept every grammar-conforming text, and `MAY` set limits|narrowed by `Policy`, and bounded by the resource limits|never claimed unconditionally|
|3629 §3, §4|invalid sequences must be rejected; the `UTF8-char` ABNF|transcribed clause for clause in `LeanLLVM/JSON/Utf8.lean`; the parser's strict reading is checked against it, and the extracted validator's emitted body is proved against it too — `utf8_stage_refines` states the returned word is zero exactly when the staged window is a valid prefix, and `utf8_stage_refines_chars` the complete-character case at `n % 64 ≠ 0`|overlongs, encoded surrogates and `> U+10FFFF` are not JSON texts|
|7493 §2.1|no Surrogates or Noncharacters in names and string values|`Policy`|the only narrowing of the language|
|7493 §2.3|no duplicate member names|not adopted|duplicates preserved; no I-JSON conformance is claimed|

## 2. Policy decisions

| Concern | Decision |
|---|---|
| Input encoding | Strict UTF-8; malformed sequences and overlong encodings rejected |
| Byte-order mark | Rejected, as an explicit API policy |
| String escapes | The standard escapes and four-hex-digit `\uXXXX` validated |
| Unicode surrogates and noncharacters | Well-formed pairs required; unpaired escaped surrogates and noncharacters rejected, as RFC 7493 §2.1's character policy |
| Numbers | JSON number grammar enforced; exact lexeme preserved; no `NaN`/`Infinity` extension |
| Duplicate object keys | Preserved in order, including duplicates; no implicit last-wins map |
| Output | A tape with checked spans into the input, plus a unique decoded value |
| Diagnostics | Syntax rejection required; diagnostic text and exact earliest-error position are not part of the equivalence contract |
| Limits | Input length, nesting depth and output capacity are explicit; exhaustion is distinguishable from invalid input |
| Parser reuse | Supported only through explicitly owned reusable buffers; fresh and reused modes are measured separately |

The recognised language is therefore RFC 8259's grammar restricted by RFC 7493
§2.1's character constraint.  `accepted_is_rfc_text` and
`rfc_text_accepted_on_policy` state the two directions; both are conditional on
`Policy` and the latter also on the resource limits, so neither is RFC 8259 §9's
unconditional `MUST`.  `"\uDEAD"` and the noncharacters RFC 7493 §2.1 forbids
are texts this API refuses, and that pairing is the deliberate restriction.

## 3. Theorem families and their repository names

Proposed names from the programme map onto the following obligations. A name
may change; the strength may not.

| Obligation | Intended statement | Where it lives |
|---|---|---|
| Reference correctness | `parseRef_sound`, `parseRef_complete`: acceptance and decoding agree with the byte-level JSON semantics, subject to policy and limits | `LeanLLVM/JSON/Correct.lean` |
| Tape interpretation | `tape_valid`, `decodeTape_correct`: spans well formed, nesting and values consistent, decoded meaning correct; a source-backed tape owns its input for its lifetime | `LeanLLVM/JSON/TapeCorrect.lean` (`tape_valid`), `LeanLLVM/JSON/Correct.lean` (`decodeTape_correct`) |
| Adherence, forward | `accepted_is_rfc_text`: everything accepted is an RFC 8259 text, with an interpretation — `Accepted → RfcText` | `LeanLLVM/JSON/Correct.lean` |
| Adherence, backward | `rfc_text_accepted_on_policy`: every RFC 8259 text whose interpretation satisfies `Policy`, inside the resource limits, is accepted and decodes to that interpretation — `RfcText ∧ Policy → Accepted` | `LeanLLVM/JSON/Correct.lean` |
| Block correctness | `scanBlock_correct`: the candidate block operation refines the scalar transition, including next state and error information | `LeanLLVM/JSON/ScanBlock.lean` (`scanBlock_correct`) |
| Whole-scan correctness | `scan_simd_refines_scalar`: the per-quote refinement of the block/tail scan against the parser's own string scanner — at a body's opening quote, a body `scanCharsEnd` accepts closes where the block scan stops, and every position the block scan accepts ends at a quote; `scanStringBlocks_refusal` is the contrapositive, a body the block scan refuses being one `scanCharsEnd` never accepts, and `tailRun_ended` is finalisation: at end of input an open body, an unfinished escape and an unfinished UTF-8 sequence are all `.ended` | `LeanLLVM/JSON/ScanBlocks.lean` |
| Actual LLVM refinement | `scannerLLVM_refines`: the imported baseline and candidate bodies, under this repository's semantics — not two Lean models compared to each other | `LeanLLVM/Refinement/*` + fixtures. The J2 instance (`LeanLLVM/Refinement/JsonClassifyIR.lean`) is candidate-against-reference: it relates the emitted classifier body to the verified scalar transition's mask, because the pair has no baseline *body* — the fragment has no pointer arithmetic, so no scalar byte-walking body can be written in it — and **the baseline-body half of this obligation remains open**. A second instance, for the stage-1 mask unit, is the same shape and does not close that half either: `s1_masks_refines` (`LeanLLVM/Refinement/JsonS1MasksSteps.lean`) relates the body pinned from `probes/install/ir/json-s1-masks.candidate.ll` to `JsonScanSpec`'s six masks and carry, over a body that stores them, so the related side is emitted text and the reference side is the specification. A third instance, for the entry positions unit, is the same shape again and does not close that half either: `entry_pos8_refines` (`LeanLLVM/Refinement/JsonEntrySteps.lean`) and `entry_b8_refines` (`LeanLLVM/Refinement/JsonB8Steps.lean`) relate the two bodies pinned from `probes/install/ir/json-entry.candidate.ll` to the entry word `JsonEntSpec` specifies — the returned cursor, the words each body writes read as the model's positions, and every byte outside the span its stores reach unchanged — so the related side is again emitted text and the reference side the specification, and the selection that fills the entry stream is not related at all |
| Contextual replacement | `replaceScanner_sound`: the local statement transported through the parser caller and the linking environment | `RefinesWithinAcross` / `CallRefinesWithin`. The J2 instance (`LeanLLVM/Refinement/JsonSeam.lean`) carries the relation through `scanCaller`, a staging caller of its own — not through the JSON parser, which is why the parser half of this obligation stays open |
| Build acceptance | the installation gate binds theorem, artifacts, toolchain, target, data layout and attributes into one checked record | `probes/install/*` |

The local relation is stated schematically as `Γ ⊢ candidate ⊑ baseline`, where
`Γ` records bounds, ownership, external calls, target configuration and
admissible initial states. It covers observable results, memory effects,
definedness and divergence: matching return values only when both executions
terminate is too weak.

For the deterministic scalar reference, no admissible input may gain undefined
behaviour or divergence that the reference does not have.

## 4. Scanner contract

```text
scanBlock (state, block, validByteCount) → (nextState, structuralInfo, status)
```

State must carry everything that crosses a block boundary: whether the scan is
inside a string, whether a trailing backslash run changes the next byte's
escaping, pending UTF-8 continuation requirements, and whatever else a
successor needs to recognise token starts. The invariant that makes a state
admissible is part of the contract: local refinement may assume it only with a
proved initialisation and a proved preservation step.

The J2 instance does not yet meet that list: no emitted body carries state
across a block. `LeanLLVM.JSON.ScanState` (`LeanLLVM/JSON/ScanBlock.lean:68`)
carries the cursor (`pos`) and nothing else, and stays cursor-only because
`scanBlock` returns it — a cursor advance and a mask. The state that crosses a
block boundary is `BodyState` (`LeanLLVM/JSON/ScanBody.lean:39`): one state
carrying the in-string flag (`inside`), the escape-run parity (`oddRun`) and
the pending UTF-8 requirement (`utf8`), which `LeanLLVM/JSON/ScanWindow.lean`'s
window fold threads through the byte rule, with `carryAt` the lane-indexed
specification its carry is proved equal to (`windowOf_carry:1028`,
`carryAt_append:1058`). `scanBlock_correct` is therefore a
statement about classification and cursor advance, not about a state that
crosses a block boundary in a scanner.

Finalisation is explicit: end of input rejects an incomplete string, an
incomplete escape sequence and an incomplete UTF-8 sequence. The grammar stage
handles unmatched containers; each rule is validated in exactly one stage and
no rule may be lost between stages.

### Lane-mask regression (required test, not an implementation note)

The subtraction-based zero-byte idiom is **not** an exact per-byte mask:

```text
x  = 0x0000000000002D2C
m  = x XOR 0x2C2C2C2C2C2C2C2C
(m - 0x0101010101010101) AND NOT m AND 0x8080808080808080  = 0x8080
exact high-bit comma mask                                  = 0x0080
```

The adjacent lane is set by borrowing. This repository already uses the
no-borrow form (`LeanLLVM/Refinement/CommaMask.lean:31`) and proves it equal to an
exact per-lane specification (`:19`, `CommaMaskKernel.lean`); the regression
above is to be carried into the JSON scanner's test corpus so that the property
is tested on the code that ships, not only on the model.

## 5. Memory, ownership and buffers

For every memory-using replacement the certificate must record: the input's
logical length and readable extent; output capacity and the maximum number of
produced indexes and tokens; the read and write footprint; alias restrictions
and ownership; permitted and actual load alignment; input and output lifetimes
and pointer provenance; fixed-width index overflow constraints; and the
behaviour on insufficient capacity and resource exhaustion.

Masking the result of an out-of-bounds vector load does not make the load
valid. Proofs quantify over every allowed alignment and tail length, not only
over padded benchmark buffers. `OutOfCapacity`, depth-limit exhaustion and
allocation failure are distinguished from a demonstration that the input is
invalid.

## 6. Compilation seam

1. Compile the verified scalar Lean definition into a separate baseline unit.
2. Have the caller reference a compatible external declaration so its optimiser
   cannot inline the baseline before replacement.
3. Capture baseline and candidate LLVM and certify both under the same boundary
   contract.
4. Install the accepted candidate; otherwise link the baseline, or fail in
   strict mode.
5. Resume ordinary LLVM optimisation, linking and execution.

An opaque declaration alone does not connect execution to the Lean function.
That bridge is either proved or recorded as an explicit trust assumption; no
source-to-extern axiom may be counted as a proved end-to-end result. A Lean
`ByteArray` is **not** assumed to have a raw pointer/length ABI; any wrapper or
adapter stays visible with its correctness assumptions and its cost.

The installation record **must** bind: content hashes, the covering theorem,
the semantic version, source commits, toolchains, target triple, data layout,
feature set, semantic attributes, declarations, call-site assumptions and
external contracts. The record as it exists today carries seventeen fields and
does not yet bind source commits, declarations, call-site assumptions or
external contracts; the rest lives in the manifest. Hashes prevent stale
pairing; they do not prove importer or exporter correctness.

## 7. Trust ledger

What a result here inherits when it is read as a claim about an installed
artifact. The rows were written at revision `a706a17`. The Lean-caller entries —
row 9, §7.1 item 5 and the runtime clause of §7.2 — are corrected against
`dedbf66`, where the native JSON route exists; no other row was re-measured, and
they stand as written at `a706a17`. One row per trusted step, with the basis it
rests on and the artifact in this tree that carries it. The bases are a closed
vocabulary:

- **proved** — a kernel-checked theorem in this repository.
- **assumed** — a definition or a fact outside the kernel: reviewed, not proved.
- **checked by an executable pin** — a compiled `#guard`, `decide` or script
  that stops the run when the text or the bytes disagree.
- **outside the kernel's reach** — a step no Lean term can express, recorded so
  that a reader can audit it.

A claim is licensed only by the rows its evidence column names. A clean axiom
footprint licenses row 1 and nothing below it.

| # | Layer | What is trusted here | Basis | Evidence in this tree |
|---|---|---|---|---|
| 1 | Proof logic | The Lean kernel and the three approved axioms; no project axiom is declared | proved | Every soundness theorem is pinned with `#guard_msgs in #print axioms`, in `LeanLLVMTest/` or beside the theorem in its own module: `LeanLLVMTest/Json.lean` (the six parser theorems, `scanBlock_correct`, `scan_simd_refines_scalar`), `LeanLLVMTest/Refinement.lean` (`IR_refines`, `loop_refines_candidate_within`, `depth_count_refines`, `classifySeam_refines`, `replaceScanner_sound`, `replaceScanner_ret`, `s1_masks_refines`, `entry_pos8_refines`, `entry_b8_refines`, `utf8_stage_refines`, `escape_expand_satisfies_of_arms`), and `JsonEscapeExpandAssembly.lean` (`escape_expand_satisfies_unconditional`, `expandArms_inhabited`). Footprint `[propext, Classical.choice, Quot.sound]`; no `axiom` declaration exists under `LeanLLVM/` or `LeanLLVMTest/` |
| 2 | Specification | `LeanLLVM/JSON/Spec.lean`'s inductive relations as the intended reading of RFC 8259 with RFC 3629, and `Policy` as the only narrowing of the language | assumed | §1.1's clause map is the audit, and it is prose: `RfcText` is a hand-transcribed relation, not derived from a machine-readable grammar. `accepted_is_rfc_text` concludes `RfcText` from acceptance alone; `rfc_text_accepted_on_policy` additionally hypothesises `Policy` and the resource limits, so no unconditional RFC 8259 §9 claim is made |
| 3 | LLVM semantics | `LeanLLVM/Semantics.lean`'s fuel semantics and `Calls` environment as the intended LLVM behaviour of the modelled fragment | assumed | The fragment is enumerated in `docs/capabilities.md`, "Language and IR coverage", with the construct in the fixture that each form serves. `phi` has paired evidence (`tests/phi-fragment.lean`) and a differential observation (`tests/phi-differential.sh`, which records itself as an observation, not a proof). No conformance theorem exists, and every refinement theorem is stated under this semantics, not under LLVM's |
| 4 | Intrinsics models | `LeanLLVM/Refinement/BitLanes.lean`'s lane definitions (eleven spellings, ten definitions) and the per-unit `Calls` environments (`s1Calls`, `entryCalls`, `utf8Calls`, `escapeCalls`, and `Pclmul.clmul` for `pclmulqdq`) as the meaning of the instructions a fixture calls | assumed | `Parser.checkIntrinsicShape` fixes each admitted shape; the bound set is compared with the fixture's measured call set by `tests/escape-intrinsics.lean` (with a negative control) for the escape unit only. Flags and poison are written at the arm: `cttz` deliberately differs from LLVM at `is_zero_poison=true` and is admissible only because no clause reads that lane. No model is proved equal to hardware, and target-feature lowering is recorded by the capture, not modelled |
| 5 | Fixture normalisation | That reducing an emission or a printed body to the syntax the parser models leaves the computed value unchanged | outside the kernel's reach | Per-item records exist for six units: `json-{entry,escape,s1-masks,utf8,pipeline}.{strip,rewrites}.tsv` and `stage2.{strip,rewrites}.tsv`. The comma-mask pair's removal list is in `capture.sh`; the classifier's is in `capture-json.sh` and the fixture header, by class rather than per item. Captures refuse constructs outside the fragment (`refuse_unmodelled`) and the result is checked with `opt -passes=verify`. Each removal is a per-item claim, not a proof; entry's `nuw`, `nsw`, `nneg` and `disjoint` are stripped with the widening recorded as "not re-established". `loop.ll`, `json-scan-body.ll` and `json-caller.ll` are printer output with nothing stripped |
| 6 | Fixture-to-AST association | The parser, `include_str`, and the executable pin that bind each proof's literal AST to the committed fixture bytes | checked by an executable pin | `#guard decide` over `parseModule src` in `JsonClassifyIR.lean`, `JsonEntryIR.lean`, `JsonEscapeIR.lean`, `JsonS1MasksIR.lean`, `JsonUtf8IR.lean` and `JsonSeam.lean`; the depth pin is restated in `LeanLLVMTest/Refinement.lean`. `probes/install/check.sh` mutates the candidate and loop fixtures and requires the guard to fail. Fixtures are not `lake build` inputs, so the pin is read only when its module is elaborated; the certificate producer re-elaborates the module from source, and that is what makes the pin current on the installation path |
| 7 | Printer | That `LeanLLVM/Printer.lean`'s text means to real LLVM what the AST means here, and is accepted by it | checked by an executable pin | The three F3 decisions are written at the printer: no `inbounds`; a register index at the width its definition binds; `align 1` on load and store, with an `alloca`'s alignment printed as parsed. `LoopEmit.lean` refuses to print unless its output parses back to the same function; `json-caller.ll` and `json-scan-body.ll` are printed and pinned. Round trips are pinned in `LeanLLVMTest/Core.lean`; `llvm-as` acceptance is exercised in `tests/phi-differential.sh` and `opt -passes=verify` in the captures. The printer is inside the artifact path for `loop`, whose installed object is built from printed text |
| 8 | Native compilation | That clang, the LLVM backend and assembler, and `ld` preserve the fixture's meaning, and that a rebuild reproduces the object | outside the kernel's reach | `probes/install/build.sh` compiles each unit with `clang -c` and links its marker with `ld -r`; `probes/install/select.sh` rebuilds from the fixtures under the same basenames and requires the same object hash. Captures and installations record their flags and target (`-O2 -mavx2` for the classifier; `target_features=none`, triple and data layout in the manifest); `probes/install/toolchain-id.sh` pins the Lean, clang and ld versions. A byte-equal rebuild shows the object is that fixture's output; it says nothing about the instructions the machine executes |
| 9 | Lean execution bridge | That a Lean caller's `@[extern]` call reaches the certified symbol with a compatible ABI | outside the kernel's reach | Comma-mask seam only: `probes/install/Caller.lean` and `probes/app/App.lean` declare the symbol `opaque`; `probes/app/build.sh` compiles with `lean -c` then `leanc`, requires the call to survive (`app.ll` and `nm -u`), and `probes/app/check.sh` links it against the candidate, baseline and loop units, runs each, and compares answers. No theorem connects the extern declaration to the body, and the ABI agreement is observed at link and run. **A JSON Lean caller now exists**: `probes/json/route/` builds `RouteMain.lean`, whose `@[extern]` declaration is compiled by Lean's own compiler, against the assembled object; `shim.c` copies its buffers into the ABI, `build.sh` requires the symbol to be imported by the adapter and defined by the executable (`nm`), and `check.sh` compares its verdict, four cursors and error offset with an independent C caller on every default-profile corpus row. The caller exists; its **semantic correspondence remains open** — a source build of an opaque extern is not a kernel proof that the linked implementation has the declared behaviour, and the route's README records that it does not establish the object executes the pinned body the theorems are about. `JsonSeam.scanCaller` remains a Lean AST printed through the framework printer, so its compiled form is not Lean's compiler's output |
| 10 | Installation | The certificate producer and selector as written, the hashes they compare, and the shell manifest | outside the kernel's reach | `InstallCertificate.lean` writes seventeen fields; `probes/install/select.sh` compares each with the file it names, rebuilds the units, re-elaborates the proof module and reproduces the certificate. Gates: `tests/m3-certificate-gate.sh` (47 runs), `tests/m4-loop-install-gate.sh`, `tests/m4-depth-install-gate.sh`. `tests/json-scan-select-gate.sh` is the JSON selection gate and currently stops at setup, refusing the fixture at the missing `scanWindowLLVM_refines` pin, so no JSON selection gate passes. The certificate does not bind source commits, declarations, call-site assumptions or external contracts (§6), and the manifest is executed as shell. A hash binds bytes, not their semantics |

### 7.1 Where the tree is weaker than a clean ledger suggests

Each of these is a deliberate record, not an oversight, and each narrows what a
claim over the rows may assert.

1. **Intrinsic conformance is assumed per instruction, and coverage is checked
   for one unit.** Lane order, signedness and the poison corner are written into
   the lane definitions, and the flag divergence is documented; but no model is
   proved against hardware, and the inventory-versus-environment comparison is
   compiled only in `tests/escape-intrinsics.lean`. `JsonEntryIR`,
   `JsonS1MasksIR`, `JsonPipelineIR` and `JsonStage2IR` name their inventory
   files in prose without a compiled comparison against the set their
   environment binds, and `JsonUtf8IR` names none.
2. **Normalisation is per item for six units and per class for the rest.**
   `capture.sh` and `capture-json.sh` record their removals as a class list with
   a reason each; only the six measured kernels have a row per removed token.
   Stripping `nuw`, `nsw`, `nneg` or `disjoint` is recorded as widening and
   explicitly not re-established, so the refinement statement is about the
   stripped text and no theorem answers for the flag it removed.
3. **The fixture pin is executable and can be stale.** Because a fixture is not
   a `lake build` input, a green `lake build` does not show that the pin read the
   current text. The mutation controls run in `probes/install/check.sh`; the
   depth mutation is described there and not committed. Re-elaboration by the
   certificate producer is the route that restores freshness, and it exists only
   for the units the producer knows.
4. **The printer is repaired by decision and pin, not by a semantic theorem.**
   F3's three cases are settled, and the printed text is accepted by `llvm-as`
   where a route exercises it, but no theorem gives printed text its real LLVM
   meaning. One exporter loss remains outside those three: `Function.render`
   writes an unadorned `define`, so linkage, visibility and calling convention
   cannot be printed — the AST has no field for them. The fixtures printed here
   start from an AST that carries no such field, so nothing is lost on the
   artifact path, but a parsed external source with `internal` linkage would not
   round-trip to text with the same linkage. For `loop` the printer is on the
   artifact path.
5. **The Lean execution bridge covers the comma-mask seam and the native JSON
   route, and neither is proved semantically.** Its ABI correspondence is
   observed by link and run. For the seam the caller is printer output rather
   than compiler output. `probes/json/route/` calls the assembled pipeline from a
   Lean program whose extern Lean compiles: `RouteMain.lean` takes the library's
   `admission` decision, `shim.c` copies the staged bytes into the ABI, and
   `check.sh` compares the route's observations with an independent C caller's
   on every admitted default-profile row. That is a source build of an opaque
   extern plus an observed agreement, not a theorem: nothing in the kernel says
   the linked object implements the body the stage-2 and pipeline theorems are
   about, and the route does not establish that the object executes the pinned
   body. What *is* proved is the document side: the decision is `admission`'s and
   the record's document clauses follow from it (§7.5), so a document on the fast
   path is inside `pipelineSpecPre`'s domain by proof, and every other document
   is answered by the reference parser rather than by the object.
6. **Installation covers four units, none of them JSON.** `select.sh` knows
   `json_scan`, but `JsonScanIR.scanWindowLLVM_refines` is a name no theorem
   inhabits (the instruction-level step of `scanWindowStatement` is open), so the
   producer refuses the unit and the gate refuses it at the missing axiom pin.
   The classifier is not in the selector's table at all. The only installed
   replacement in the tree is the comma-mask seam, which is not a JSON
   operation.
7. **Semantic conformance has no theorem.** The model's fragment is enumerated
   and its captures refuse what it does not model; over-approximating source and
   target does not by itself transport a refinement to real LLVM, and no
   per-kernel adequacy statement replaces that argument.
8. **The model's call discipline does not allocate a fresh frame.** A callee in
   `Semantics.lean` runs at the caller's `Mem`: there is no fresh frame, so a
   body's own stack objects are caller-supplied addresses (`JsonStage2IR`'s
   `stage2Args` appends eight, and `stage2StagedPre` stages them). A compiled
   callee's stack is disjoint from its caller's objects; here nothing states
   that, so a stage-2 selection may write the pipeline's `sc`, `mk`, `entw`,
   `nk`, `nxp` or `xcarry`. Consequently the pipeline's unit post can only claim
   `UnchangedOutside` over the caller's buffers *plus* the stage-2 walk's seven
   appended objects (`pipelineUnitsPost`, `stage2StagedWrites`), and the
   specification's frame is stated at that same list rather than at the caller's
   buffers alone: `SigmaFrame` names the caller's thirteen regions extended by
   the callee's seven (`CallsFootprint.CallerView`), so
   `JsonPipelineRefine.pipeline_units_finalisation` derives it from the units'
   post's own witnesses and `pipeline_satisfies_of_parser` carries no frame
   premise. That is the limit stated rather than discharged — in the program the
   seven are private stack objects, and here the clause has to admit them. The
   one fact of this kind the tree still carries as a hypothesis is
   `PipelineDischarge.Stage2SlotKeeps` (the callee leaves the caller's two count
   slots alone), because those two slots appear in no list the stage-2 record
   declares for itself. What the specification's frame cannot be is a universal:
   `SigmaFrame` over every argument list, memory and outcome is false, because its
   extent component is a reading of the returned memory
   (`LeanLLVMTest.Counterexamples.pipeline_frame_hsem_false`). The repair that
   would let the frame be claimed over the caller's buffers alone is a fresh-frame
   call semantics — a callee scratch region disjoint from the caller's objects —
   which is a change to what the semantics models, not a theorem.

### 7.2 The claim this ledger licenses

> A specified Lean JSON operation replaced by a particular SIMD implementation,
> proved equivalent under explicit input and staging conditions in an audited
> LLVM fragment, with compiler, runtime and artifact-binding assumptions listed
> separately.

The rows above license this claim only in the following parts.

| Clause | Status (as at `a706a17`, with row 9 read at `dedbf66`) |
|---|---|
| a specified Lean JSON operation | Met for one operation: the block layer's masked classification, `maskOf` (the `maskOfList` scalar transition) over a 32-byte window, which is what `scanBlock_correct` relates the block operation to. The parse — the operation a product needs — is not the subject of any installed result |
| replaced by a particular SIMD implementation | Met at the model for `json-classify.candidate.ll`, whose bytes are pinned and whose capture records `-O2 -mavx2`. Not met as a deployment: the classifier is not a selector unit and no certificate covers it |
| proved equivalent under explicit input and staging conditions | Met as a directional refinement, not symmetric equivalence: `scannerLLVM_refines` holds for every block readable at the argument, with the caller's memory unchanged, and `classifySeam_refines` and `replaceScanner_sound` carry it through the staging caller. The reference is the verified Lean transition; the baseline-body half is open because the fragment has no pointer arithmetic, so no scalar byte-walking body can be written in it |
| in an audited LLVM fragment | Met for fixture membership: the fragment is enumerated, the captures refuse what it does not model, and the fixture's construct inventory is measured. Model conformance to real LLVM remains an assumption (row 3) |
| compiler, runtime and artifact-binding assumptions listed separately | Met by rows 8–10 for the comma-mask seam, which has a real Lean caller and an installation record. For the JSON pipeline a Lean caller now exists — `probes/json/route/`, compiled by Lean and linked against the object — so the runtime row is no longer empty; what is missing there is the correspondence, since no theorem connects the extern, the adapter and the linked object to the pinned body. No JSON unit is installed, so there is still no artifact binding |

Clauses not yet met: the deployment of any JSON body; equivalence against a
baseline LLVM body; replacement through the parser (`docs/capabilities.md`
records "Refinement of the parser through the classifier" as missing); and an
artifact binding for a JSON unit. What the ledger licenses today is the
block-layer refinement, and separately the comma-mask installation through the
seam whose bridge is row 9. The JSON route's caller licenses nothing further by
itself: a caller is not a correspondence, so the pipeline remains a specification
with an executed build rather than a proved implementation.

### 7.3 Why the axiom list is insufficient

Row 1 is about the theorem, and the theorem is about a literal AST. Associating
that AST with the committed source text takes the parser and a successful
executable pin (row 6). Associating the fixture with the emission takes the
capture script and its per-item removals (row 5). Associating the fixture with
the installed object takes clang, `ld` and a rebuild comparison (row 8).
Associating the object with a Lean call takes the extern bridge (row 9), and
associating all of it with the certificate takes the producer, the selector and
the hashes (row 10). None of these adds a logical axiom to the theorem — the
proof term is still kernel-checked — and all of them add trusted machinery to a
claim about installed bytes. A `#print axioms` line answers only the first
question.

### 7.4 Evidence that is not a trusted step

Tactics and imported proofs are not rows: their output is a kernel-checked proof
term. The differential transcript (`probes/install/build/differential.txt`), the
corpus windows in `tests/json-classify/check.sh`, the benchmark numbers in
`docs/json-pipeline-performance.md` and the medians in `probes/bench` are
observations and measurements. They support no row and license no clause; they
are named where they are used so they cannot be mistaken for one.

### 7.5 The route's document domain, and the fallback

The route's decision on a document is one predicate, `admission`
(`LeanLLVM/JsonKernelDomain.lean`), and each of its clauses is one checker with
its own certificate (`LeanLLVM/JsonKernelCertificate.lean`): the non-empty
document, the input bound `Limits.default.maxInput`, the measured nesting depth
`docDepth`, and the reference's character policy read through the parser's own
body scanner.  The clause set is exactly the document clauses `pipelineSpecPre`
excludes — `admission_documentDomain` turns an `admitted` decision into
non-emptiness, the input bound and the parser's `depthExceeded`,
`outOfCapacity` and policy exclusions, and `routeSpecPre` composes that with the
staging construction.  Nothing about the domain is asserted without a proof, and
the capacity exclusion is a theorem about the parser (`parseBytes`
never returns `.outOfCapacity` inside the input bound), not a policy choice.

**The two addresses are words, and the record says so.**  The staging now states
`base < 2 ^ 64` and `ep < 2 ^ 64` beside the capacities it already bounded
(`pipelineStaging`, `JsonPipelineContract`), and `routePre` states the same two
facts of the caller's layout (`JsonCallRoute`); `0 < base` follows from the
three-byte prefix room the layout already requires.  The stage-2 record's
precondition states the corresponding facts at its own thirteen arguments
(`0 < b`, `b < 2 ^ 64`, `ep < 2 ^ 64`, `JsonStage2Contract.stage2Pre`): the entry
block's `%invariant.gep` is a signed `getelementptr` at `-1`, so a zero base is
not a caller the body can be run for, and a base or entry-stream address at or
above `2 ^ 64` cannot round-trip through the eight-byte word the staging writes.
The record's inhabitedness witness (`stage2_pre_inhabited`) is at `b = 1` for the
same reason.  These are properties of every real caller, not narrowing the
admitted documents, and the pre's `0 < nep` remains *obliged* rather than
stated: the empty entry stream is the all-whitespace document, which the route
admits and the body must be proved to refuse.

The scalar reference parser is the **fallback** for a document the decision does
not admit, and for nothing else.  The route's three outcomes are `admitted`
(the native pipeline answers), `refused` (the reference parser refuses, with its
own reason and position) and `fallback` (the reference parser accepts, and its
tape is the answer).  The fallback is not a pre-filter: a document `admission`
admits never reaches it.  It is the *current totality mechanism* — the API is
total today because every document outside the domain is answered by the
reference — and it is expected to shrink.

The stated direction is that the **fast path may later become total by other
approaches**, and the shape of the code is chosen for that: the clauses are
separate functions with separate certificates, so widening the domain means
removing a clause from `admission` and dropping its certificate, not
renegotiating the interface.  The depth clause reads the stage-1 depth
counter's own fold: `docDepth` is the maximum of the counter's running depth
over the document's structural delimiter sequence (the `{`/`[`/`}`/`]` bytes
outside string bodies, in document order — the sequence the stage-1 index
stream carries), computed with the counter's step `deltaZ`.  The certificate
states the bridge in both directions: `depth_measured_no_refusal` turns the
measured bound into the absence of the parser's `depthExceeded`, and
`depth_refusal_deep` turns a `depthExceeded` into a witness that the document
nests past the bound.  The unconditional converse of the pair cannot hold — a
document the parser refuses for *syntax* before it reaches the depth check is
not a depth refusal however deeply it nests — which is why the clause keeps its
own measurement rather than restating the parse.

Widening this clause was a deletion: the opener-count clause and its
certificate (`openersTotal`, `depthExceeded_openers`) are gone, and a
deep-but-balanced document — `probes/bench/json/scale-4096.json` carries 179
opener bytes at nesting depth 2 — is admitted rather than answered by the
fallback.  `tests/json-depth-clause.lean` is the oracle gate: it compares the
clause's verdict with the reference's own depth verdict on the deep-but-balanced
class, the boundary, and the corpus's depth rows, and reproduces the deleted
clause as a control that disagrees on exactly that class.

**The route's native character-policy scan is proved at the model level; its
body correspondence is not.**  The probe's `probes/json/route/policy.c` decides
the policy clause natively, and
`LeanLLVM/Refinement/JsonPolicyModel.lean` writes its transition beside the
reference's and proves the two the same step.  The transition is the emission's
`policy_step` at its own byte and lookahead, in the emission's branch order,
with the three-valued class `policy_class_of` reads; the reference's reading is
`refClass` over `scanCharsFrom`.

`policyStep_spec` is the one-step equivalence: every branch of the emission's
step is the reference's step at the same byte — the same refusal class at the
same labelled position, or the reference's own decomposition into the character
it accepted and the scan of the suffix the emission continues at, or a branch
that answers nothing where the reference does not refuse on the policy's
account (it ends, or fails for syntax).  `policyWalk_spec` carries it over a
whole scan, `policyClass_refClass` reads that at the fuel `policyClass`
supplies, and `policyClass_backward` states the backward fill's recurrence —
`cls[i]` is the step's own class or the class already filled at `cls[next]`,
which is what makes a pass filling slots from the buffer's end the forward walk.
The position scan is covered too: `scanCharsEnd_error` in
`LeanLLVM/JSON/Scan.lean` names the error side (the success side was already
`scanCharsEnd_sound`), and `refClass_scanCharsEnd` states that the refusal
`policyRefusalAt` reads through `scanCharsEnd` is the reference's, reason and
position.  All six theorems are at `[propext, Quot.sound]`, pinned in the model
module beside a `Classical.choice` control.

What that does **not** establish is that the emitted body computes this
transition.  The emission is outside the modelled fragment — `switch`,
`insertvalue`/`extractvalue` and an anonymous-struct return — so the step from
the instructions to `policyStep`'s branch structure is unproved, and no proof in
this fragment can close it while the fragment stays as it is.  So this row
claims model-level agreement and says nothing about the emitted body; the
policy clause's runtime evidence remains the route's observation (§7.1 item 5
and `probes/json/route/README.md`), and the body correspondence is the open,
structural obligation.

### 7.6 The stage-2 helpers' correspondence

The emitted `s2_walk` calls six functions out of line — `s2_init`,
`s2_value_pos`, `s2_after_value`, `s2_string_body`, `od_scalar_value` and
`num_fast_el1`.  `kernel/json/stage2.c` defines them, and
`probes/install/ir/stage2.candidate.ll` *declares* them: the derivation keeps each
as a call (`stage2.rewrites.tsv` class r2, "their bodies are outside this
fragment ... each is resolved by the fixture's `Calls` environment at the record
or tier theorem that states its contract").  `LeanLLVM/Refinement/JsonStage2Body`
therefore models each function's observable at the call boundary — the returned
word, the words it writes, and the memory it leaves — and
`stage2SubCalls` selects those six.
`probes/install/ir/capture-stage2-helpers.sh` captures each helper's own
`define` block from the same emission the walk's fixture is taken from, and
`LeanLLVM/Refinement/JsonStage2HelperIR` pins the bodies the fragment expresses —
proved to parse back to the ASTs it states — and proves one contract of its
emitted body.  What follows is the correspondence for each of the six, in the
ledger's own vocabulary: what is proved, what is trusted, and what a caller must
still supply.

**The trust, once for each helper.**  No model is a refinement of the compiled
function.  The models are transcriptions, and the transcription is pinned by text:
`JsonStage2Body`'s `#guard`s assert that the lines each model encodes are lines of
`kernel/json/stage2.c`, with `#guard !occurs stage2Src "…// absent"` as the
control that the marker discriminates.  A transcription is not a proof of
equivalence, and the distance between the two is the pipeline's body-faithfulness
seam (§7.1 items 1–3 and row 5): the pin says the source text is where the model
says it is, and nothing in the kernel says the instructions execute that text.
Row 5's basis — outside the kernel's reach — is this row's basis too.
Where a row's basis is *proved (body)* the distance that is closed is the
transcription-to-body one: the emitted `define` block, as captured, runs at the
contract's staging and satisfies the contract.  The body-to-binary distance is
row 5's and is untouched by that proof.

| # | Helper | What the model states, and what the tree proves about it | Basis | Evidence in this tree |
|---|--------|--------------------------------------------------------|-------|------------------------|
| a | `s2_init` | The `S2` record's fifteen field stores at the five arguments the emitted call passes; **proved**: the call answers there (`s2Init_answers`), every answer is that store list (`s2Init_sound`), and the frame over the record's extent (`s2Init_framed`) — `s2InitContract` | proved (body) | `JsonStage2Body.stage2Init`, `s2InitStores`; the stores' offsets are `S2`'s (`stage2.c:981-988`); the emitted body: `stage2.helper.s2_init.ll`, `JsonStage2HelperIR.s2InitBody_run`, `s2InitBody_contract` |
| b | `s2_value_pos` | The value-position test's bit at the four arguments the call passes, with the caller's memory returned unchanged; **proved**: the call answers there (`stage2ValuePos_answers`, `stage2ValuePos_zero`) and the answer satisfies the post at the empty footprint (`s2ValuePosContract`) | proved (body) | `JsonStage2Body.stage2ValuePos`, `stage2ValuePosCall`; `stage2.c:990-997`; the emitted body: `stage2.helper.s2_value_pos.ll` pinned to `JsonStage2HelperIR.s2ValuePosBody`, run at the contract's staging and proved of it — `JsonStage2HelperIRBodies.s2ValuePosBody_contract`, read through the instance as `s2ValuePosBody_satisfies`, over the three arms `s2ValuePos_run_zero`, `s2ValuePos_run_object`, `s2ValuePos_run_array` |
| c | `s2_after_value` | The root flag at depth zero or one container-stack byte at the running depth; **proved**: the call answers there (`stage2AfterValue_answers`) and the write is inside the one-byte or four-byte region (`s2AfterValueContract`) | proved (body) | `JsonStage2Body.stage2AfterValue`; `stage2.c:998-1003`; the emitted body: `stage2.helper.s2_after_value.ll` pinned to `JsonStage2HelperIR.s2AfterValueBody`, run at the contract's staging and proved of it — `JsonStage2HelperIRBodies.s2AfterValueBody_contract`, read through the instance as `s2AfterValueBody_satisfies`, over the two arms `s2AfterValue_run_zero`, `s2AfterValue_run_above`; the byte the store writes is the model's own (`s2_convBytes`), not merely one of the same width |
| d | `s2_string_body` | The three forms (body-itself, escaped, refused), the cursor word, the decoded-length word, the decoded prefix at `dst`, and the body's own eight-byte slot at the call's `next`; **proved**: every branch answers (`stage2StringBody_answers`), the decoded form is never longer than its body (`escapeDecodeGo_length_le`), the decoded length is inside the body's extent (`s2StringBody_outn_le`), and the frame over the cursor, length, body, slot and error regions (`s2StringBodyContract`) | assumed (model); body pinned and its expander clause stated, proof open | `JsonStage2Body.stage2StringBody`; `stage2.c:1017-1047`; the emitted body: `stage2.helper.s2_string_body.ll`, which the fragment parses — `ptrtoint` is modelled and its AST is pinned block by block at `JsonStage2StringBody.s2StringBodyBody` (ten blocks, `#guard`ed against the fixture, with a source mutation and an AST mutation each failing the guard) — the refusal message is `null` here by one strip rewrite (the call boundary has no global table; `Operand.global`'s body-level evidence is `tests/core-extension.lean`'s acceptance pins), and the expander's clause at this call's eight arguments is stated beside the pin with both arms proved (`escapeExpand8_decoded`, `escapeExpand8_refused`).  What remains is the body proof: the ten blocks' run, the scan's `BoundLoop` instance, and the closing memory term at the shape the post now names |
| e | `od_scalar_value` | The appended number record (`T_NUM` and the value's eight bytes), the literal tag after the literal check, the refusal's `od_fail` record, and the event cursor's write-back at `o + 8`; **proved**: where the calls answer and what they write (`emitBlobs_spec`, `emitBlobs_frame`, `arenaAppend_spec`, `arenaAppend_frame`), that a record inside the reserve is written (`emitBlobs_complete`), and the frame over the cursor, record and error regions (`s2ScalarValueContract`) | assumed (model); body pinned, proof obstructed | `JsonStage2Body.stage2ScalarValue`; `stage2.c:929-957`; the emitted body: `stage2.helper.od_scalar_value.ll`, pinned by shape at `JsonStage2HelperIR`, obstructed by its `num_fast_el1` callee and the `outTag`/`emitBlobs` match; its four refusal arms are `stage2ErrSetMsg`'s three-field record, which `stage2ErrSetMsg_frame` covers over the record's staged extent |
| f | `num_fast_el1` | **Both exits**: the accepted lexeme's eight bytes at `out`, and the first rejected position at `err`; **proved**: the scan's refusal of `1e`, `01`, `-` and its acceptance of the controls (the `#guard`s above), the offset's bound `off ≤ n` (`numLexScan_fst_le`), the accepted value's `strtodSpec` agreement (`numFastEmitted_strtodSpec`), and both exits' frame over the value and offset slots (`s2NumFastContract`) | assumed (model); body pinned, proof open | `JsonStage2Body.numLexScan`, `stage2NumFast`; `stage2.c:379-455`; the emitted body: `stage2.helper.num_fast_el1.ll`, which the fragment now parses after two strip rewrites — its one `llvm.umin.i64` folds to the `icmp ult`/`select` pair that is the same function at `i64`, and `ashr exact` loses a flag the model has no term for, so the pinned body is the flag-erased form and the flag's obligation is a staging fact the text does not carry (`JsonStage2HelperIR.numFast_ashr_admits_shifted_out_bit` is the witness that the model is weaker there) — and with `%struct.Stk`'s 1 568-byte extent supplied as the pin's declared `Layout`, the number the body's own `llvm.lifetime.start` names.  `JsonStage2HelperIR` pins the parsed shape (255 blocks, 1 157 instructions, four parameters) with the same bytes under no declared layout refused as the control, and `tests/core-extension.lean` pins the decimal literals; the capture refuses if the emission stops carrying the constructs it measures or if the struct's lifetime marker stops naming 1 568 bytes — and it records the shape, the two rewrites and the flag in `stage2.helpers.tsv` |

Two things about the table are deliberate.  First, **each row's frame is proved
at the helper's whole footprint.**  `JsonStage2Body`'s per-emitter frame lemmas
(`emitBlobs_frame`, `arenaAppend_frame`) are over one region each; the caller's
statement is `HelperContract.framed`, which composes the model's per-arm writes
into the region list below, so a call block applies it by membership
(`HelperContract.keeps`) or as its own view (`HelperContract.view`).  The regions
are, in the same order as the table:
`(s, 120)` for the `S2` record;
nothing for `s2_value_pos`; the root flag's four bytes or one stack byte for
`s2_after_value`; the cursor word, the length word, the decoded-body slot at `dst`
and the error record at `c + 1112`'s pointer for `s2_string_body`; the stream's
cursor word, the appended record's thirteen-byte slot and the error record for
`od_scalar_value`; the value and offset slots for `num_fast_el1`.  Four of the six
write the body-allocated objects `%ei.i`, `%root_done.i`, `%xj.i` and `%outn.i`
(`JsonStage2IR.allocaTypes` pins their widths: 8, 4, 8, 8), which are *not* among
the eight staging objects `stage2StagingArgs` passes and are consequently in no
staged region list — so a walk invariant whose region claim covers the seven
staged objects alone has no clause covering them, and a write to one of the four
breaks `Owns` unless the claim names it: `s2_after_value`, `s2_string_body` and
`num_fast_el1` each write at least one.  The footprints name those four at the
pointers their calls pass; the region claim a walk invariant makes over them is
the invariant's own, and it is the one part of a class F link the contracts do not
close.

Second, **the number path's two agreements are separate and both stay visible**.
The conversion's agreement is `strtodSpec`'s, proved for every well-formed
lexeme: `numFastEmitted_strtodSpec`.  The *lexical* agreement is not: which
lexemes reach a conversion is the emitted function's own scan, modelled as
`numLexScan` and checked by `#guard`s at the three malformed tokens the
assessment names and at accepted controls —

```
#guard numLexScan [0x31, 0x65] = (2, false)              -- "1e"
#guard numLexScan [0x30, 0x31] = (1, false)              -- "01"
#guard numLexScan [0x2D] = (1, false)                    -- "-"
#guard numLexScan [0x31, 0x65, 0x2B, 0x35] = (4, true)   -- "1e+5", control
#guard numLexScan [0x2D, 0x30, 0x2E, 0x35] = (4, true)   -- "-0.5", control
```

The scan's acceptance is the *emitted function's*, not a proof that a token the
stage-1 scanner classifies as a number is RFC 8259 §6's: that step is the
scanner's token-extent obligation, and it is stated here rather than assumed.  A
model that converted every readable lexeme would answer a value where the emitted
function answers a refusal, which is why the refusal is modelled and not skipped.

**What is stated, and what is not.**  The six *caller-side* records are in the
tree and each is proved of its model; three are now also proved of their emitted
bodies (rows a, b and c).
`LeanLLVM/Refinement/JsonStage2HelperIR` pins three bodies to their parsed ASTs
and the other three by shape, and pins each captured fixture's parse; the body
proofs of rows a, b and c are in `JsonStage2HelperIRBodies`, and the module names
per helper what stays open (below).  The rest of this paragraph is the
caller-side record.
`LeanLLVM/Refinement/JsonStage2Helpers` states `HelperContract` — the staging, the
post, the footprint, and the three facts a call block applies (it resolves at the
staging, every answer satisfies the post, and every answer's memory is the
caller's outside the footprint) — together with the six staging predicates, the
six posts, the six footprints at the region lists above, the frame steps a proof
composes with (`UnchangedOutside.write_le`, `stage2WriteStores_frame`,
`stage2ErrSet_frame`, `UnchangedOutside.of_subset`), and now the six instances:
`s2InitContract`, `s2ValuePosContract`, `s2AfterValueContract`,
`s2StringBodyContract`, `s2ScalarValueContract` and `s2NumFastContract`.  So
`HelperContract.resolves` applies at a call block for every helper the emitted walk
calls out of line, which is what `JsonStage2WalkScope`'s class F — the nineteen
links whose callee is one of these six — needs at the contract level.

Two stagings are more than readability: the one for `od_scalar_value` must include
the event stream's room for the widest record (its remaining `none` arms are the
reserve's fault, the source's `__builtin_trap`), which is
`emitBlobs_complete`'s hypothesis; and the one for `s2_string_body` must include
the escape list's spacing, because the decoded-length bound is
`escapeDecodeGo_length_le`'s and that lemma is about a spaced list.  A caller that
cannot supply the spacing has no bound on the escaped form; with it, the bound the
walk's cursor advance reads is `s2StringBody_outn_le`.

**Axiom footprints.**  Five contracts print `[propext, Quot.sound]`, the footprint
`JsonStage2Helpers`'s frame lemmas carry.  `s2NumFastContract` prints
`Classical.choice` besides, inherited from `JsonStage2Body.numLexScan_fst_le`, the
lexeme bound its post's refusing arm carries; the choice is the model module's,
not the contract's.  The body-level statements print `[propext, Classical.choice,
Quot.sound]` (`JsonStage2HelperIR`'s `#guard_msgs` pins): the choice there is the
`gep` step's, `BitVec.signExtend`'s core lemma, not a choice the proof makes — the
same instrument, reading a different module.  That the instrument discriminates
is checked by a control: a declaration proved with `sorry` prints `sorryAx` under
the same `#print axioms`.

**What remains open, per row.**  Rows a, b and c have basis *proved (body)*: the
emitted block runs at the staging and satisfies the post and frame, so for those
three the transcription-to-body distance is closed.  Row b's proof reads the
`phi` thread — each arm's incoming operand is the edge's, through
`Term.br`/`Term.condbr` into the `phi`'s own run — and the `and i8, -3 = 0`
equivalence, enumerated over the 256 eight-bit words (`s2_and253_eq_zero_iff`);
row c's reads the 32-bit `sp + (-1)` index (`s2TopIdx`) and the byte-value
plumbing (`s2_convBytes`).  Neither proof restates the contract: the statements
are `JsonStage2Helpers`' own `pre`, `post` and `foot`, read at the instances the
call sites use.  Row d is a program of
this fragment — the address conversions and the symbol operand are modelled — and
its body is pinned; what remains there is the body proof, and nothing in the
fragment or the model now blocks it.  The two things that did are closed: the
refusal record's message word (`stage2ErrSetMsg`, below) and the body's own
`alloca i64`, which writes eight bytes at the call's `next` and advances the
cursor by them, so the model returns the slot, the post names it
(`r.mem = writeBytes m next slot`, `r.next = next + 8`) and the footprint carries
`(next, 8)`.  The body's 64-bit arithmetic is what the `pre` gained with it: both
addresses below `2 ^ 64`, `base ≤ p` so the subtraction is the model's `Nat` one,
`p - base + len` not wrapping, and the cursor and the list count below `2 ^ 63`
so the scan's `getelementptr i32` takes its forward branch.  The same slot
question is row f's at a larger scale: `num_fast_el1` allocates 936 bytes
(`[768 x i8]` and `%struct.Stk`), which `stage2AllocaWrites`' five entries do not
cover.
Row f's body is pinned now too: the capture folds its one `llvm.umin.i64` to the
`icmp`/`select` pair and drops `ashr exact`'s flag, and the pin declares
`%struct.Stk`'s 1 568-byte extent, so the three surfaces the row used to be
refused at are closed on the text's own numbers; its proof is open.
The literal spelling rows used to be refused at, `-0.000000e+00`, is read now:
LLVM prints binary64 with the exponent's sign written and a sign in front of the
mantissa, and the double reader takes both, as `tests/core-extension.lean` pins.
Both contracts are stated at the call boundary — d's and f's alike — because
their proofs are open rather than because a denotation is missing.  Row e is
expressible and pinned but obstructed by `num_fast_el1` and the
`outTag`/`emitBlobs` match.  Every
row's body-to-binary distance is the pipeline's body-faithfulness seam (§7.1 items
1–3 and row 5), the seam `numFastEmitted_strtodSpec` and the `#guard` pins already
rest on; the body proof moves one row's *transcription* off that basis and leaves
the binary side where it was.

The gap the body text carried is closed on both sides.  The refusal paths of
`s2_string_body` and `od_scalar_value` store the error record's message pointer at
`e + 16` — the source's `err_set` writes `ok`, `off` and `msg`
(`kernel/json/stage2.c:69-73`) — and the model wrote only the first two, twelve
bytes, so the body's memory was not the model's and the sixteen-byte regions the
footprints named did not cover the third store.  `stage2ErrSetMsg` is now the
three-field record: the two helpers' refusal arms leave it, the footprints name
the record's staged extent (`stage2ErrorExtent`, 24 bytes — the region the walk's
staged-writes list always claimed), and `stage2ErrSetMsg_frame` is the frame.
`stage2ErrSet` stays as the two-store prefix, so the walk's links that observe
only those two writes keep their proofs; the one link that reads the whole record
(`WalkLink.if_then425_i_refuse`) now reads the three-field shape, and
`stage2ErrSetMsg`'s message word is the zero word the `null`-rewritten text
stores.

## 8. Out of scope for the first contract

`NaN`/`Infinity` as inputs the first contract's route reasons about, the
decimal-to-binary64 conversion as a proved equivalence (the model's `double`
forms, NaN and infinity included, are modelled and `strtodSpec` computes the
value; that an emitted conversion computes it is owed), NDJSON, incremental
input, concurrent parsing, diagnostic text or positions,
and any vector operation the semantics does not model. The modelled vector
forms — `Ty.vec` with integer lanes, `Const.splat`, a vector `load`, lane-wise
`icmp` and integer binops, and `bitcastMask` — are listed in
`docs/capabilities.md`, "Language and IR coverage", with the construct in
`probes/install/ir/json-classify.candidate.ll` that each one serves; the core
extension's forms — the global-symbol operand, `ptrtoint`/`inttoptr`, binary64
and aggregates — are listed there too, with the stage-2 helper body each serves.
Each further extension is a later, explicitly stated change.
