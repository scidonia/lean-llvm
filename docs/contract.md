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
| Token payload | `TokenBytes`, `tape_tokenBytes`: every token of an accepted tape carries its class's document facts — a literal's span and bytes, a number's span and maximal lexeme, a key or string's quote and body — and `walkTraceRow_of_position` assembles the stage-2 trace row from per-index records | `LeanLLVM/JSON/TapeCorrect.lean` (`TokenBytes`, `tape_tokenBytes`), `LeanLLVM/Refinement/JsonStage2TraceRow.lean` |
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
   callee's silence over the caller's two count slots is *derived* rather than
   assumed: the pipeline runs its stage-2 slot under the fixed record
   `JsonStage2WalkFlushPost.Γ_stage2fixed`, whose post names the callee's whole
   touched extent — the five ABI writes, the seven appended objects, `%d.i` and
   the stack interval — and the caller's staging separates `%nk` and `%nxp` from
   every one of them (`PipelineDischarge.stage2StagedRegions_sep`), so
   `PipelineDischarge.stage2SlotKeeps_of_frame` turns that frame into the two
   slot reads `PipelineDischarge.pipelineTailTarget` needs.

   What the specification's frame cannot be is a universal:
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
`JsonStage2HelperIR`, `JsonStage2StringBody`, `JsonStage2HelperIRNumFast` and
`JsonStage2HelperIROdScalar` pin the bodies the fragment expresses — each proved
to parse back to the AST its module states — and contracts are proved of four of
the six bodies.  What follows is the correspondence for each of the six, in the
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
| d | `s2_string_body` | The three forms (body-itself, escaped, refused), the cursor word, the decoded-length word, the decoded prefix at `dst`, and the body's own eight-byte slot at the call's `next`; **proved**: every branch answers (`stage2StringBody_answers`), the decoded form is never longer than its body (`escapeDecodeGo_length_le`), the decoded length is inside the body's extent (`s2StringBody_outn_le`), and the frame over the cursor, length, body, slot and error regions (`s2StringBodyContract`) | proved (body), under the expander clause | `JsonStage2Body.stage2StringBody`; `stage2.c:1017-1047`; the emitted body: `stage2.helper.s2_string_body.ll`, which the fragment parses — `ptrtoint` is modelled and its AST is pinned block by block at `JsonStage2StringBody.s2StringBodyBody` (ten blocks, `#guard`ed against the fixture, with a source mutation and an AST mutation each failing the guard) — the refusal message is `null` here by one strip rewrite (the call boundary has no global table; `Operand.global`'s body-level evidence is `tests/core-extension.lean`'s acceptance pins), and the expander's clause at this call's eight arguments is stated beside the pin with both arms proved (`escapeExpand8_decoded`, `escapeExpand8_refused`).  The ten blocks are run — `s2StringBody_entry_denote`, `_landRhs_denote`, `_whileBody_denote`, `_landLhsTrue_denote`, `_ifThen_denote`, `_ifEnd_denote`, `_ifThen11_denote`, `_ifEnd14_denote`, `_cleanup_denote`, `_cleanup16_denote`, each pinned to its block by `decide` and each stated at the state its predecessor left — and the scan's `BoundLoop` is `s2StringBodyScanBoundLoop` (head `land.rhs`, both exits, `cost` a parameter, `N = c + r` the budget, `s2StringBodyScanAtBound` the two ways out), with `s2StringBodyScan_run_at` reading its fuel as `(N + 1) * cost`.  Each block is also a control step (`step_at_block` and eleven `step_…` theorems, their branch bits named by the environment's own cells), the write order they need is proved (`writeBytes_writeBytes_same`: writing a region twice is the second write, with `writeBytes_cons_outside` and `writeByte_swap_of_readByte` beneath it), and **the scan is a `BoundLoop` value**: `s2StringBodyScanInv` carries the head's edge, its four registers and the lane as the model's `ps` entry (`readLanes32_lane`, with `s2StringBodyScan_bits_of_not_atBound` turning the head's test into both branch bits); `s2StringBodyScan_step_loop` is one iteration's two control steps with every clause re-established — the cursor's write is `s2StringBodyScan_advance`, the lane's transfer the region's disjointness — and `s2StringBodyScan_step_exit` is the exit in its two shapes (one step at the head, two through `while.body` when the counter has reached the count), so `s2StringBodyScanLoop` is the instance at `cost = 2`, `land.lhs.true ∨ if.then` its exits, and `s2StringBodyScan_run` its fuel `(N + 1) * 2`.  The entry's step is the run's prefix (`s2StringBodyEntry_prefix_landRhs`/`_ifThen`), and the invariant is *seated* there from the staging (`s2StringBodyScanInv_seat`): its memory clause is `stage2ReadWord_writeBytes_self` — a region the memory holds is written back in place, proved with `writeByte_readByte_self`/`writeBytes_of_readBytes_self` — composed with the pre's existing cursor-word read, so **`s2StringBodyPre` gains no presence conjunct**: a read already says the bytes are present, and the spacing remains the only memory clause it states.  **proved of the pinned body**: `s2StringBodyBody_contract` runs the ten-block body from `s2StringBodyPre` at `s2StringBodyBudget` and returns the outcome the body reaches, `s2StringBodyPost` at it, and the frame over `s2StringBodyFoot` — the instance's own post and foot, not a restatement — under `s2StringBodyCalls`, whose expander answers are `escapeExpand8`'s eight-argument clause.  That clause is this call's reading of the expander's rule, and it is not related here to the expander's body: `escape_expand_satisfies_unconditional` states the body (`usDecFunction`) against `Γ_escape_expand` under `escapeCalls`, whose calls carry the table the eight-argument call does not, and no theorem in this module identifies the two call models.  The clause, not the body, is what the run consumes, so the proof is conditional on it; that conditionality is a recorded boundary, not a queued proof — the call passes eight arguments where the record takes nine (`tab` and `readBytes mem tab 256 = some unescapeTable`), `Calls` carries no module-level global, and `escapeExpand8`'s docstring states what closing the gap would take |
| e | `od_scalar_value` | The appended number record (`T_NUM` and the value's eight bytes), the literal tag after the literal check, the refusal's `od_fail` record, and the event cursor's write-back at `o + 8`; **proved**: where the calls answer and what they write (`emitBlobs_spec`, `emitBlobs_frame`, `arenaAppend_spec`, `arenaAppend_frame`), that a record inside the reserve is written (`emitBlobs_complete`), and the frame over the cursor, record and error regions (`s2ScalarValueContract`) | assumed (model); body pinned whole (whole-parse literal + `#guard`, mutated-pivot control), no body-level proof — obstructed | `JsonStage2Body.stage2ScalarValue`; `stage2.c:929-957`; the emitted body: `stage2.helper.od_scalar_value.ll`, pinned whole at `JsonStage2HelperIROdScalar.odScalarValueBody` (the whole-parse literal against `#guard decide (firstFunction odScalarValueSrc = some odScalarValueBody)`, with a mutated-pivot control that parses and is not the body), with no body-level contract proof: obstructed by its `num_fast_el1` callee and the `outTag`/`emitBlobs` match; the pin is a statement about the text, not a theorem about the run; its four refusal arms are `stage2ErrSetMsg`'s three-field record, which `stage2ErrSetMsg_frame` covers over the record's staged extent |
| f | `num_fast_el1` | **Both exits**: the accepted lexeme's eight bytes at `out`, and the first rejected position at `err`; **proved**: the scan's refusal of `1e`, `01`, `-` and its acceptance of the controls (the `#guard`s above), the offset's bound `off ≤ n` (`numLexScan_fst_le`), the accepted value's `strtodSpec` agreement (`numFastEmitted_strtodSpec`), and both exits' frame over the value and offset slots (`s2NumFastContract`) | assumed (model); body pinned block by block (255 `findBlock` equations), refusal arm proved of the body, conversion arm open — its three callees are unanswered at the walk's environment, so the conversion is `ub` there (`JsonStage2NumFastArm.numFast_runFuel_ifEnd268_ub`, `_whileBodyPreheader_ub`, `_ifThen178_ub`, and the arm's statement `NumFastBodyArm`), while the supplied environment in the evidence column answers them and stages the tables, and the arm stays open for the runs rather than the environment | `JsonStage2Body.numLexScan`, `stage2NumFast`; `stage2.c:379-455`; the emitted body: `stage2.helper.num_fast_el1.ll`, which the fragment now parses after two strip rewrites — its one `llvm.umin.i64` folds to the `icmp ult`/`select` pair that is the same function at `i64`, and `ashr exact` loses a flag the model has no term for, so the pinned body is the flag-erased form and the flag's obligation is a staging fact the text does not carry (`JsonStage2HelperIR.numFast_ashr_admits_shifted_out_bit` is the witness that the model is weaker there) — and with `%struct.Stk`'s 1 568-byte extent supplied as the pin's declared `Layout`, the number the body's own `llvm.lifetime.start` names.  `JsonStage2HelperIR` pins the parsed shape (255 blocks, 1 157 instructions, four parameters) with the same bytes under no declared layout refused as the control, and `tests/core-extension.lean` pins the decimal literals; the capture refuses if the emission stops carrying the constructs it measures or if the struct's lifetime marker stops naming 1 568 bytes — and it records the shape, the two rewrites and the flag in `stage2.helpers.tsv`.  Every block is pinned in `JsonStage2HelperIRNumFast` (255 `findBlock` equations generated from the parse by `capture-stage2-helpers.sh --emit-pins`, with the absent-name, distinct-block and mutated-text controls); the digit scan is a `BoundLoop` with two exits (`JsonStage2NumFastScan.numFastScanBoundLoop`, head `land.lhs.true41`, exits `if.end68`/`if.end230`, fuel `(n + 1) * 4`); and the empty lexeme's refusal is proved of the body against this contract's own `post` and `foot` (`JsonStage2NumFastBody.numFastBody_contract_empty`, four control steps, the offset zero and `out` untouched); the conversion's three out-of-line callees are answered by a supplied environment and the two tables are staged (`JsonStage2NumFastCalls.stage2NumFastCalls`, `numFastTables_holds`), and the merge block's two counters are read at the model (`JsonStage2NumFastCounters.numFast_ifEnd230_counts`), while the three digit runs' arms remain open |

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
tree and each is proved of its model; four are now also proved of their emitted
bodies (rows a, b, c and d), and row f's refusal arm is proved of its body at the
empty lexeme.
No body is pinned by shape any more, and every fixture is parsed back to the AST
its module states: `JsonStage2HelperIR` pins `s2_init`, `s2_value_pos` and
`s2_after_value`; `JsonStage2StringBody` pins `s2_string_body` and proves its
contract of that body; `JsonStage2HelperIRNumFast` pins `num_fast_el1` block by
block (255 `findBlock` equations, generated from the parse); and
`JsonStage2HelperIROdScalar` pins `od_scalar_value` whole.  The body proofs are
in `JsonStage2HelperIR` (row a, `s2InitBody_contract`),
`JsonStage2HelperIRBodies` (rows b and c, `s2ValuePosBody_contract` and
`s2AfterValueBody_contract`), `JsonStage2StringBody` (row d,
`s2StringBodyBody_contract`) and `JsonStage2NumFastBody` (row f's refusal arm,
`numFastBody_contract_empty`), and each module names per helper what stays open
(below).  The rest of this paragraph is the caller-side record.
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

**What remains open, per row.**  Rows a, b, c and d have basis *proved (body)*:
the emitted body runs at the staging (row d at the contract's budget) and
satisfies the post and frame, so for those four the transcription-to-body
distance is closed.  Row b's proof reads the
`phi` thread — each arm's incoming operand is the edge's, through
`Term.br`/`Term.condbr` into the `phi`'s own run — and the `and i8, -3 = 0`
equivalence, enumerated over the 256 eight-bit words (`s2_and253_eq_zero_iff`);
row c's reads the 32-bit `sp + (-1)` index (`s2TopIdx`) and the byte-value
plumbing (`s2_convBytes`).  Neither proof restates the contract: the statements
are `JsonStage2Helpers`' own `pre`, `post` and `foot`, read at the instances the
call sites use.  Row d is a program of
this fragment — the address conversions and the symbol operand are modelled — and
its body is pinned whole and its contract proved of it: `s2StringBodyBody_contract`
composes the scan's `BoundLoop`, the four arms' terminal runs and the memory term
into the instance's post and frame, under the expander clause the row names.  The
two things that used to block it are closed: the
refusal record's message word (`stage2ErrSetMsg`, below) and the body's own
`alloca i64`, which writes eight bytes at the call's `next` and advances the
cursor by them, so the model returns the slot, the post names it
(`r.mem = writeBytes m next slot`, `r.next = next + 8`) and the footprint carries
`(next, 8)`.  The body's 64-bit arithmetic is what the `pre` gained with it: both
addresses below `2 ^ 64`, `base ≤ p` so the subtraction is the model's `Nat` one,
`p - base + len` not wrapping, and the cursor and the list count below `2 ^ 63`
so the scan's `getelementptr i32` takes its forward branch.  The same slot
question is row f's at a larger scale: `num_fast_el1`'s `entry` takes 2 352 bytes
from the allocator (768 for `[768 x i8]`, 1 568 for `%struct.Stk`, then `i32`,
`i32` and `double` — `JsonStage2NumFastBody.numFastEntryEnv` names the five cells
and `numFast_entry_denote` advances the allocator by their sum), which
`stage2AllocaWrites`' five entries do not cover.
Row f's body is pinned now, block by block: the capture folds its one
`llvm.umin.i64` to the `icmp`/`select` pair and drops `ashr exact`'s flag, the pin
declares `%struct.Stk`'s 1 568-byte extent, so the three surfaces the row used to
be refused at are closed on the text's own numbers, and
`JsonStage2HelperIRNumFast` states a `findBlock` equation for each of the 255
blocks.  What is proved of the body is the **refusal** arm — the digit scan as a
`BoundLoop` whose two exits share one induction, and the empty lexeme's four-block
run satisfying the contract's post and footprint — and the **conversion** arm is
open, at a boundary `JsonStage2NumFastArm` states as facts rather than as a
paragraph.

The boundary is the walk's `Calls` selection.  `s2HelperCalls` is
`stage2Calls noCalls` — two lifetime markers, `memset`, the trap, and nothing
else — and the conversion's three out-of-line callees are not entries of it: the
eight-digit reader `num_d8_el1` (called from the inlined scan's SIMD run at
`while.body.preheader` and `while.body`), the 128-bit kernel `num_el_el1` (at
`if.end268`) and the fallback's big multiply `stk_mul_u64` (at `if.then178.i.i`).
At each of those blocks the block's `denoteCode` is `none`, so the body's `step`
is `ub` and the run is `some .ub` — the body does not fall through to a slower
path when a callee is absent, because the call is not guarded by an answer
(`JsonStage2NumFastArm.numFast_ifEnd268_denote_none`,
`numFast_whileBodyPreheader_denote_none`, `numFast_ifThen178_denote_none`, and
their `step`/`runFuel` forms).  A body-level proof of the arm cannot therefore be
carried by the body's run at the walk's environment: the conversion's arithmetic
is unreachable there, and `NumFastBodyArm`'s `Calls` parameter is what a proof
must supply first.  None of
the three callees is captured as a fixture — no `define` for them exists under
`probes/` or `kernel/` — so their answers' shape (the digit pair, the kernel's
decision and code, the multiply's product) is a decision to make, not a fact to
read.

Two further inputs are outside the contract's staging, and `NumFastBodyArm`
carries them as hypotheses rather than silently taking them.  The first is the
inlined scan's counters: `JsonStage2NumFastScan` fixes the digit run's
`BoundLoop` shape and states its two arms as per-iteration facts, the arms are
not discharged, and the fraction and exponent runs have no instance at all, so
the model's `digitCount`/`numEff` are not yet the body's counters.  The second is
the two tables: the tier-1 expression reads `@NUMF_EL1_P10[fdig]` and
`@NUMF_EL1_POW10[eff]`, both `Operand.global` and both loaded from memory, and
`s2NumFastPre` fixes four arguments and a lexeme and stages no global —
`NumFastTables` is the staging a proof must add (twenty integer powers and
twenty-three binary64 ones, each stated as the encoding `uitofpBits` gives a
value below `2 ^ 53`).  The decimal-to-binary64 equivalence §8 places outside the
first contract is what remains above those three inputs, so row f's basis stays
off *proved (body)*.
The literal spelling rows used to be refused at, `-0.000000e+00`, is read now:
LLVM prints binary64 with the exponent's sign written and a sign in front of the
mantissa, and the double reader takes both, as `tests/core-extension.lean` pins.
Rows e's and f's contracts are stated at the call boundary because their body
proofs are open, not because a denotation is missing: f's conversion arm is the
binary64 equivalence §8 places outside the first contract, and e is expressible
and pinned whole but obstructed by `num_fast_el1` and the `outTag`/`emitBlobs`
match.  Every
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

### 7.7 The stage-2 report at its boundary

`stage2Boundary` (`LeanLLVM/Refinement/JsonStage2Contract.lean`) is the stage-2
unit's post, and these are the four decisions it states at the definition, where
a consumer meets them.

**The four decisions a consumer of this record inherits.**  Each was implicit
once.  They are stated here, with the witnesses named, so that a consumer reads
the boundary and the walk's vocabulary together.

1. **The used cursor and the reserved extent are two numbers.**  The arena slot
reports `ndstU`, the decoded extent — the word the log's cursor cell held at the
loop head — and that is what the report carries.  The extent the run *reserved*
is `ndst'`, the walk's arena cursor.  They differ because the reserve charges a
window before the body is decoded: a decoded body is never longer than its
bytes, and an escaping string's is strictly shorter, so an escaping input leaves
the slot short of its reserve (`ndst0 ≤ ndstU ≤ ndst' ≤ ndst0 + n`).  Presence,
the arena read `readBytes m dst ndst'`, the frame's arena entry and the capacity
bound `ndst' + stage2ArenaReserve ≤ dstcap` are therefore stated at `ndst'` and
not at the slot: a clause at the slot would leave the decoder's slack outside
every extent the record names.  `SigmaFrame`'s arena entry is the reserved one
for the same reason — `(dst, ndst' + 64)`, with `ndstU ≤ ndst'` carried beside
it (`JsonPipelineSpec`).
2. **The report reads the slot, not the carry.**  The two cursor clauses are
`readBytes m ndst 8 = some (wordBytes 8 ndstU)` and
`readBytes m nev 8 = some (wordBytes 8 nev')`: the words the run stored back.
The carry is the walk's internal state, and this boundary has only the words.  A
caller needs the *used* extent in the arena slot because it is the only number
that says where the decoded bytes end; the reserve the run was charged at is the
run's own number, not the caller's.  Both extents lie below the word's width —
`ndstU ≤ ndst' < 2 ^ 64` and `nev' ≤ evcap < 2 ^ 64` — which is what lets a
consumer name them at all (`pipelineOutputExtents`).
3. **The invariant admits states the head's clauses do not reach.**  `WalkInv`'s
log clauses read the record's fields at `%z + 8`, `+16`, `+32`, `+48` and `+56`;
the arena's is the existential `log_alen` — some `a` with `G.ndst0 ≤ a` and
`a ≤ C.alen`, read at `%z + 48`, a word between the arena's staged start and the
carried cursor — because the carry reserves a body's window before the block
that writes the word back, so between the two the memory is short of the carry.
The event clause is block-keyed, `C.events.length ≤ C.k + walkEmitC C.block`, so
it is a statement about the state at its block rather than a consequence at the
head.  A seam state — the written token record a tail starts from — is therefore
not covered by the head state's invariant, and the transports that close the gap
are `JsonStage2WalkHcontSeamInv`'s: `contTailStartInv_of_cleanup`,
`scSeamInv_of_scalar` and `hlastTailInv_of_facts`, and — for the default arm's
two letters classes — `JsonStage2WalkDispatchLettersRows`'
`lettersSeamInv_of_chain`/`fLetterSeamInv_of_chain`.
4. **The census is exhaustive, and the arms are total over the bytes and the states.**  `HeadArm.complete` gives
every byte exactly one head arm, so the byte census is exhaustive by theorem,
and every state the invariant admits whose class the arms' premises hold is
dispatched by an arm.  The continuing enumeration is `HcontArm`, twenty constructors: the string opener is
one class with three arms (`.twoEntry`, `.stringOpenAboveZeroMerge`,
`.stringOpenAboveZeroRefuse`), the high bytes `126`/`127` one class with two
(`.ws`, `.cleanup`), and the two openers one class with three (`.containerOpen`,
`.openAtCap` at the answer `1`, `.containerOpenRefuse` at the answer `0`).  The last entry's
enumeration is `LastEntryArm`, seventeen constructors.  Each opener constructor is not a
byte but a *state*: `if.then.i` branches on the value-position call's answer, and the three
arms are the two answers crossed with the depth split the push's guard makes.  Where a class's route is a counted chain of its own, the arm takes
that chain as a row: `.classC` its span past the head chain,
`.stringOpenAboveZeroMerge` its segment to the merge.  The `.letters`/`.fLetter`
classes take no tail row: their head chain is produced from the lane's document
row and their three-link tail is produced from the seam's cells and the callee
rows (`JsonStage2WalkDispatchLettersRows`).  The document and seam rows are
`JsonStage2WalkDispatchClassRows`', one row per class, and the seam state's
invariant is produced by the transports above rather than carried as a row.

**The openers' class is total by state as well as by byte.**  The class is the byte,
but `if.then.i` branches on the value-position call's answer, and the answer is the
state's: the callee's model returns `0` or `1` and nothing else
(`s2ValuePos_ret_zero_or_one`, through `stage2ValuePos_lt_two`), so a head in the class
takes exactly one of three routes — answer `1` at or below depth `519`
(`.containerOpen`, the merge), answer `1` at depth `520` (`.openAtCap`, the push's guard's
false side), answer `0` at any depth (`.containerOpenRefuse`, `if.then16.i`'s offset store
and the copy).  The refusal is the arm the earlier census lacked, and it is reachable: at
depth zero the callee answers `1` only when the root word is `0`
(`s2ValuePos_rootWord_of_answer`), a depth-zero `s2_after_value` writes that flag `1`
(`s2AfterValuePost_rootSlot_at_zero`) — the walk's own call at `if.then109.i` passes
`%sub.i = %sp - 1`, so the close of a top-level container sets it — and
`JsonStage2WalkDispatchOpenersDomain` stages the second-value documents (`[0][`, `[0][0`)
at whose second opener the slot holds `1` and the answer is `0`
(`secondValue_last_refuses`, `secondValue_cont_refuses`).  The document-level step from
the seeded head to that opener is not a theorem of this tree — the close, its
`s2_after_value` and the header's pass are the walk's own execution — so the staged
theorems take the slot's word as their state's premise while *deriving* the answer from
the callee's model.  The control is the same class at the same depth with the slot at `0`:
`firstValue_answer_one` gives the answer `1`, and `[0]`'s head takes `.containerOpen`.
What the value does **not** need is a clause: the slot's writers are `entry`'s initial `0`
and the callee's flag `1`, so `0` is not among them (`s2AfterValuePost_rootSlot_above`
leaves the slot alone above depth zero), and the arms carry the word as the witness
`rdv` — the read is `walkReadBytes_rootSlot_word`'s, from `root_slot`'s four present
bytes.

### 7.8 The dispatch's per-row ledger

Every arm the two enumerations contain is either **derived** — a theorem at the state the
invariant names — or it takes a **row**, and each row is a fact about one of four kinds:
the document, a callee's argument list, the scan's traversal, or the counted segment of a
route the walk's own blocks compose.  This is the ledger, one entry per row, with the
statement's state and memory, the theorem that produces it, the proof that consumes it
and the assumption that remains.  A row is *not* a bundle: no entry below carries an arm,
and no entry carries the execution segment its own producer builds.

| # | Row: statement | Producer | Consumer | Remaining assumption |
|---|---|---|---|---|
| c1 | `.ws` (bytes `126`/`127`, `C.k + 1 < G.nep`): the head state's memory carries the next entry's lane word, the byte before the entry's end with its no-run class, the whitespace stop `k` with its per-index `∀`, the landing's byte and its three reads | `hcontFacts_of_staging` (`JsonStage2WalkHcontFactsOfStaging`), whose traversal fields are `scanRoundField`/`scanByteField`/`scanTokField` (`JsonStage2WalkRevolutionScanRound`) | `HcontArm.ws` → `HcontArm.dispatch` | the visited byte's class as a document row, stated at the scan's own span.  Both former shape defects are repaired: the visited-byte row is `k < p + 1` throughout (`hcontFacts_of_staging`, `scanByteField`, every `hbyte`, `ScanVisits`), and the seam's invariant and cells are the class's state group (`HcontWsSeam`, `hcontWsSeam_of_body`) produced from the run's body (`HcontRunBody`/`contWsRunBody`) and the class-C span, so the tail is `hcontScanTail_of_seam`'s.  What remains is the traversal's class bits — the document's content — and the payload wiring of the class groups.  The round, the byte's address and read, the loaded register, the three local facts and the token register are produced; `hguard` is gone (see below) |
| c2 | `.cleanup` (bytes `126`/`127`, entry left): the head state's memory carries the next entry's lane word and read, the bound's compare, the byte before the entry's end with its scan-free class (the `defaultLane` row's `.scanFree` disjunct) | `hcontCleanupDoc_of_lane` (`JsonStage2WalkDispatchClassRows`) from the lane's `defaultLane` row and its scan-free disjunct | `hcontSpan17_of_doc` → `contTailStartInv_of_doc` → `hcontArm_cleanup_of_rows` | **none** on top of the lane row, its disjunct, the head invariant and the seam's three call rows: the seventeen links, the seam's cells and the root slot's word are produced (`JsonStage2WalkDispatchSeamRows`) |
| c3 | `.twoEntry` (byte `34`, `C.sp = 0`): the standalone string's lane — the next entry's word, the root slot's word, the log's two words, the decoded length — and the body's two call rows | `HcontLane.string`, `HcontAbi.string` (`JsonStage2WalkDispatchSupply`) | `hcontArm_twoEntry_of_staging` → `HcontArm.dispatch` | the lane's five reads and the two callee rows.  **Four of the five reads are proofs, not rows** (`JsonStage2WalkDispatchSupply`): the next entry's position word (`walkReadBytes_entryPos_word`: `G.entries` and the frame's silence over the entry stream, then `readLanes32_nth`), the root slot's word as a word (`walkReadBytes_rootSlot_word`: `root_slot`'s four present bytes through `natToBytes_bytesToNat`, the clause fixing no value), the log's arena word (`walkReadBytes_logArena_word`: `log_alen`'s read at `%z + 48`), and the log's capacity word (`walkReadBytes_logCap_word`: `log_acap`'s `dstcap`).  The fifth, the decoded length at `%outn.i`, is statable but not carried: `%outn.i` is one of the four `alloca` slots `owned` deliberately omits, so a clause naming its eight bytes is an invariant edit; its *value* is the previous body call's, produced at the answered memory by `s2StringBody_outn_le` and transported across the private slot's write in `strPath9`/`strPath10`, but neither `s2StringBodyPre` nor the two answers (`HcontStringCalls.hxv`, `HcontStringCalls.hy`) mentions the slot, so no theorem carries the word to the head where `HcontStringLane.houtn` reads it.  So the lane's row is one slot's presence at the head and one carrier at the call, and the two callee rows are the helper boundary.  The value-position *precondition* is not a row: `s2ValuePosPre`'s depth clause is `Or.inl` at zero and the two stack maps at a positive depth, and the call's staging at the state's own root word is `HcontAbi.openCall`'s row (`HcontOpenCall`), which carries the read and the answer.  `C.sp = 0` is the class's own split |
| c4 | `.stringOpenAboveZeroMerge` (byte `34`, `C.sp ≠ 0`): the class's byte, depth and two stack bytes at `C.sp - 1`, and the value-position call's staging at the state's root word | `cont_reg8` + `WalkInv.tyBytes`/`stBytes`; the staging and the call are `HcontCall`'s (`HcontAbi.openCall`), at the word the slot holds | `hcontArm_stringOpenAboveZeroMerge_of_staging` (`JsonStage2WalkDispatchHcontStringDeep`), from `HcontDeepRow.merge` | **the route's counted segment** to `cleanup478.i`, carried as the class's own row (`HcontDeepRow`, `JsonStage2WalkDispatchClassRows`) and projected into the producer by `hcontArm_stringOpenAboveZero_of_class` (`JsonStage2WalkDispatchClassCase`); no theorem states it, and the arm's producer does not assume it.  Every link of the route is proved (`if_end256_i`, `z_arena_reserve_exit`, `NodeBlock31_at`, `LeafBlock29_at`, `if_then281_i`/`if_else285_i_at`, `if_end290_i`, `if_then328_i`, `walkIfThen330_at`), so the segment is statable, and the rows that stop its composition are named exactly: at a state at `if.end256.i` the three cells `.twoEntry`'s bundle carries — `%conv211.i`'s word (bound by `if.end207.i`, so a head-chain cell, not a seam one), the cursor pin `C.alen ≤ G.ndst0 + entryPos G C.k` (`pending = none` does not carry it) and the window bound `C.alen + ext ≤ G.n` — beside the body's staging at the call's memory.  The staging has a producer (`s2StringBodyPre_of_staging`), and `s2StringBodyBody_contract` fits the call in the only sense that matters here: the walk's call consumes `s2StringBodyContract` (`s2StringBodyPre` plus the model's answers, soundness and frame), and the emitted body's contract proves that model is the ten-block body at the same fuel — so the contract is not the missing clause; what is missing is the transport of the staging's separation facts across the reservation's two stores, and the three cells.  **What the arm's `hseg` adds, and why the row is larger than five blocks**: the segment's source is the loop head, so the composition also carries the head chain to `if.then219.i` and the two marker links, and that chain reads the next entry's lane word (`f.q`, the document's position table) and the root slot's word (`f.rd`) — the document facts of the two-entry bundle.  So the route is document-free *past the nest* and not from the head, and `hseg`-from-the-head is the row; a tail stated at `if.end245.i` would close the nest's four remaining links' worth and leave that chain.  Writing the composition is the row's work |
| c5 | `.stringOpenAboveZeroRefuse` (same class): the nest's own test clear, the offset store and the copy | `stringDeepRefuse_at` (two links from `if.end245.i`'s state) | `hcontArm_stringOpenAboveZeroRefuse_of_staging` | **none**: the refusal is composed |
| c6 | `.scalar` (the tag test's true arm): the numeral's document row — the class bits, the span, the entry's non-emptiness, the byte before the entry's end and its route (`HcontByteRoute`: the scan-free, low or high leaf) — the lane's word and its read, and the three calls at `scSeamByte` | `scSeamInv_of_cells` (`JsonStage2WalkHcontSeamInv`) for the seam's invariant, from that document row and the byte's route; `scSeamSegByte` (`JsonStage2WalkHcontScalar`) for the route's counted chain to the seam; `scTailByte_of_calls` (`JsonStage2WalkDispatchSegments`) for the tail, at the callee rows | `hcontArm_scalar_of_rows` → `walkDispatch_at_scalar_of_rows` (`JsonStage2WalkDispatchScalarRows`) | **none** on top of the document row (`HcontScalarPrefix`), the lane word and its read, and the three call rows at `scSeamByte … pre.hb`: the seam's invariant, the route's chain, the arm and the dispatch are produced, and the route's two agreements — the kind literal `7` and the root slot's word, transported across the token-record stores by `sLand_rootRead`/`scSeamByte_rootRead` — are the callee group's tie to the state |
| c7 | `.letters`/`.fLetter` (`0 … 109`, `128 … 255`, the tag test clear): the head chain to `if.else387.i` with its endpoint's lane word, the seam's two test cells and the root slot's word | `lowHeadChain_of_lane` … (`JsonStage2WalkDispatchDefaultLane`) from `HcontLane.defaultLane` for the chain (`HcontHeadChain` carries `v` with `contSeamMid_ee`/`contSeamMid_cond` and the root transport `contSeamMid_rootRead`); `lettersSeamInv_of_chain`/`fLetterSeamInv_of_chain` for the seam's invariant; `lettersSeamCells_of_chain`/`fLetterSeamCells_of_chain` for the seam's cells; `emptyTail_of_cells` for the tail | `hcontArm_letters_of_rows`/`hcontArm_fLetter_of_rows` → `walkDispatch_at_letters_of_rows`/`_fLetter_of_rows` (`JsonStage2WalkDispatchLettersRows`) | **none** on top of the three call rows at `LetS413`/`FS413` and the chain's own data: the seam's invariant, its cells (`%ee.1.i`, `%cond350.i` at the chain's one `Nat`, the root word across the suffix's three token-record stores) and the three-link tail are produced, and the route's two agreements — the kind literal `0` (`if.else405.i`) or `9` (`if.then397.i`), and the root slot's word read at the head state — are the callee group's tie to the state |
| c8 | `.classC` (`110 … 125`): the same head chain plus the byte's own span | `classCSpan_at` from the class's `slt %8 110` bit for the span — the four leaves' spans are `c56TrueSpan`/`c56ElseSpan`/`c58TrueSpan`/`c58ElseSpan` | `hcontArm_classC_56True_of_rows` … `walkDispatch_at_classC_58Else_of_rows` (`JsonStage2WalkDispatchClassCLeaves`) | **the three call rows**, and nothing else: the endpoint's seam cells are produced at the four named leaf states — `ClsS413T` (`110`), `ClsS413F` (`111 … 115`), `ClsS58T` (`116`), `HeadS413` (`117 … 125`) — by `classCSeamCells_56True` … `…_58Else`, from the leaf's own `phi` incoming (`10`, `0`, `8`, `0`), the endpoint's invariant, the chain's one `Nat` read through the leaf's binds and the root word's transport past the kind record's store (`classCSeam_rootRead`).  Each arm takes the chain, the leaf's bits, its call group at the named seam and the root word's agreement; the tail is `emptyTail_of_cells` at the produced cells, so no row sits at an unnamed endpoint |
| c9 | `.run` (the same six default classes on the run continuation): the check state's cells, the whitespace stop, the landing and the scan's traversal | `hcontRunFacts_of_rows` → `runFacts_of_runBundle` (`JsonStage2WalkDispatchRunHead`), with the c1 round/byte/token fields transported (the same terms, at the check state) | `HcontArm.run` → `dispatch` | the run's document rows, and of the traversal the same narrow row as c1 (`k < p + 1`, carried by `HcontRunRows`/`RunFacts`); its round and byte read are c1's produced terms, and its tail is `hcontScanTailAt_leaf`, whose leaf, invariant and call rows are the byte's own (`HcontRunLeaf`: the six producers `hcontRunLeaf_letters` … `_58Else`, wired to the seam's supply per leaf by `hcontRunLeafAt_letters` … `_58Else` and applied to the row by `hcontRunRowAt_letters` … `_58Else`, `JsonStage2WalkDispatchRunRow`), so no bundle's tail gates it and no leaf is pinned.  Its production at a given leaf remains a supply item: `HcontClassRows.runRow` takes the leaf, because the kind literal the leaf's `phi` selects is part of the memory the first call reads |
| c10 | the four delimiter refusals and the two above-zero delimiter pairs | `bracketRefuse_at`, `commaRefuse_at`, `colonRefuse_at`, `closeBraceZero_at`, `commaBraceMerge_at` … | `hcontArm_of_derivedClass` (`JsonStage2WalkDispatchResidual`) | **none**: the class bits and `WalkInv`'s own cells |
| c11 | `.containerOpen`/`.openAtCap`/`.containerOpenRefuse` (bytes `91`/`123`): the value-position call's row at the root slot's witness word, and the answer that selects the arm | `HcontAbi.openCall` (the witness, its read, the staging and the outcome — no answer); `s2ValuePos_ret_zero_or_one` for the split | `walkDispatch_at_open91_of_payload` … | **the call's row at the witness word**, and nothing else.  The *value* is the arm's witness `rdv`, read by `walkReadBytes_rootSlot_word` from `root_slot`'s four present bytes, and **not derivable**: `entry` writes the initial `0` and `s2_after_value`'s depth-zero arm writes `1` (`s2AfterValuePost_rootSlot_at_zero`), while above depth zero it leaves the slot alone (`s2AfterValuePost_rootSlot_above`), so `0` is not among the callee's writes and the word is a function of the path.  That distinction is recorded rather than repaired: no clause pins the word and none is owed, because the arms carry it.  The *answer* is derived, not assumed: the callee's model returns `0` or `1` (`stage2ValuePos_lt_two`), so the `1` arms (`.containerOpen` at depth `≤ 519`, `.openAtCap` at `520`) and the `0` arm (`.containerOpenRefuse`, `if.then16.i`'s offset store to the copy, six links) are exhaustive over the class's states.  The call's *precondition* at the witness word follows by the same depth case split `stringOpenAboveZero_pre_of_inv` applies (`Or.inl` at depth zero, the two stack maps at a positive depth), though no theorem states the general case yet; the row is the call itself |
| c12 | `.closeWithOpen` (`93`/`125` at `C.sp ≠ 0`): the two stack bytes and the callee's precondition at `%ctype.i + (%sp - 1) - 1` | `s2AfterValuePre_of_inv` (`JsonStage2WalkDispatchResidual`) | `hcontArm_of_derivedClass` | **none** |
| l1 | last entry `.highByte`: the last byte's **route** (whichever non-whitespace leaf the document's byte selects), the byte before the token's end, the three calls, the root-done word | `HlastResidue`'s rows, whose `hb` is the route; `hlastFacts_of_staging` (`JsonStage2WalkDispatchWitnessHlast`) composes `hlastTailSegByte` and `hlastTailByte_of_calls` (the tail at the class's own seam); `hlastTail_rootSlot_word` (`JsonStage2WalkDispatchSupply`) for the slot's read | `LastEntryArm.highByte` → `dispatch` | **none**: `HlastFacts`'s seam word `rdv` with its read is produced.  `hlastTail_rootSlot_word` reads the slot as a word from `WalkInv.root_slot` (`walkReadBytes_rootSlot_word`) and transports it across the tail's four token-record stores — the position, the gap, the seam's end and the kind — each of which the record's extent separates from `G.next0 + 8` (`readBytes_rootSlot_tokWrite`).  `rdv` is the memory's witness, which is what the row's *variable* word means: the slot's writers are `entry`'s `0` and `s2_after_value`'s depth-zero `1`, and no consumer pins which.  The last entry's openers take the same witness row as c11's (`HcontOpenCall`, at the exhausted count), so neither level's lane carries a value clause |
| l2 | last entry `.scalar`: the three call rows at `TailStartC`/`hlastTail` | `scalarTail_of_calls` (`JsonStage2WalkDispatchScalar`) | `LastEntryArm.scalar` | the three call rows at the last entry's seam and the seam state's own cells: `scalarTail_of_calls` composes the tail from the three callees' preconditions and answers at `TailStartC`'s argument lists, so the segment is produced and what remains is the helper boundary — no document row and no arm |
| l3 | last entry `.letters`/`.fLetter`/`.classC`: the seven-link suffix and the class's four-pivot prefix | `contDefLastSeg`, `contLastLowHeadSeg` … (`JsonStage2WalkDispatchLettersHead`) | `LastEntryArm.letters` … | the tail's three call rows at the last entry's seam: the seven-link suffix and each prefix class's chain are theorems (`contDefLastSeg` at seven, `contLastLowHeadSeg` … `contLastBrcHeadSeg` at ten or eleven), so no link of the route is a row and what remains is the helper boundary at the seam |
| l4 | last entry `.run`: the terminal run's document bounds and the credit its index consumed | `RunLastFacts` + `runLastMerge_at`, `runLast_price_with_credit`; `terminalStop_bounds` (`JsonStage2WalkDispatchRunOfStaging`) for the three bounds | `LastEntryArm.run` | **none** for the bounds: `terminalStop_bounds` derives `hstart`/`hNdoc`/`hspanDoc` from the terminal stop's two (`terminalStop_ge`, `terminalStop_le`) and the geometry's width (`WalkGeom.doc`), and `runLastFacts_of_staging` fills them with it; the price and the credit are derived from them (`runLast_price_with_credit`), so no segment and no callee row is taken.  What the bundle still takes is the traversal's own numbers — the counter `i`, the seam's bound `c`, `i < c`, and the two ties that name them (`i = terminalStop G.bs (entryPos G C.k)`, `c = G.n`) — and the tail's call row, not a document bound |
| l5 | last entry refusals, `.stringOpener`, `.openAtCap`, `.containerOpenRefuse` | `quoteRefuse_at`, `bracketRefuse_at`, `closeBraceZero_at`, `containerOpenCap_at`, `containerOpenRefuse_at` | `LastEntryArm.dispatch` | **none**: the class bits, `WalkInv`'s own cells and the call's row at the slot's witness word — the answer `0` is the state's, and the arm composes its six links |

**What c2 establishes, and why it is the shape the others take.**  `JsonStage2WalkDispatchSeamRows`
produces, from the class's document row alone: the seventeen-link chain
(`hcontSpan17_of_doc`), the seam's invariant (`contTailStartInv_of_doc`), the seam's five
environment cells from that invariant's `regs`, the predecessor and its `phi` with the kind
literal `0` it selects (`contTailStart_pre`, `contTailStart_phi`, `contTailStart_op`), and
the root slot's word transported across the seam's three token-record stores
(`contTailStart_mem`, `contTailStart_rootRead` with `walkReadBytes_rootSlot_of_tokStore`).
The arm is then `hcontArm_cleanup_of_rows`, and it takes no segment, no bundle and no
assumption about the chain it establishes.  The two word equalities it requires (`cA = 0`,
`rdv = 0`) are the callee group's agreement with those cells, not a second reading of the
state.

**The guard that was false.**  The composite `walkScanRounds457` (since deleted, see below)
took a hypothesis `hguard` of type
`ScanGuard s "%q.0.i246" "%cond350.i" inner`, and the traversal bundles carried it as a row.
`ScanGuard` quantifies over *every* pair of naturals whose words are the two registers' with
`c - i ≤ inner`; above the word's width the subtraction saturates at zero, so such a pair
exists at every state whose registers hold words and the claim `i + 1 < c` fails there.  The
statement is therefore false, the bundles carrying it were uninhabited, and the rows
dependent on them vacuous.  Its production never existed for the same reason, and
`walkScanRound457`'s proof did not read it: the visit's `i + 1 < c` is a premise of the
round.  `JsonStage2WalkRevolutionScanRound` proves the round without the guard
(`scanRound_at`, `scanRoundField`) and the row now carries the round's own `∀`, stated at the
state's cells below the word's width.  The guard is deleted from `HcontFacts`,
`HcontRunFacts` and `HcontRunRows` rather than weakened in place.

**The two traversal lemmas, restated by dropping the guard.**  The composite lemmas also
took it, and the repair is the same test applied one level up: does the proof read it?
`walkScanRounds457`'s induction forwarded its `hguard` to the recursive hypothesis and read
it nowhere else — the step's `i + 1 < c` comes from `c - 1 - i = r + 1` together with
`i < c` — and `walkScanArrival457` only passed it to `walkScanRound457`, which did not read
it either.  So the parameter is **dropped, not restated**: 
`walkScanRounds457_of_cell` and `walkScanArrival457_of_cell` state both results with no
`ScanGuard` hypothesis at all, are inhabited (their only hypotheses are the round, the
byte's totality, the state's cells and the count bounds), and are proved — the arrival at
the guard-free round.  A restatement of `ScanGuard` at the state's cells would be a strictly
weaker hypothesis than the one the lemmas need, which is none.

The originals are **deleted**, not restated, and the reachability check is the deletion's
warrant.  Gone from `JsonStage2WalkInduce.lean`: `walkScanRounds457`, `walkScanArrival457`
and `walkScanRound457`.  Gone from `JsonStage2WalkScope.lean`: `whitespace_scan`,
`string_scan`, `escape_scan`, `extraToken_scan` and the four `WalkLink.whileBody370`/
`whileBodyI104`/`whileBody76`/`whileBody462` wrappers, each with its `#print axioms` line.
The calls, read by name across every module: the four arms were called only from their own
wrapper, the wrappers from nothing, `walkScanRounds457` only from `walkScanArrival457`,
`walkScanRound457` only from `walkScanArrival457`, and `walkScanArrival457` from nothing.
Nothing that produces a row reached any of them.  The guard-free `walkScanRounds` (the
scan-agnostic traversal in `JsonStage2WalkInduce`) and
`walkScanRounds457_of_cell`/`walkScanArrival457_of_cell` remain, and the round is
`scanRound_at`/`scanRoundField`.  `ScanGuard` itself stays in `JsonStage2WalkScope`, its
docstring stating that it is false at every state whose registers hold words and that
nothing takes it.  The deletion also moved four blocks out of the link census — 157 links
become 153, and class H1's four scan headers are counted as counted rounds instead of as
one-block links — and `JsonStage2WalkScope`'s `#guard` sums, class table and three
narrative sites record that re-expression: the coverage is unchanged, the method differs.

**What this ledger says about closure.**  The continuing classes' rows are now stated, and
each has its branch: `HcontClassRows` (`JsonStage2WalkDispatchClassRows`) carries the
scan-free class's document row, the plain-value class's seam row, the default arm's
scan-free classes' seam rows, the four class-C leaves' seam rows and the positive-depth
opener's route, and `JsonStage2WalkDispatchClassCase`'s branches project each into its
producer (`hcontArm_scalar_of_class`, `hcontArm_letters_of_class`,
`hcontArm_fLetter_of_class`, `hcontArm_classC_56True_of_class` …,
`hcontArm_cleanup_of_class`, `hcontArm_stringOpenAboveZero_of_class`).  Of the seventeen
rows, c2, c4, c5, c6, c7, c8, c10, c12 and c11's call row are consumed by a branch; c3 is
consumed by the payload's own `walkDispatch_of_payload_covered`.  What is left is c1 and
c9's *run* class — closed since: `HcontRunRow` (`JsonStage2WalkDispatchClassRows`) carries
the check state's rows and the seam's state group, and `hcontRunFacts_of_seam`
(`JsonStage2WalkDispatchSeams`) joins them to `RunFacts`, with `hcontArm_run_of_class`
projecting the row into the arm.  The continuing side's remaining items are the `.cleanup`
leaf classes' *tail* — closed since: `hcontTailByte_of_calls`
(`JsonStage2WalkDispatchSegments`) produces it at the byte's route, and `HcontCleanupFacts`
carries that route — and the class bits' transport into `letters`/`fLetter`/`classC`.  On
the last side, `RunLastFacts` is derived from a seam group
(`JsonStage2WalkDispatchRunLastSeam`), and l2/l3's asset is **closed**: `HlastFacts` and
`HlastResidue` carry the last byte's route (`hb : HcontByteRoute (head35 (G.bs.getD (G.n -
1) 0))`) in place of the scan-free bits, `hlastTailByte_of_calls` produces the tail at the
class's own seam, and `hlast_toMerge`/`hlast_finish`/`hlast_refuse` state the path at the
route's count (`12 + hlastByteCount hb + 3 + 1 ≤ 20`, priced at `22 ≤ 32` and `25 ≤ 32` at
`Δk = 1`), so `.highByte` selects whichever leaf the document's byte names.  No row is a
bundle or an arm, and the one row that carries a segment — c4's merge route — is the arm's
own route, named as such and not assumed by a producer beside the row.
The quantifiers are the class's and the state's: a
row is stated at the continued head it belongs to (`C.k + 1 < G.nep` for c1–c12) or at the
exhausted count (`¬ (C.k + 1 < G.nep)` for l1–l5), never at every head.

**The two bundle theorems, and the repairs behind them.**  The statements are
`walkContinueFacts_of_payload (hp : HcontPayload G) (hc : HcontClassRows G)
(hw : HcontWsRows G) : WalkContinueFacts G` (`JsonStage2WalkDispatchContinuing`, the class
case over `HcontClass.complete` beside the payload's `HcontByteClass`, read out of its
`Nonempty` by `Classical.choice` because the arm is data) and
`walkLoopEnd_of_payload (hp : HlastPayload G) (hc : HlastClassRows G)
(ha : HlastArmRows G) : WalkLoopEnd G` (`JsonStage2WalkPremisesOfStaging`, the class case
over the head switch's own bits).  Both are in the default target, with axioms `propext`,
`Classical.choice`, `Quot.sound`.  The three shape defects that used to block the
continuing one are repaired:

* **The payload's document row carries the byte's class.**  `HcontDefaultRow.hclass` is
  `HcontByteClass G v`, a `Type`-valued disjunction with `.wsStop` and `.scanFree`, and the
  chain producers take the scan-free disjunct (`HcontScanFree`) as their own argument; the
  `.ws`/`.run` arms take `.wsStop`.  `HcontScanFree.not_wsStop` records the exclusion the
  old unconditional row asserted — the reason `HcontPayload` was uninhabited at the
  whitespace states.  The default chain's other non-whitespace sub-classes (the byte below
  `13` or at or above `32`, via `LeafBlock33`/`LeafBlock37`) are named rows, not this
  structure's to assert.
* **The visited-byte row is the scan's.**  `hcontFacts_of_staging`, `scanByteField`, every
  `hbyte` (`HcontFacts`, `HcontRunFacts`, `HcontRunRows`, `RunFacts`, `RunLastFacts`) and
  `ScanVisits` carry the visits' lower bound (`k < p + 1`), and the traversals
  (`walkScanRounds457_of_cell`, `walkScanArrival457_of_cell`, `scanRoundsAt`,
  `scanWsRounds`, `contScanRounds`) thread it.  `cont_hbyteClass_not_wsCont`
  (`JsonStage2WalkHcontFactsOfStaging`) records the wide form's contradiction.
* **The whitespace seam is a state group.**  `HcontRunBody`/`contWsRunBody`
  (`JsonStage2WalkRevolution`) state the run's own rows, and `HcontWsSeam` /
  `hcontWsSeam_of_body` / `hcontScanTail_of_seam` (`JsonStage2WalkDispatchSeams`) produce
  the seam's invariant and cells from the body and the class-C span, then the tail from the
  three calls — no bundle's `hTail` enters.
* **The positive-depth opener's merge is the class's own route.**  `HcontDeepRow`
  (`JsonStage2WalkDispatchClassRows`) carries the merge's counted segment and endpoint, or
  the refusal's witness, as the class's row; `hcontArm_stringOpenAboveZero_of_class` projects
  it into `hcontArm_stringOpenAboveZeroMerge_of_staging`.  The arm's producer no longer
  assumes a state fact the class does not have: the two arms' constructors take the
  value-position call at the state's *own* root word (`rdv`), where they used to pin it to
  `0`, so the class is total over the slot's values rather than only where the slot holds
  zero.

The continuing level's per-class `∀`-fields are stated (`HcontClassRows`: the scan-free
class's document row, the plain-value class's seam row at its prefix and the document
byte's route, the default arm's
scan-free classes' seam rows at `LetS413`/`FS413`, the four class-C leaves' at
`ClsS413T`/`ClsS413F`/`ClsS58T`/`HeadS413`, the positive-depth opener's route, and the
seam's three calls at `contTailStart`), and each has its branch in
`JsonStage2WalkDispatchClassCase`.  The class case is two-dimensional — the head class does
not fix the next byte's class — and of its cells the ones reached by the rows above all
have a producer: the six default classes × the three non-whitespace byte classes are
`JsonStage2WalkDispatchClassTransport`'s six branches, the delimiters and openers are
`walkDispatch_of_derivedClass` and the payload's openers, `.twoEntry` at `C.sp = 0` and the
positive-depth opener are `hcontArm_twoEntry_of_payload` and
`hcontArm_stringOpenAboveZero_of_class`, `.value` × `wsByte` is
`hcontArm_scalarRun_of_class` and `.value` × {`scanFree`, `lowLeaf`, `highLeaf`} is
`hcontArm_value_of_lane` (`JsonStage2WalkDispatchRunRow`), which produces the prefix
(`hcontScalarPrefix_of_inv`) from the row's lane and the class's bits; and the run class's
leaf is wired at each of the six leaves.  The six `.run` cells' document rows are the
payload's now (`HcontClassRows.runSkip`/`runTail`), and the row is `hcontRunRow_of_rows`',
which derives the head part from the class's prefix segment's invariant and takes the body
(`hcontRunBody_of_skip`), the record and the rows as arguments.  The composition at one leaf
is `hcontRunArmAt`: prefix segment + `hcontRunHeadCells_of_prefix` /
`hcontRunCheckCells_of_head` + `hcontRunBody_of_skip` + `runTail` +
`hcontRunRow_of_rows` + `HcontClassRows.run`, with the span chosen by the *leaf* rather than
by the prefix's class.  The six branches are theorems now:
`hcontArm_run_defaultValueLow`, `hcontArm_run_defaultValueMid`, `hcontArm_run_otherValue`,
`hcontArm_run_defaultValueBracket`, `hcontArm_run_defaultValueBrace` and
`hcontArm_run_defaultValueBracketHigh` (the last dispatching on the byte's pivots to the four
class-C/letters/`'f'` leaves) — each stated at the class's own terms and rewriting the body's
equations (`HcontRunBodyAt.hb35`, `.hx1`, `.hk`) where the leaf's pivots and the span need
them.  The seam's root word is a field of `HcontSeamKind` (`hroot`), so no branch supplies a
memory fact; each leaf reads its own item's (`scan`, `scanF`, `scan56True`, `scan58True`).

`.ws` — `.defaultValueHigh` × `wsByte` — is closed as a payload group: `HcontWsRows`
(`JsonStage2WalkDispatchWsRows`) carries the run's own rows at the class's check state
(`HcontRunBody`), the tail's rows (the seam's three calls with their `if.else405.i` `0`, the
root word, the record the scalar call appends and the landing's byte with its class) and the
traversal's per-index class on the visits' window `[k + 1, v)`; `hcontFacts_of_rows`
produces `HcontFacts` from the payload's `defaultLane` and the group, deriving the tail
through `hcontWsSeam_of_body` and `hcontScanTail_of_seam` rather than taking it.  The
traversal's class is the one row the skip's class cannot produce — the skip's window is
`[entryPos C.k, k)` and the visits' is `[k + 1, v)`, the document is arbitrary, and the
stop's own byte admits `13`/`32` while the visits' class is the `9`/`10` arm — so it is
named there, not weakened.

`walkContinueFacts_of_payload` is the class case over those cells
(`JsonStage2WalkDispatchContinuing`): each cell of the matrix reads its producer, and the
bundle is the `Nonempty` the case proves, read by `Classical.choice`.  The last level's
case is closed:


* **The continuing level's run class is a produced row, and its leaf is no longer pinned.**
  `hcontRunRow_of_rows` produces the run's row (the check state's rows plus the byte's leaf,
  guarded by the default lane's whitespace class) from the class's prefix segment and two
  payload groups, `runSkip` (the skip's class) and `runTail` (the landing's byte, its reads,
  the traversal and the appended record); `HcontClassRows.run` joins the row to
  `RunFacts` through `hcontRunFacts_of_seam`.  The old `HcontClassRows.runRow` field is
  **replaced**, not kept beside the producer: it had no producer and made the field an
  assumption about a document.  `HcontRunRows`/`HcontRunFacts` state the
  tail's source at the leaf `ss`, its target and every landing field at
  `ScanEntry ss …`, and carry the four cells `ScanEntry`/`Latch462S` bind nothing of
  (`%ee.1.i`, `%cond350.i`, `%inc.i`, `%nep`); `runFacts_of_runBundle` reads `f.ss`, so
  `RunFacts`'s own `ss` is the leaf's.  The six leaves' producers are
  `hcontRunLeaf_letters`, `_fLetter`, `_56True`, `_56Else`, `_58True` and `_58Else`
  (`JsonStage2WalkDispatchClassCase`), the class-C else instance is
  `hcontRunLeaf_of_seam` (`JsonStage2WalkDispatchSeams`), and each leaves' span is the
  byte's own (`lettersSpan`, `fSpan`, `c56TrueSpan` … `c58ElseSpan`).  Their supply is
  wired per leaf by `hcontRunLeafAt_letters` … `_58Else`
  (`JsonStage2WalkDispatchRunRow`), and the row is **produced**, not supplied:
  `hcontRunRow_of_rows` derives the head part — the class's prefix to `sw.default.i`, the
  shared four's cells and the entry's lane — from the prefix segment's invariant and the
  payload's row, and takes the body (`hcontRunBody_of_skip`, from the payload's skip class),
  the appended record and `HcontRunRows` as arguments.  The kind
  literal (`%.sink372`) is part of the memory the first call reads
  (`s2ValuePosPre`'s `writeBytes … (natToBytes cA.toNat 4)`), so `102`/`110`/`116` —
  `if.then397.i`'s `9`, `if.then403.i`'s `10`, `LeafBlock58`'s `8` — have their own groups
  (`HcontSeamAbi.scanF`/`scan56True`/`scan58True`), while the three leaves whose
  predecessor is `if.else405.i` (kind `0`) take the seam's rows by
  `HcontSeamCalls.cast`.  Those three are **not** new supply: their seam is the one state
  `contWsTailStart` builds, so one item (`scan`) serves all three, the leaf's span leaving
  that state only for the carry it binds.  The three nonzero ones are, and
  `HcontSeamAbi`'s four continuing fields therefore state their literal
  (`HcontSeamKind`), because a cast preserves `cA` and the leaf's `hval` pins it —
  `HcontRunLeaf.cA_of_imm` is that pinning stated.  That is why the leaf is the row's
  argument: one row cannot serve two leaves whose kinds differ.
  The continuing case is two-dimensional — the head class does not fix the next byte's
  class — and at `HcontClass.value` (the tag test is `1`) the constructor is
  `HcontArm.scalar`, whose bundle and document row now carry the byte's
  route (`HcontScalarFacts.hb`, `HcontScalarPrefix.hb`); its seam row is stated at
  `scSeamByte … pre.hb`, its chain to the seam is `scSeamSegByte` and its tail
  `scTailByte_of_calls`, so `.value` × {`scanFree`, `lowLeaf`} are produced.  The fourth
  cell — `.value` × `wsByte`, the whitespace run after a numeral — is `HcontArm.scalarRun`
  (`JsonStage2WalkHcontWsScalar`): its bundle is `HcontScalarWsFacts` (the numeral prefix's
  document cells, the byte's class with the run's stop and its per-index facts, the seam's
  own cells, the tail's segment and the scan's landing), its row is
  `HcontClassRows.scalarRun` (`HcontScalarWsRow`, the seam's three calls in place of the
  tail's segment), its producer is `hcontArm_scalarRun_of_row`, which builds the tail from
  the calls (`scanTailSeg_at`), and its branch is `hcontArm_scalarRun_of_class`.  So no
  cell of the plain-value row is a missing arm.
* **The last level's groups are stated and the case is closed.**  `HlastArmRows`
  (`JsonStage2WalkDispatchLastRows`) carries the five groups whose types name states above
  `DispatchClassRows` — `HlastScalarRows`, `HlastLettersRows`, `HlastFLetterRows`,
  `HlastClassCRows`, `HlastRunRows` — each a `lastEntryArm_*_of_staging` producer's
  argument list after the invariant, the guard and the class bits, and each field's
  consumer is named in its docstring.  `walkLoopEnd_of_payload (hp : HlastPayload G)
  (hc : HlastClassRows G) (ha : HlastArmRows G) : WalkLoopEnd G` is proved by the class
  case over the head switch's bits, with axioms `propext`, `Classical.choice`,
  `Quot.sound`.

The last level's route asset is closed: `HlastFacts`/`HlastResidue` carry
`hb : HcontByteRoute (head35 (G.bs.getD (G.n - 1) 0))`, `hlastTailByte_of_calls` produces
`hTail` at the class's own seam, the merge path is counted at the route (`hlast_toMerge`,
`hlast_finish`, `hlast_refuse`), and the closure theorem's class case is written, so
`.highByte` is total over the three non-whitespace leaves.

**What the two words at `G.next0 + 8` need, and why neither is a value row.**  The
slot is the root-done flag `%root_done.i`: `entry` writes it `0` among its four allocations,
and its other writer is the callee `s2_after_value`, whose depth-zero arm stores `1` through
it (`s2AfterValuePost_rootSlot_at_zero`) and whose positive-depth arm rewrites one
state-stack byte and leaves the slot alone (`s2AfterValuePost_rootSlot_above`).  Both facts
are theorems of the contract's post, and together they are the whole of the callee's effect
on the slot: **`0` is not among its writes.**  So the slot's value is a function of the path,
not of the byte class, and the only honest statement of it is a witness.  The openers' arms
and the last entry's take that witness (`rdv`) with its read, and the two arms of the
value-position answer are the split; nothing needs the word pinned, and an invariant clause
asserting `0` would be false at exactly the heads a depth-zero call has flagged.

l1 is closed.  Its word `rdv` is a witness, so what the row needs is the read, and
`hlastTail_rootSlot_word` produces it: `WalkInv.root_slot`'s four present bytes read back as
a word (`walkReadBytes_rootSlot_word`, through `natToBytes_bytesToNat`) and transported
across the tail's four token-record stores, each separated from the slot by the record's
extent (`readBytes_rootSlot_tokWrite`).  The value stays open only in the sense that nothing
pins it, which is what "variable word" meant.

c11 is closed as a *value* row by being stated as a witness, and the substitution that made
that possible is now the code's.  Its `hrd` used to be the value `if.then.i`'s `load` hands
the value-position call, consumed by `openTailSeg` as a memory fact, with `HcontOpenCall`
staging the *literal* `0`; the callee's contract therefore could not produce it.  The two
`WalkStep`-level changes are made: `openIfThenI_term` and `openTailSeg` (with `openCapTailSeg`,
`containerOpenSeg`, `containerOpenMerge_at`, `containerOpenCap_at`) read the slot at a
witness word `rd`, and the arms and the payload's row (`HcontOpenCall`) name it.  With the
witness in place the answer is derived rather than assumed — `s2ValuePos_ret_zero_or_one`
splits the callee's two bits — and the missing arm exists: `if.then16.i`, the refusal's
offset store, is `.containerOpenRefuse`/`LastEntryArm.containerOpenRefuse`, six links from
the head (`containerOpenRefuse_at`) with the copy's word by `refuseSegment_word_of_store`.
So the byte class `91`/`123` *is* total over the state space: the two answers are the whole
branch and each has its arm, and `HcontLane.root`/`HlastLane.root` — the value clauses that
used to stand in for it — are retired.  The reachability that was only recorded is now
stated at two staged documents (`secondValue_last_refuses`, `secondValue_cont_refuses`,
`JsonStage2WalkDispatchOpenersDomain`), with the first value as the answer's control.
The same holds for the log's base word in `HlastFacts`: a witness, never a pinned value.

### 7.9 The event relation is instantiated

`EventStreamRel` (`LeanLLVM/Refinement/JsonPipelineSpec.lean`) is no longer a
free parameter at the specification: `LeanLLVM/Refinement/JsonStage2Spec.lean`
defines

```text
stage2EventRel : EventStreamRel :=
  fun bs arena evs toks => Stage2EventRel bs arena evs toks
```

and the record `Γ_pipeline_stage2` is `Γ_pipeline stage2EventRel`.  The relation
is inductive and consumes the emitted encoding byte for byte: `tagRecord` is
`out_tag`'s one byte, `numberRecordBytes` is `T_NUM` plus the eight payload
bytes, and `strRecordBytes` is the tag, the four-byte length and the eight-byte
span-or-arena field (`EventRecord`, the trace `JsonStage2Body` pins to
`stage2.h:68-75`).  Comma and colon tokens have no record and are consumed by
their own constructors.

Its payload correspondence is the parser's own vocabulary.  A number record's
payload is `bitsBytes (strtodSpec d).toBits` for a well-formed `Decimal d` whose
lexeme is the token's span (`EventStreamNumberArm` in `Strtod`); a plain
string/key record is span-addressed (`plainSpan`) and its body reads as the
token's code points; an escaped one's arena slice reads back through
`escapeCodePoints` as those code points; scalars and containers are the ABI's
tags at the token's span.  The coverage lemmas are
`stage2EventRel_scalars`, `_string_plain`, `_string_arena`, `_number`, `_array`
and `_object`, each universal in its payload, not a list of examples.  The
arena side of the escaped-string form is inhabited for every code-point list by
`stage2EventRel_string_arena_inhabited` (`escapeCodePoints_encode`).  The number
clause binds the record to `strtodSpec`; that the emitted `num_fast`/`strtod`
path computes that function is `NumberArmOwed` in `Strtod`, still owed and not
claimed by the relation.  The pinned body's own form of the obligation is
`JsonStage2NumFastArm`'s, and its shape is different in one respect: at the
walk's `Calls` selection the body's conversion is `ub` at each of its three
out-of-line callees (`num_d8_el1`, `num_el_el1`, `stk_mul_u64`), so the
statement a proof owes is about a `Calls` that answers them and a staging that
stages the two tables (`NumFastBodyArm`), not about the environment the walk's
contracts are proved in.

The used prefix is derived where the post supplies the reserved read:
`usedPrefix_of_reserved` splits `readBytes m dst ndst' = some arena` at
`ndstU ≤ ndst'`, and `stage2Boundary_usedArena` states the used-prefix read.
`stage2Boundary_acceptedValue` and `stage2Boundary_refusal` are the semantic
correspondences at the named stage-2 boundary witnesses: the accepted value is
`decodeTape`'s, with `ValidDocument` from `decodeTape_correct`, read at the used
prefix and the reported event cursor; the refused offset is `RefusalOffset`'s.
The reserved extent `ndst'` remains the presence, capacity and frame extent —
this module narrows no memory claim to `ndstU`.

The refusal policy is `RefusalOffset` on both sides: `refusalOffset_walk` reads
the parser's constructor position for a walk-owned refusal and
`refusalOffset_utf8` the document's end for a UTF-8-owned one.  The resource
policy is `Stage2ResourcePolicy` (the input bound and the two parser limits the
pipeline's ABI does not carry), derived from `pipelineSpecPre` by
`pipelineSpecPre_resourcePolicy`.  The axioms are pinned: the relation and its
coverage constructors at `[propext]`, and the used-prefix, semantic,
refusal and policy theorems at `[propext, Quot.sound]`.

### 7.10 The parser half is produced, at the walk's own trace

`pipeline_satisfies_stage2`'s premise is `hsem`: at each outcome an execution
produces, `ParserHalfForOutcome stage2EventRel` — the acceptance equivalence at
that outcome's verdict, the accepted tape with its decoded value and validity,
and the policy on the refusal word.  `LeanLLVM/Refinement/JsonStage2Hsem.lean`
produces it:

```text
hsem_of_evidence :
  (∀ args mem next o ndst' nev', pipelineStaging … → BehFromState … o →
     pipelineOutputExtents … → Stage2OutcomeEvidence base args mem ndst' nev' o) →
  ∀ args mem next o ndst' nev', pipelineStaging … → BehFromState … o →
     pipelineOutputExtents … → ParserHalfForOutcome stage2EventRel base args mem ndst' nev' o
```

`pipeline_satisfies_stage2_of_evidence` is that statement applied where the
bridge consumes it — the units' record and the per-outcome evidence give
`Satisfies calls f (Γ_pipeline_stage2 tab base)` — so the produced shape is the
one `pipeline_satisfies_stage2` asks for rather than a lookalike.

**The two vocabularies are joined by the record trace.**  The specification's
relation is stated over bytes; the walk's invariant carries a
`List EventRecord` and states the event stream's written suffix as its
flattening (`(C.events.map EventRecord.encodedBytes).flatten`).  `Stage2Records`
is the relation at that vocabulary — one constructor per record class, consuming
the record at the head instead of its bytes — and `Stage2Records.toEventRel`
transports it to `Stage2EventRel` (`stage2EventRel_of_records` is the form the
producer uses).  `Stage2Records.append` is what makes a walk step composable: one
step relates one record to one token, and the trace is the concatenation.
`pair_records` and `null_records` instantiate it at two documents with the
emitted bytes computed rather than assumed; §7.11 states and proves the relation's
general form, which makes those two instances rather than the claim.

**What the producer derives, and what it names.**  `Stage2OutcomeEvidence` is the
evidence at one outcome: the document the arguments name, and the run's answer.
Derived from it are the decoded value (`decodeTape_correct`), the tape's validity
and span discipline (`tape_valid`), the byte-level relation (the trace), the
acceptance equivalence (the outcome's verdict, its two-valuedness and the
parser's answer at that verdict), and — on the accept path — the refusal policy
(`refusalOffset_of_parseOk`: both of `RefusalOffset`'s clauses are vacuous at an
accepted document whose staged window passed the UTF-8 stage).  Named, not
derived, is the one thing the tree has no theorem for: that the records the walk
emitted are the *reference parser's* tokens.  The walk's trace records each
event's shape and payload; that those are `parseBytes`'s tokens at that document
is a row-per-arm obligation of the walk proof, and it is not a consequence of the
boundary post — `stage2Post`'s verdict is two-valued and says nothing about the
stream's meaning (`JsonStage2Contract`).  On the refusal path the evidence also
carries the policy at the written word; the offset's two clauses are
`refusalOffset_walk`'s and `refusalOffset_utf8`'s.

**No accepted run's output is only related.**  The accepted clause's value is
`decodeTape`'s and its validity is `ValidDocument`'s; the arena and event bytes
are *related to* the tokens that value came from, which is what a record stream
means.  So strings and containers are decoded by the tape's spans and the
relation's constructors, and a number record's payload is `strtodSpec`'s
encoding — the value is never left as "some bytes satisfying a predicate".
§7.11 carries the same statement to the *stream*: its record skeleton is a
function of its bytes, and each record's kind and payload are the token's class
agreement rather than a predicate the bytes merely satisfy.

**Coverage by value class.**  The record relation's constructors are the five
classes: scalars (`null`, `true`, `false` as `tag 8`/`9`/`10` at their literal
spans), containers (`tag 1`–`4` at their one-byte spans), plain strings (`str`
with `plainSpan`, the body's code points read off the document), escaped strings
(`str` with an arena offset below `2 ^ 63`, the slice read back through
`escapeCodePoints`), and numbers (`number`, `strtodSpec`'s eight bytes at a
well-formed lexeme).  `null_records` and `pair_records` instantiate the scalar
and container rows; the two string rows are the specification's
`stage2EventRel_string_plain`/`_arena` at the same hypotheses, and the arena form
is inhabited for every code-point list
(`stage2EventRel_string_arena_inhabited`).

**The numeric arm's boundary is a staging boundary, not a numeric defect.**  The
number row costs no arithmetic at the model: `stage2NumFast` is what the walk's
`num_fast_el1` slot is answered by at `stage2SubCalls`, and at a well-formed
lexeme its eight bytes are `strtodSpec`'s
(`stage2NumFast_writes_strtodSpec`, from `numFastEmitted_strtodSpec`).  The
*pinned helper body* is the different statement.  At `stage2Calls noCalls` the
slot has no answer (`stage2Calls_noCalls_numFast`, with
`stage2Calls_subCalls_numFast` as the control that the same reading answers the
model), and `JsonStage2NumFastArm` shows that at each of the body's three
out-of-line callees — `num_d8_el1`, `num_el_el1`, `stk_mul_u64` — the step is
`ub`.  A body-level conversion proof therefore needs a call environment that
answers the three callees and a staging that stages the two tables.  Both are
now supplied, and that is all `NumFastBodyArm`'s hypotheses needed:
`JsonStage2NumFastCalls.numFastCalls` answers the three symbols (each modelled
from its measured C text), `stage2NumFastCalls` composes it with the walk's
`s2HelperCalls`, at each of the three sites the step is a jump rather than `ub`
(`numFast_*_denote_some`/`_step_jump`), and `numFastTables_holds` is
`NumFastTables` at a concrete twenty-row/twenty-three-row staging.  What remains
open is the conversion's *run*, not its environment: the three digit runs' arms,
their starts, the inlined tier-1 arithmetic, and tier 3's region.  Two pieces of
the run are now supplies rather than obligations.  The eight-digit fast path's
blocks are chained (`JsonStage2NumFastSeams`): `fpCleanup_denote_pre`/
`_denote_body` and `fpCleanup_step_body`/`_step_end` are the fold block at both
its edges, `fpBody_denote_ok`/`_denote_refuse` and `fpBody_step_ok`/
`_step_refuse` are the second group's reader call, `fpWhileEnd_denote_cleanup`
reads the exit's three `phi`s, and `fpCleanup112Instrs`/`fpBody100Instrs`/
`fpWhileEnd115Instrs` are the fraction's copies with
`fpWhileEnd115_denote_cleanup`/`_denote_thread` at the two edges a fraction byte
leaves by; the loop's own `runFuel` composition and the taken guard's entry into
`intRunInv` are what the fast path still owes.  The accumulator's tie at
`if.end230` is stated: `intRunExit`'s end-of-lexeme exit now carries the
length's cell beside the incremented index (both `BitVec.ofNat 64 i1`), and
`intRunExit_gate` reads `%ip.4` and `%7` as the merge's `%ip.5708717729` and
`%idig.4709716730` — the fold's word and the digit count `d0 + (n - i0)` — so the
tie `ip_word_digitsNat` takes is available from the run's own exit.  The merge's
registers are then read as the model's at the two digit edges:
`JsonStage2NumFastSeams.t1_intRun_tie` (the integer run's end-of-lexeme exit
reaches `if.then241` with `%ip.5708717729` the part's `digitsNat` and
`%idig.4709716730` its `intDigits`), `t1_fracRun_tie` (the fraction run's exit,
with `%fr.5718728` the fraction's `digitsNat` and `%fdig.4719727` its
`fracDigits`), and the two cells that feed them, `t1_headTie` (the `if.end68`
seam) and `t1_fracCount_tie` (the fraction's count preheader).  What the store
chain still takes as its entry is the exponent edge's incoming cells
(`t1_store_run`'s hypotheses): the digit parts' cells carried through `if.end144`
are the same ties, while `%exp10.4`'s reading as `expVal d` is the exponent
nest's exit.  Tier 3's
three links are stated and proved at their statements
(`JsonStage2NumFastTier3`): the traversal with the trip count
(`t3_traversal_counts_1_3`, two `runFuel` steps from the peeled entry at a count
in `0 < k < 4`, with the reached state's two `poison` cells holding the marker and
unread — `t3_traversal_markers`); the window's copy (`copy_retained` is the
retained array as `m / 10 ^ stkDrop m`, `copy_sticky` the copy's sticky bit as
the model's remainder test, `copy_counters` the emitted `S` and `f` as `E +
stkDrop m` and `leadM`, with `copy_retained_window`/`copy_sticky_window`/
`copy_S_window`/`copy_lead_window` the same at `windowOf`'s own fields, and
`t3_copy_denote` the store block at its pin); and the
proximity estimate at the tree's own rounding (`roundMag_dist_le_step` bounds one
rounding by one lattice step, `fmulBits_dist_le_step`/`fdivBits_dist_le_step` are
that bound at the emitted operations, `proximity_scale` composes the two-step
bracket, and `t3_scale_of_ulp` concludes `valLeqBoundary m E (2 * J) eB`, the
premise `shift_of_near` takes).  The epilogue block itself is chained
(`t3_epil_denote` is `for.body.i.i566.i.i.epil`'s fourteen instructions at its
pin, with `t3_epil_step_lcssa`/`t3_epil_step_self` its two successors and the
three `i128` operations stated width-generically).  The copy loop's blocks are
then stepped per edge (`JsonStage2NumFastTier3CopySteps`: the head
`for.body87.i.i`, the three unrolled tests, the store and both latches, each at
its own predecessor), and the residual loop's measure, invariant and exit are
fixed (`JsonStage2NumFastTier3CopyLoop.t3EpilLoopOf`, whose two visits are the
piece not discharged).  The starting approximation's fold is
`JsonStage2NumFastTier3Fold`: `if.end198.i.i` forms `top` and `e10`, the two
ladder operations are `while.body206.i.i`'s `fmul` and `while.body232.i.i`'s
`fdiv`, `t3Approx` is the emitted double, and `t3Fold_two_step` is its two-step
error.  What the region still owes is the unrolled nest's `BoundLoop` shape and
the residual loop's two visits, both named in that module's record of the
boundary.
The kernel's bound is not among the obstructions: `num_el_el1`'s mantissa is a
`uint64_t`, and the body's own argument at `if.end268` is `%add244`, a 64-bit
word, so `NumFastElAgrees`'s `w < 2 ^ 64` domain is met at the body
(`numFast_ifEnd268_domain`).  Tier 2 is
closed on the model side too: `JsonStage2NumFastTier2.NumFastElAgrees` proves
`numElEl1` is the guard's decision for the kernel's `w < 2 ^ 64` mantissa, so
`elGuardRefinesOn`'s exactness transfers to the model, and
`not_numFastElUnbounded` records that the bound is the kernel's.
`JsonStage2NumFastCounters` reads the merge block's two counters at the model
(`numFast_ifEnd230_counts`), and the runs' starts are now dispatched:
`JsonStage2NumFastStarts.intRun_start` reaches `land.lhs.true41` from the sign
check with `intRunInv … (negIndex b + 1) 1 bs … 0`, `fracRun_start` reaches
`land.lhs.true119` from the `.` test with `fracRunInv … (i5 + 1) 0 bs … 0`, and
`expRun_start` reaches `land.lhs.true195` from the exponent's digit gate at
`lor.lhs.false180` with `expRunInv … i11 bs … 0`; the `0`-alone arm
(`ifThen11`/`if.end68`) is there too.  The dispatch is proved *behind* the two
eight-digit fast-path guards, and the exponent's marker nest between `if.end144`
and `lor.lhs.false180` is the piece of the scan that still fixes an index
(`%i.11`) rather than being fixed by this module; both are named at the block in
`JsonStage2NumFastArm`.
The conversion's arithmetic is not in question, and the relation's number
clause is discharged at the model.  No theorem here uses `sorry`, `admit` or
`native_decide`; the §7.10 environment and reachability theorems are pinned at
`[propext]` or `[propext, Quot.sound]`, while the tier-2 bridge carries
`Classical.choice` through Mathlib's `Nat.size` lemmas and the three run-start
theorems carry it through the digit-window lemmas' `by_contra`.

### 7.11 The correspondence, record for record

§7.10 left one thing named rather than derived: that the records the walk emitted
are the reference parser's tokens.
`LeanLLVM/Refinement/JsonStage2TokenCorrespondence.lean` states what that
correspondence *says* and proves its content and its statement at the run's own
reads; the one row it still names is stated at the end of this subsection, with
the reason it is not a consequence of what precedes it.

**The relation is one record per record-carrying token, in order.**
`TokenRecord (bs arena) r tok` is the ten-constructor relation at one record
and one token — the whole-trace `Stage2Records` peeled to a single step — and

```text
stage2Records_iff_forall₂ {bs arena : List UInt8} {rs : List EventRecord}
    {toks : List Token} :
  Stage2Records bs arena rs toks ↔
    List.Forall₂ (TokenRecord bs arena) rs (Token.nonSeparators toks)
```

is the exactness statement.  The trace relates to the token list exactly when the
two are the same length and each record agrees with its token, with commas and
colons *removed* by the function `Token.nonSeparators` rather than consumed by a
side condition, so the relation has no slack beyond the class agreement.  What the
removal leaves outside the relation is the separators' own spans: a comma's or a
colon's position is the tape's and is not re-checked here, while every
record-carrying token's kind, span and payload is.  The tree's two instantiations
are therefore instances rather than the claim: `null_records_of_forall₂`
rederives the `null` document's trace from the general form.

**The class agreement is one elimination per class.**  `tokenRecord_tagVal` gives
the value of a record's tag byte as the token's class tag — the four containers,
the three literals and the number — and states that a key/string record's
`T_KEY`/`T_STR` is the grammar position's choice, so no class tag is claimed for a
string token.
`tokenRecord_tag` gives the seven one-byte classes' kinds, spans and document
bytes.  `tokenRecord_number` gives the number's lexeme (`s.stop = s.start +
d.lexeme.length`, with the document holding `d.lexeme`), its well-formedness and
the record's payload `(strtodSpec d).toBits`.  `tokenRecord_string` gives the
span's opening quote, its code points through `bodyCodePoints`, and the two forms'
fields: `plainSpan (s.start + 1)` over the document's body, or an arena offset
below `2 ^ 63` whose slice reads back through `escapeCodePoints`.  The five value
classes the contract names are the constructors, and there is no sixth.

**The stream's record structure is decoded.**  The encoding writes the tag first
and then a fixed-width payload, so `parseSkeleton` — each record's tag, stepping
over the width its own byte announces — is a total function of the stream, and

```text
parseSkeleton_trace (rs : List EventRecord) (h : ∀ r ∈ rs, r.Tagged) :
  parseSkeleton (rs.map EventRecord.encodedBytes).flatten = rs.map EventRecord.tagVal
```

reads a related trace's bytes back as its tag sequence.  So an emitted stream is
not left as a bare relation: its record boundaries and classes are a function of
its bytes, and each record's payload is the class's own — the document's bytes at
the span, the arena slice decoding to the token's code points, or `strtodSpec`'s
bits.

**The statement at the run's own reads.**  `stage2Records_at_accept` is the
correspondence at an accepted run:

```text
stage2Records_at_accept {bs arena evs : List UInt8} {t : Tape}
    {rs : List EventRecord} {m : Mem} {dst ev ndst' nev' ndstU : Nat}
    (hparse : parseBytes Limits.default (ByteString.literal bs) = .ok t)
    (hdst : readBytes m dst ndst' = some arena)
    (hU : ndstU ≤ ndst')
    (hev : readBytes m ev nev' = some evs)
    (hrecs : evs = (rs.map EventRecord.encodedBytes).flatten)
    (hrel : Stage2Records bs (arena.take ndstU) rs t.tokens) :
  t.input = ByteString.literal bs ∧
    readBytes m dst ndstU = some (arena.take ndstU) ∧
    List.Forall₂ (TokenRecord bs (arena.take ndstU)) rs
      (Token.nonSeparators t.tokens) ∧
    readBytes m ev nev' = some evs ∧
    parseSkeleton evs = rs.map EventRecord.tagVal
```

The tape is the reference parser's for the *same* bytes, the arena reads at the
**used** prefix (derived from the reported reserved read by
`usedPrefix_of_reserved`), the event stream reads at its reported cursor, the
trace agrees with the tape's tokens record for record, and the stream's skeleton
is the trace's tags.  Its hypotheses are the accept path's own — `parseBytes … =
.ok t`, the two extent reads, the trace's flattening and the relation at the used
prefix — which is the shape `parserHalf_accept` consumes from
`Stage2OutcomeEvidence`.

**The relation separates the classes and the spans.**  `null_trueTag_not_records`
refutes a `true` tag on the `null` document's token and
`trueTag_null_span_not_records` refutes the `null` document's token at a span
holding `true`'s bytes.  The correspondence is not a wrapper that admits any
trace: a wrong class or a wrong span leaves no constructor.

**What is still named, and why.**  The relation is *between* the walk's trace and
the parser's tokens; it does not say the walk emitted this trace.  That row — the
walk's `C.events` equal to the tokens' encoding — needs an alignment of the entry
stream's positions (`WalkGeom.ent`, ordered and inside the document, with no
clause of `stage2Pre` tying them to `parseValue`'s cursors) with the parser's
token starts.  §7.12 states that alignment and what it closes; what the alignment
does not do is produce the per-entry record rows, and §7.12 names the row that
remains.  So the accept clause's evidence still names the trace relation, and what
§7.11 adds is that the named relation is exact, per class, and decodable rather
than opaque.

**The number class's boundary.**  At the model the number row costs no arithmetic
beyond `strtodSpec`: `tokenRecord_number` binds the record to `strtodSpec` of the
span's lexeme.  A binary64 value's bits are a word (`toBits_lt_two_pow_64`,
`[propext, Quot.sound]`); the composition at `strtodSpec d` is cited rather than
written, because elaborating an application of `strtodSpec_isCode` reduces
`(strtodSpec d).IsCode`, whose `strtodSpec` unfolding reaches a `10 ^ 2098`-scale
exponent and exceeds the elaborator's recursion depth.  The *body's* conversion is
the staging boundary §7.10 names: `ub` at each of the three callees at the walk's
selection (`stage2Calls_noCalls_numFast`).

**Axioms.**  Every theorem above is pinned in its module: `TokenRecord`, the four
class lemmas, `forall₂`, `of_forall₂`, `stage2Records_iff_forall₂`, `tagged` and the
three controls at `[propext]`; `toBits_lt_two_pow_64`, `parseSkeleton`,
`parseSkeleton_encodedBytes`, `parseSkeleton_trace` and `stage2Records_at_accept`
at `[propext, Quot.sound]`.  No `sorry`, `admit`, `native_decide` or
`Classical.choice`.

### 7.12 The entry alignment: the clause, its preservation, and its limit

§7.11's remaining row needs the walk's entry positions to *be* the parser's token
boundaries.  `LeanLLVM/Refinement/JsonStage2WalkAlignment.lean` states that as a
clause over the staging and the tape — not over the walk's carry — and proves
what follows from it and what does not.

**The clause.**  The class of a document byte is the parser's own first-byte
dispatch, written as a function (`classOfByte`, with the number class read as `-`
or a digit; its `if` chain is `decide`-based because `UInt8`'s `BEq` carries
`Classical.choice`), and a token's class is its constructor's (`tokenClass`).
The alignment is:

```text
WalkAlign {m0 : Mem} (G : WalkGeom m0) (t : Tape) : Prop :=
  t.input = ByteString.literal G.bs ∧
    G.nep = t.tokens.length ∧
    (∀ k, k < G.nep → ∃ tok : Token, ∃ b : UInt8,
      t.tokens[k]? = some tok ∧ tok.span.start = entryPos G k ∧
        G.bs[entryPos G k]? = some b) ∧
    (∀ k, k < G.nep → ∀ (tok : Token) (b : UInt8),
      t.tokens[k]? = some tok → G.bs[entryPos G k]? = some b →
        classOfByte b = some (tokenClass tok)) ∧
    (∀ k, k + 1 < G.nep → ∃ tok : Token,
      t.tokens[k + 1]? = some tok ∧ tok.span.start = entryPos G (k + 1))
```

At each entry index the parser's token starts at `entryPos G k`, the byte there is
the class its constructor names, and the next entry is the next token's start.
`WalkAlign.at`, `.class` and `.next` are the clause's three readings (the last at
the index's successor); the class clause is an implication rather than a component
of the token existential so that the two parts are read separately.

**The loop head's reading.**  `WalkAlign.head` reads the clause at a head state:
the parser's token at the carried index starts at `entryPos G C.k`; the walk's
`%8` is that token's class byte (`WalkIter.reg8` at `entryByte = b`); `%idxprom.i`
and `%arrayidx10.i` are its start and its address (`WalkInv.idx_reg`,
`WalkIter.regarr`).  `WalkAlign.head_class` and the eleven `head_*` corollaries
turn a byte test of the walk's into the parser's constructor — `.punct`, `.null`,
`.bool`, `.string` or `.number` — which is the form a per-arm proof consumes: the
arm's branch on `%8` is then a statement about the parser's token rather than a
byte the arm alone knows.

**Preservation.**  The clause mentions only `G`, `t`, so no step of the walk can
change it: `WalkScope.WalkLink.align` carries it across a link and
`WalkScope.WalkChain.inv_align` across a trace, beside `WalkInv`.  That would be
vacuous if the memory changed under the two reads it rests on; it does not.
`WalkInv.doc_read` and `WalkInv.entries_read` state that every state of the walk
still reads the staged document and the staged entry stream, from
`WalkInv.frame` and the `doc_outside`/`entry_outside` exclusions (the two objects
end at or below the call's cursor, so the run's write extents miss them).  The
walk's index advance is the clause's own next-entry conjunct at `k + 1`
(`WalkAlign.next`).  What the clause does *not* do at the seed is establish
itself: `stage2Pre`'s entry-stream clause is order and inside-the-document only,
and the positions' provenance is the stage-1 emitter's (`entryMask64`'s lanes,
`JsonEntSpec`), whose composition with `parseValue`'s token starts is outside this
tree.  So the alignment is a staging hypothesis of the same kind as the record's
other clauses, and it is not derivable from `stage2Pre`.

**What the clause closes.**  The four container classes' rows are theorems rather
than an arm's obligation.  The alignment fixes the start and the byte; the tape's
span discipline (`checkSpans`, reached through `spansWellFormed`, and
`checkSpans_mem` for one token of the list) fixes the one-byte stop; and
`TokenRecord`'s own constructor follows (`tokenRecord_punct`): the class's tag at
the class's span, given the arm's own byte test.  The two separators carry no
record, so they owe no row.

**What it does not close: the trace.**  The alignment says which token an entry
is; it says nothing about the record an arm appended, so it does not imply the
encoding.  `align_not_enough` proves that rather than asserting it: at the `null`
document an entry stream of `[0]` satisfies the alignment, and an empty trace at
that geometry still satisfies it while `Stage2Records` is false of the pair.  The
row still owed is `WalkTraceRow bs arena t rs` — the pointwise `TokenRecord`
relation over `rs` and the parser's non-separator tokens, which is
`stage2Records_iff_forall₂`'s right side — and `emittedStream_of_row` is the
composition that turns it into `Stage2Records`, the stream's `Stage2EventRel` and
the decoded skeleton `parseSkeleton evs = rs.map EventRecord.tagVal`.
`emittedStream_at_walk` reads that composition at a walk state: `WalkInv.evBytes`
names the bytes at the log's cursor as the trace's flattening, so the stream the
walk has written is the tokens' encoding exactly when the row holds.  The three
payload classes are why that row is not a theorem here: a literal's exact span, a
string's body and a number's lexeme are the parser's token-construction facts, and
they are now exported rather than private (`TokenBytes` and `tape_tokenBytes`; see
§7.13), so the row's *elements* are theorems and what stays an arm's obligation is
the record the arm appended and, for a string, which of the two forms it chose.
Punctuation's one-byte shape is the class the span discipline alone supplies —
hence the four container rows above.

**Axioms.**  The module pins every declaration at `[propext]` or
`[propext, Quot.sound]`; the bare definitions (`classOfByte`, `tokenClass`,
`punctByte`, `punctTag`, `TokClass`, and the ten one-byte `classOfByte_*`
equations) depend on no axioms at all.  No `sorry`, `admit`, `native_decide` or
`Classical.choice` — the last is why `classOfByte` compares with `decide` rather
than `BEq`.

### 7.13 The per-record row: the parser's token facts and the record each class carries

§7.12 leaves one row: `WalkTraceRow`, the pointwise `TokenRecord` relation between
the walk's trace and the parser's record-carrying tokens.  Its elements are the
parser's token-construction facts, and those are what
`LeanLLVM/JSON/TapeCorrect.lean` now states per class and proves of every token of a
tape the decoder accepts.

**The facts.**  `TokenBytes bs tok` is the document-side statement a token carries:

```text
TokenBytes bs (.punct _ s)      :=  s.stop = s.start + 1
TokenBytes bs (.null s)         :=  (bs.drop s.start).take 4 = literal "null"  ∧ s.stop = s.start + 4
TokenBytes bs (.bool true s)    :=  (bs.drop s.start).take 4 = literal "true"  ∧ s.stop = s.start + 4
TokenBytes bs (.bool false s)   :=  (bs.drop s.start).take 5 = literal "false" ∧ s.stop = s.start + 5
TokenBytes bs (.number s)       :=  ∃ lex, (bs.drop s.start).take (s.stop - s.start) = lex
                                      ∧ lex.length = s.stop - s.start ∧ RfcNumber lex
TokenBytes bs (.string s)       :=  bs[s.start]? = some 0x22
                                      ∧ ∃ cs, StringAt .strict bs s.start s.stop cs
```

`tape_tokenBytes` proves it of every token of a tape with `decodeTape t = some v`,
by the decoder's own recursion (`decodeTokenBytes_aux`, the three mutual functions
at the guards that produced each token).  Nothing private had to be exported for
it: the facts are read off the guards rather than restated from the parser's
soundness theorem, so `DecodesValue` and the per-branch `valueAt_*_inv` lemmas stay
`private` and no claim about the parser is duplicated.  The punctuation byte is
deliberately *not* in `TokenBytes`: the run's own read supplies it (`WalkAlign.class`
plus the arm's byte test), which is why §7.12's four container rows need nothing
from the tape but the one-byte stop.

**The record each class carries.**  `LeanLLVM/Refinement/JsonStage2TraceRow.lean`
reads those facts at the byte list the records are stated over
(`TokenBytes.of_input`, then `tape_tokenBytes_null`/`_true_`/`_false_`/`_number`/
`_string`) and hands them to `TokenRecord`'s constructors one class at a time:
`tokenRecord_null_of_tape`, `_true_`, `_false_`, `tokenRecord_number_of_tape`,
`tokenRecord_string_plain_of_tape` and `tokenRecord_string_arena_of_tape`.  The
parser supplies the span and payload; what stays the walk's is the record it
appended — its class, and for a number the `Decimal` whose lexeme is the bytes the
span holds, for a string the form and the remaining slice.

**The payloads, named.**  `tokenRecord_number` and `tokenRecord_string` instantiated
at those records are `row_number_payload_of_tape` and `row_string_payload_of_tape`:
a walked number's bits are `strtodSpec`'s of a well-formed decomposition of exactly
the bytes the token's span holds, and a walked string's slice decodes to the code
points `bodyCodePoints` reads off the span — which `bodyCodePoints_of_stringAt`
derives from the tape's own `StringAt` through `scanChars_iff` and
`scanCharsEnd_ok_of_scanCharsFrom`.  The plain form's `escapeCodePoints` premise is
the walk's reading of a body it emitted unescaped, so the two forms differ only in
where the body lives.

**The row.**  `forall₂_of_position` assembles `List.Forall₂` from length agreement
plus `TokenRecord` at every index, and `walkTraceRow_of_position` is that at
`WalkTraceRow` — the "one record per step" shape a per-arm proof produces, which
`emittedStream_of_row` then turns into `Stage2Records`, `Stage2EventRel` and the
decoded skeleton.  `null_row_of_tape` is the worked instance at the `null`
document's tape, where the record comes from `tokenRecord_null_of_tape` rather than
from a constructor chain.  Every theorem is pinned at `[propext, Quot.sound]`
(`TokenBytes.of_input` at `[propext]`), with no `Classical.choice`, `sorry`,
`admit` or `native_decide`.

### 7.14 The native route's artifact boundaries

The route §7.5's domain describes now runs: `probes/json/route/` builds the Lean
program, its C adapter, the six kernel units at `-O2` and the proved depth
counter, and `check.sh` compares its answers with the reference on the corpus.
What the route installs is not what the proofs read, and
[the artifact boundaries page](json-route-artifact-boundaries.md) records the
distance per unit: each fixture's emission line and capture rewrites, the staged
ABI and the stage-2 helpers' body-versus-model basis, the numeric conversion's
`NumberArmOwed`, and the trust rows a route number rests on.  Hash and rebuild
checks there are identity evidence — the object is that fixture's compilation
under that toolchain — and not compiler-preservation theorems, exactly as row 8
says.

The caller's side is `LeanLLVM/JsonCallRoute.lean`: `routePre` and
`checkRoute` are the wrapper's obligations, and `decodeRouteCall`,
`decodeRecords` and `routeView_decodes` are its reader, stated at
`Stage2EventRel` and the record-for-record `TokenRecord` correspondence, with
the arena at the used extent `ndstU` and the event stream at the reported
cursor.  What neither page claims is a relation between a run of the linked
object and `pipelineUnitsPost`; that is row 9's step, and the route's evidence
for it is the observation `check.sh` makes.

## 8. Out of scope for the first contract

`NaN`/`Infinity` as inputs the first contract's route reasons about, the
decimal-to-binary64 conversion as a proved equivalence (the model's `double`
forms, NaN and infinity included, are modelled and `strtodSpec` computes the
value; that an emitted conversion computes it is owed, and
`JsonStage2NumFastArm` states where the pinned body's proof stops: at the walk's
own `Calls` its three conversion callees are absent, so the conversion's
arithmetic is stuck there, while at the supplied `stage2NumFastCalls` and table
staging the three sites are jumps and the kernel's `w < 2 ^ 64` domain is met by
the body's own word — `JsonStage2NumFastTier3.numFast_ifEnd268_domain` — so what
`NumFastBodyArm` still owes is the conversion's run, and tier 3's three links
are stated in `JsonStage2NumFastTier3`), NDJSON, incremental
input, concurrent parsing, diagnostic text or positions,
and any vector operation the semantics does not model. The modelled vector
forms — `Ty.vec` with integer lanes, `Const.splat`, a vector `load`, lane-wise
`icmp` and integer binops, and `bitcastMask` — are listed in
`docs/capabilities.md`, "Language and IR coverage", with the construct in
`probes/install/ir/json-classify.candidate.ll` that each one serves; the core
extension's forms — the global-symbol operand, `ptrtoint`/`inttoptr`, binary64
and aggregates — are listed there too, with the stage-2 helper body each serves.
Each further extension is a later, explicitly stated change.
