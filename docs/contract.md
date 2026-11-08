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
| Actual LLVM refinement | `scannerLLVM_refines`: the imported baseline and candidate bodies, under this repository's semantics — not two Lean models compared to each other | `LeanLLVM/Vellum/*` + fixtures. The J2 instance (`LeanLLVM/Vellum/JsonClassifyIR.lean`) is candidate-against-reference: it relates the emitted classifier body to the verified scalar transition's mask, because the pair has no baseline *body* — the fragment has no pointer arithmetic, so no scalar byte-walking body can be written in it — and **the baseline-body half of this obligation remains open**. A second instance, for the stage-1 mask unit, is the same shape and does not close that half either: `s1_masks_refines` (`LeanLLVM/Vellum/JsonS1MasksSteps.lean`) relates the body pinned from `probes/install/ir/json-s1-masks.candidate.ll` to `JsonScanSpec`'s six masks and carry, over a body that stores them, so the related side is emitted text and the reference side is the specification. A third instance, for the entry positions unit, is the same shape again and does not close that half either: `entry_pos8_refines` (`LeanLLVM/Vellum/JsonEntrySteps.lean`) and `entry_b8_refines` (`LeanLLVM/Vellum/JsonB8Steps.lean`) relate the two bodies pinned from `probes/install/ir/json-entry.candidate.ll` to the entry word `JsonEntSpec` specifies — the returned cursor, the words each body writes read as the model's positions, and every byte outside the span its stores reach unchanged — so the related side is again emitted text and the reference side the specification, and the selection that fills the entry stream is not related at all |
| Contextual replacement | `replaceScanner_sound`: the local statement transported through the parser caller and the linking environment | `RefinesWithinAcross` / `CallRefinesWithin`. The J2 instance (`LeanLLVM/Vellum/JsonSeam.lean`) carries the relation through `scanCaller`, a staging caller of its own — not through the JSON parser, which is why the parser half of this obligation stays open |
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
no-borrow form (`LeanLLVM/Vellum/CommaMask.lean:31`) and proves it equal to an
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

## 7. Trust ledger (initial position)

Trusted, and named wherever a result depends on them:

1. The Lean kernel and the approved axioms — the standard footprint
   `[propext, Classical.choice, Quot.sound]`.
2. The semantic definitions as an audited statement of intended LLVM behaviour;
   their agreement with the real LLVM is an assurance obligation, not a result.
3. Lean lowering, clang and the downstream LLVM backend, and the linker.
4. The manifest shell, and the local integrity of the repository it runs in.
5. Any FFI or extern bridge between the Lean function and the compiled unit,
   until a theorem connects them.

Nothing else is trusted. In particular, the certificate is a hash-and-rebuild
bridge: it binds the checked proof artifact to the bytes installed, and it proves
nothing about lowering, linking or machine instructions.

## 8. Out of scope for the first contract

`NaN`/`Infinity`, binary floating-point conversion as a proved equivalence,
NDJSON, incremental input, concurrent parsing, diagnostic text or positions,
and any vector operation the semantics does not model. The modelled vector
forms — `Ty.vec` with integer lanes, `Const.splat`, a vector `load`, lane-wise
`icmp` and integer binops, and `bitcastMask` — are listed in
`docs/capabilities.md`, "Language and IR coverage", with the construct in
`probes/install/ir/json-classify.candidate.ll` that each one serves. Each
further extension is a later, explicitly stated change.
