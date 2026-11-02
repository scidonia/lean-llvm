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

## 2. Policy decisions

| Concern | Decision |
|---|---|
| Input encoding | Strict UTF-8; malformed sequences and overlong encodings rejected |
| Byte-order mark | Rejected, as an explicit API policy |
| String escapes | The standard escapes and four-hex-digit `\uXXXX` validated |
| Unicode surrogates | Well-formed pairs required; unpaired escaped surrogates rejected, as a stated Unicode policy |
| Numbers | JSON number grammar enforced; exact lexeme preserved; no `NaN`/`Infinity` extension |
| Duplicate object keys | Preserved in order, including duplicates; no implicit last-wins map |
| Output | A tape with checked spans into the input, plus a unique decoded value |
| Diagnostics | Syntax rejection required; diagnostic text and exact earliest-error position are not part of the equivalence contract |
| Limits | Input length, nesting depth and output capacity are explicit; exhaustion is distinguishable from invalid input |
| Parser reuse | Supported only through explicitly owned reusable buffers; fresh and reused modes are measured separately |

Rejecting unpaired surrogate escapes recognises a strict subset of
grammar-legal JSON. This restriction is deliberate and must be stated wherever
the recogniser theorem is quoted.

## 3. Theorem families and their repository names

Proposed names from the programme map onto the following obligations. A name
may change; the strength may not.

| Obligation | Intended statement | Where it lives |
|---|---|---|
| Reference correctness | `parseRef_sound`, `parseRef_complete`: acceptance and decoding agree with the byte-level JSON semantics, subject to policy and limits | new JSON module |
| Tape interpretation | `tape_valid`, `decodeTape_correct`: spans well formed, nesting and values consistent, decoded meaning correct; a source-backed tape owns its input for its lifetime | new JSON module |
| Block correctness | `scanBlock_correct`: the candidate block operation refines the scalar transition, including next state and error information | new JSON module |
| Whole-scan correctness | `scan_simd_refines_scalar`: blocks, tails and end-of-input finalisation composed | new JSON module |
| Actual LLVM refinement | `scannerLLVM_refines`: the imported baseline and candidate bodies, under this repository's semantics — not two Lean models compared to each other | `LeanLLVM/Vellum/*` + fixtures |
| Contextual replacement | `replaceScanner_sound`: the local statement transported through the parser caller and the linking environment | `RefinesWithinAcross` / `CallRefinesWithin` |
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
and any vector operation the semantics does not model. Each is a later,
explicitly stated extension.
