# Capability ledger — JSON project against lean-llvm

Ledger statuses: **implemented and checked**, **implemented but unverified**,
**missing**, **out of scope**. Every "checked" row names the command that
produced the evidence and the revision it was run at.

## Environment audited

|Item|Value|Evidence|
|---|---|---|
|Repository revision|`376641f`|`git log --oneline -1`|
|Lean|`4.35.0`, Release, from the flake (binary-cached)|`nix develop -c lean --version`|
|C / LLVM|clang, opt `21.1.8`|`nix develop -c clang --version`, `opt --version`|
|Target|`x86_64-unknown-linux-gnu`|`clang -print-target-triple`; `probes/install/build/manifest.env` `target=`|
|Data layout|`e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128`|`probes/install/build/manifest.env` `datalayout=`|
|Host features|`avx2` present; no `avx512f`|`grep -o 'avx2\|avx512f' /proc/cpuinfo \| sort -u`|
|Build, unchanged|`lake build` 812–1609 jobs, `lake build LeanLLVMTest` 814 jobs, both exit 0|this session, at `376641f`|
|Probes and gates|install and app probes `ok`; four `m4-loop-gate` modes; four `m4-loop-install-gate` modes; 47-run certificate matrix|this session, at `376641f`|

## Semantics and refinement

|Capability|Status|Evidence|
|---|---|---|
|Fuel semantics with an effect environment: `runFuel`, `Beh`, `Refines`|implemented and checked|`LeanLLVM/Semantics.lean:405` (`Beh`), `:411` (`Refines`); pass `Sound` theorems and their axiom pins in `LeanLLVMTest`|
|A call environment that carries memory and allocator state|implemented and checked|`Semantics.lean:53` (`Calls := String → List Value → Mem → Nat → Option CallOutcome`), `.call` at `:257`; commit `ca81217`|
|Framed memory relation: `AgreesOutsideMem`, `MemConfined`, `Band`, `AllocFrame`, `MemPrivate`|implemented and checked|`LeanLLVM/Frames.lean` (`AgreesOutsideMem:31`, `Band:157`, `AllocFrame:163`); used by the loop certificate|
|Directional environment relation `CallRefines`|implemented and checked|`LeanLLVM/CallRefinement.lean:33`; `Beh_calls_refines` and the instance checks|
|Framed call relation `CallRefinesWithin`|implemented and checked|`CallRefinement.lean:54`; commit `376641f`|
|Contextual replacement across two environments: `RefinesWithinAcross`, `replaceFunction_sound`|implemented and checked for a value-level caller|`LeanLLVM/Vellum/ModuleRefinement.lean`; commit `376641f`|
|Contextual replacement **of a call-taking-memory callee by a real caller**: `loop_seam_within_refines`, `caller_replaces_loop_within`, `memCaller_replaces_loop_within`|implemented and checked for the comma-mask loop only|`ModuleRefinement.lean:225,303,465`; commit `376641f`|
|Tree-level directed simulation `simtt`, `simtt_loop`, bridge to `Refines`|implemented but unverified (no consumer in any pass or route)|`LeanLLVM/ITree/*`; `LeanLLVM/ITree/README.md` states no route reasons through it|
|Loop rule without bounded unrolling (function level)|implemented and checked|`loop_refines_candidate_within` at `LeanLLVM/Vellum/CommaMaskLoop.lean:839`, pinned in `LeanLLVMTest/Vellum.lean`; the general tree-level rule `simtt_loop` (`LeanLLVM/ITree/LoopRule.lean:87`) is implemented but has no consumer|

## Installation, certificate and policy

|Capability|Status|Evidence|
|---|---|---|
|Certificate producer, seventeen fields, per-unit theorem and axiom footprint|implemented and checked|`probes/install/InstallCertificate.lean`; `probes/install/check.sh` `ok`|
|Selector with strict refusal, fallback and lease/lock discipline|implemented and checked|`probes/install/select.sh`; `tests/m3-certificate-gate.sh` (47 runs), `tests/m4-loop-install-gate.sh`|
|Attribute policy|implemented and checked, but only `reject`|`select.sh:435`; any richer policy is **missing**|
|Certificate as a hash-and-rebuild bridge, not a theorem about compiled code|out of scope (declared trust)|`docs/lean-vellum-development-programme.md` §7; stated at every certificate|
|The manifest is executed as shell; its integrity is assumed|out of scope (declared trust)|same section|

## Language and IR coverage

|Capability|Status|Evidence|
|---|---|---|
|Parser and printer for the modelled fragment, refusing unmodelled constructs by name|implemented and checked|`LeanLLVM/Parser.lean:109-110` (`unsupported type '{s}'`), vector types at `:116` (`expectTy`), round-trip checks in `LeanLLVMTest/Core.lean`|
|Types|`int w`, `ptr`, `void`, and `vec n elem` — vectors of integer elements are modelled, with `<32 x i8>` and `<32 x i1>` distinct types|`LeanLLVM/Basic.lean:12-20`; `sizeBytes` `Basic.lean:26`; `Value.vec` `Basic.lean:55`, `Value.vecLanes` `Semantics.lean:119`|
|Vector operations, shuffles, mask extraction, AVX2 intrinsics|**implemented and checked for the six forms the classifier's body uses**: `Ty.vec` with integer lanes, splat constants (`Const.splat (n w)(v : BitVec w)`, non-integer splats unrepresentable), a vector `load`, lane-wise `icmp` to `vec n i1`, lane-wise integer binops, and `bitcast <n x i1> to iN`, with vector type parsing/printing; vector `alloca`/`store`/`select` are refused by name, vector `icmp` is confined to `eq` and `ult` (`Parser.lean:341-343`), and the five lane-wise integer binops `or`/`and`/`xor`/`add`/`sub` are admitted (`Parser.lean:252`; per lane at `Semantics.lean:272-281`), of which the body uses `or` and `add`; a vector `shl` is refused. **Missing**: shuffles, mask extraction (`movemask`), `llvm.vector.reduce.*`, AVX2 intrinsics, a vector store, `getelementptr`, and any stateful scanner over the modelled types|`LeanLLVM/Syntax.lean:31-35` (`icmpVec`, `binopVec`, `bitcastMask`), `Semantics.lean:198` (`evalInstr`), `:127` (`lanesToNat`), `Parser.lean:116` (`expectTy`), `:188` (`parseSplatValue`), `:197` (`parseOperand`, the three element-position refusals); the proofs are `scannerLLVM_refines` (`LeanLLVM/Vellum/JsonClassifyIR.lean:838`) and `scanBlock_correct` (`LeanLLVM/JSON/ScanBlock.lean:228`), and the emitted fragment is inventoried in `docs/json-scanner-ir-inventory.md`|
|Byte-level JSON semantics, scalar parser, tape|implemented and checked|`LeanLLVM/JSON/Spec.lean` (`Value:22`, `ValueAt:393`, `TextAt:463`, `RfcText:468`, `StrictText:473`, `Policy:479`), `Scan.lean:166` (`scanChars`), `Parse.lean:206,377` (`parseValue`, `parseBytes`), `Tape.lean:48,73,115,314` (`Tape`, `spansWellFormed`, `decodeValue`, `decodeTape`). The six theorems — `parseRef_sound`, `parseRef_complete`, `decodeTape_correct`, `accepted_is_rfc_text`, `rfc_text_accepted_on_policy` (`Correct.lean:2707,4029,4079,4092,4106`) and `tape_valid` (`TapeCorrect.lean:1041`) — each print `[propext, Quot.sound]` under `#print axioms` and are pinned at `LeanLLVMTest/Json.lean:388-410`. Run in this session against the worktree based on `4411f6a`: `lake build` (1627 jobs), `lake build LeanLLVMTest` (824), `lake env lean tests/json-api.lean`, `lake env lean tests/json-tape.lean`, `bash tests/json/check.sh` — all exit 0. Limits: a number keeps its source lexeme and is never converted to a float; SIMD classification is certified at the IR level (`scannerLLVM_refines`, `LeanLLVM/Vellum/JsonClassifyIR.lean:838`, over `probes/install/ir/json-classify.candidate.ll`), but **no LLVM refinement of the parser** exists: the classifier is called by a staging caller (`LeanLLVM/Vellum/JsonSeam.lean`), not through the parser; the corpus is hand-written|
| Refinement of compiler-emitted bodies for the **pure seam** | implemented and checked | `probes/install/ir/capture.sh:8-11` and `baseline.ll:1-12`: `baseline.ll` is the verbatim `define` block of Lean's own C emission (`lean -c` → clang `-O0` → `opt -passes='function(mem2reg),instnamer'`), with the listed syntax stripped; `CommaMaskIR.IR_refines` (`LeanLLVM/Vellum/CommaMaskIR.lean`) proves the seam over that text, pinned in `LeanLLVMTest/Vellum.lean` |
| Refinement of the **unmodified boxed-`Nat` loop** emission | missing | the loop fixture is the framework printer's output (`LoopEmit.lean`), and the unmodified `lean -c` emission of a memory-backed loop lowers to boxed runtime code (spike at `/tmp/leanllvm-spike1`: `lean_array_set`, `lean_unbox_uint64`, refcounts), which the modelled fragment does not admit |
|JSON block layer: the mask and the block operation|implemented and checked|`LeanLLVM/JSON/ScanBlock.lean`: `IsStructuralB:19` marks the eight bytes `"` `\` `:` `,` `{` `}` `[` `]`, and `IsStructOrSpaceB:24` adds RFC 8259 §2 `ws`; `maskOfList:29` is the scalar transition, `Block32:38`, `maskOf:41`, `ScanState:47` (the cursor, `pos`, alone), `BlockStatus:58` (availability, not validity), `scanBlock:67`. Read back per lane by `maskOfList_getLsbD:184`, with `maskOfList_take:198`, `ofFn_of_length:206` and `tab_newline_range:218` (the body's tab/newline range test); `scanBlock_correct:228` holds for every `valid ≤ 32`, with `ok` only at 32 and the cursor advanced by exactly 32. Pins `[propext, Quot.sound]` at `LeanLLVMTest/Json.lean`: `maskOfList_getLsbD:478`, `maskOfList_take:486`, `ofFn_of_length:490`, `tab_newline_range:494`, `scanBlock_correct:498` (the `rfl` lemma `maskOf_eq_maskOfList:482` is `[propext]` alone and is outside that claim); `JB3` in `tests/json-classify.lean`|
|Emitted classifier body, checked at the LLVM level|implemented and checked, candidate against the verified reference|`probes/install/ir/json-classify.candidate.ll` is the `define` block of `@leanllvm_json_classify32` at `-O2 -mavx2`, regenerated by `probes/install/ir/capture-json.sh` and verified by `opt -passes=verify`; `LeanLLVM/Vellum/JsonClassifyIR.lean:38` includes it and `:93` pins the parsed AST. `scannerLLVM_refines:838`: for every block readable at `%arg` the body returns `maskOf block` and the caller's memory unchanged; `classify32_undefined_of_no_read:853` where it is not readable; `classify32_next_independent:811` removes the allocator-state dependence. Axioms `[propext, Classical.choice, Quot.sound]` for the first and third and `[propext, Quot.sound]` for the second (`LeanLLVMTest/Json.lean:537,543,549`), the widening carried by `zip_replicate_right` from core's `Nat.right_eq_add`, attributed beside the pins at `LeanLLVMTest/Json.lean:530-535`. **The baseline-body half is not demonstrated**: the pair has no baseline LLVM body, so the source side is the verified scalar transition (`envForMask`, `JsonSeam.lean:52`)|
|The JSON seam and a caller of its own|implemented and checked for the staging caller|`LeanLLVM/Vellum/JsonSeam.lean`: `envForMask:52` is the reference, `envForBodySym:70` the installed body, `scanCaller:104` stages four `i64` words into locals from address 1 and is pinned to `probes/install/ir/json-caller.ll` at `:126`, printed by `lake exe leanllvm-json-emit`; `classifySeam_refines:335`, `replaceScanner_sound:552` at `fun _ => False` and proved from the relation at the caller's one call, `replaceScanner_ret:589`, negative control `wrongMask_not_refines:692`. Pins `[propext, Classical.choice, Quot.sound]` at `LeanLLVMTest/Vellum.lean:1771-1783`; `JB4`, `JB5`|
|Installed classifier object against the verified reference over the corpus|implemented and checked on aligned windows|`nix develop -c bash tests/json-classify/check.sh` exits 0 at `554ce4a`: the committed mixed block is the runner's own emission, 9 manifest rows agree with hand-written masks, 70 corpus windows over 130 files with boundary counts `pad31` 0, `pad32` 1, `pad33` 2, `pad64` 33, `pad65` 34, and the object rebuilt from the fixture agrees with the Lean body on 71 windows; the defect object differing in the comma class differs only at `tests/json-classify/mixed.block` offset 0 (`0x7bd6f7b7` → `0x7bd4f7a7`), and a tampered expectation is a mismatch. The 70 corpus windows are all `0xffffffff`, so they are a **no-regression** set and the mixed block is the discriminator. `probes/json/classify_driver.c` stages each window in a 32-byte-aligned buffer, so the arm claims agreement on aligned windows only: the object needs **16-byte** alignment in this build (`clang -c`, no `-mavx2`) and **32** under `-mavx2`, and the fixture's load carries no alignment clause because `Instr.load` has no field for one. The transcript is runtime evidence, not a certificate|
|Refinement of the parser through the classifier|**missing**|no theorem connects `LeanLLVM/JSON`'s parser to the classifier; `tests/json/check.sh` and the two `#guard` routes are a no-regression control over the unchanged parser, not a refinement claim|
|Buffer ownership, aliasing and alignment contract|missing|`AllocFrame`/`Band` give a band only; no provenance or alias relation|

## Measurement

|Capability|Status|Evidence|
|---|---|---|
|Benchmark harness or record|implemented and checked for the seam units only|`probes/bench/bench.sh:1-12` (driver `probes/bench/driver.c`) measures one call to each installed seam unit linked from `probes/install/build/<unit>.o`, reporting medians and minima over repetitions and presenting no ratio as proof — "the certificate says the units agree, this harness only says how fast each one ran here". A recorded run at `b29716c` measured baseline 4.55 ns/call and candidate 8.12 ns/call (ratio 1.785) with identical checksums (`docs/json-task-ledger.md:21`). **No parser timing and no native-reference comparison**: J5 and J6 are open, so the corpus and parser are unmeasured and the seam numbers are not a parser number|

## Directly reusable for the JSON work

1. **The exact comma mask is already proved.** `LeanLLVM/Vellum/CommaMask.lean:19` defines the
   per-lane exact `spec`, `:31` the no-borrow `swar`, `:36` the lane fold
   `byteLoop`; `CommaMaskKernel.lean` proves both meet `spec` per lane. On the
   document's own regression input `x = 0x0000000000002D2C`:
   `plain subtraction idiom → 32896 (0x8080)`, `swar → 128 (0x80)`,
   `spec → 128 (0x80)`, `decide (swar x = spec x) → true`.
   The subtraction-based idiom is **not** used here, and the regression is
   recorded below as a required test rather than a discovered defect.
2. **A call can now write memory and be observed by its caller** — the scanner
   boundary the JSON work needs is the one this repository just built.
3. **The installation gate's per-unit mechanism generalises, but the gate as
   shipped is not unit-generic.** A per-unit theorem field exists (`loop_theorem`)
   and is checked, yet `probes/install/select.sh:121-126` hardcodes the expected
   theorem, contract, symbol and marker for the three units it knows, and
   `:280-283,391-393,518-520,552-554` dispatch exactly `baseline|candidate|loop`.
   A JSON scanner unit therefore needs its own expected declarations and a new
   unit case, not merely a certificate.
