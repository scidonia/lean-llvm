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
|Fuel semantics with an effect environment: `runFuel`, `Beh`, `Refines`|implemented and checked|`LeanLLVM/Semantics.lean:334` (`Beh`), `:340` (`Refines`); pass `Sound` theorems and their axiom pins in `LeanLLVMTest`|
|A call environment that carries memory and allocator state|implemented and checked|`Semantics.lean:53` (`Calls := String → List Value → Mem → Nat → Option CallOutcome`), `.call` at `:211`; commit `ca81217`|
|Framed memory relation: `AgreesOutsideMem`, `MemConfined`, `Band`, `AllocFrame`, `MemPrivate`|implemented and checked|`LeanLLVM/Frames.lean` (`AgreesOutsideMem:31`, `Band:157`, `AllocFrame:163`); used by the loop certificate|
|Directional environment relation `CallRefines`|implemented and checked|`LeanLLVM/CallRefinement.lean:33`; `Beh_calls_refines` and the instance checks|
|Framed call relation `CallRefinesWithin`|implemented and checked|`CallRefinement.lean:54`; commit `376641f`|
|Contextual replacement across two environments: `RefinesWithinAcross`, `replaceFunction_sound`|implemented and checked for a value-level caller|`LeanLLVM/Vellum/ModuleRefinement.lean`; commit `376641f`|
|Contextual replacement **of a call-taking-memory callee by a real caller**: `loop_seam_within_refines`, `caller_replaces_loop_within`, `memCaller_replaces_loop_within`|implemented and checked for the comma-mask loop only|`ModuleRefinement.lean:220,294,451`; commit `376641f`|
|Tree-level directed simulation `simtt`, `simtt_loop`, bridge to `Refines`|implemented but unverified (no consumer in any pass or route)|`LeanLLVM/ITree/*`; `LeanLLVM/ITree/README.md` states no route reasons through it|
|Loop rule without bounded unrolling (function level)|implemented and checked|`loop_refines_candidate_within` at `LeanLLVM/Vellum/CommaMaskLoop.lean:834`, pinned in `LeanLLVMTest/Vellum.lean`; the general tree-level rule `simtt_loop` (`LeanLLVM/ITree/LoopRule.lean:87`) is implemented but has no consumer|

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
|Parser and printer for the modelled fragment, refusing unmodelled constructs by name|implemented and checked|`LeanLLVM/Parser.lean:104` (`unsupported type '{s}'`), round-trip checks in `LeanLLVMTest/Core.lean`|
|Types|`int w`, `ptr`, `void`, and `vec n elem` — vectors of integer elements are modelled, with `<32 x i8>` and `<32 x i1>` distinct types|`LeanLLVM/Basic.lean:12-20`; `sizeBytes` `Basic.lean:30`; `Value.vec` `Basic.lean:55`, `Value.vecLanes` `Semantics.lean:119`|
|Vector operations, shuffles, mask extraction, AVX2 intrinsics|**implemented but unverified**: splat constants (`Const.splat (n w)(v : BitVec w)`, non-integer splats unrepresentable), lane-wise `icmp` to `vec n i1`, lane-wise integer binops, `bitcast <n x i1> to iN`, and vector type parsing/printing; vector `alloca`/`store`/`select` are refused by name. **Missing**: shuffles, mask extraction (`movemask`), AVX2 intrinsics, and any scanner over them|`LeanLLVM/Syntax.lean:31-35` (`icmpVec`, `binopVec`, `bitcastMask`), `Semantics.lean` (`evalInstr`, `lanesToNat`), `Parser.lean` (vector `expectTy`, `parseSplatValue`, the three element-position refusals); the classifier's emitted fragment is inventoried in `docs/json-scanner-ir-inventory.md`|
|Byte-level JSON semantics, scalar parser, tape|implemented and checked|`LeanLLVM/JSON/Spec.lean` (`Value:22`, `ValueAt:393`, `TextAt:463`, `RfcText:468`, `StrictText:473`, `Policy:479`), `Scan.lean:166` (`scanChars`), `Parse.lean:206,377` (`parseValue`, `parseBytes`), `Tape.lean:48,73,115,314` (`Tape`, `spansWellFormed`, `decodeValue`, `decodeTape`). The six theorems — `parseRef_sound`, `parseRef_complete`, `decodeTape_correct`, `accepted_is_rfc_text`, `rfc_text_accepted_on_policy` (`Correct.lean:2707,4029,4079,4092,4106`) and `tape_valid` (`TapeCorrect.lean:1041`) — each print `[propext, Quot.sound]` under `#print axioms` and are pinned at `LeanLLVMTest/Json.lean:388-410`. Run in this session against the worktree based on `4411f6a`: `lake build` (1627 jobs), `lake build LeanLLVMTest` (824), `lake env lean tests/json-api.lean`, `lake env lean tests/json-tape.lean`, `bash tests/json/check.sh` — all exit 0. Limits: a number keeps its source lexeme and is never converted to a float; nothing SIMD; no LLVM refinement of the parser (J2–J4 are open); the corpus is hand-written|
| Refinement of compiler-emitted bodies for the **pure seam** | implemented and checked | `probes/install/ir/capture.sh:8-11` and `baseline.ll:1-12`: `baseline.ll` is the verbatim `define` block of Lean's own C emission (`lean -c` → clang `-O0` → `opt -passes='function(mem2reg),instnamer'`), with the listed syntax stripped; `CommaMaskIR.IR_refines` (`LeanLLVM/Vellum/CommaMaskIR.lean`) proves the seam over that text, pinned in `LeanLLVMTest/Vellum.lean` |
| Refinement of the **unmodified boxed-`Nat` loop** emission | missing | the loop fixture is the framework printer's output (`LoopEmit.lean`), and the unmodified `lean -c` emission of a memory-backed loop lowers to boxed runtime code (spike at `/tmp/leanllvm-spike1`: `lean_array_set`, `lean_unbox_uint64`, refcounts), which the modelled fragment does not admit |
|Buffer ownership, aliasing and alignment contract|missing|`AllocFrame`/`Band` give a band only; no provenance or alias relation|

## Measurement

|Capability|Status|Evidence|
|---|---|---|
|Benchmark harness or record|missing|`docs/m0-runtime-noise-report.md:323,328` record that "a benchmark remain[s] open" and "no benchmark" as a standing limit; no timing script in the tree|

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
