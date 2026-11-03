# Task ledger — JSON project

Milestones follow the ultra-compilation plan. Status vocabulary matches
`docs/capabilities.md`. A milestone is complete only when its exit gate is met
and the evidence is recorded here.

## J0 — audit, contract, seam

|Task|Status|Evidence|
|---|---|---|
|Record toolchain, target, data layout, revision|done|`docs/capabilities.md` "Environment audited"|
|Unchanged builds and existing gates green|done|`lake build`, `lake build LeanLLVMTest`, both probes, four + four gate modes, 47-run certificate matrix, at `376641f`|
|Capability ledger with the four statuses|done|`docs/capabilities.md`|
|Fixed contract and trust ledger|done|`docs/contract.md`|
|First pure block operation chosen|done|the comma/structural byte-mask classifier; the exact mask is already proved (`CommaMask.lean:19,31,36`, `CommaMaskKernel.lean`)|
|Memory-using scanner boundary chosen|done|`scanBlock (state, block, validByteCount) → (nextState, info, status)` with the input read and the index buffer written; the call boundary that can observe a callee's writes exists as of `ca81217`/`376641f`|
|IR inventory: baseline compiler output and unsupported constructs|available|`docs/m0-runtime-noise-report.md` §1 records the `lean -c` baseline (13 definitions / 9 declarations, tagged-pointer arithmetic, refcount operations, bounds assertions, three bignum calls), reproducible with `probes/m0/check.sh`; `/tmp/leanllvm-spike1` holds a `-O0` and `-O2` emission of a memory-backed loop. At J0 no `.ll` anywhere in the tree contained a vector type; the J2 fixture `probes/install/ir/json-classify.candidate.ll` now does|
|Seam identified|done|the opaque external declaration + separate baseline unit, i.e. the route the installation probe already drives (`probes/install/select.sh`, `InstallCertificate.lean`)|
|Inventory unsupported output constructs and separate application runtime noise from work inside the selected unit|available, to be recorded for JSON|`docs/m0-runtime-noise-report.md` §1 for the current baseline; the JSON equivalent waits on J1's compiled output|
|Capture baseline C/LLVM and show the intended call survives caller optimisation|available for the pure seam and the loop, missing for JSON|`probes/install/ir/capture.sh`, `probes/install/check.sh`; the JSON baseline capture waits on J1|
|Establish a repeatable benchmark driver before changing performance-sensitive code|done|`probes/bench/bench.sh` (driver `probes/bench/driver.c`): median over repetitions, deterministic input stream, identical-checksum guard, and it records revision, toolchain, triple and unit digests. First record at `b29716c`: baseline 4.55 ns/call, candidate 8.12 ns/call, ratio 1.785, both checksums equal|

J0 exit gate: reproducible unchanged builds (met), capability ledger (met),
IR inventory (baseline compiler output recorded, and the recogniser inventory
done — the stateful scanner's inventory follows its candidate), written trust
ledger (met), and a repeatable benchmark driver (met, `probes/bench/bench.sh`).
**J0 is met** for the scope it can reach before a candidate exists.

## J1 — independent semantics, scalar parser, tape

|Task|Status|Evidence|
|---|---|---|
|Byte-level JSON semantics (independent of any parser)|implemented and checked|`LeanLLVM/JSON/Spec.lean`: `Value` (`:22`), `ValueAt` (`:393`), `TextAt`/`RfcText`/`StrictText` (`:463,468,473`), `Policy` (`:479`); the meaning is RFC 8259 §2's grammar as a relation over the bytes, `Utf8Char` is RFC 3629 §4 (`Utf8.lean:17`), and `Policy` is RFC 7493 §2.1's character constraint (`Bytes.lean:82,87`), so no parser is consulted|
|Scalar Lean parser: scanner, grammar, tape builder|implemented and checked|`Scan.lean:166` (`scanChars`), `Parse.lean:88,206,377` (`Parsed`, `parseValue`, `parseBytes`), `Tape.lean:48,314` (`Tape`, `decodeTape`); `scanChars_iff` (`Scan.lean:1500`) ties `scanChars` to the strict string-body relation `StrChars .strict` over RFC 3629 §4's `UTF8-char`, and `valid_iff_strict` (`Scan.lean:1763`) ties the strict grammar to RFC 8259 under `Policy`|
|`parseRef_sound`, `parseRef_complete` under policy and limits|implemented and checked|`Correct.lean:2707` and `:4029`; both print `[propext, Quot.sound]` under `#print axioms`, pinned in `LeanLLVMTest/Json.lean:388-410`, as do the corollaries `accepted_is_rfc_text`, `rfc_text_accepted_on_policy`, `parseRef_inputTooLong` and `parseRef_not_invalid_on_valid`|
|`tape_valid`, `decodeTape_correct`|implemented and checked|`TapeCorrect.lean:1041` and `Correct.lean:4079`; same pins. The zero-copy seams are separate theorems — `decoded_number_is_span_bytes` and `decoded_string_is_span_literal`|
|Scalar executable over fixtures|implemented and checked|`JsonMain.lean` (`leanllvm-json`, with the `default`, `depth2`, `tok4` and `in8` limits profiles) runs `tests/json/manifest.tsv`: 130 rows over 130 corpus files, `bash tests/json/check.sh` exit 0. `lake env lean tests/json-api.lean` and `lake env lean tests/json-tape.lean` exit 0, with `lake build` (1627 jobs) and `lake build LeanLLVMTest` (824). Run in this session against the worktree based on `4411f6a`|

Gate: soundness and completeness under the policy and limits; tape meaning
established; the scalar executable runs the corpus. **Met** on that content:
`parseRef_sound` and `parseRef_complete` under `Policy` and the limits,
`tape_valid` and `decodeTape_correct`, and `bash tests/json/check.sh` over the
130 rows, all at `[propext, Quot.sound]`.

The routes' staged cuts are recorded in `docs/json-route-evidence.md`: the API
route reddens eight refusals including the `01` number case, the corpus route
reddens its tampered-expectation assertion, and the tape route reddens six
guards including `correctTape`.  Those cuts are runtime overrides in
throwaway copies, not edits to definitions that carry proofs; the tape route's
individual span-mismatch refusals are not shown sensitive by a cut, and the
evidence document says so.

C13 is a separate item and is not absorbed into that verdict: it is landed at
this revision — `docs/contract.md` §1.1 names RFC 8259, RFC 3629 and RFC 7493
§2.1 with the clause map, §3 carries the two adherence rows, the strict-subset
note is replaced by the two-direction statement naming unpaired surrogates and
noncharacters, and the rows above name the three standards.

## J2 — pure block candidate and restricted contextual integration

|Task|Status|Evidence|
|---|---|---|
|Structurally different pure candidate emitted as LLVM|done|`probes/install/ir/json-classify.candidate.ll` — the `define` block of `@leanllvm_json_classify32`, regenerated by `probes/install/ir/capture-json.sh` from `probes/install/json/classify.candidate.c` at `-O2 -mavx2`, verified with `opt -passes=verify`, and pinned by `#guard` in `LeanLLVM/Vellum/JsonClassifyIR.lean`|
|`scanBlock_correct` for the pure block operation|done|`LeanLLVM/JSON/ScanBlock.lean:228`, for every `valid ≤ 32` with `ok` reachable only at 32 and the cursor advanced by exactly 32; pins `[propext, Quot.sound]` at `LeanLLVMTest/Json.lean:498`; `JB3` in `tests/json-classify.lean`|
|`scannerLLVM_refines` at the actual LLVM level|done for the candidate against the verified reference|`LeanLLVM/Vellum/JsonClassifyIR.lean:838`: every block readable at `%arg` returns `maskOf block` with the caller's memory intact; `classify32_undefined_of_no_read:853`, `classify32_next_independent:811`. Pins `LeanLLVMTest/Json.lean:537,543,549`; the `Classical.choice` widening is `zip_replicate_right`'s, from core's `Nat.right_eq_add`, attributed at `LeanLLVMTest/Json.lean:530-535`. **The baseline-body half is open**: the pair has no baseline LLVM body, so the source side is `maskOfList`|
|`replaceScanner_sound` through a restricted context theorem|done for the staging caller|`LeanLLVM/Vellum/JsonSeam.lean:552`, proved from `classifySeam_refines:335` at the caller's one call; `replaceScanner_ret:589`; negative control `wrongMask_not_refines:692`; pins `LeanLLVMTest/Vellum.lean:1771-1783`; `JB4`, `JB5`|
|IR inventory recorded|done|`docs/json-scanner-ir-inventory.md` "Consequences" item 2; the counts are asserted by `probes/install/ir/capture-json.sh`|

Gate: a pure candidate certified at the LLVM level and called through a checked
restricted context. **Met at `554ce4a`** on that content: the emitted body, the
block operation, the seam and the corpus route. What the gate does **not**
cover: a baseline body (there is none in the fragment), a parser routed through
the classifier (the caller is a staging caller, `scanCaller`), the object's
behaviour on unaligned pointers, an artifact-bound installation (the route
records `sha256` in a transcript, not a certificate), and any performance
claim.

## J3 — stateful SIMD scanner model

Missing: quote/escape logic, UTF-8 state, block composition, tails and
finalisation. The vector fragment is **sized from IR** rather than guessed:
`docs/json-scanner-ir-inventory.md` "Consequences" item 2 measures what
`probes/install/ir/json-classify.candidate.ll` contains — a vector type with
splat constants, a vector `load` and no vector `store`, lane-wise `icmp eq` and
one `icmp ult` into `vec n i1`, lane-wise `or` on predicate vectors and `add`
on integer vectors, and `bitcast <32 x i1> → i32`; no shuffle and no target
intrinsic. Cross-byte state (string mask, parity) can stay scalar on the
32-bit masks.

## J4 — memory-using LLVM scanner and installation

Missing: the stateful scanner (J3), a scanner body that writes its index output
(no vector `store` is modelled and no index-emission body exists), a baseline
body for the pair, and an artifact-bound installation. The classifier's vector
and memory operations **are** modelled and its imported body **is** refined
(`scannerLLVM_refines`), the caller theorem holds for the staging caller
(`replaceScanner_sound`), and the corpus route compares the installed object
against the verified reference — but the route's transcript is runtime
evidence, not a certificate. The installation machinery is ready and
unit-generic; a JSON unit still needs its own expected declarations and a new
unit case in `probes/install/select.sh`.

## J5 — complete parser demonstration

Missing. Requires J1 and J4, an adversarial and differential corpus, and a
measured full-parser improvement.

## J6 — performance refinement and synthesis

Missing. The harness exists and has a recorded run (`probes/bench/bench.sh`,
`b29716c`; see blocker 4), but there is no parser timing and no reproducible
comparison against a native reference; J6 requires J5 and that comparison.

## Standing blockers, stated rather than assumed

1. **Vector semantics** — *partly present since J2's WP2* (2026-11-03). `Ty`
   now carries `vec n elem` (`LeanLLVM/Basic.lean:12-20`) and the classifier's
   fragment is modelled: splat constants, lane-wise `icmp` into `<n x i1>`,
   lane-wise integer binops, and `bitcast <n x i1> to iN`
   (`LeanLLVM/Syntax.lean:31-35`), with the three element-position refusals in
   the parser. The classifier's emitted body is proved against the modelled
   fragment (`scannerLLVM_refines`, `LeanLLVM/Vellum/JsonClassifyIR.lean:838`).
   Still absent and still blocking J3+: shuffles, mask extraction, AVX2
   intrinsics, a vector store, and any stateful scanner written over the
   modelled vector types — the classifier classifies one block and carries no
   cross-byte state.
   `docs/capabilities.md` carries the same status. The host has `avx2` and no
   `avx512f`.
   *(Before this date the row read "absent — `Ty` is `int w | ptr | void`"; that
   stopped being true at `694e5d7`'s successor and is corrected here rather than
   left to be discovered.)*
2. **Compiler-emitted memory-backed bodies** — absent for the unit the JSON
   work needs. The pure seam **is** refined over Lean's own C emission
   (`probes/install/ir/capture.sh:8-11`, `baseline.ll:1-12`,
   `CommaMaskIR.IR_refines`), but the loop fixture is the framework printer's
   output and the unmodified `lean -c` emission of a memory-backed loop lowers
   to boxed runtime code, so that provenance form needs its own plan.
3. **Buffer ownership and aliasing** — absent. `AllocFrame`/`Band` express a
   byte band, not provenance, aliasing or alignment.
4. **Benchmarking** — the harness exists, the parser is unmeasured.
   `probes/bench/bench.sh` measures one call to each seam unit already
   installed, linked from `probes/install/build/<unit>.o`, and reports medians
   and minima over repetitions; it presents no ratio as a proof of anything,
   because the certificate says the units agree and the harness only says how
   fast each ran here. A recorded run at `b29716c` measured baseline
   4.55 ns/call and candidate 8.12 ns/call (ratio 1.785) with identical
   checksums. There is no parser timing and no native-reference comparison —
   J5 and J6 are open — so nothing in the corpus or parser is measured, and the
   seam numbers are not a parser number.
5. **Unfinished evidence for the module theorem.** The memory-aware module
   theorem is committed and pushed (`376641f`), but its contract corpus is not
   yet in the repository (three setup lines in the untracked
   `tests/call-memory.lean` still need repair) and the axiom pins for the new
   theorems are not yet added to `LeanLLVMTest`.
6. **Known limitation: parser cost is quadratic in input size.** The working
   byte representation (`List UInt8`) makes per-token access cost grow with the
   token's position, so document cost grows with the square of the input;
   documents of hundreds of kilobytes are not practical until the
   representation and the access pattern change together. The theorems are
   stated over `List UInt8`, so re-stating the lemmas that index a byte string
   is the price of that change, not a local edit. Tracked as J3's opening
   question.
