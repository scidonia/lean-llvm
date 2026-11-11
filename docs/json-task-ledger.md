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
|Byte-level JSON semantics (independent of any parser)|implemented and checked|`LeanLLVM/JSON/Spec.lean`: `Value` (`:24`), `ValueAt` (`:396`), `TextAt`/`RfcText`/`StrictText` (`:466,471,476`), `Policy` (`:482`); the meaning is RFC 8259 §2's grammar as a relation over the bytes, `Utf8Char` is RFC 3629 §4 (`Utf8.lean:19`), and `Policy` is RFC 7493 §2.1's character constraint (`Spec.lean:482`; `IsScalar`/`IsNoncharacter`/`CharAllowed` at `Bytes.lean:232,235,240`), so no parser is consulted|
|Scalar Lean parser: scanner, grammar, tape builder|implemented and checked|`Scan.lean:363` (`scanChars`), `Parse.lean:88,212,385` (`Parsed`, `parseValue`, `parseBytes`), `Tape.lean:50,317` (`Tape`, `decodeTape`); `scanChars_iff` (`Scan.lean:2804`) ties `scanChars` to the strict string-body relation `StrChars .strict` over RFC 3629 §4's `UTF8-char`, and `valid_iff_strict` (`Scan.lean:3068`) ties the strict grammar to RFC 8259 under `Policy`|
|`parseRef_sound`, `parseRef_complete` under policy and limits|implemented and checked|`Correct.lean:2728` and `:4058`; both print `[propext, Quot.sound]` under `#print axioms`, pinned in `LeanLLVMTest/Json.lean:391-413`, as do the corollaries `accepted_is_rfc_text`, `rfc_text_accepted_on_policy`, `parseRef_inputTooLong` and `parseRef_not_invalid_on_valid`|
|`tape_valid`, `decodeTape_correct`|implemented and checked|`TapeCorrect.lean:1041` and `Correct.lean:4110`; same pins. The zero-copy seams are separate theorems — `decoded_number_is_span_bytes` and `decoded_string_is_span_literal`|
|Scalar executable over fixtures|implemented and checked|`JsonMain.lean` (`leanllvm-json`, with the `default`, `depth2`, `tok4` and `in8` limits profiles) runs `tests/json/manifest.tsv`: 130 rows over 130 corpus files, `bash tests/json/check.sh` exit 0 at this revision. The two `#guard` routes, `lake env lean tests/json-api.lean` and `lake env lean tests/json-tape.lean`, also exit 0 at this revision, their byte literals written in the carrier's spelling. They were broken by the carrier change at `77abc35` alone, before that notation update (46 and 53 errors); the X5 readings recorded before it are `d13d633`'s, the run `docs/json-route-evidence.md` records. `lake build` is green (1635 jobs) and `lake build LeanLLVMTest` (828) at this revision|

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
|Structurally different pure candidate emitted as LLVM|done|`probes/install/ir/json-classify.candidate.ll` — the `define` block of `@leanllvm_json_classify32`, regenerated by `probes/install/ir/capture-json.sh` from `probes/install/json/classify.candidate.c` at `-O2 -mavx2`, verified with `opt -passes=verify`, and pinned by `#guard` in `LeanLLVM/Refinement/JsonClassifyIR.lean`|
|`scanBlock_correct` for the pure block operation|done|`LeanLLVM/JSON/ScanBlock.lean:263`, for every `valid ≤ 32` with `ok` reachable only at 32 and the cursor advanced by exactly 32; pins `[propext, Quot.sound]` at `LeanLLVMTest/Json.lean:543`; `JB3` in `tests/json-classify.lean`|
|`scannerLLVM_refines` at the actual LLVM level|done for the candidate against the verified reference|`LeanLLVM/Refinement/JsonClassifyIR.lean:838`: every block readable at `%arg` returns `maskOf block` with the caller's memory intact; `classify32_undefined_of_no_read:853`, `classify32_next_independent:811`. Pins `LeanLLVMTest/Json.lean:1240,1246,1234`; the `Classical.choice` widening is `zip_replicate_right`'s, from core's `Nat.right_eq_add`, attributed at `LeanLLVMTest/Json.lean:1224-1229`. **The baseline-body half is open**: the pair has no baseline LLVM body, so the source side is `maskOfList`|
|`replaceScanner_sound` through a restricted context theorem|done for the staging caller|`LeanLLVM/Refinement/JsonSeam.lean` (`replaceScanner_sound`), proved from `classifySeam_refines` at the caller's one call; `replaceScanner_ret`; negative control `wrongMask_not_refines`; pins `LeanLLVMTest/Refinement.lean:1771-1783`; `JB4`, `JB5`|
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

|Task|Status|Evidence|
|---|---|---|
|One carry and one byte rule: in-string flag, escape-run parity and pending UTF-8 in a single state|done|`LeanLLVM/JSON/ScanBody.lean`: `BodyState:39` carries `inside`, `oddRun` and `utf8`, `bodyStep:136` is the byte rule; `BodyState.init_wellFormed:819` and `BodyState.body_wellFormed:822` establish `WellFormed`, `bodyStep_wellFormed:828` preserves it, and `step_rejects_cont:97`/`step_rejects_lead:101` refuse an out-of-range continuation and a byte no character starts with|
|The UTF-8 requirement accepts exactly `Utf8Char`'s byte counts, so one character advances at most four bytes|done|`utf8Len_iff:753`, `utf8Char_length:767`|
|The window fold: the masks, the first stop, and a refusal rule proved rather than assumed|done|`LeanLLVM/JSON/ScanWindow.lean`: `windowOf:87`, `windowOf_content_agrees:469`, `windowOf_delim:499`, `windowOf_stop_close:564`, `windowOf_stop_spec:845`, `windowOf_quote:873`, `windowOf_backslash:897`, `windowOf_structural:973`, `windowOf_carry:1028`, `windowOf_wellFormed:1036`; the escape-by-parity alternative is refuted by `backslashParityEscapes_not_refines:1084`|
|The window-driven scan takes its boundary from the block operation|done|`LeanLLVM/JSON/ScanString.lean`: `scanStringAt:290` recurs at `(scanBlock …).1.pos`, `scanStringAt_succ:310` pins that wiring, `scanWindow_stop:215`, `scanStringAt_pos:331`|
|Tails and end-of-input finalisation|done|`tailRun:281` passes the remainder as its fuel and reports `.error (.ended, i)` at `open`; `tailRun_ended` (`LeanLLVM/JSON/ScanBlocks.lean:1223`); the run's bounds `bodyRun_bound:345`, `bodyRun_open_bound:375`, `bodyRun_open_at_end:413`, `bodyRun_open_window:450`, `tailRun_open_at:462`|
|The whole-scan statement against the parser's own string scanner|done|`LeanLLVM/JSON/ScanBlocks.lean`: `scan_simd_refines_scalar:1175`, `scanStringBlocks_ok_of_scanCharsEnd:1203`, `scanStringBlocks_refusal:1211`|
|Every new theorem pinned and restated|done|`nix develop -c lake build LeanLLVMTest`; `LeanLLVMTest/Json.lean` pins at `:586-610`, `:659-699`, `:784-820` and `:947-959`, each restated by an `example` in the same section|
|The parser's chain does not reach the model|done|`bash tests/json-import-boundary.sh`|

The vector fragment is **sized from IR** rather than guessed:
`docs/json-scanner-ir-inventory.md` "Consequences" item 2 measures what
`probes/install/ir/json-classify.candidate.ll` contains — a vector type with
splat constants, a vector `load` and no vector `store`, lane-wise `icmp eq` and
one `icmp ult` into `vec n i1`, lane-wise `or` on predicate vectors and `add`
on integer vectors, and `bitcast <32 x i1> → i32`; no shuffle and no target
intrinsic. Cross-byte state (string mask, parity) can stay scalar on the
32-bit masks.

The model is Lean and no module emits it: no stateful scanner over the modelled
vector types exists, and the classifier's body still classifies one block with
no cross-byte state.

## J4 — memory-using LLVM scanner and installation

Missing: a scanner body that writes its index output (the widened vector
`store` is modelled since the entry unit, and the entry unit is itself an
index-emission body — `kernel/json/entry.c`'s two position kernels, proved by
`entry_pos8_refines` and `entry_b8_refines` — but no body joins classification
to emission: J3's model is Lean and emits none, and the loop that would call
both units is the pipeline's, not this tree's),
a baseline body for the pair, and an artifact-bound installation. The
classifier's vector and memory operations **are** modelled and its imported
body **is** refined (`scannerLLVM_refines`), the caller theorem holds for the
staging caller (`replaceScanner_sound`), and the corpus route compares the
installed object against the verified reference — but the route's transcript
is runtime evidence, not a certificate. The installation machinery is ready and
unit-generic; a JSON unit still needs its own expected declarations and a new
unit case in `probes/install/select.sh`.

## J5 — complete parser demonstration

Missing. Requires J1 and J4, an adversarial and differential corpus, and a
measured full-parser improvement.

## J6 — performance refinement and synthesis

Missing. The harness exists and has recorded runs (`probes/bench/bench.sh`,
`b29716c`; the parser three-column scaling comparison at `3159514`, `e46b17f`
and `a0a1df2`, blocker 6), but there is no reproducible comparison against a
native reference, and J5 is still open, so J6 requires J5 and a
native-reference comparison. The scaling comparison shows no quadratic growth
over 4–64 KiB once the parser reads at a position; the measured law is no longer
an obstacle to J6.

## The route's document domain decision

Landed with this record: the route's decision on a document is one certified
predicate, and the scalar parser is its fallback.

|Task|Status|Evidence|
|---|---|---|
|The admission predicate and its clauses|done|`LeanLLVM/JsonKernelDomain.lean`: non-empty, `kernelMaxInput`, the opener-count nesting bound, and the reference character policy through `scanCharsEnd`; `admission`, `admitted`, `documentDecision` and the three outcomes are separate definitions|
|Each clause certified|done|`LeanLLVM/JsonKernelCertificate.lean`: `depthExceeded_openers`, `parseBytes_policyRefusal`, and the capacity exclusion `parseBytes_no_outOfCapacity` (through `parseValue_ne_outOfCapacity`, `tokens_length_le_input`, `tape_valid` and the span discipline). All at `[propext, Quot.sound]`, pinned in the module with a `Classical.choice` control|
|The implication to the record|done|`admission_documentDomain` and `admitted_documentDomain` give non-emptiness, the input bound and the parser's three exclusions; `routeSpecPre` derives `pipelineSpecPre` from `routePre`, so the shell's fast path is inside the record's domain by proof|
|The shell and the fallback|done|`JsonCallRoute.documentDecision`/`checkRoute`: `admitted` (the pipeline answers), `refused` and `fallback` (the reference parser answers, with its own reason or tape). The fallback is consulted for out-of-domain documents only, never as a pre-filter|
|The executable route uses the same definition|done|`probes/json/route/RouteMain.lean` imports `admission` and `parseBytes` (no second scan); `check.sh`: 107 admitted rows agree with the C driver, 14 policy rows and the empty/over-bound/depth-129+ documents fall back with the reference's answers, divergence 0|
|Controls|done|four shell cuts (`depthBound`, the two policy reasons, `inputTooLong`, and the admitted arm) redden their assertions and pass when restored; recorded in `probes/json/route/README.md`|

The direction is recorded in `docs/contract.md` §7.5: the domain is exactly what
the certified checkers decide, the fallback is the current totality mechanism,
and the fast path may later become total by other approaches — each a clause
removed from `admission` with its certificate, the depth clause's opener count
being the first (it is conservative by construction, and the fallback's
acceptance of an opener-rich document is measured by `check.sh`).

## Standing blockers, stated rather than assumed

1. **Vector semantics** — *partly present since J2's WP2* (2026-11-03). `Ty`
   now carries `vec n elem` (`LeanLLVM/Basic.lean:12-20`) and the classifier's
   fragment is modelled: splat constants, lane-wise `icmp` into `<n x i1>`,
   lane-wise integer binops, and `bitcast <n x i1> to iN`
   (`LeanLLVM/Syntax.lean`: `Instr.icmpVec`, `Instr.binopVec`, `Instr.bitcastMask`), with the three element-position refusals in
   the parser. The classifier's emitted body is proved against the modelled
   fragment (`scannerLLVM_refines`, `LeanLLVM/Refinement/JsonClassifyIR.lean:838`).
   Still absent and still blocking the emitted scanner (J4+): `movemask` as a
   form — the mask `bitcast` covers what the bodies extract — and any stateful
   scanner written over the modelled vector types — the classifier classifies
   one block and carries no cross-byte state.  Three items left this list after
   the 2026-11-03 reading: `shufflevector` with a defined mask, the five
   stage-1 intrinsic spellings, and a vector `store`, the last admitted at a
   whole-byte total width; they are checked by `tests/vector-s1.lean` and
   `tests/vector-entry.lean`.
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
4. **Benchmarking** — the seam harness exists and the parser now has a measured
   scaling run. `probes/bench/bench.sh` measures one call to each seam unit
   already installed, linked from `probes/install/build/<unit>.o`, and reports
   medians and minima over repetitions; it presents no ratio as a proof of
   anything, because the certificate says the units agree and the harness only
   says how fast each ran here. A recorded run at `b29716c` measured baseline
   4.55 ns/call and candidate 8.12 ns/call (ratio 1.785) with identical
   checksums. The parser scaling comparison — list carrier at `3159514`,
   pre-fix carrier at `e46b17f`, fixed carrier at `a0a1df2` — is recorded in
   blocker 6: same synthetic documents, input read inside the timed region, a
   floor calibration, medians over repetitions, and an identical-output check
   over the corpus. The scaling instrument itself is now in the
   repository: `probes/bench/JsonBench.lean`, built as `leanllvm-json-bench`, over
   the documents in `probes/bench/json/` and driven by
   `probes/bench/json-bench.sh` (floor first, then the sizes; its `--digest`
   mode covers the timed documents, and the direct
   `leanllvm-json-bench --digest <dir>` form covers any directory, including
   the 130-document corpus). A timed region there
   contains a file read and the parse, and folds the parse's token count into an
   accumulator, because a pure call over a loop-invariant buffer is hoisted out of
   a repetition: a region that stays flat while the wall clock grows is measuring
   nothing, and the instrument reports the repetitions it took so that can be
   seen. There is still no native-reference comparison, so no ratio here is a
   claim against a best-in-class parser.
5. **Unfinished evidence for the module theorem.** The memory-aware module
   theorem is committed and pushed (`376641f`), but its contract corpus is not
   yet in the repository (three setup lines in the untracked
   `tests/call-memory.lean` still need repair) and the axiom pins for the new
   theorems are not yet added to `LeanLLVMTest`.
6. **Parser cost in input size: quadratic under both list-shaped access
   patterns, near-linear once the parser reads at a position.** The working byte
   representation is the contiguous carrier `ByteString` (`ByteArray`) that
   `Bytes` abbreviates, so a byte is read at an index rather than walked to, and
   the theorems are stated over that carrier. The scaling question has been
   measured on the tracked instrument (`probes/bench/JsonBench.lean`, driven by
   `probes/bench/json-bench.sh`) over the same synthetic documents at 4, 16 and
   64 KiB, with the input read inside the timed region, a cheapest-document
   floor first, medians over 21 repetitions for the sizes (the floor
   calibration takes 5), the parse's token count accumulated, and the parse
   results of the 130-document corpus, by
   `leanllvm-json-bench --digest tests/json/corpus`, compared byte for byte:
   under the bench limits 65 documents are accepted and 65 refused, at every
   revision (the manifest's per-row limits profiles accept 62). The three
   columns are the list carrier at `3159514`, the carrier whose scans read by
   index but whose parser still drops a suffix at `e46b17f`, and the carrier
   read at a position throughout at `a0a1df2`. Over 4–64 KiB the exponents are
   **1.97 (list), 2.00 (pre-fix carrier), 1.05 (fixed carrier)**. The fixed
   column's figure is the per-size median over five interleaved 21-repetition
   rounds (1.034; the individual rounds span 0.96–1.04), and the same binaries
   at 5 repetitions give 1.09, so that column's exponent is sensitive to the
   repetition count at the low end. Every row's floor is under 3 % of that
   row, and the accumulated token count is equal across the three revisions at
   each size.
   The container alone did not change the law. At `8f2b445`, one commit after
   the carrier migration at `77abc35` (the two share their library sources;
   `8f2b445` differs only in docs and route tests), every token rebuilt the
   carrier through a list: `drop` is
   `literal (bs.data.toList.drop n)`, so a token handed a dropped suffix paid a
   list view of the whole array and then a copy of the suffix, and
   `spaceRun`/`numRun` built a further list view per token on top of that. The
   carrier's exponent over 4–96 KiB was 2.00 against the list carrier at
   `3159514`'s 1.98, and it was **slower** than that list carrier at every size
   measured. That measurement is what isolated the cause: the representation
   had changed without the access pattern changing. (`Array.extract` is a
   different operation — it is the one copy `tailFrom` makes, not the per-token
   drop.)
   The access pattern is what changes the law. At `e46b17f` the scanners already
   read by index, but the parser still handed them a dropped suffix per token,
   and the exponent is 2.00 — the same quadratic. At `a0a1df2` the scanner
   interface takes an offset (`scanCharsEnd`, `numRunFrom`, `HasPrefixB`) and no
   compiled call site drops a suffix, and the exponent is 1.05: the cost grows
   close to proportionally to the document, with a small residual across the
   range. The carrier read at a position is faster than the list carrier at
   every measured size; the shape alone bought nothing, because at `8f2b445`
   the carrier was slower than the list carrier at `3159514` at every size
   measured. What separates the two carrier columns is the access pattern, and
   that is what the exponent responds to. The quadratic limitation is
   resolved by measurement rather than by argument, and the quadratic term that
   made larger documents impractical at `8f2b445` is not present in the measured
   range.
   Scope of the claim: the measured range is 4–64 KiB on these documents. No
   claim is made about larger documents, about a native-reference comparison, or
   about sizes beyond those measured here; J5 and J6 keep their remaining
   requirements. Only the scaling law, the equality checks and the probe
   protocol are stated here; the timed rows are not reproduced in the tree.
