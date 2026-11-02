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
|IR inventory: baseline compiler output and unsupported constructs|available|`docs/m0-runtime-noise-report.md` §1 records the `lean -c` baseline (13 definitions / 9 declarations, tagged-pointer arithmetic, refcount operations, bounds assertions, three bignum calls), reproducible with `probes/m0/check.sh`; `/tmp/leanllvm-spike1` holds a `-O0` and `-O2` emission of a memory-backed loop. No `.ll` anywhere in the tree contains a vector type|
|Seam identified|done|the opaque external declaration + separate baseline unit, i.e. the route the installation probe already drives (`probes/install/select.sh`, `InstallCertificate.lean`)|
|Inventory unsupported output constructs and separate application runtime noise from work inside the selected unit|available, to be recorded for JSON|`docs/m0-runtime-noise-report.md` §1 for the current baseline; the JSON equivalent waits on J1's compiled output|
|Capture baseline C/LLVM and show the intended call survives caller optimisation|available for the pure seam and the loop, missing for JSON|`probes/install/ir/capture.sh`, `probes/install/check.sh`; the JSON baseline capture waits on J1|
|Establish a repeatable benchmark driver before changing performance-sensitive code|missing|no timing harness exists; this is a J0 task that has not been done and is why J0 is partial|

J0 exit gate: reproducible unchanged builds (met), capability ledger (met),
IR inventory (baseline compiler output recorded; the JSON candidate's is
**blocked** on J2), written trust ledger (met), and a repeatable benchmark
driver (**not done**). J0 is therefore **partially met**, for two separate
reasons recorded above: no candidate to inventory, and no benchmark driver.

## J1 — independent semantics, scalar parser, tape

|Task|Status|
|---|---|
|Byte-level JSON semantics (independent of any parser)|missing|
|Scalar Lean parser: scanner, grammar, tape builder|missing|
|`parseRef_sound`, `parseRef_complete` under policy and limits|missing|
|`tape_valid`, `decodeTape_correct`|missing|
|Scalar executable over fixtures|missing|

Gate: soundness and completeness under the policy and limits; tape meaning
established; the scalar executable runs the corpus.

## J2 — pure block candidate and restricted contextual integration

|Task|Status|
|---|---|
|Structurally different pure candidate emitted as LLVM|missing|
|`scanBlock_correct` for the pure block operation|missing|
|`scannerLLVM_refines` at the actual LLVM level|missing|
|`replaceScanner_sound` through a restricted context theorem|missing|
|IR inventory recorded|missing|

Gate: a pure candidate certified at the LLVM level and called through a checked
restricted context. **Blocked on vector semantics only if the candidate is
vectorised**; a scalar block candidate can proceed on today's fragment.

## J3 — stateful SIMD scanner model

Missing in full: classification, quote/escape logic, UTF-8 state, block
composition, tails, finalisation. Depends on vector semantics in `LeanLLVM`
(`Ty` has no vector constructor today).

## J4 — memory-using LLVM scanner and installation

Missing: memory and vector semantics for the candidate's actual instructions,
`scannerLLVM_refines` for the imported bodies, the caller theorem, and an
artifact-bound installation. The installation machinery is ready and
unit-generic; the semantics and the imported-body refinement are not.

## J5 — complete parser demonstration

Missing. Requires J1 and J4, an adversarial and differential corpus, and a
measured full-parser improvement.

## J6 — performance refinement and synthesis

Missing. Requires a benchmark harness (see below), J5, and reproducible
comparison against a native reference.

## Standing blockers, stated rather than assumed

1. **Vector semantics** — absent. `Ty` is `int w | ptr | void`
   (`LeanLLVM/Basic.lean:12-16`); no vector operations, shuffles, mask
   extraction or AVX2 intrinsics are modelled. Every SIMD milestone waits on
   this, and the host has `avx2` and no `avx512f`.
2. **Compiler-emitted memory-backed bodies** — absent for the unit the JSON
   work needs. The pure seam **is** refined over Lean's own C emission
   (`probes/install/ir/capture.sh:8-11`, `baseline.ll:1-12`,
   `CommaMaskIR.IR_refines`), but the loop fixture is the framework printer's
   output and the unmodified `lean -c` emission of a memory-backed loop lowers
   to boxed runtime code, so that provenance form needs its own plan.
3. **Buffer ownership and aliasing** — absent. `AllocFrame`/`Band` express a
   byte band, not provenance, aliasing or alignment.
4. **Benchmarking** — absent. No timing harness exists; the programme records
   "no benchmark" as a standing limit, so no performance claim can be made or
   refuted yet.
5. **Unfinished evidence for the module theorem.** The memory-aware module
   theorem is committed and pushed (`376641f`), but its contract corpus is not
   yet in the repository (three setup lines in the untracked
   `tests/call-memory.lean` still need repair) and the axiom pins for the new
   theorems are not yet added to `LeanLLVMTest`.
