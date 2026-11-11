# Installation probe: link-time selection at an opaque seam

This probe exercises the installation point described in
`docs/m0-runtime-noise-report.md` and the accompanying design discussion.

- `Caller.lean` sees only `@[extern]` declarations for the seam and an
  implementation marker.
- `probes/install/ir/` holds the emitted IR that the refinement proofs parse,
  pin and prove. `capture.sh` regenerates the three comma-mask fixtures:
  `baseline.ll` and `candidate.ll` from the C emissions, recording the exact
  `clang` and `opt` invocations and the textual syntax removed before the
  parser sees them, and `loop.ll` by printing the Lean AST, with nothing
  removed. `capture-json.sh` regenerates the fourth fixture,
  `json-classify.candidate.ll`, from
  `probes/install/json/classify.candidate.c` at `-O2 -mavx2`, recording the
  same provenance and stripping decisions.
- `Baseline.lean` and `Candidate.lean` are the Lean bodies. `build.sh` compiles
  them as **provenance** objects and compares them with the proved units on a
  differential corpus.
- The installed units are compiled from `ir/baseline.ll` and
  `ir/candidate.ll` plus their marker objects (`ir/marker_*.ll`), so each unit
  is the program the refinement theorem is about rather than a separately
  authored body.
- `ir/loop.ll` is the memory-backed loop. It is printed from the `loopFunction`
  AST in `LeanLLVM/Refinement/CommaMaskLoopBody.lean` by
  `lake exe leanllvm-loop-emit` (`LoopEmit.lean`) through
  `LeanLLVM.Function.render`: the framework's own printer, not Lean's native
  compiler (`lean -c`). `LeanLLVM/Refinement/CommaMaskLoop.lean` parses that file
  and pins it to the same AST before proving a correctness and framed-memory
  statement about it; the certificate for the loop names that statement
  (`loop_refines_candidate_within`: the loop refines the unrolled candidate
  within the band its own two allocations cover), and `UNIT=loop` installs the
  loop from it in strict and non-strict mode. The gate is
  `tests/m4-loop-install-gate.sh`, described below.
- `depth_count` is the stage-1 census kernel `tests/v16/depth_count.ll`, the
  per-function text `LeanLLVM/Refinement/DepthCountRefine.lean` parses and pins
  before proving that the run returns and stores the depth fold `depthSpec`
  (`depth_count_refines`). Its installed object is the fixture plus
  `ir/marker_depth_count.ll`; its certificate names that theorem and the
  propositional boundary `depthContract` (the theorem's own hypothesis set and
  conclusion, with `depthContract_holds` as its witness) rather than the
  comma-mask units' pure `commaContract`, which does not describe a kernel that
  reads a buffer through an index array. Its caller is the corpus driver
  `depth_driver.c`, not the one-word comma seam, so `UNIT=depth_count` links the
  driver. The gate is `tests/m4-depth-install-gate.sh`, and the numeric route is
  `tests/depth-count/check.sh`.
- `json_scan` is the window scanner's certified body `ir/json-scan-body.ll`,
  printed from the `scanWindowBody` AST in
  `LeanLLVM/Refinement/JsonScanBody.lean` by `lake exe leanllvm-json-scan-emit`
  and pinned to that AST by `LeanLLVM/Refinement/JsonScanIR.lean`. The unit is
  known to `select.sh` and to the producer, which name its own theorem
  (`json_scan_theorem`), boundary (`json_scan_contract`) and symbol
  (`json_scan_symbol`), but no certificate can be issued for it: the refinement
  statement is `JsonScanIR.scanWindowStatement`, and it is unproved.  The
  refutation `JsonScanIR.scanWindowStatement_false` is about the body before the
  stop word's fix — it reported `control` where the model refuses with `badUtf8`
  on a continuation byte outside its requirement, and the prose statement's
  band-disjointness hypothesis is load-bearing.  The emitted body's statement was
  then corrected rather than refuted: its frame stops at the state region the
  unit's footprint declares.  A scanner request is refused at
  the covering theorem, and its gate `tests/json-scan-select-gate.sh` refuses at
  the missing `#print axioms` pin before it reaches the selector.
- `build.sh` builds everything in a private staging directory and publishes
  `differential.txt`, `proof_baseline.env`, `proof_candidate.env`,
  `proof_loop.env`, `proof_depth_count.env` and `manifest.env` only after every
  check passes, one file at a time with the
  manifest last, so a failed build leaves the previously published bytes in
  place. The manifest binds the schema, the target triple and data layout, the
  target-feature policy (`none`: the build passes no `-march`/`-mattr`, so
  clang's triple default applies), the contract and every unit's theorem name
  (`theorem` for the candidate and the baseline, `loop_theorem` for the loop,
  `depth_count_theorem` and `depth_contract` for the depth counter, and
  `json_scan_theorem`, `json_scan_contract` and `json_scan_symbol` for the
  window scanner), the
  attribute policy, every fixture and marker hash, the caller, depth-caller and
  unit hashes, the differential transcript as ancillary evidence, and the four
  certificate paths and digests. `select.sh` recomputes the triple and data
  layout from the toolchain and rejects a mismatch.
- `InstallCertificate.lean` is the certificate producer. The imported proof
  graph is rebuilt from current project source, `CommaMaskIR` is re-elaborated
  from source and — for a loop certificate — so is `CommaMaskLoop`, which
  imports it; a depth certificate re-elaborates `DepthCountRefine`, and a
  scanner certificate would re-elaborate `JsonScanIR`, which carries the scanner
  fixture through `include_str`. The
  producer imports those fresh modules, checks the statement of the theorem
  that covers the requested unit, the contract or boundary link and the
  axiom footprint, and writes the certificate described below. The unit dispatch
  is one table with no fall-through: a unit it does not know has no covering
  theorem and no contract, and the producer refuses it by name rather than
  certifying it under the comma-mask pair. It also refuses
  a proof module whose pinned fixture text differs from the file it hashes, so
  a stale module cannot certify changed bytes. `toolchain-id.sh` prints the
  toolchain revision the certificate records.
- `select.sh` verifies the hashes, target and layout, requires the manifest's
  contract and the theorem that covers the requested unit (the global `theorem`
  and `contract` for the candidate and the baseline, `loop_theorem` for the
  loop, `depth_count_theorem` and `depth_contract` for the depth counter, and
  `json_scan_theorem` and `json_scan_contract` for the window scanner),
  **rebuilds each unit from its fixtures**, parses the requested unit's
  certificate as closed data, compares every field with the object, fixture,
  marker, manifest and observed toolchain, and then rebuilds the imported proof
  graph, re-elaborates the proof module and reproduces the certificate with the
  producer, requiring the same bytes. Only then does it link the unit with its
  caller (the depth corpus driver for `UNIT=depth_count`, and the seam's caller
  for `UNIT=json_scan`, which imports the scanner's symbol). An unknown unit is
  refused; `STRICT=1` fails instead of falling back, and a non-strict request
  whose certificate is missing or rejected installs the baseline and records
  the rejection as a fallback. A strict refusal names the certificate field that
  disagreed when the disagreement is a wrong theorem or contract name.
- `build.sh`, the app build and `select.sh` take the
  `.lake/install-certificate.lock` directory around the proof-module rebuilds
  and the producer, so two routes cannot overlap. The install builder holds it
  through the final manifest publication, and the selector holds it from before
  the manifest is sourced through the link and selection record. Lake warm-up
  builds and the fixture
  emitter run through `lake-locked.sh`, which takes the same lock for that one
  command and releases it before the caller's builder runs; the app build takes
  the lock before it removes its previous output and holds it through the
  manifest publication. A contender refuses; a lock directory left by a
  crashed run is removed by hand only after checking that no owner is running.
  A lock that cannot be removed fails the route that held it instead of being
  reported as a warning.
- `check.sh` runs the whole flow, including the proof gate for both pinned
  fixtures, a stale-candidate fallback, a strict-mode rejection, a loop install
  with its own certificate in both modes, a loop-hash-mismatch fallback and
  strict rejection, a depth install with its own certificate in which the
  selection record's object and certificate digests are checked and the
  installed executable's numeric output is compared with `depthSpec`, a
  mutated-fixture failure at the source guard with the
  published bytes asserted unchanged, a stale imported proof source refused by
  the real build and both selector modes under a restoring trap, the full
  certificate-gate matrix (seventeen fields in both modes, three
  absent-certificate routes, four structural malformations and two
  stale-import routes), the loop installation gate in its four modes, the depth
  installation gate in its five modes, the depth numeric scenario with its
  three controls, and the lock, warm-up and release-failure checks.

Run from the repository root:

```bash
nix develop -c bash probes/install/check.sh
nix develop -c bash tests/m3-certificate-gate.sh --strict theorem
nix develop -c bash tests/m3-certificate-gate.sh --fallback theorem
nix develop -c bash tests/m3-certificate-gate.sh --strict proof_candidate
nix develop -c bash tests/m3-certificate-gate.sh --strict-malformed duplicate
nix develop -c bash tests/m4-loop-gate.sh --strict   # no loop theorem or certificate bound: refused
nix develop -c bash tests/m4-loop-gate.sh --fallback # the same manifest falls back to the baseline
nix develop -c bash tests/m4-loop-install-gate.sh --strict          # the loop installs
nix develop -c bash tests/m4-loop-install-gate.sh --strict-theorem  # a wrong theorem is refused
nix develop -c bash tests/m4-loop-install-gate.sh --strict-hash     # a wrong object hash is refused
nix develop -c bash tests/m4-loop-install-gate.sh --fallback-hash   # a wrong hash falls back
nix develop -c bash tests/m4-depth-install-gate.sh --strict           # the depth counter installs
nix develop -c bash tests/m4-depth-install-gate.sh --strict-theorem   # another unit's theorem is refused by name
nix develop -c bash tests/m4-depth-install-gate.sh --strict-contract  # another unit's contract is refused by name
nix develop -c bash tests/m4-depth-install-gate.sh --strict-hash      # another unit's object hash is refused
nix develop -c bash tests/m4-depth-install-gate.sh --fallback-hash    # a wrong hash falls back
nix develop -c bash tests/depth-count/check.sh   # the installed object against depthSpec, with controls
```

`check.sh` must run once before the commands below that read the generated
files. The gate scenarios build their manifest and tool shims in a private
temporary directory, so they exercise the selector without a compiler or a
network.

## What is checked

Two kinds of certificate, with different reach:

1. **Semantic.** `LeanLLVM/Refinement/CommaMaskIR.lean` pins `baseline.ll` and
   `candidate.ll` by parsed AST and proves `Refines candidateFunction
   baselineFunction`; `LeanLLVM/Refinement/CommaMaskLoop.lean` pins the printed
   `loop.ll` to `loopFunction` and proves the loop's correctness and
   framed-memory statements; `LeanLLVM/Refinement/DepthCountRefine.lean` pins
   `tests/v16/depth_count.ll` to `depthFunction` and proves
   `depth_count_refines`, the kernel's returned depth and stored statistics
   against `depthSpec`. The kernel argument for the comma-mask bodies is in
   `CommaMaskKernel.lean`. Axiom footprints are pinned in
   `LeanLLVMTest/Refinement.lean`.
2. **Installation.** `proof_baseline.env`, `proof_candidate.env`,
   `proof_loop.env` and `proof_depth_count.env` are the
   kernel-derived certificates. Each is a deterministic data file with exactly
   these fields, in this order: `schema` (`leanllvm-install-v1`), `unit`, the
   unit's object, fixture and marker hashes, the baseline/candidate object,
   fixture and marker hashes, `theorem`, `axioms`
   (`Classical.choice,Quot.sound,propext`, read from `collectAxioms` rather than
   from printed output), `contract`, `target_triple`, `data_layout` and
   `toolchain_revision` (the `sha256:` of a
   fixed nine-line record over the pin files and the `lean`, `clang` and `ld`
   version output). `theorem` names the statement that covers that unit:
   `LeanLLVM.Refinement.CommaMaskIR.IR_refines` on the baseline's and the
   candidate's certificates,
   `LeanLLVM.Refinement.CommaMaskLoop.loop_refines_candidate_within` on the loop's,
   because `IR_refines` relates the candidate to the baseline and says nothing
   about the memory-backed loop, and
   `LeanLLVM.Refinement.DepthCountRefine.depth_count_refines` on the depth
   counter's. `contract` names `LeanLLVM.Refinement.commaContract` for the
   comma-mask units and `LeanLLVM.Refinement.DepthCountRefine.depthContract` for
   the depth counter: the latter is a proposition — the hypothesis set and
   conclusion of `depth_count_refines`, with `depthContract_holds` as its
   witness — because the pure `BitVec 64 → BitVec 64` structure does not
   describe a kernel that reads through an index array and writes statistics
   words. The producer checks the depth theorem's type against that proposition
   by definitional equality and checks the contract definition's own body, not
   just its name. The selector never sources a certificate: it
   parses the closed grammar, compares each field with the input it names, and
   reproduces the bytes from a fresh kernel check. A manifest digest of a
   certificate only says the file is the byte sequence the manifest names,
   which is why a field mutation, an absent certificate or a malformed one is
   refused even after the digest is repaired.

   `differential.txt` remains ancillary runtime evidence, not a proof. It
   records that the proved units and the Lean-emitted provenance objects agree
   on the corpus, and that each of them agrees with the lane-wise specification
   `diff.c` computes for itself, and it says what it covers:
   `covers: candidate-vs-baseline, loop-vs-candidate`, `not-covered: none`.
   Each installed unit also has a certificate, so the transcript is not offered
   as the proof of any of them. The same detector is
   first shown to reject a seam that returns zero for every input, on a corpus
   word with a comma byte, so its verdict is not an inert pass. A transcript
   that ends `RESULT: PASS` is still never treated as a proof of a unit.

The binding between the proved fixtures and the installed objects is the object
rebuild plus the certificate in `select.sh`: the selector compiles the fixtures
with the same basenames `build.sh` used, requires byte equality with the
installed objects, and accepts a unit only when the manifest names the contract
and the theorem covering that unit, the certificate's fields match those objects
and fixtures, and the producer reproduces the certificate from a fresh kernel
check of that unit. clang records the module name in the object, so the names
are part of the input and a rename is a different object. The depth counter's
caller is the corpus driver, so the selector links the driver with the depth
object rather than the comma-mask caller. A field mutation, a
missing certificate or a malformed certificate is a rejection; non-strict mode
still installs the baseline and records the rejection as a fallback, strict mode
emits nothing.

`lake build` does not track `include_str` inputs, so a changed fixture alone
does not invalidate a cached module. `check.sh` therefore elaborates the proof
modules from source every time, and it mutates a fixture to show that each
pin bites: the candidate mutation makes `CommaMaskIR` fail, the real build route
stops at that guard without publishing a new certificate or manifest, and
selection falls back; the loop mutation makes `CommaMaskLoop`'s `#guard` fail;
both are restored and re-checked. A depth selection re-elaborates
`DepthCountRefine` from source, and the producer refuses that module when its
`include_str` text differs from the fixture file it hashes, so a stale olean
cannot certify changed bytes for any of the four units.

`attributes=reject` records the attribute policy: the fixtures carry none, and
the parser refuses an unmodelled attribute in a function definition's header
rather than dropping it silently -- `tests/m4-loop-emission.sh --return-attr`
and `--function-attr` exercise that at the driver's command line. The loop
fixture needs no stripping: the printer writes the modelled AST, and the
emitter refuses to print unless its own output parses back to the same
function. For `baseline.ll` and `candidate.ll` `capture.sh` removes `noundef`,
`align`, `tbaa`, attribute groups and module-level lines the parser does not
model; the parser would refuse the unstripped text. That removal is justified
per item in the script's comment and is an assertion about the value each
retained instruction computes; it is not a proof that the stripped and original
texts are semantically equivalent, and it does not undo assumptions an
already-compiled caller may have drawn from those attributes. Declaration
headers are not attribute-checked: the parser's `declare` route still accepts
some unmodelled tokens, so the refusal promise covers function definitions, not
`declare` lines.

## Known limits

- The certificate is a hash-and-rebuild bridge, not a theorem about machine
  code. It binds the proved fixture to the installed object by content hash and
  by reproducing the certificate from a fresh kernel check at selection time;
  it does not prove that clang, `ld` or the runtime preserve behaviour, and no
  theorem states compiler/object equivalence. The manifest is still executed as
  shell, so it is trusted to be locally produced: a hostile manifest that runs
  commands or assigns the caller's `req_*` variables is outside the selector's
  defences. A different compiler with the same reported version and bytes, a
  broken hash, or a compromised local proof source are likewise residual
  trusted risks. The attribute policy remains `attributes=reject` over
  attribute-free fixtures; it is not a semantic attribute model.
- The candidate fixture is generated from `ir/candidate_lanes.c`, a lane-by-lane
  transcription of `Candidate.lean`'s fold, not from Lean's own emission of that
  loop. The differential transcript is the evidence that the transcription
  agrees with the Lean body; it is not a proof.
- `ir/loop.ll` is printed from the Lean AST by the framework's printer, so the
  text the proofs parse is what that AST renders to. It is **not** the output of
  Lean's native compiler: a loop produced by `lean -c`, lowered by clang and
  then related to the Lean AST has not been demonstrated, so the
  compilation-chain form of loop provenance is open.
- The loop's certificate names a statement about the loop body and its frame,
  not a compiled-code equivalence. The framed statement in
  `LeanLLVM/Refinement/CommaMaskLoop.lean` relates the loop's returned value and
  the bytes outside the band its own allocations cover, using the general
  relation in `LeanLLVM/Frames.lean` (`AgreesOutsideMem`, `MemPrivate`,
  `AllocFrame`, `RefinesWithin`). The footprint is read off the allocator
  state of the execution rather than written into the theorem, and a write
  outside it fails the relation. `select.sh` therefore installs `UNIT=loop`
  from `proof_loop.env` naming that theorem, on the same hash-and-rebuild
  bridge the other two units use — the object is bound to the proved fixture by
  content hash and by reproducing the certificate from a fresh kernel check, not
  by a theorem about machine code. The `IR_refines` statement still relates only
  the candidate and the baseline; the loop has its own statement and its own
  field.
- The depth counter's certificate names `depth_count_refines` — a theorem about
  the model's execution of the parsed fixture — and `depthContract`, which is
  that theorem's own type stated as a proposition with `depthContract_holds` as
  its witness. It is not a compiled-code equivalence, and it is not a
  `LeanLLVM.Refinement.Contract`: the pure one-word structure cannot express the
  memory and index-array hypotheses. `tests/depth-count/check.sh` compares the
  installed object with `depthSpec` over a fixed corpus, with a tampered
  expectation, a sequential-reader defect and a return-only defect as controls;
  that comparison is runtime
  evidence, not the proof, and the corpus is finite.
- The contextual replacement theorem covers a caller (in the semantics) whose
  body is a call to the seam whose result it returns
  (`LeanLLVM/Refinement/SeamContext.lean`), in both an equality form and the
  directional form of `LeanLLVM/CallRefinement.lean`. The environment is
  deterministic; `none` is `ub`, so a defined target call refines an undefined
  source one but not the reverse. An environment returns the callee's value,
  memory and allocator state, and the caller adopts them; the replacement
  theorem's environment agreement covers all three, so the theorem's frame is
  inert and no contextual replacement whose frame is load-bearing is claimed.
- One toolchain, one target, no benchmark: no timing was measured, and none of
  the checks above is evidence about speed.

Inspect the evidence:

```bash
cat probes/install/build/manifest.env
cat probes/install/build/proof_baseline.env
cat probes/install/build/proof_candidate.env
cat probes/install/build/proof_loop.env
cat probes/install/build/proof_depth_count.env
cat probes/install/build/selection_candidate.env
cat probes/install/build/selection_loop.env
cat probes/install/build/selection_depth_count.env
cat probes/install/build/differential.txt
cat probes/install/build/diff_wrong.txt
cat probes/install/build/out_candidate.txt
cat probes/install/build/out_loop.txt
cat probes/install/build/out_depth_count.txt
cat probes/install/build/out_fallback.txt
cat probes/install/build/gate.log
```
