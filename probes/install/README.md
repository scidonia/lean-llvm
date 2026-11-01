# Installation probe: link-time selection at an opaque seam

This probe exercises the installation point described in
`docs/m0-runtime-noise-report.md` and the accompanying design discussion.

- `Caller.lean` sees only `@[extern]` declarations for the seam and an
  implementation marker.
- `probes/install/ir/` holds the emitted IR that the refinement proofs parse,
  pin and prove. `capture.sh` regenerates all three fixtures: `baseline.ll` and
  `candidate.ll` from the C emissions, recording the exact `clang` and `opt`
  invocations and the textual syntax removed before the parser sees them, and
  `loop.ll` by printing the Lean AST, with nothing removed.
- `Baseline.lean` and `Candidate.lean` are the Lean bodies. `build.sh` compiles
  them as **provenance** objects and compares them with the proved units on a
  differential corpus.
- The installed units are compiled from `ir/baseline.ll` and
  `ir/candidate.ll` plus their marker objects (`ir/marker_*.ll`), so each unit
  is the program the refinement theorem is about rather than a separately
  authored body.
- `ir/loop.ll` is the memory-backed loop. It is printed from the `loopFunction`
  AST in `LeanLLVM/Vellum/CommaMaskLoopBody.lean` by
  `lake exe leanllvm-loop-emit` (`LoopEmit.lean`) through
  `LeanLLVM.Function.render`: the framework's own printer, not Lean's native
  compiler (`lean -c`). `LeanLLVM/Vellum/CommaMaskLoop.lean` parses that file
  and pins it to the same AST before proving a correctness and framed-memory
  statement about it. No checked theorem binds that object to the seam's
  contract, so `UNIT=loop` is refused: strict mode fails and non-strict mode
  installs the baseline. The gate is `bash tests/m4-loop-gate.sh`, described
  below.
- `build.sh` builds everything in a private staging directory and publishes
  `differential.txt`, `proof_baseline.env`, `proof_candidate.env` and
  `manifest.env` only after every check passes, one file at a time with the
  manifest last, so a failed build leaves the previously published bytes in
  place. The manifest binds the schema, the target triple and data layout, the
  target-feature policy (`none`: the build passes no `-march`/`-mattr`, so
  clang's triple default applies), the contract and theorem names, the
  attribute policy, every fixture and marker hash, the caller and unit hashes,
  the differential transcript as ancillary evidence, and the two certificate
  paths and digests. `select.sh` recomputes the triple and data layout from the
  toolchain and rejects a mismatch.
- `InstallCertificate.lean` is the certificate producer. The imported proof
  graph is rebuilt from current project source and `CommaMaskIR` is then
  re-elaborated from source; the producer imports that fresh module, checks
  `IR_refines`'s statement, the `commaContract` link and the axiom footprint,
  and writes the certificate described below. It also refuses a proof module
  whose pinned fixture text differs from the file it hashes, so a stale module
  cannot certify changed bytes. `toolchain-id.sh` prints the toolchain
  revision the certificate records.
- `select.sh` verifies the hashes, target and layout, requires the manifest's
  `theorem` and `contract` to be the installation ones, **rebuilds each unit
  from its fixtures**, parses the requested unit's certificate as closed data,
  compares every field with the object, fixture, marker, manifest and observed
  toolchain, and then rebuilds the imported proof graph, re-elaborates the
  proof module and reproduces the certificate with the producer, requiring the
  same bytes. Only then does it link. `UNIT=loop` and an unknown unit are
  refused; `STRICT=1` fails instead of falling back, and a non-strict request
  whose certificate is missing or rejected installs the baseline and records
  the rejection as a fallback.
- `build.sh`, the app build and `select.sh` take the
  `.lake/install-certificate.lock` directory around the imported-graph
  rebuild, the proof-module olean rewrite and the producer, so two routes
  cannot overlap. The install builder holds it through the final manifest
  publication, and the selector holds it from before the manifest is sourced
  through the link and selection record. Lake warm-up builds and the fixture
  emitter run through `lake-locked.sh`, which takes the same lock for that one
  command and releases it before the caller's builder runs; the app build takes
  the lock before it removes its previous output and holds it through the
  manifest publication. A contender refuses; a lock directory left by a
  crashed run is removed by hand only after checking that no owner is running.
  A lock that cannot be removed fails the route that held it instead of being
  reported as a warning.
- `check.sh` runs the whole flow, including the proof gate for both pinned
  fixtures, a stale-candidate fallback, a strict-mode rejection, a refused loop
  with baseline fallback, a mutated-fixture failure at the source guard with the
  published bytes asserted unchanged, a stale imported proof source refused by
  the real build and both selector modes under a restoring trap, the full
  certificate-gate matrix (seventeen fields in both modes, three
  absent-certificate routes, four structural malformations and two
  stale-import routes), and the lock, warm-up and release-failure checks.

Run from the repository root:

```bash
nix develop -c bash probes/install/check.sh
nix develop -c bash tests/m3-certificate-gate.sh --strict theorem
nix develop -c bash tests/m3-certificate-gate.sh --fallback theorem
nix develop -c bash tests/m3-certificate-gate.sh --strict proof_candidate
nix develop -c bash tests/m3-certificate-gate.sh --strict-malformed duplicate
nix develop -c bash tests/m4-loop-gate.sh --strict   # the loop is refused
nix develop -c bash tests/m4-loop-gate.sh --fallback # the baseline is installed
```

`check.sh` must run once before the commands below that read the generated
files. The gate scenarios build their manifest and tool shims in a private
temporary directory, so they exercise the selector without a compiler or a
network.

## What is checked

Two certificates, with different reach:

1. **Semantic.** `LeanLLVM/Vellum/CommaMaskIR.lean` pins `baseline.ll` and
   `candidate.ll` by parsed AST and proves `Refines candidateFunction
   baselineFunction`; `LeanLLVM/Vellum/CommaMaskLoop.lean` pins the printed
   `loop.ll` to `loopFunction` and proves the loop's correctness and
   framed-memory statements. The kernel argument for the two bodies is in
   `CommaMaskKernel.lean`. Axiom footprints are pinned in
   `LeanLLVMTest/Vellum.lean`.
2. **Installation.** `proof_baseline.env` and `proof_candidate.env` are the
   kernel-derived certificates. Each is a deterministic data file with exactly
   these fields, in this order: `schema` (`leanllvm-install-v1`), `unit`, the
   unit's object, fixture and marker hashes, the baseline/candidate object,
   fixture and marker hashes, `theorem`
   (`LeanLLVM.Vellum.CommaMaskIR.IR_refines`), `axioms`
   (`Classical.choice,Quot.sound,propext`, read from `collectAxioms` rather than
   from printed output), `contract` (`LeanLLVM.Vellum.commaContract`),
   `target_triple`, `data_layout` and `toolchain_revision` (the `sha256:` of a
   fixed nine-line record over the pin files and the `lean`, `clang` and `ld`
   version output). The selector never sources a certificate: it parses the
   closed grammar, compares each field with the input it names, and reproduces
   the bytes from a fresh kernel check. A manifest digest of a certificate only
   says the file is the byte sequence the manifest names, which is why a field
   mutation, an absent certificate or a malformed one is refused even after the
   digest is repaired.

   `differential.txt` remains ancillary runtime evidence, not a proof. It
   records that the proved units and the Lean-emitted provenance objects agree
   on the corpus, and that each of them agrees with the lane-wise specification
   `diff.c` computes for itself, and it says what it covers:
   `covers: candidate-vs-baseline`, `not-covered: loop`. The same detector is
   first shown to reject a seam that returns zero for every input, on a corpus
   word with a comma byte, so its verdict is not an inert pass. A transcript
   that ends `RESULT: PASS` is never treated as a proof of the loop body.

The binding between the proved fixtures and the installed objects is the object
rebuild plus the certificate in `select.sh`: the selector compiles the fixtures
with the same basenames `build.sh` used, requires byte equality with the
installed objects, and accepts a unit only when the manifest names the
installation theorem and contract, the certificate's fields match those objects
and fixtures, and the producer reproduces the certificate from a fresh kernel
check of that unit. clang records the module name in the object, so the names
are part of the input and a rename is a different object. A field mutation, a
missing certificate or a malformed certificate is a rejection; non-strict mode
still installs the baseline and records the rejection as a fallback, strict mode
emits nothing.

`lake build` does not track `include_str` inputs, so a changed fixture alone
does not invalidate a cached module. `check.sh` therefore elaborates both proof
modules from source every time, and it mutates a fixture to show that each pin
bites: the candidate mutation makes `CommaMaskIR` fail, the real build route
stops at that guard without publishing a new certificate or manifest, and
selection falls back; the loop mutation makes `CommaMaskLoop`'s `#guard` fail;
both are restored and re-checked. The certificate producer additionally refuses
a loaded proof module whose pinned fixture text differs from the fixture file it
is hashing, so a stale olean cannot certify changed bytes.

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
- The loop has no installation certificate. The framed statement in
  `LeanLLVM/Vellum/CommaMaskLoop.lean` relates the loop's returned value and
  the bytes outside the band its own allocations cover, using the general
  relation in `LeanLLVM/Frames.lean` (`AgreesOutsideMem`, `MemPrivate`,
  `AllocFrame`, `RefinesWithin`). The footprint is read off the allocator
  state of the execution rather than written into the theorem, and a write
  outside it fails the relation. That is a proof about the loop body, not a
  statement that the object may be installed: `select.sh` refuses `UNIT=loop`
  because the manifest's theorem relates only the candidate and the baseline.
- The contextual replacement theorem covers a caller (in the semantics) whose
  body is a call to the seam whose result it returns
  (`LeanLLVM/Vellum/SeamContext.lean`), in both an equality form and the
  directional form of `LeanLLVM/CallRefinement.lean`. The environment is
  deterministic; `none` is `ub`, so a defined target call refines an undefined
  source one but not the reverse. Calls still have no memory effects, so there
  is no memory-aware module theorem.
- One toolchain, one target, no benchmark: no timing was measured, and none of
  the checks above is evidence about speed.

Inspect the evidence:

```bash
cat probes/install/build/manifest.env
cat probes/install/build/proof_baseline.env
cat probes/install/build/proof_candidate.env
cat probes/install/build/selection_candidate.env
cat probes/install/build/differential.txt
cat probes/install/build/diff_wrong.txt
cat probes/install/build/out_candidate.txt
cat probes/install/build/out_fallback.txt
cat probes/install/build/gate.log
```
