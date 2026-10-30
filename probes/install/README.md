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
- `build.sh` writes `differential.txt` and `manifest.env`. The manifest binds
  the target triple and data layout, the target-feature policy (`none`: the
  build passes no `-march`/`-mattr`, so clang's triple default applies), the
  contract and theorem names, the attribute policy, every fixture and marker
  hash, and the caller, unit and certificate hashes. `select.sh` recomputes the
  triple and data layout from the toolchain and rejects a mismatch.
- `select.sh` verifies all of that, requires the manifest's `theorem` to cover
  the *requested* unit, **rebuilds each unit from its fixtures** and compares
  the result with the installed bytes, then links either unit. `STRICT=1` fails
  instead of falling back.
- `check.sh` runs the whole flow, including the proof gate for both pinned
  fixtures, a stale-candidate fallback, a strict-mode rejection, a refused loop
  with baseline fallback, a mutated-fixture rejection and a comparison of the
  semantic outputs.

Run from the repository root:

```bash
nix develop -c bash probes/install/check.sh
nix develop -c bash tests/m4-loop-gate.sh --strict   # the loop is refused
nix develop -c bash tests/m4-loop-gate.sh --fallback # the baseline is installed
```

The gate scenarios build their manifest and tool shims in a private temporary
directory, so they exercise the selector without a compiler or a network.

## What is checked

Two certificates, with different reach:

1. **Semantic.** `LeanLLVM/Vellum/CommaMaskIR.lean` pins `baseline.ll` and
   `candidate.ll` by parsed AST and proves `Refines candidateFunction
   baselineFunction`; `LeanLLVM/Vellum/CommaMaskLoop.lean` pins the printed
   `loop.ll` to `loopFunction` and proves the loop's correctness and
   framed-memory statements. The kernel argument for the two bodies is in
   `CommaMaskKernel.lean`. Axiom footprints are pinned in
   `LeanLLVMTest/Vellum.lean`.
2. **Installation.** `differential.txt` is a runtime transcript, not a proof.
   It records that the proved units and the Lean-emitted provenance objects
   agree on the corpus, and that each of them agrees with the lane-wise
   specification `diff.c` computes for itself, and it says what it covers:
   `covers: candidate-vs-baseline`, `not-covered: loop`. The same detector is
   first shown to reject a seam that returns zero for every input, on a corpus
   word with a comma byte, so its verdict is not an inert pass. A transcript
   that ends `RESULT: PASS` is never treated as a proof of the loop body.

The binding between them is the object rebuild plus the coverage table in
`select.sh`: the selector compiles the fixtures with the same basenames
`build.sh` used, requires byte equality with the installed objects, and accepts
a unit only when the manifest's theorem covers that unit. clang records the
module name in the object, so the names are part of the input and a rename is a
different object.

`lake build` does not track `include_str` inputs, so a changed fixture alone
does not invalidate a cached module. `check.sh` therefore elaborates both proof
modules from source every time, and it mutates a fixture to show that each pin
bites: the candidate mutation makes `CommaMaskIR` fail and selection fall back,
and the loop mutation makes `CommaMaskLoop`'s `#guard` fail; both are restored
and re-checked.

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
cat probes/install/build/selection_candidate.env
cat probes/install/build/differential.txt
cat probes/install/build/diff_wrong.txt
cat probes/install/build/out_candidate.txt
cat probes/install/build/out_fallback.txt
```
