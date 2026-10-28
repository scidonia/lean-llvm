# Installation probe: link-time selection at an opaque seam

This probe exercises the installation point described in
`docs/m0-runtime-noise-report.md` and the accompanying design discussion.

- `Caller.lean` sees only `@[extern]` declarations for the seam and an
  implementation marker.
- `probes/install/ir/` holds the emitted IR that
  `LeanLLVM/Vellum/CommaMaskIR.lean` parses, pins and proves. `capture.sh`
  regenerates it from the Lean emission and records the exact `clang` and `opt`
  invocations plus the textual syntax removed before the parser sees it.
- `Baseline.lean` and `Candidate.lean` are the Lean bodies. `build.sh` compiles
  them as **provenance** objects and compares them with the proved units on a
  differential corpus.
- The installed units are compiled from `ir/baseline.ll` and `ir/candidate.ll`
  plus their marker objects (`ir/marker_*.ll`). Each unit is therefore the
  program the refinement theorem is about, not a separately authored body.
- `build.sh` writes `differential.txt` and `manifest.env`. The manifest binds
  the target, the contract and theorem names, the attribute policy, every
  fixture and marker hash, and the caller, unit and certificate hashes.
- `select.sh` verifies all of that, **rebuilds each unit from its fixtures**
  and compares the result with the installed bytes, then links either unit.
  `STRICT=1` fails instead of falling back.
- `check.sh` runs the whole flow, including the proof gate, a stale-candidate
  fallback, a strict-mode rejection, a mutated-fixture rejection and a
  comparison of the semantic outputs.

Run from the repository root:

```bash
nix develop -c bash probes/install/check.sh
```

## What is checked

Two certificates, with different reach:

1. **Semantic.** `LeanLLVM/Vellum/CommaMaskIR.lean` pins both fixtures by
   parsed AST and proves `Refines candidateFunction baselineFunction`. The
   kernel argument for the two bodies is in `CommaMaskKernel.lean`. Axiom
   footprints are pinned in `LeanLLVMTest/Vellum.lean`.
2. **Installation.** `differential.txt` is a runtime transcript, not a proof.
   It records that the proved units and the Lean-emitted provenance objects
   agree on the corpus.

The binding between them is the object rebuild: `select.sh` compiles the
fixtures with the same basenames `build.sh` used and requires byte equality with
the installed objects. clang records the module name in the object, so the
names are part of the input and a rename is a different object.

`lake build` does not track `include_str` inputs, so a changed fixture alone
does not invalidate a cached module. `check.sh` therefore elaborates the proof
module from source every time, and it mutates a fixture to show that the pin
bites: the proof fails and selection falls back until the fixture is restored.

`attributes=reject` records the attribute policy: the fixtures carry none, and
the parser refuses a construct it does not model rather than dropping an
attribute silently. Data layout and target features are not yet bound; the
fixtures carry neither and clang supplies the target default.

## Known limits

- The candidate fixture is generated from `ir/candidate_lanes.c`, a lane-by-lane
  transcription of `Candidate.lean`'s fold, not from Lean's own emission of that
  loop. The differential transcript is the evidence that the transcription
  agrees with the Lean body; it is not a proof.
- The contextual replacement theorem covers a caller (in the semantics) whose
  body is a call to the seam whose result it returns
  (`LeanLLVM/Vellum/SeamContext.lean`), in both an equality form and the
  directional form of `LeanLLVM/CallRefinement.lean`. The environment is
  deterministic; `none` is `ub`, so a defined target call refines an undefined
  source one but not the reverse. Calls still have no memory effects.
- One toolchain, one target, no benchmark.

Inspect the evidence:

```bash
cat probes/install/build/manifest.env
cat probes/install/build/selection_candidate.env
cat probes/install/build/differential.txt
cat probes/install/build/out_candidate.txt
cat probes/install/build/out_fallback.txt
```
