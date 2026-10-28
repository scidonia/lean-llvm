# Application probe: a real caller behind the seam

`App.lean` uses the comma mask for its intended task — locating commas in
eight-byte chunks of a CSV record — rather than wrapping it. `build.sh`
compiles the module to C and to LLVM IR, builds the two proved units from
`probes/install/ir/`, and writes a manifest in the shape `probes/install/select.sh`
verifies. `check.sh` links the application against each unit and runs it.

Run from the repository root:

```bash
nix develop -c bash probes/app/check.sh
```

## What it establishes

- The seam call survives the compiler. `build.sh` emits `app.ll` with
  `clang -O2` and fails unless the module still contains
  `call i64 @leanllvm_comma_mask8`, and unless the application object imports
  the symbol. This is the M0 boundary-survival claim on a caller with real
  work around the call, not on a wrapper.
- The application links against either proved unit through the same selector
  the installation probe uses: hashes, fixture rebuild, target, symbols.
- Both builds produce the same result (`offsets=[7, 12, 20, 21, 24, 29]`,
  `fields=7`), while the linked bodies are demonstrably different: the
  disassembly of `leanllvm_comma_mask8` differs between the two executables.
- A stale candidate hash falls back to the baseline, and strict mode rejects it.

The equality of the two runs is runtime evidence about this input, not the
certificate: the certificate is `IR_refines` over the units, and the selector
checks that the linked units are those fixtures.

## Limits

- One application, one input, no benchmark.
- The application is a small Lean module written for this probe. It is a real
  caller in the sense that the seam call is embedded in surrounding work and
  survives `-O2`; it is not a production code base.
- The call is tail-position in the emitted IR. Calls with memory effects are
  outside the modelled semantics; the seam is pure.
