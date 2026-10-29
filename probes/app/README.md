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
- The application links against the candidate or the baseline through the same
  selector the installation probe uses: hashes, fixture rebuild, target,
  symbols, and a theorem that covers the requested unit.
- Both builds produce the same result (`offsets=[7, 12, 20, 21, 24, 29]`,
  `fields=7`), while the linked bodies are demonstrably different: the seam's
  instruction lines, with addresses and headers stripped, differ between the two
  executables. The extraction is applied to the candidate twice and the two
  listings must match before the pair is compared, so a failed or empty
  extraction cannot pass as a difference. What this shows is that two different
  instruction sequences were linked; the proof is `IR_refines` over the units.
- A stale candidate hash falls back to the baseline, and strict mode rejects it.
- The loop unit is **refused**: no checked theorem covers it, so strict mode
  exits nonzero without emitting a loop executable and non-strict mode installs
  the baseline for the same request.

The equality of the two runs is runtime evidence about this input, not the
certificate: the certificate is `IR_refines` over the candidate and the
baseline, which are the units the selector accepts. The loop's framed
correctness proof is a statement about its parsed fixture and does not make the
loop installable.

## Limits

- One application, one input, no benchmark: no timing was measured.
- The application is a small Lean module written for this probe. It is a real
  caller in the sense that the seam call is embedded in surrounding work and
  survives `-O2`; it is not a production code base.
- The call is tail-position in the emitted IR. Calls with memory effects are
  outside the modelled semantics; the seam is pure, so the replacement theorem
  here is not a memory-aware module theorem.
