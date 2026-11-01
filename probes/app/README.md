# Application probe: a real caller behind the seam

`App.lean` uses the comma mask for its intended task — locating commas in
eight-byte chunks of a CSV record — rather than wrapping it. `build.sh`
compiles the module to C and to LLVM IR, builds the two proved units from
`probes/install/ir/`, produces their kernel-derived installation certificates,
and writes a manifest in the shape `probes/install/select.sh` verifies.
`check.sh` links the application against each unit and runs it.

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
  symbols, and the requested unit's certificate, re-derived by the producer
  from a fresh kernel check before the link.
- Both builds produce the same result (`offsets=[7, 12, 20, 21, 24, 29]`,
  `fields=7`), while the linked bodies are demonstrably different: the seam's
  instruction lines, with addresses and headers stripped, differ between the two
  executables. The extraction is applied to the candidate twice and the two
  listings must match before the pair is compared, so a failed or empty
  extraction cannot pass as a difference. What this shows is that two different
  instruction sequences were linked; the proof is `IR_refines` over the units.
- A stale candidate hash falls back to the baseline, and strict mode rejects it.
- The loop unit installs from its own certificate: the selector links it in
  strict mode, the record names `loop`, and the application prints the same
  offsets and field count.

The equality of the runs is runtime evidence about this input, not the
certificate: each installed unit is accepted because its own certificate checks
out — `IR_refines` on the candidate's and the baseline's, and
`loop_refines_candidate_within` (the loop's framed refinement to the unrolled
candidate within the band its own allocations cover) on the loop's. Every one of
them is a hash-and-rebuild bridge from the proved fixture to the linked object,
not a theorem about compiled code.

## Limits

- One application, one input, no benchmark: no timing was measured.
- The application is a small Lean module written for this probe. It is a real
  caller in the sense that the seam call is embedded in surrounding work and
  survives `-O2`; it is not a production code base.
- The call is tail-position in the emitted IR. Calls with memory effects are
  outside the modelled semantics; the seam is pure, so the replacement theorem
  here is not a memory-aware module theorem.
