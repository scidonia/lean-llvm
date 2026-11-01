# Loop installation gate

The installer selects one body for the `leanllvm_comma_mask8` seam from a
manifest.  The manifest binds a contract, a theorem, the fixture and object
hashes, and a differential transcript.  The loop unit is the memory-backed
counterpart of the unrolled candidate; the transcript records runtime agreement
on a corpus and is not a theorem about the loop body.

A selection is accepted only when the requested unit's own theorem is bound and
its certificate checks out.  `IR_refines` covers the candidate and the
baseline; the loop has its own theorem field (`loop_theorem`) and its own
certificate (`proof_loop`), checked by the same gate
(`tests/m4-loop-install-gate.sh`).  The scenarios below drive a manifest that
binds neither, so the loop has nothing to check and is not installed.

A manifest supplies the facts a build produced — the unit paths, the hashes and
the theorem name.  The selector sources it as trusted, locally produced shell
configuration, so generated `unit` and `strict` fields cannot decide the
request: the requested unit and strictness are captured under separate `req_*`
names before the manifest is sourced.  That protects against that field
collision only.  It does not contain the manifest's shell code — a crafted
manifest can still rebind the `req_*` names or the output paths, or shadow the
tools with shell functions — and reading the manifest with a closed, validated
key=value parser instead of sourcing it would be a separate change.

The checks drive `probes/install/select.sh` with local tool shims in a private
temporary directory, so no compiler, linker or network is used:

    bash tests/m4-loop-gate.sh --strict
    bash tests/m4-loop-gate.sh --fallback
    bash tests/m4-loop-gate.sh --strict-conflict
    bash tests/m4-loop-gate.sh --fallback-conflict

### G1 — a strict loop request without a loop proof is refused

- **Actor:** the build integrator.
- **Given:** a manifest whose hashes match its fixtures and objects, whose
  `theorem` is `LeanLLVM.Vellum.CommaMaskIR.IR_refines` (candidate to baseline
  only), and whose differential transcript ends `RESULT: PASS`, and whose
  manifest binds no `loop_theorem` and no `proof_loop` certificate; and a
  baseline selection from the same input that succeeds and produces an
  executable, so a working link and output are known to be detectable.
- **When:** the integrator invokes the selector with `UNIT=loop STRICT=1`,
  pointing `MANIFEST`, `OUT` and `RECORD` at isolated fixtures.
- **Then:** it exits nonzero, emits no loop executable, and writes no selection
  record naming the loop.
- **Why:** a strict request must fail closed rather than install a unit with no
  theorem or certificate bound to it.

### G2 — a non-strict loop request falls back to the baseline

- **Actor:** the build integrator.
- **Given:** the same input and the same successful baseline control.
- **When:** the integrator invokes the selector with `UNIT=loop STRICT=0`.
- **Then:** it exits zero, the selection record's `selected` field is
  `baseline`, and the object handed to the linker is that recorded unit's
  object — the baseline, not the loop.
- **Why:** denying the loop must keep the installed baseline usable rather than
  remove the seam.

### G3 — a manifest cannot replace the strict requested unit

- **Actor:** the build integrator.
- **Given:** the same manifest input as G1, whose hashes match its fixtures and
  objects and whose differential transcript ends `RESULT: PASS`, plus a
  conflicting manifest that repeats it and ends with `unit=candidate` and
  `strict=0`; and the clean-manifest baseline selection that succeeds and
  produces an executable, so a working link and output are known to be
  detectable.
- **When:** the integrator invokes the selector with `UNIT=loop STRICT=1` and
  the conflicting manifest.
- **Then:** it exits nonzero, emits no executable at the requested output path,
  and writes no selection record naming the candidate or the loop.
- **Why:** a manifest that overwrites the caller's request would install a unit
  nobody asked for; in strict mode it would install the candidate even though
  `LeanLLVM.Vellum.CommaMaskIR.IR_refines` covers the candidate and not the
  requested loop.

### G4 — a manifest cannot replace the non-strict fallback unit

- **Actor:** the build integrator.
- **Given:** the same conflicting manifest and the same clean-manifest baseline
  control.
- **When:** the integrator invokes the selector with `UNIT=loop STRICT=0` and
  the conflicting manifest.
- **Then:** it exits zero, the selection record's `selected` field is
  `baseline`, and the object handed to the linker is the baseline fixture's
  object — not the candidate's and not the loop's.
- **Why:** the loop has no theorem or certificate bound to it in this manifest,
  so the fallback must install the baseline rather than a unit the manifest
  substituted for the request.
