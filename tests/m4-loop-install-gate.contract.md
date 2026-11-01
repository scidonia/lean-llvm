# Certificate-bound loop installation gate

The installer selects one body for the `leanllvm_comma_mask8` seam from a
manifest.  The manifest binds a contract, the fixture and object hashes, a
differential transcript, and the theorem and certificate of each unit it names.
The loop unit is the memory-backed counterpart of the unrolled candidate; the
transcript records runtime agreement on a corpus and is not a theorem about the
loop body.

`LeanLLVM.Vellum.CommaMaskIR.IR_refines` covers the candidate and the baseline.
The loop has its own covering theorem,
`LeanLLVM.Vellum.CommaMaskLoop.loop_refines_candidate_within`, bound by the
manifest's `loop_theorem` field, and its own certificate, bound by `proof_loop`
and `proof_loop_sha256`.  The manifest's `theorem` field keeps naming
`IR_refines` for every request: it is the binding for the candidate/baseline
cross-hashes, not the loop's.

A certificate is the same deterministic, data-only `key=value` file for every
unit, and the gate is the same: `unit` names the unit it certifies, `theorem`
names that unit's own theorem — `IR_refines` for the baseline and the
candidate, `loop_refines_candidate_within` for the loop — the three `unit_*`
hashes bind the certified unit's object, fixture and marker, and the six pair
hashes bind both operands of the relation to their own files.  A certificate
whose `theorem`, hash, fixture or marker disagrees with the unit it certifies is
refused, whatever its digest in the manifest says, because that digest attests
the bytes and not what they claim.  For a loop request the gate additionally
re-elaborates `LeanLLVM/Vellum/CommaMaskLoop.lean` after the imported
`CommaMaskIR` graph is rebuilt, then has the producer derive the certificate
again and compares the bytes.

The checks drive `probes/install/select.sh` — a copied, unmodified production
file invoked as an external process — with local tool shims in a private
temporary directory, so no compiler, linker, proof checker, network, clock or
service is reached.  The proof checker the selector drives is a `lake` shim
that accepts exactly these invocations: the imported-graph rebuilds
`lake build LeanLLVM.Vellum.CommaMaskIR` and
`lake build LeanLLVM.Vellum.CommaMaskLoop`, the source rebuilds
`lake env lean -o .lake/build/lib/lean/LeanLLVM/Vellum/CommaMaskIR.olean
LeanLLVM/Vellum/CommaMaskIR.lean` and
`lake env lean -o .lake/build/lib/lean/LeanLLVM/Vellum/CommaMaskLoop.olean
LeanLLVM/Vellum/CommaMaskLoop.lean`, and the producer
`CERT_UNIT=<unit> CERT_MANIFEST=<manifest> CERT_OUT=<path>
lake env lean probes/install/InstallCertificate.lean`.  Every form validates its
arguments and succeeds; the producer publishes the canonical certificate of the
requested unit, derived from the manifest inputs before any change is made, so a
changed certificate is never echoed back.  Any other `lake` invocation is
refused.  The certificates the checks use are test data: their hashes are
computed from the fixture files the manifest names, their theorem is the one the
manifest binds to that unit, their axiom set is that theorem's pinned footprint,
their target and data layout come from the shimmed compiler, and their version
component comes from the shimmed `lean`, `clang` and `ld` version output.  The
temporary tree mirrors the repository root, so the selector resolves the
revision-bearing pin files and the project olean directory it expects; nothing
outside the temporary directory is written.

    bash tests/m4-loop-install-gate.sh --strict
    bash tests/m4-loop-install-gate.sh --strict-theorem
    bash tests/m4-loop-install-gate.sh --strict-hash
    bash tests/m4-loop-install-gate.sh --fallback-hash

Every run first makes a strict baseline selection from the same input and
asserts that it exits 0, links the baseline object and emits an output file, so
a working link and a detectable output are known before the same detector is
used to judge the loop.  `--strict` then selects with the valid loop
certificate.  The other three modes also select with the valid loop certificate,
and then make one change to that certificate — L2 its `theorem` field, L3 and
L4 an exchange of its `unit_object_sha256` value with its own
`baseline_object_sha256` value, so every hash token stays in the file and only
the field-to-file relation breaks — rewrite the manifest's digest of the
certificate to the changed bytes, and select again into separate output and
record paths, so the result is attributable to the change made.

### L1 — a strict loop request with a matching certificate installs the loop

- **Actor:** the build integrator.
- **Given:** a manifest whose `loop`, `loop_fixture` and `loop_marker` hashes
  match the fixtures and the rebuilt loop object, whose `theorem` is
  `LeanLLVM.Vellum.CommaMaskIR.IR_refines`, whose `loop_theorem` is
  `LeanLLVM.Vellum.CommaMaskLoop.loop_refines_candidate_within`, and whose loop
  certificate carries, for every field, the value that field is supposed to
  have — `unit=loop`, `theorem=
  LeanLLVM.Vellum.CommaMaskLoop.loop_refines_candidate_within`, and the
  cross-hashes of the baseline and candidate objects, fixtures and markers the
  manifest also names; and a strict baseline selection from the same input that
  exits 0, links the baseline object and emits an output file.
- **When:** the integrator invokes the selector with `UNIT=loop STRICT=1`,
  pointing `MANIFEST`, `OUT` and `RECORD` at the isolated fixtures.
- **Then:** it exits 0, the selection record's `selected` field is `loop`, the
  loop object is the one handed to the linker, and the record's `proof_sha256`
  field equals the digest of the loop certificate file the manifest's
  `proof_loop` names, computed from that file rather than merely being
  non-empty.
- **Why:** a unit with its own theorem and a certificate that agrees with it
  must be installable by the same gate as the candidate and the baseline, and
  the record must bind the installed unit to the certificate it was decided on.

### L2 — a strict loop request refuses a certificate naming another unit's theorem

- **Actor:** the build integrator.
- **Given:** the same manifest and the same valid-loop control as L1, with the
  loop certificate's `theorem` field changed from
  `LeanLLVM.Vellum.CommaMaskLoop.loop_refines_candidate_within` to
  `LeanLLVM.Vellum.CommaMaskIR.IR_refines`, a validly-shaped name that does not
  cover the loop, and the manifest's `proof_loop_sha256` rewritten to the
  changed bytes; the manifest's own `loop_theorem` field stays correct.
- **When:** the integrator invokes the selector with `UNIT=loop STRICT=1` into
  separate `OUT` and `RECORD` paths.
- **Then:** it exits nonzero, no loop executable is emitted, no selection
  record names the loop, and the selector's stderr carries the exact line
  `  - proof certificate invalid`.
- **Why:** the certificate is refused for stating a theorem that does not cover
  the unit it certifies, and the refusal must say so rather than be explained
  by a digest that no longer matches.

### L3 — a strict loop request refuses a certificate whose object hash is another unit's

- **Actor:** the build integrator.
- **Given:** the same manifest and the same valid-loop control as L1, with the
  loop certificate's `unit_object_sha256` value exchanged with its own
  `baseline_object_sha256` value, so both hash tokens stay in the file and only
  the certified-object relation breaks, and the manifest's `proof_loop_sha256`
  rewritten to the changed bytes.
- **When:** the integrator invokes the selector with `UNIT=loop STRICT=1` into
  separate `OUT` and `RECORD` paths.
- **Then:** it exits nonzero, no loop executable is emitted, no selection
  record names the loop, and the selector's stderr carries the exact line
  `  - proof certificate invalid`.
- **Why:** a certificate whose unit hash names an object that is not the
  selected unit's does not certify that unit, and the digest attests the bytes
  and not what they claim.

### L4 — a non-strict loop request with that certificate falls back to the baseline

- **Actor:** the build integrator.
- **Given:** the same manifest, the same valid-loop control and the same
  exchanged-hash certificate as L3.
- **When:** the integrator invokes the selector with `UNIT=loop STRICT=0` into
  separate `OUT` and `RECORD` paths.
- **Then:** it exits 0, the selection record's `selected` field is `baseline`,
  the linker is given the baseline object and not the loop's, and the record's
  `reason` field equals exactly `proof rejected: invalid certificate;
  installed baseline fallback`.
- **Why:** a refused loop certificate must keep the seam installed at the
  baseline and must be recorded as a rejection, not as an accepted proof and not
  as a blanket refusal of the loop.
