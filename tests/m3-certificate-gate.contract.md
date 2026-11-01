# Kernel-derived installation certificate gate

The installer selects one body for the `leanllvm_comma_mask8` seam from a
manifest.  A selection is accepted only when the candidate or baseline unit
carries a proof artifact that agrees, field by field, with the inputs the
selection actually uses: the selected object, its fixture and marker, the
baseline/candidate pair's objects, fixtures and markers, the manifest's
contract, theorem, target triple and data layout, the checked axiom set, and
the toolchain the selection observes.

A proof artifact is a deterministic, data-only `key=value` file.  It holds
exactly these fields, in this order:

`schema`, `unit`, `unit_object_sha256`, `unit_fixture_sha256`,
`unit_marker_sha256`, `baseline_object_sha256`, `candidate_object_sha256`,
`baseline_fixture_sha256`, `candidate_fixture_sha256`,
`baseline_marker_sha256`, `candidate_marker_sha256`, `theorem`, `axioms`,
`contract`, `target_triple`, `data_layout`, `toolchain_revision`.

The artifact is not a compilation input.  `unit` names the unit the artifact
certifies, the three `unit_*` hashes bind that unit's object, fixture and
marker, and the six pair hashes bind both operands of the relation to their
own files.  The artifact is read as data with closed key and value
validation; it is never sourced or evaluated.  `schema` is
`leanllvm-install-v1`, and `toolchain_revision` is `sha256:` followed by the
lowercase digest of a fixed nine-line record: a `leanllvm-toolchain-v1`
header, then the digest of `lean-toolchain`, `flake.nix`, `flake.lock`,
`lakefile.toml`, `lake-manifest.json`, `lean --version`, `clang --version`
and `ld --version`, each line terminated by one LF.  A single component
change changes the digest.

A digest of the artifact recorded in the manifest only says that the artifact
is the byte sequence the manifest names.  It says nothing about whether the
values inside it match the files they claim, which is why a change inside the
artifact must be refused even after that digest is repaired.

The checks drive `probes/install/select.sh` with local tool shims in a private
temporary directory, so no compiler, linker, proof checker, network, clock or
service is reached.  The proof checker the selector drives is a `lake` shim
that accepts exactly three invocations: the imported-graph rebuild
`lake build LeanLLVM.Vellum.CommaMaskIR`, the source rebuild
`lake env lean -o .lake/build/lib/lean/LeanLLVM/Vellum/CommaMaskIR.olean
LeanLLVM/Vellum/CommaMaskIR.lean`, and the producer
`CERT_UNIT=<unit> CERT_MANIFEST=<manifest> CERT_OUT=<path>
lake env lean probes/install/InstallCertificate.lean`.  The graph rebuild
validates its arguments and normally succeeds; it returns nonzero only when
the copied imported source carries the appended invalid-Lean line, and no real
Lean elaboration or proof checking runs.  The direct source check validates
its arguments and succeeds, and the producer publishes the canonical
certificate of the requested unit, derived from the manifest inputs before any
change is made, so a changed artifact is never echoed back.  Every other `lake`
invocation is refused.  The artifact the checks use is test data: its hashes
are computed from the fixture files the manifest names, its target and data
layout come from the shimmed compiler, its theorem and contract come from the
manifest, and its version components come from the shimmed `lean`, `clang` and
`ld` version output.  The temporary tree mirrors the repository root, so the
selector and the checker resolve the revision-bearing pin files, the project
olean directory and the imported proof source
`LeanLLVM/Vellum/CommaMaskKernel.lean` they expect; the imported source is
copied there, so a stale-import run marks only that copy.

    bash tests/m3-certificate-gate.sh --strict theorem
    bash tests/m3-certificate-gate.sh --fallback theorem

The argument names one field of the artifact, and one invocation changes and
selects on that one field only, so `--strict` and `--fallback` each run the
same matrix, one invocation per field.  The two modes that remove an artifact
instead are:

    bash tests/m3-certificate-gate.sh --strict proof_candidate
    bash tests/m3-certificate-gate.sh --fallback proof_candidate
    bash tests/m3-certificate-gate.sh --strict-baseline proof_baseline

`--strict-malformed` and `--fallback-malformed` instead take one variant,
`duplicate`, `missing`, `reordered` or `extra`, and one invocation applies one
variant to the candidate artifact's serialized structure.  The two modes that
mark the imported proof source instead take its module, `CommaMaskKernel`:

    bash tests/m3-certificate-gate.sh --strict-stale-import CommaMaskKernel
    bash tests/m3-certificate-gate.sh --fallback-stale-import CommaMaskKernel

One invocation appends one line that is not a Lean command to the copied
`LeanLLVM/Vellum/CommaMaskKernel.lean` in the fixture tree, so the imported
graph no longer elaborates.

Every run first selects with the valid artifact and asserts that the selection
succeeds, emits an output and hands the requested unit's object to the
linker.  A field run then changes the nominated field — for a paired object,
fixture or marker hash, by exchanging it with its counterpart, so every hash
token remains in the file and only the field-to-file relation breaks — and
rewrites the manifest's digest of the artifact to the changed bytes, so a stale
outer digest cannot explain the result; an absence run removes the artifact
file while the manifest keeps its path and the digest of the bytes it recorded,
so the absence is the only change.  A malformation run repeats the exact valid
`contract` line for `duplicate`, deletes it for `missing`, swaps the adjacent
`theorem` and `axioms` lines for `reordered`, and appends `extension=x` before
the terminal LF for `extra`, leaving every other field's value, `key=value`
syntax and position unchanged, and rewrites the manifest's digest to the
malformed bytes.  A stale-import run instead appends the invalid-Lean line to
the copied imported source and leaves the certificate, the manifest's digest
of it and every object's bytes unchanged, so the imported graph is the only
input that differs.  Each run then selects again into separate
output and record paths, using the same selector and the same linker detector,
so a stale output cannot stand in for the second selection, and the refusal or
fallback must be attributable to the change made.

### H1 — a strict candidate request refuses an artifact with one changed field

- **Actor:** the build integrator.
- **Given:** a manifest whose object, fixture, marker and transcript hashes
  match the files it names, whose baseline and candidate objects rebuild from
  their fixtures with the tools the selector observes, and whose candidate
  proof artifact carries, for every field, the value that field is supposed to
  have; and a strict candidate selection from that input that exits 0, selects
  the candidate, emits an output and hands the candidate object to the linker.
- **When:** one field of the candidate artifact is changed — this invocation
  tests exactly one field — and the manifest's digest of the artifact is
  rewritten to the changed bytes; a paired object, fixture or marker hash is
  exchanged with its counterpart, so every hash token is still present in the
  file and only the field-to-file relation is broken.  The integrator then
  invokes the selector with `UNIT=candidate STRICT=1`, pointing `MANIFEST`,
  `OUT` and `RECORD` at the fixtures.
- **Then:** it exits nonzero, no executable exists at the requested output, no
  selection record names the candidate, and the linker was not given the
  candidate object for that output.
- **Why:** a strict request must refuse a unit whose artifact disagrees with
  an input the selection uses, even when the artifact's digest matches the
  file, because the digest attests the bytes and not what they claim.

### H2 — a non-strict candidate request falls back for one changed field

- **Actor:** the build integrator.
- **Given:** the same manifest, the same single-field change with the
  manifest's digest rewritten, and the same valid-artifact control, run with
  `STRICT=0`; this invocation tests exactly one field.
- **When:** the integrator invokes the selector with `UNIT=candidate
  STRICT=0`.
- **Then:** it exits 0, the selection record's `selected` field is `baseline`,
  the linker is given the baseline object by the same detector that saw the
  candidate object on the control, the candidate object is not linked, and the
  record's `reason` field equals exactly `proof rejected: invalid certificate;
  installed baseline fallback`.  The control's own `reason` field is the
  acceptance reason for the unchanged artifact, so the fallback is recorded as
  a rejection of the changed certificate, not as an accepted proof and not as
  a merely different sentence.
- **Why:** a refused certificate must keep the seam installed at the baseline
  rather than remove it, and the record must not describe the fallback as if
  the changed artifact had been accepted.

### H3 — a strict candidate request refuses an absent candidate proof

- **Actor:** the build integrator.
- **Given:** the same manifest and the same valid-artifact control, with the
  candidate artifact removed while the manifest still names its path and the
  digest of the bytes it recorded.
- **When:** the integrator invokes the selector with `UNIT=candidate
  STRICT=1`.
- **Then:** it exits nonzero, no executable exists at the requested output, no
  selection record names the candidate, and the linker was not given the
  candidate object for that output.
- **Why:** a unit whose certificate is absent is not certified, and a strict
  request must fail closed on the absence rather than on a hash comparison.

### H4 — a non-strict candidate request installs the baseline for an absent candidate proof

- **Actor:** the build integrator.
- **Given:** the same absent candidate artifact and the same valid-artifact
  control, run with `STRICT=0`.
- **When:** the integrator invokes the selector with `UNIT=candidate
  STRICT=0`.
- **Then:** it exits 0, the selection record's `selected` field is `baseline`,
  the linker is given the baseline object, the candidate object is not linked,
  and the record's `reason` field equals exactly
  `proof rejected: missing certificate; installed baseline fallback`, the
  control's own `reason` field being the acceptance reason for the artifact it
  still has.
- **Why:** an absent certificate must not be read as an accepted one, and the
  seam must remain installed at the baseline.

### H5 — a direct strict baseline request requires its own proof artifact

- **Actor:** the build integrator.
- **Given:** a manifest with a valid candidate artifact and a valid baseline
  artifact, and a strict baseline selection from that input that exits 0,
  selects the baseline, emits an output and hands the baseline object to the
  linker; then the baseline artifact is removed while the manifest still names
  its path and digest.
- **When:** the integrator invokes the selector with `UNIT=baseline STRICT=1`.
- **Then:** it exits nonzero, no executable exists at the requested output, no
  selection record names the baseline, and the linker was not given the
  baseline object for that output.
- **Why:** a unit selected directly in strict mode must carry its own
  certificate, so the baseline is not installable on the strength of the
  candidate's artifact.

### H6 — a strict candidate request refuses a structurally malformed proof artifact

- **Actor:** the build integrator.
- **Given:** the same manifest, the same valid candidate artifact and the same
  strict candidate control as H1; one invocation applies exactly one variant
  to the artifact's serialized bytes and leaves every source input unchanged:
  `duplicate` repeats the exact valid `contract` line, `missing` deletes it,
  `reordered` swaps the adjacent `theorem` and `axioms` lines, and `extra`
  appends `extension=x` before the terminal LF.  The remaining fields keep
  their values, their `key=value` syntax and their order.
- **When:** the integrator applies the variant, rewrites the manifest's digest
  of the artifact to the malformed bytes, and invokes the selector with
  `UNIT=candidate STRICT=1` into separate `OUT` and `RECORD` paths.
- **Then:** it exits nonzero, no executable exists at the requested output, no
  selection record names the candidate, and the linker was not given the
  candidate object for that output.
- **Why:** validity is a property of the artifact's serialized structure, not
  only of the values a substring search can find, so a repeated, absent,
  reordered or unknown line must be refused even when the artifact's digest
  matches the file.

### H7 — a non-strict candidate request falls back for a structurally malformed proof artifact

- **Actor:** the build integrator.
- **Given:** the same manifest, the same valid candidate artifact and the same
  candidate control as H6, with the same one-variant malformation and repaired
  manifest digest, run with `UNIT=candidate STRICT=0`.
- **When:** the integrator invokes the selector with `UNIT=candidate
  STRICT=0` into separate `OUT` and `RECORD` paths.
- **Then:** it exits 0, the selection record's `selected` field is `baseline`,
  the linker is given the baseline object and not the candidate object, and
  the record's `reason` field equals exactly `proof rejected: invalid
  certificate; installed baseline fallback`, the control's own `reason` field
  being the acceptance reason for the unchanged artifact.
- **Why:** a malformed certificate must keep the seam installed at the
  baseline and must be recorded as a rejection, not as an accepted proof.

### H8 — a strict candidate request refuses a stale imported proof source

- **Actor:** the build integrator.
- **Given:** the fixture tree's copy of `LeanLLVM/Vellum/CommaMaskKernel.lean`,
  which the proof module imports, a manifest whose object, fixture, marker and
  transcript hashes match the files it names, and a valid candidate artifact;
  and a strict candidate selection from that input that exits 0, selects the
  candidate, emits an output and hands the candidate object to the linker.  The
  integrator then appends one line that is not a Lean command to that copied
  import; the certificate, the manifest's digest of it and every object keep
  their bytes.
- **When:** the integrator invokes the selector with `UNIT=candidate STRICT=1`
  into separate `OUT` and `RECORD` paths.  The `lake` shim's imported-graph
  rebuild `lake build LeanLLVM.Vellum.CommaMaskIR` returns nonzero for the
  marked source, while its direct source check and certificate producer still
  succeed.
- **Then:** it exits nonzero, no executable exists at the requested output, no
  selection record names the candidate, and the linker was not given the
  candidate object for that output.
- **Why:** a certificate is only as current as the proof module it was derived
  from, so a strict request must refuse a candidate whose imported graph no
  longer elaborates rather than trust a certificate built from the pristine
  source.

### H9 — a non-strict candidate request falls back for a stale imported proof source

- **Actor:** the build integrator.
- **Given:** the same copied import marked with the same appended line and the
  same valid-candidate control as H8, run with `UNIT=candidate STRICT=0`.
- **When:** the integrator invokes the selector with `UNIT=candidate STRICT=0`
  into separate `OUT` and `RECORD` paths.
- **Then:** it exits 0, the selection record's `selected` field is `baseline`,
  the linker is given the baseline object and not the candidate object, and
  the record's `reason` field equals exactly `proof rejected: invalid
  certificate; installed baseline fallback`, the control's own `reason` field
  being the acceptance reason for the pristine source.
- **Why:** a stale imported graph must keep the seam installed at the baseline
  and must be recorded as a rejection, not as an accepted proof built from a
  source that no longer elaborates.
