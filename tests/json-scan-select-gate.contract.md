# JSON scanner selection gate

The installer selects one body for a seam from a manifest.  This route's unit is
the JSON window scanner: a body named `leanllvm_json_scan_window`.  The request
names it `json_scan`, beside `baseline`, `candidate` and `loop`.

The selector does not yet know that name, in four places that are visible in
`probes/install/select.sh`:

- the request dispatch names `baseline`, `candidate` and `loop` and refuses
  anything else with `unknown unit <name>`;
- the certificate parser's `unit` arm accepts only those three values, so a
  certificate naming the JSON unit is malformed before its fields are compared;
- the theorem, symbol and contract expectations are one global binding
  (`expected_theorem`, `expected_symbol`, `expected_contract`) with a
  unit-specific field only for the loop (`loop_theorem`), so a JSON unit needs
  its own bindings exactly as the loop did;
- the per-unit object, fixture, marker and certificate lookups are indirect
  expansions of the unit name (`proof_$unit`, `${unit}_fixture`,
  `${unit}_marker`), so the unit name has to be a shell identifier.  The
  request name is `json_scan` for that reason, and the manifest keys are
  `json_scan`, `json_scan_fixture`, `json_scan_marker`, `json_scan_symbol`,
  `json_scan_theorem`, `json_scan_contract`, `proof_json_scan` and
  `proof_json_scan_sha256`.

The checks drive `probes/install/select.sh` — a copied, unmodified production
file invoked as an external process — with local tool shims in a private
temporary directory, so no compiler, linker, proof checker, network, clock or
service is reached.  The proof checker the selector drives is a `lake` shim that
accepts exactly two forms: a proof-module rebuild (`lake build LeanLLVM.…`,
whichever module the route re-elaborates after removing its olean) and the
producer `CERT_UNIT=<unit> CERT_MANIFEST=<manifest> CERT_OUT=<path> lake env
lean probes/install/InstallCertificate.lean`.  The producer publishes the
canonical certificate of the requested unit, derived from the manifest inputs
before any change is made, so a changed certificate is never echoed back.  Any
other `lake` invocation is refused.  The certificates the checks use are test
data: their hashes are computed from the fixture files the manifest names, their
theorem and contract are the ones the manifest binds to that unit, their axiom
set is that theorem's checked footprint, their target and data layout come from
the shimmed compiler, and their version component comes from the shimmed `lean`,
`clang` and `ld` version output and the mirrored pin files.  The temporary tree
mirrors the repository root, so the selector resolves the revision-bearing pin
files and the project olean directory it expects, and writes nothing outside the
temporary directory.

    bash tests/json-scan-select-gate.sh --strict
    bash tests/json-scan-select-gate.sh --fallback

Every mode first makes a strict baseline selection from the same input and
asserts that it exits 0, links the baseline object and emits an app, so a
working link, a digest comparison and a detectable output are known before the
same detectors are used to judge the JSON unit.  `--strict` then selects the
JSON unit with the valid certificate, and then makes one change to that
certificate — its `theorem` field, to a validly-shaped name that covers the
candidate and the baseline and not this unit — rewrites the manifest's digest of
the certificate to the changed bytes, and selects again into separate output and
record paths, so the refusal is attributable to the change made.  `--fallback`
makes the same change and selects the changed certificate with `STRICT=0`.

What this gate does not assert, and deliberately: the numeric agreement between
the emitted body and the model.  It is checked by the separate body-vs-model
route, which drives the emitted body and the real compiler over real windows; a
number written by this gate's own fixture and echoed by its own linker shim
would be the fixture's claim, not the body's.  This contract is narrowed to the
selector's decisions and the identity of the object it installs, not weakened.

## Fixtures

The JSON unit's fixtures are **scaffolding**: a `.ll` defining
`leanllvm_json_scan_window`, and a marker `.ll` defining `leanllvm_impl_id`,
both written inside the private temporary tree, with the manifest's hashes
computed from those bytes.  A certificate bound to the emitted scanner body is a
separate delivery: these stand-ins are replaced by fixtures built from that
body, and no `Then` below changes when they are.  The stand-in returns a
constant that no assertion reads, because the body's value is not this route's
observable.

The certificate names the unit's own statement and contract, which are the
scanner's and not the classifier's: `theorem=LeanLLVM.Refinement.JsonScanIR.scanWindowLLVM_refines`
and `contract=LeanLLVM.Refinement.JsonScanABI.jsonScanContract`, bound by the
manifest's `json_scan_theorem` and `json_scan_contract`.  The manifest's global
`theorem` and `contract` keep naming
`LeanLLVM.Refinement.CommaMaskIR.IR_refines` and `LeanLLVM.Refinement.commaContract` for
the baseline and the candidate.  The certificate's `axioms` field is the named
theorem's pinned footprint in `LeanLLVMTest/` — **and nothing else**.  At this
revision the pin does not exist, and the reason is stronger than a missing
statement: the statement is now a declaration, `JsonScanIR.scanWindowStatement`,
and it is **refuted** — `scanWindowStatement_false` proves its negation at a
witness that satisfies every hypothesis.  Two body defects account for it: the
stop word's first-selection chain tests the bad-lead bit where the model tests
the bad-continuation path, and the band hypothesis the docstring elides is
load-bearing.  So the gate **refuses and names the missing pin** rather than
reading the selector's expectation in its place; the fixture cannot be built, and
JS1 and JS2 are unreachable until the scanner's body is corrected and the theorem
restated.  A gate that substituted the selector's set would have produced a
certificate for a unit whose theorem is false.

### JS1 — a strict `json_scan` request with a matching certificate installs the unit

- **Actor:** the build integrator.
- **Given:** a manifest that binds the baseline and candidate objects, fixtures
  and markers with hashes computed from their bytes, the global comma contract
  and theorem, the unit's own theorem and contract in `json_scan_theorem` and
  `json_scan_contract`, its symbol `leanllvm_json_scan_window` in
  `json_scan_symbol`, and a `json_scan` certificate that carries
  `unit=json_scan`, the JSON unit's object, fixture and marker hashes, the
  baseline and candidate cross-hashes, its own theorem and contract, and the
  observed toolchain revision; and a strict baseline selection from the same
  input that exits 0, links the baseline object and emits an app.
- **When:** the integrator invokes the selector with `UNIT=json_scan STRICT=1`,
  pointing `MANIFEST`, `OUT` and `RECORD` at the isolated fixtures.
- **Then:** it exits 0; the selection record's `selected` field is `json_scan`;
  the record's `proof_sha256` field equals the sha256 of the certificate file
  the manifest's `proof_json_scan` names, computed from that file; and the
  sha256 of the object the linker was handed equals the sha256 of the
  manifest's `json_scan` object, computed from that file.
- **Why:** a unit with its own statement, contract and certificate must be
  installable by the same gate as the baseline and the candidate, and the record
  and the link must both bind the installed bytes to the certificate they were
  decided on.

### JS2 — a strict `json_scan` request refuses a certificate naming another unit's theorem

- **Actor:** the build integrator.
- **Given:** the same manifest, the same valid-certificate install as JS1, and
  the JSON unit's certificate with its `theorem` field changed from
  `LeanLLVM.Refinement.JsonScanIR.scanWindowLLVM_refines` to
  `LeanLLVM.Refinement.CommaMaskIR.IR_refines`, a validly-shaped name that covers
  the candidate and the baseline and not this unit, and the manifest's
  `proof_json_scan_sha256` rewritten to the changed bytes.
- **When:** the integrator invokes the selector with `UNIT=json_scan STRICT=1`
  into separate `OUT` and `RECORD` paths.
- **Then:** it exits nonzero; no app is emitted at `OUT`; and the selector's
  stderr carries the exact line `  - proof certificate invalid`.
- **Why:** the certificate is refused for stating a theorem that does not cover
  the unit it certifies, and the refusal must say so rather than be explained
  by a digest that no longer matches.

### JS3 — a non-strict `json_scan` request with that certificate falls back to the baseline

- **Actor:** the build integrator.
- **Given:** the same manifest, the same valid-certificate install as JS1, and
  the same theorem-changed certificate with its manifest digest as JS2.
- **When:** the integrator invokes the selector with `UNIT=json_scan STRICT=0`
  into separate `OUT` and `RECORD` paths.
- **Then:** it exits 0; the selection record's `selected` field is `baseline`;
  and the record's `reason` field equals exactly `proof rejected: invalid
  certificate; installed baseline fallback`.
- **Why:** a refused JSON unit certificate must keep the seam installed at the
  baseline and must be recorded as a rejection, not as an accepted proof and not
  as a blanket refusal of the unit.
