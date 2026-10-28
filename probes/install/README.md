# Installation probe: link-time selection at an opaque seam

This probe exercises the installation point described in
`docs/m0-runtime-noise-report.md` and the accompanying design discussion.

- `Caller.lean` sees only `@[extern]` declarations for the seam and an
  implementation marker.
- `Baseline.lean` and `Candidate.lean` are separate objects that define the
  same seam symbol with different bodies. The baseline is the exact SWAR
  mask; the candidate is a byte loop.
- `build.sh` compiles the three modules to C, then to objects, runs a
  differential corpus through both bodies, writes `differential.txt` and
  `manifest.env`, and records the hashes.
- `select.sh` verifies the manifest, the certificate, the target, the symbol
  and the caller import, then links either the candidate or the baseline.
  `STRICT=1` fails instead of falling back.
- `check.sh` runs the whole flow, including a stale-candidate fallback a
  strict-mode rejection, and compares the semantic outputs.

Run from the repository root:

```bash
nix develop -c bash probes/install/check.sh
```

The certificate is a **differential transcript**, not a Lean proof. The probe
certifies the installation mechanics: artifact binding, selection, fallback and
the surviving seam. The semantic proof and the contextual theorem remain the
next work package.

Inspect the evidence:

```bash
cat probes/install/build/selection_candidate.env
cat probes/install/build/selection_fallback.env
cat probes/install/build/out_candidate.txt
cat probes/install/build/out_fallback.txt
```
