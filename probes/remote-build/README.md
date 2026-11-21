# Remote Lean lane

A leased Compute Engine worker carries a warm copy of this repository and its
Lake state, so a second cone can elaborate while the local checkout builds.
Nothing here is committed from the worker: it is a build lane, not a committer.

## Prerequisites

- `gcloud` under `nix shell nixpkgs#google-cloud-sdk`, `bun`, and the `agents`
  configuration (`gcloud auth print-access-token --configuration=agents`).
- A worker leased for the session, from the pack checkout (the Lean image is
  chosen automatically in a Lean project; `--lean` forces it):

  ```bash
  bun scripts/gcloud-worker.ts create --purpose lean-prover --cores 8 \
    --memory-gb 64 --disk-gb 80 --lease 8h --session <session-id>
  ```

  The worker is spot, has no external address, and every byte reaches it
  through the IAP tunnel.  Teardown is `delete --session <session-id>`.

## Provisioning (once per worker)

The Lean image (`nixos-lean-x86-64`) already carries Lean 4.35.0 and Lake
5.0.0-src from `/run/current-system/sw/bin`; the flake uses the same toolchain.
Mathlib and every Lean library it requires come from the flake's
`leanPackagesWithExports`, whose closure is copied to the worker once (11 GiB
over the tunnel, 9m55s) or baked into the image.  The worker has no internet.

```bash
R=/home/gavin/dev/Scidonia/lean-llvm
# same absolute path on the worker, owned by the OS Login user
<remote> run -- "sudo -n mkdir -p $R && sudo -n chown -R $(id -un):$(id -gn) /home/gavin"
```

Transfer from a **quiescent** checkout, so oleans, traces and sources describe
the same revision.  Exclude executables (`.lake/build/bin`); keep `.ir`, oleans,
ileans, `.hash` and `.trace` — dropping `.ir` invalidates modules and forces a
full re-elaboration.  The excluded executables are relinked on the worker from
the transferred `.ir` tree's `.c.o.export` bitcode; no mathlib module is
recompiled.  The repository carries no `.lake/packages`.

```bash
W=$(nix develop -c bash -c 'command -v lake')
<remote> closure "$(readlink -f "$W")"

tar -C "$R" -cf - --exclude=./.git --exclude=./.direnv \
  --exclude=./.lake/build/bin --exclude=./.lake/install-certificate.lock . \
  | zstd -T0 -3 -o /tmp/repo-cache.tar.zst
<remote> copy --to /tmp/repo-cache.tar.zst /tmp/repo-cache.tar.zst
<remote> run -- "cd $R && zstd -d -c /tmp/repo-cache.tar.zst | tar -xf -"
```

Measured on the 8-vCPU worker: the package closure is 11 GiB and takes 9m55s
through the tunnel once per worker; the repository bundle is 1,017 MiB packed to
251.6 MB in 1 s and uploaded in 21 s.  The first full build after extraction
takes **78 s** over 2,186 jobs, 24 s of it the `leanllvm` relink; its trace names
768 exports under the store packages and none under `.lake/packages`.

## Worker sizing

The standard and its decision rule are in `AGENTS.md` ("Remote worker sizing").
This file records the measurements that set them.

| date | tree | shape | command | peak | note |
|---|---|---|---|---|---|
| 2026-11-19 | `d3a3d13` | `e2-highmem-8` | `lake env lean …/JsonStage2WalkScopeClassAB.lean` | **1,908 MB** / 15 s | single largest leaf; idle ~1.4 GB; 0.5 s sampling |
| 2026-11-20 | `986d7bc` | `e2-standard-8` | `bash probes/install/lake-locked.sh build` | **24,240 MB** / 1,690 s, 2,209 jobs | full default target, fresh tree with no `.lake`; `free -m` used, 0.5 s sampling; ~7 GB spare on 32 GB, so the standard shape holds |

Measure on the worker with the shipped instrument, running the full default
target (not one module):

```bash
<remote> copy --to /tmp/measure-peak.sh probes/remote-build/measure-peak.sh
<remote> run -- "export PATH=<store-wrapper>/bin:\$PATH; cd $R && \
  bash /tmp/measure-peak.sh -- bash probes/install/lake-locked.sh build"
```

Record a row here with the date, tree, command, peak and the shape chosen.
`free` at a 0.5 s interval can miss a sub-second spike; a systemd
`MemoryPeak` is the stronger instrument where a user manager exists.

## Building a cone

`remote-lean.sh` copies the named files and runs one Lake command on the
worker under the same elaboration lock:

```bash
SID=<session-id> bash probes/remote-build/remote-lean.sh \
  --files LeanLLVM/Refinement/Foo.lean -- build LeanLLVM.Refinement.Foo
```

Only the named files are sent; the worker's `.lake/build` keeps everything
already built.  A file the target imports but that was not named is stale on
the worker, so name every changed source the target reads.

## Limits

- The worker's repository path must equal the local one; `remote-lean.sh` uses
  the same absolute path on both sides.  The store package tree must exist at
  its recorded paths (copied once or baked into the image); a replay hashes the
  toolchain from its version string, but a re-elaboration names the running
  sysroot.
- A cancelled client does not stop the remote build.  Run a build expected to
  outlive the tunnel under `setsid` with a pid and status file, and kill it by
  that pid; `pkill -f` from inside `run` matches the ssh command string and
  kills its own shell.
- A copied `.lake/build` is **not** a cache to trust: an olean can be older than
  its `.trace` (a copied tree can pair a current trace with an older olean), and
  Lake will load it as current, failing later on a lemma the source has. Rebuild
  the target's closure from source, or probe a recently added lemma with
  `strings <olean> | grep`, before reading a build result from a copied tree.
- Do not tar `.lake/build` while a build or a `lake serve` is running: a stale
  snapshot silently pairs new sources with old oleans, or omits a module's
  output entirely.
- Do not time benchmarks here; the hardware differs from the measurement host.
- A spot worker can be preempted mid-build; that is a rerun, not a result.
