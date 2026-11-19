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
5.0.0-src from `/run/current-system/sw/bin`.  At the revision this lane was
validated against, the image's `lake` and the dev shell's resolved to the same
store path, so no toolchain closure is copied; only the repository and the Lake
cache travel.  The worker has no internet.

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
recompiled.

```bash
tar -C "$R" -cf - --exclude=./.git --exclude=./.direnv \
  --exclude=./.lake/build/bin --exclude=./.lake/install-certificate.lock . \
  | zstd -T0 -3 -o /tmp/repo-cache.tar.zst
<remote> copy --to /tmp/repo-cache.tar.zst /tmp/repo-cache.tar.zst
<remote> run -- "cd $R && zstd -d -c /tmp/repo-cache.tar.zst | tar -xf -"
```

Measured at `35b9d40` on the 8-vCPU worker: the source and cache tree is
8.6 GB and 155,415 files; zstd at level 3 packs it to **2.18 GiB in 25 s**, the
tunnel carries **2.34 GB in 3m46s**, and extraction takes **28.8 s**.  The
default `lake build` then finishes in **22 s** (2,186 jobs, links `leanllvm`),
a replayed cone takes 5 s, and an explicit relink after removing
`.lake/build/bin` takes 9 s.  No project or mathlib module re-elaborated.

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
  the same absolute path on both sides.  The recorded toolchain store paths need
  not exist on the worker: a replay hashes the toolchain from its version
  string, but a re-elaboration names the running sysroot.
- A cancelled client does not stop the remote build.  Run a build expected to
  outlive the tunnel under `setsid` with a pid and status file, and kill it by
  that pid; `pkill -f` from inside `run` matches the ssh command string and
  kills its own shell.
- Do not tar `.lake/build` while a build or a `lake serve` is running: a stale
  snapshot silently pairs new sources with old oleans, or omits a module's
  output entirely.
- Do not time benchmarks here; the hardware differs from the measurement host.
- A spot worker can be preempted mid-build; that is a rerun, not a result.
