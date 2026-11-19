# Remote Lean lane

A leased Compute Engine worker carries a warm copy of this repository and its
Lake state, so a second cone can elaborate while the local checkout builds.
Nothing here is committed from the worker: it is a build lane, not a committer.

## Prerequisites

- `gcloud` under `nix shell nixpkgs#google-cloud-sdk`, `bun`, and the `agents`
  configuration (`gcloud auth print-access-token --configuration=agents`).
- A worker leased for the session, from the pack checkout:

  ```bash
  bun scripts/gcloud-worker.ts create --purpose lean-prover --cores 8 \
    --memory-gb 64 --disk-gb 80 --lease 8h --session <session-id>
  ```

  The worker is spot, has no external address, and every byte reaches it
  through the IAP tunnel.  Teardown is `delete --session <session-id>`.

## Provisioning (once per worker)

The worker has no internet, so tools arrive as Nix closures and the repository
arrives as a cache bundle.  Use the pack transport
(`scripts/gcloud-remote.ts`); `--to` names the local path and the positional
argument the remote path.

```bash
R=/home/gavin/dev/Scidonia/lean-llvm
# same absolute path on the worker, owned by the OS Login user
<remote> run -- "sudo -n mkdir -p $R && sudo -n chown -R $(id -un):$(id -gn) /home/gavin"
# tool closures: lake/lean, clang, git, coreutils, zstd, tar, bash
<remote> closure <lean> <clang> <git> <coreutils> <zstd> <tar> <bash>
```

Then transfer the source tree and the Lake cache from a **quiescent** checkout,
so oleans, traces and sources describe the same revision:

```bash
tar -C "$R" -cf - --exclude=./.git --exclude=./.direnv \
  --exclude=./.lake/build --exclude=./.lake/install-certificate.lock . \
  | zstd -T0 -3 -o /tmp/repo.tar.zst
<remote> copy --to /tmp/repo.tar.zst /tmp/repo.tar.zst
<remote> run -- "cd $R && zstd -d -c /tmp/repo.tar.zst | tar -xf -"

tar -C "$R" -cf - ./.lake/build | zstd -T0 -3 -o /tmp/build.tar.zst
<remote> copy --to /tmp/build.tar.zst /tmp/build.tar.zst
<remote> run -- "cd $R && zstd -d -c /tmp/build.tar.zst | tar -xf -"
```

Measured at `550c03611c` on an `e2-highmem-8`: 2.0 GiB source+cache bundle,
556 MiB build bundle, roughly six minutes of transfer; the module target
elaborated in 104 s and the full target replayed in 2 s.

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

- The worker's paths and Nix store paths must match the local ones; the script
  names the store paths it was provisioned with.
- Do not tar `.lake/build` while a build is running: a stale snapshot silently
  pairs new sources with old oleans.
- Do not time benchmarks here; the hardware differs from the measurement host.
- A spot worker can be preempted mid-build; that is a rerun, not a result.
