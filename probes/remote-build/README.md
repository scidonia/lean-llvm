# Remote Lean lane

A leased Compute Engine worker carries a warm copy of this repository and its
Lake state, so a second cone can elaborate while the local checkout builds.
Nothing here is committed from the worker: it is a build lane, not a committer.

## Prerequisites

- `gcloud` under `nix shell nixpkgs#google-cloud-sdk`, `bun`, and the `agents`
  configuration (`gcloud auth print-access-token --configuration=agents`).
- A worker leased for the session, booted from the project's precompiled image
  family for its architecture, with the image's 50 GB boot disk:

  ```bash
  bun scripts/gcloud-worker.ts create --purpose lean-prover --cores 8 \
    --memory-gb 64 --disk-gb 50 --lease 8h --session <session-id> \
    --image-family lean-llvm-precompiled-x86-64
  ```

  `--arch aarch64 --image-family lean-llvm-precompiled-aarch64` selects the Arm
  family.  The worker is spot, has no external address, and every byte reaches
  it through the IAP tunnel.  Teardown is `delete --session <session-id>`.

## Provisioning (once per worker)

A worker from a precompiled family already has the checkout at the OS Login
user's home (`$HOME/lean-llvm`), the bare mirror beside it, the realised dev
shell and the full build, so it does not re-clone.  It fetches the task's ref
into the existing tree and only what changed is re-elaborated:

```bash
bun scripts/gcloud-remote.ts git-push --session <session-id> \
  --repo . --remote $HOME/lean-llvm.git --ref main
bun scripts/gcloud-remote.ts run --session <session-id> --dir $HOME/lean-llvm -- \
  'git fetch origin main && git merge --ff-only FETCH_HEAD && nix develop -c lake build'
```

Measured on the 8-vCPU bake instances (`n4d-highmem-8` for x86-64,
`n4a-highmem-8` for aarch64): the second `nix develop -c lake build` takes
**1.6 s** and **2.0 s**.  The first build on a freshly booted 4-vCPU worker
(`n4-standard-4`, `n4a-standard-4`, both in `europe-west4-b`) takes 29 s and
15 s because the I/O and startup are cold, then about a second.  The full
build the image contains took 21.5 and 17.3 minutes.  Both families were baked
on 2026-11-23 from revision `8c65035` (image labels `source-rev`/`source-repo`),
are stored in `europe-west4`, need `--disk-gb 50`, and nothing rebuilds them
automatically.

### From a plain worker

A worker from a plain image has Nix but no Lean; the flake's dev shell supplies
the toolchain and mathlib, so the shell's closure is the whole environment.
Use this route for a tree far from the baked revision.

```bash
R=$HOME/lean-llvm
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

## Rebaking the images

The families `lean-llvm-precompiled-x86-64` and `lean-llvm-precompiled-aarch64`
commit to one revision each, so they are rebaked when the tree has moved far
enough that a checkout on top of the bake re-elaborates for minutes.  The
triggers are in `AGENTS.md` ("Precompiled worker images").

Bake from the plain image, on demand, sized for the full build (8 vCPU, 64 GB,
50 GB disk — the peak is 27.9 GB and the build about 20 minutes):

```bash
bun scripts/gcloud-worker.ts create --purpose lean-llvm-bake --cores 8 \
  --memory-gb 64 --disk-gb 50 --lease 8h --session <session-id> \
  --image-family nixos-x86-64 --ondemand
# --arch aarch64 --image-family nixos-aarch64 for the Arm bake
```

Push the target commit into a bare mirror in the worker's home, clone it, and
build.  The first `nix develop` realises the dev shell (8m39s on x86-64 and
3m46s on aarch64 — different regions, so that gap is mostly download; both
substitute from `cache.nixos.org`), and the build takes 21.5 minutes on
`n4d-highmem-8` and 17.3 minutes on `n4a-highmem-8`.

```bash
bun scripts/gcloud-remote.ts run --session <id> -- 'git init -q --bare -b main $HOME/lean-llvm.git'
bun scripts/gcloud-remote.ts git-push --session <id> --repo . \
  --remote $HOME/lean-llvm.git --ref main
bun scripts/gcloud-remote.ts run --session <id> -- \
  'git clone -q $HOME/lean-llvm.git $HOME/lean-llvm'
bun scripts/gcloud-remote.ts tmux-run --session <id> --dir $HOME/lean-llvm -- \
  'nix develop -c lake build'
```

Keep the bare mirror in the image and leave the clone's `origin` pointing at
it: that is how a spawned worker receives its ref.  Root the shell closure and
the flake inputs so a garbage collection cannot remove what an offline
`nix develop` needs:

```bash
<remote> run --dir $HOME/lean-llvm -- 'mkdir -p $HOME/.nix-roots &&
  nix build --out-link $HOME/.nix-roots/devshell .#devShells.<system>.default &&
  for p in /nix/store/*-source; do
    nix-store --add-root $HOME/.nix-roots/in-$(basename "$p") --indirect -r "$p"
  done'
```

Run `nix develop -c lake build` a second time and require about two seconds: a
longer build means the package cache is copying again (its stamps are gone) or
the checkout is dirty.  Then write the provenance file, stop the instance, and
freeze its disk under the family — the same family name, the base image's guest
OS features (`GVNIC`, plus `UEFI_COMPATIBLE` on Arm), and the revision label:

```bash
<remote> run --dir $HOME/lean-llvm -- 'printf "%s\n" <family> \
  "revision $(git rev-parse HEAD)" "baked <date>" > $HOME/lean-llvm.IMAGE && sync'

gcloud --configuration=agents compute instances stop <instance> --zone=<zone>
gcloud --configuration=agents compute images create <family>-<date> \
  --project=agentic-resources --source-disk=<instance> --source-disk-zone=<zone> \
  --family=<family> --storage-location=europe-west4 \
  --guest-os-features=GVNIC --labels=source-rev=<short-sha>,source-repo=lean-llvm
```

`--source-disk` reads the disk directly, so nothing goes through the image
bucket and the `agents` identity's `compute.instanceAdmin.v1` is enough.  Add
`UEFI_COMPATIBLE` on Arm.

Keep both families in the same storage location (`europe-west4`): a worker
created in another region streams the image there, which inflates its create
time and makes spawn timings look like an architecture difference.  An image
already stored elsewhere is moved by creating a new image from it —
`--source-image=<old> --storage-location=europe-west4` with the same family and
guest OS features, then deleting the old one; the location cannot be changed in
place.

Finally boot a disposable worker from the family with `--disk-gb 50` and
require the baked revision, then the **second** `lake build` to report about a
second — the first pays cold I/O and may take 30 s:

```bash
bun scripts/gcloud-worker.ts create --purpose verify --cores 4 --memory-gb 16 \
  --disk-gb 50 --lease 1h --session <id> --image-family <family> --ondemand
bun scripts/gcloud-remote.ts run --session <id> --dir $HOME/lean-llvm -- \
  'git log -1 --format=%H && time nix develop -c lake build &&
   time nix develop -c lake build'
```

Delete the bake and verify instances afterwards; the previous image stays
bootable (and billed) until it is deleted, and the newest image in a family is
what a spawn gets.

`gcloud-remote.ts` resolves a worker by `--session`.  With more than one worker
in the session (a bake and a verify at the same time, say) that lookup is
ambiguous; pass `--name <instance> --zone <zone>` instead.

## Worker sizing

The standard and its decision rule are in `AGENTS.md` ("Remote worker sizing").
This file records the measurements that set them.

| date | tree | shape | command | peak | note |
|---|---|---|---|---|---|
| 2026-11-19 | `d3a3d13` | `e2-highmem-8` | `lake env lean …/JsonStage2WalkScopeClassAB.lean` | **1,908 MB** / 15 s | single largest leaf; idle ~1.4 GB; 0.5 s sampling |
| 2026-11-20 | `986d7bc` | `e2-standard-8` | `bash probes/install/lake-locked.sh build` | **24,240 MB** / 1,690 s, 2,209 jobs | full default target, fresh tree with no `.lake`; `free -m` used, 0.5 s sampling; superseded by the `e3f8f2e` row once b3 and v2 merged |
| 2026-11-20 | `e3f8f2e` | `e2-standard-8` | `lake --packages=…/overrides.json build` | **27,867 MB** / 1,888 s, 2,227 jobs | merged b3 + phase-split v2 tree; first full-build peak above the 24 GB line, so the full default target takes **64 GB**; 32 GB leaves only ~4 GB headroom |

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
- Lean's package overrides live at `$HOME/.cache/lean-llvm/packages/overrides.json`
  on the worker; a host building outside `nix develop` finds the same tree at
  `/nix/store/<hash>-lean-packages-with-exports/lake-overrides.json`.  Pass the
  path that exists on the machine in hand; a missing overrides file is a setup
  error, not a proof failure.
- The `lake` shim runs `lean-llvm-overrides`, which copies each workspace
  package into `$HOME/.cache/lean-llvm/packages` once and records the store
  path in a stamp.  The stamps are what keep a second invocation from copying
  again; `tests/lake-cache-stamps.sh` checks both the copy and the no-copy
  case.  A cache that loses its stamps re-copies every package, which resets
  the mtimes Lake reads and makes each build redo its C objects.
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
