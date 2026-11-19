#!/usr/bin/env bash
# remote-lean.sh -- send changed files to the session's GCE worker and run one
# Lake command there.
#
#   SID=<omp session id> bash probes/remote-build/remote-lean.sh \
#     --files LeanLLVM/Refinement/Foo.lean [more...] -- \
#     build LeanLLVM.Refinement.Foo
#
# The worker holds a warm copy of this repository at the same absolute path,
# transferred once with the recipe in README.md.  This script copies only the
# named files and then runs one command under probes/install/lake-locked.sh on
# the worker.  It never edits or commits the repository.
#
# Requires: gcloud (nix shell nixpkgs#google-cloud-sdk), bun, the `agents`
# gcloud configuration, and a worker reachable by SID (see README.md).
set -euo pipefail

repo=$(cd "$(dirname "$0")/../.." && pwd)
pack=${PACK:-/home/gavin/.omp/plugins/node_modules/@scidonia/omp-tools}
sid=${SID:?set SID to the OMP session id whose worker to use}
remote_root=${REMOTE_ROOT:-$repo}

# A worker image that already carries the dev shell's Lean and Lake needs no
# store variables: builds resolve them from the image's profile.  Set a
# variable only when the worker lacks that tool and the closure was copied to
# it; the repository's own `.lake/packages` supplies mathlib and the Lake
# dependencies, so no dependency store path is needed here.
lake_store=${LAKE_STORE:-}
lean_store=${LEAN_STORE:-}
clang_store=${CLANG_STORE:-}
git_store=${GIT_STORE:-}
coreutils_store=${COREUTILS_STORE:-}
bash_store=${BASH_STORE:-}
# zstd/tar are only needed by the provisioning recipe, not by builds.

remote() {
  ( cd "$pack" && nix shell nixpkgs#google-cloud-sdk nixpkgs#bun -c \
      bun scripts/gcloud-remote.ts "$@" )
}

files=()
while [ "$#" -gt 0 ]; do
  case $1 in
    --files) shift; while [ "$#" -gt 0 ] && [ "$1" != -- ]; do files+=("$1"); shift; done ;;
    --) shift; break ;;
    *) echo "remote-lean: unexpected argument $1" >&2; exit 2 ;;
  esac
done
[ "${#files[@]}" -gt 0 ] && [ "$#" -gt 0 ] || {
  echo "usage: SID=<id> bash probes/remote-build/remote-lean.sh --files <path>... -- <lake args...>" >&2
  exit 2
}

for f in "${files[@]}"; do
  [ -f "$repo/$f" ] || { echo "remote-lean: no such file: $f" >&2; exit 2; }
  remote copy --session "$sid" --to "$repo/$f" "$remote_root/$f" >/dev/null
done

path=""
for d in "$lake_store" "$lean_store" "$clang_store" "$git_store" "$coreutils_store" "$bash_store"; do
  [ -n "$d" ] && path="$path$d/bin:"
done
path="${path%:}"
if [ -n "$path" ]; then
  prefix="export PATH=$path:\$PATH; "
else
  prefix=""
fi
echo "remote-lean: building on worker: lake $*" >&2
remote run --session "$sid" -- \
  "${prefix}cd $remote_root && bash probes/install/lake-locked.sh $*"
