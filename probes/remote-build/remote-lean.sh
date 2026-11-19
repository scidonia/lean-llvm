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

# Tool store paths copied to the worker by the provisioning recipe.  A change
# here is a provisioning change: copy the new closure first (README.md).
lean_store=${LEAN_STORE:-/nix/store/2kbz20qdy9vdnc0ilrnmpnd551dk0z09-lean4-4.35.0}
clang_store=${CLANG_STORE:-/nix/store/i52d7j6ma8bh4ggg4r2hl4af7bychdpa-clang-wrapper-21.1.8}
git_store=${GIT_STORE:-/nix/store/xgw813vgzl2q0696sq45adpj0xd690jq-git-2.56.0}
coreutils_store=${COREUTILS_STORE:-/nix/store/cb987zkxvsv0490753ilrvn5yk7ylgxi-coreutils-9.12}
bash_store=${BASH_STORE:-/nix/store/nnm9gdr70ihc6zc9298mzz8jpcgaciql-bash-5.3p20}
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

path="$lean_store/bin:$clang_store/bin:$git_store/bin:$coreutils_store/bin:$bash_store/bin"
echo "remote-lean: building on worker: lake $*" >&2
remote run --session "$sid" -- \
  "export PATH=$path:\$PATH; cd $remote_root && bash probes/install/lake-locked.sh $*"
