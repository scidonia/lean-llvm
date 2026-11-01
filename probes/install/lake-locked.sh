#!/usr/bin/env bash
# Run one Lake command under the repository source-elaboration lock.
#
#   bash probes/install/lake-locked.sh build LeanLLVM.Vellum.CommaMaskIR
#   bash probes/install/lake-locked.sh exe leanllvm-loop-emit
#
# Lake rewrites the project's oleans and executables, so a warm-up build or the
# emitter that regenerates a fixture is a source-elaboration writer like the
# certificate producer.  It takes the same
# `.lake/install-certificate.lock` directory the install builder, the app
# builder and the selector take, and releases it before the caller's own
# builder runs.  A contender refuses instead of racing, and a lock that cannot
# be removed is a nonzero exit rather than a warning.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
lock_dir="$repo/.lake/install-certificate.lock"
lock_held=0

[ "$#" -gt 0 ] || {
  echo "lake-locked: usage: lake-locked.sh <lake arguments...>" >&2
  exit 2
}

acquire_lock() {
  mkdir -p "$repo/.lake"
  if ! mkdir "$lock_dir" 2>/dev/null; then
    echo "lake-locked: another source elaboration holds $lock_dir" >&2
    echo "lake-locked: if no such run exists, verify that and remove that directory" >&2
    return 1
  fi
  lock_held=1
}

release_lock() {
  [ "$lock_held" = 1 ] || return 0
  lock_held=0
  if ! rmdir "$lock_dir" 2>/dev/null; then
    echo "lake-locked: could not remove $lock_dir" >&2
    echo "lake-locked: verify that no run owns it and remove that directory" >&2
    return 1
  fi
}

cleanup() {
  local status=$?
  release_lock || status=1
  exit "$status"
}
trap cleanup EXIT

if ! acquire_lock; then
  exit 1
fi
cd "$repo"
lake "$@"
