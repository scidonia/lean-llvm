#!/usr/bin/env bash
# Run a command under a hard memory cap.
#
# A runaway elaboration does not fail -- it grows until the host has nothing
# left and every other process starts failing instead.  Three probes did that
# here in one session: 13 GB, 8 GB and 24 GB, each after several minutes, while
# the machine sat at 0-3 GB free and unrelated commands timed out.
#
# A cap turns that into one failed command with a diagnosable exit, which is
# what a probe that will not converge should look like.
#
# Usage:
#   probes/install/mem-capped.sh -- lake env lean /tmp/probe.lean
#   probes/install/mem-capped.sh --cap 12G -- lake build LeanLLVM.Refinement.Foo
#
# The default is deliberately generous: a module that legitimately needs more
# than this is better rebuilt than unbuildable.
set -euo pipefail

cap=${LEAN_MEM_MAX:-6G}
if [ "${1:-}" = "--cap" ]; then cap=$2; shift 2; fi
[ "${1:-}" = "--" ] && shift
[ $# -ge 1 ] || { echo "mem-capped: no command given" >&2; exit 2; }

if ! command -v systemd-run >/dev/null 2>&1; then
  echo "mem-capped: systemd-run absent; running uncapped" >&2
  exec "$@"
fi

exec systemd-run --user --scope --quiet \
  -p MemoryMax="$cap" -p MemorySwapMax=0 -- "$@"
