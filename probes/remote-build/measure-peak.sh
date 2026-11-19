#!/usr/bin/env bash
# Measure the peak memory of one command on a worker.
#
#   bash measure-peak.sh -- bash probes/install/lake-locked.sh build <target>
#
# Run it on the worker, with `lake` on PATH (the store wrapper, when the
# packages come from the flake).  It samples `free -m`'s used column, which
# excludes page cache, and prints the peak, the elapsed time and the sample
# count.  The sample interval is 0.5 s by default (`INTERVAL` overrides it);
# a sub-interval spike can be missed, so a systemd `MemoryPeak` is the
# stronger instrument where a user manager exists.
#
# Idle memory is not a sizing signal: run the full default target, not one
# module, and size the machine from that peak.
set -euo pipefail

[ "$#" -gt 0 ] || {
  echo "usage: measure-peak.sh -- <command...>" >&2
  exit 2
}
[ "$1" = "--" ] || {
  echo "measure-peak.sh: the command must follow --" >&2
  exit 2
}
shift

interval=${INTERVAL:-0.5}
samples=$(mktemp)
trap 'rm -f "$samples"' EXIT

( while :; do free -m | awk 'NR==2{print $3}'; sleep "$interval"; done ) > "$samples" &
sampler=$!

start=$(date +%s)
rc=0
"$@" || rc=$?
end=$(date +%s)
kill "$sampler" 2>/dev/null || true

peak=$(sort -n "$samples" | tail -1)
count=$(wc -l < "$samples")
echo "COMMAND=$*"
echo "RC=$rc ELAPSED=$((end - start))s PEAK_USED_MB=${peak:-0} SAMPLES=$count INTERVAL=${interval}s"
exit "$rc"
