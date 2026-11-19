#!/usr/bin/env bash
# Run the entry-opt experiment on `syn-strings-64k`, at the route's compiler
# line and arm, and save the transcript beside this script.
#
#   nix develop -c bash probes/json/route/entry-opt/run.sh
#   nix develop -c bash probes/json/route/entry-opt/run.sh --rounds 21 --reps 31
#
# The script builds first, runs the gates alone (so a gate failure is reported
# before any clock), then refuses to time while Lean is building or elaborating:
# an explicit `lake build` / `lake -c` / `lean -c` / `lean --run` / `leanc`
# command line, the repository's `.lake/install-certificate.lock` directory, or
# more than 5 Lean CPU ticks across the host in one wall-clock second.  Idle
# language-server `lean --server` / `lean --worker` processes are listed but are
# not a build; the CPU delta is what distinguishes them.  The process snapshot,
# the lock state and the sampled delta are written to the transcript.
#
# The harness runs its own gates before and after its clock.  A gate failure
# exits 3 and no row is a measurement.
set -euo pipefail
export LC_ALL=C

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../../.." && pwd)
log=$here/transcript.txt
doc=$repo/tests/json-units-bench/build/corpus/syn-strings-64k.json
rounds=15
reps=21
passes=8
core=0
gates_only=0
preflight=1
build=${BUILD_DIR:-}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --rounds) shift; rounds=${1:-}; [ -n "$rounds" ] || { echo "--rounds needs a value" >&2; exit 2; } ;;
    --reps) shift; reps=${1:-}; [ -n "$reps" ] || { echo "--reps needs a value" >&2; exit 2; } ;;
    --passes) shift; passes=${1:-}; [ -n "$passes" ] || { echo "--passes needs a value" >&2; exit 2; } ;;
    --core) shift; core=${1:-}; [ -n "$core" ] || { echo "--core needs a value" >&2; exit 2; } ;;
    --doc) shift; doc=${1:-}; [ -n "$doc" ] || { echo "--doc needs a value" >&2; exit 2; } ;;
    --log) shift; log=${1:-}; [ -n "$log" ] || { echo "--log needs a value" >&2; exit 2; } ;;
    --gates-only) gates_only=1 ;;
    --no-preflight) preflight=0 ;;
    --help) sed -n '2,22p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "run: unknown argument $1" >&2; exit 2 ;;
  esac
  shift
done

[ -f "$doc" ] || { printf 'SETUP: absent document %s\n' "$doc" >&2; exit 2; }
[ -n "$build" ] || build=$(mktemp -d "${TMPDIR:-/tmp}/json-entry-opt.XXXXXX")

rflag=()
doc_sha=$(sha256sum "$doc" | cut -d' ' -f1)
if [ "$(stat -c %s "$doc")" = 65536 ] &&
   [ "$doc_sha" = bd007090d7a5ab09a1fc69c0b96879f101dbf8b3f13a300d7d3e46127d26fb12 ]; then
  rflag=(--recorded)
fi

: >"$log"
emit() { printf '%s\n' "$*" >>"$log"; printf '%s\n' "$*"; }

emit "# command: $0 $*"
emit "# build directory: $build"
emit "# install: $(uname -srm)"
emit "# cpu: $(awk -F: '/^model name/ { sub(/^ /, "", $2); print $2; exit }' /proc/cpuinfo)"
emit "# cpus online: $(nproc); pinned to: cpu$core"
emit "# scaling governor (cpu0): $(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null || echo unknown)"
emit "# load average at start: $(cat /proc/loadavg)"
emit "# document: $doc size=$(stat -c %s "$doc") sha256=$(sha256sum "$doc" | cut -d' ' -f1)"
emit "# document pin: $(if [ ${#rflag[@]} -gt 0 ]; then echo recorded; else echo unrecorded; fi)"
emit "# revision: $(git -C "$repo" rev-parse HEAD 2>/dev/null || echo unknown)"
emit ""

# --- build ------------------------------------------------------------------
emit "## the build"
if ! BUILD_DIR=$build CORPUS=$doc bash "$here/build.sh" >>"$log" 2>&1; then
  emit "SETUP: build failed; see $log"
  exit 2
fi
emit ""

# --- the Lean gate ----------------------------------------------------------
comm_of() { cat "/proc/$1/comm" 2>/dev/null; }
lean_cpu_ticks() {
  local total=0 pid comm raw rest
  for d in /proc/[0-9]*; do
    pid=${d#/proc/}
    comm=$(comm_of "$pid") || continue
    case "$comm" in
      *lean*|lake) ;;
      *) continue ;;
    esac
    raw=$(cat "$d/stat" 2>/dev/null) || continue
    rest=${raw##*") "}
    set -- $rest
    total=$(( total + ${12:-0} + ${13:-0} ))
  done
  printf '%s\n' "$total"
}

lean_gate() {
  local before after delta explicit lock
  emit "## the Lean gate (immediately before this run)"
  emit "processes matching 'lake build|bin/lean':"
  pgrep -af 'lake build|bin/lean' >>"$log" 2>/dev/null || emit "  (none)"
  explicit=$(ps -eo args= --no-headers |
    grep -E '(^|/)(lake build|lake env lean -c)|lean -c |lean --run|leanc ' |
    grep -v 'grep -E' || true)
  lock="absent"
  [ -e "$repo/.lake/install-certificate.lock" ] && lock="held"
  before=$(lean_cpu_ticks)
  sleep 1
  after=$(lean_cpu_ticks)
  delta=$(( after - before ))
  emit "install-certificate lock: $lock"
  emit "lean-cpu ticks: before=$before after=$after delta=$delta (HZ=$(getconf CLK_TCK); threshold=5 ticks/s)"
  emit "load average: $(cat /proc/loadavg)"
  if [ -n "$explicit" ]; then
    emit "SETUP: a Lean build or compile is running:"
    printf '%s\n' "$explicit" >>"$log"
    emit "refusing to time"
    return 1
  fi
  if [ "$lock" = "held" ]; then
    emit "SETUP: .lake/install-certificate.lock is held; refusing to time"
    return 1
  fi
  if [ "$delta" -ge 5 ]; then
    emit "SETUP: Lean consumed $delta ticks in 1 s (>= 5); refusing to time"
    return 1
  fi
  emit "gate: no Lean build or compile active; the clock may run"
  emit ""
  return 0
}

# --- the gates alone --------------------------------------------------------
# The harness runs the same gates inside the timed process, immediately before
# its clock, and again after it.  `--no-preflight` skips this separate run when
# the machine's Lean activity leaves only a short window; nothing is untested,
# because the in-process gates are the ones a row depends on.
if [ "$preflight" = 1 ]; then
  emit "## the gates (no clock)"
  set +e
  taskset -c "$core" "$build/entry-opt" --doc "$doc" --passes "$passes" \
    "${rflag[@]}" --gates-only 2>&1 | tee -a "$log"
  gstatus=${PIPESTATUS[0]}
  set -e
  emit ""
  emit "# gates-only exit status: $gstatus"
  emit ""
  if [ "$gstatus" -ne 0 ]; then
    emit "SETUP: the gates did not hold; no measurement"
    exit 3
  fi
else
  emit "## preflight skipped (--no-preflight); the harness's in-process gates decide"
  emit ""
fi
if [ "$gates_only" = 1 ]; then
  emit "transcript: $log"
  exit 0
fi

# --- the clock --------------------------------------------------------------
if ! lean_gate; then
  exit 2
fi
before_ticks=$(lean_cpu_ticks)
sweep_start=$(date +%s%N)
set +e
taskset -c "$core" "$build/entry-opt" --doc "$doc" --rounds "$rounds" \
  --reps "$reps" --passes "$passes" "${rflag[@]}" 2>&1 | tee -a "$log"
status=${PIPESTATUS[0]}
set -e
sweep_end=$(date +%s%N)
after_ticks=$(lean_cpu_ticks)
emit ""
emit "# sweep exit status: $status"
emit "# sweep wall: $(( (sweep_end - sweep_start) / 1000000 )) ms"
emit "# lean-cpu ticks across the sweep: before=$before_ticks after=$after_ticks delta=$(( after_ticks - before_ticks ))"
emit "# load average after the sweep: $(cat /proc/loadavg)"
emit ""
if [ "$status" -ne 0 ]; then
  emit "SETUP: the run failed; the rows are not a measurement"
  exit 3
fi
if ps -eo args= --no-headers |
     grep -E '(^|/)(lake build|lake env lean -c)|lean -c |lean --run|leanc ' |
     grep -v 'grep -E' >/dev/null; then
  emit "SETUP: a Lean build began during the sweep; the rows are not a measurement"
  exit 3
fi
# A build that started and finished inside the sweep is not an explicit command
# by the time it is checked; the CPU delta over the sweep's wall time is.
if [ "$(( after_ticks - before_ticks ))" -ge 20 ]; then
  emit "SETUP: Lean consumed $(( after_ticks - before_ticks )) ticks during the sweep; the rows are not a measurement"
  exit 3
fi
emit "transcript: $log"
