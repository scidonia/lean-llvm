#!/usr/bin/env bash
# Run the C-only cost profile of the route's native interval on
# `syn-strings-64k`, arm 2, and save the transcript beside this script.
#
#   nix develop -c bash probes/json/route/cost-profile/run.sh
#   nix develop -c bash probes/json/route/cost-profile/run.sh --rounds 31 --reps 21 --core 0
#
# Two sweeps run with the same binary: `--context route`, which precedes every
# timed act with the route's fresh call and the reused admission and staging,
# and `--context none`, which runs the acts back to back.  The difference
# between the sweeps is the context term, measured rather than assumed.  After
# them, `probes/json/route/workspace.sh` runs in the same session, so the route's
# reused-native figure and this instrument's rows belong to one host state.
#
# Before every sweep the script refuses to time when Lean is building: an
# explicit `lake build` / `lean -c` / `lean --run` / `leanc` command line, or
# more than 50 ms of Lean CPU across the host in one wall-clock second (the
# language server's idle workers sit near 1 tick/s at HZ=100; a build is far
# above the threshold).  The process snapshot and the sampled delta are written
# to the transcript before each sweep.
#
# The instrument's own gates run before its clock: the separate stage-1 loop and
# stage 2 must reproduce the pipeline's streams and bytes, the independent scan
# must reproduce the escape list, the direct expander over the 620 escaped
# bodies must reproduce the arena and the cursor, and the admission must select
# arm 2.  A gate failure exits 3.  The same gates run again after the rounds.
#
# The route binary's `--consume-events` row is read as a second binary's reading
# of the same kernel and compared field by field; it is not an independent
# parser and the report says so.
set -euo pipefail
export LC_ALL=C

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../../.." && pwd)
log=$here/transcript.txt
doc=$repo/tests/json-units-bench/build/corpus/syn-strings-64k.json
route=$repo/probes/json/route/build/leanllvm-json-route
rounds=15
reps=21
core=0
win_offset=3
placement=0
build=${BUILD_DIR:-}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --rounds) shift; rounds=${1:-}; [ -n "$rounds" ] || { echo "--rounds needs a value" >&2; exit 2; } ;;
    --reps) shift; reps=${1:-}; [ -n "$reps" ] || { echo "--reps needs a value" >&2; exit 2; } ;;
    --core) shift; core=${1:-}; [ -n "$core" ] || { echo "--core needs a value" >&2; exit 2; } ;;
    --doc) shift; doc=${1:-}; [ -n "$doc" ] || { echo "--doc needs a value" >&2; exit 2; } ;;
    --win-offset) shift; win_offset=${1:-}; [ -n "$win_offset" ] || { echo "--win-offset needs a value" >&2; exit 2; } ;;
    --placement) placement=1 ;;
    --help) sed -n '2,32p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "run: unknown argument $1" >&2; exit 2 ;;
  esac
  shift
done

[ -f "$doc" ] || { printf 'SETUP: absent document %s\n' "$doc" >&2; exit 2; }
[ -n "$build" ] || build=$(mktemp -d "${TMPDIR:-/tmp}/json-cost-profile.XXXXXX")

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
emit ""

# --- build ------------------------------------------------------------------
emit "## the build"
if ! BUILD_DIR=$build CORPUS=$doc bash "$here/build.sh" >>"$log" 2>&1; then
  emit "SETUP: build failed; see $log"
  exit 2
fi
emit ""

# --- the second binary's reading of the same kernel -------------------------
route_row=""
if [ -x "$route" ]; then
  routetmp=$(mktemp)
  set +e
  taskset -c "$core" "$route" --consume-events "$doc" 3 >/dev/null 2>"$routetmp"
  rstatus=$?
  set -e
  route_row=$(grep '^row doc=' "$routetmp" | tail -1)
  emit "route binary: $route sha256=$(sha256sum "$route" | cut -d' ' -f1) status=$rstatus"
  if [ -n "$route_row" ]; then
    emit "route row: $route_row"
  else
    emit "route row: absent (no --consume-events row for this document)"
  fi
  rm -f "$routetmp"
else
  emit "route binary: absent ($route); the second reading is skipped"
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
  local before after delta explicit
  emit "## the Lean gate (immediately before this sweep)"
  ps -eo pid=,comm=,args= --no-headers |
    awk '$2 == "lake" || $2 ~ /lean/' >>"$log" || true
  explicit=$(ps -eo args= --no-headers |
    grep -E '(^|/)(lake build|lake env lean -c)|lean -c |lean --run|leanc ' |
    grep -v 'grep -E' || true)
  before=$(lean_cpu_ticks)
  sleep 1
  after=$(lean_cpu_ticks)
  delta=$(( after - before ))
  emit "lean-cpu ticks: before=$before after=$after delta=$delta (HZ=$(getconf CLK_TCK); threshold=5 ticks/s)"
  emit "load average: $(cat /proc/loadavg)"
  if [ -n "$explicit" ]; then
    emit "SETUP: a Lean build or compile is running:"
    printf '%s\n' "$explicit" >>"$log"
    printf '%s\n' "$explicit"
    emit "refusing to time"
    return 1
  fi
  if [ "$delta" -ge 5 ]; then
    emit "SETUP: Lean consumed $delta ticks in 1 s (>= 5); refusing to time"
    return 1
  fi
  emit "gate: no Lean build or compile active; timing may start"
  emit ""
  return 0
}

run_sweep() { # <context>
  local context=$1 status
  lean_gate || return 2
  set +e
  taskset -c "$core" "$build/cost-profile" --doc "$doc" --arm 2 \
    --win-offset "$win_offset" --context "$context" \
    --rounds "$rounds" --reps "$reps" 2>&1 | tee -a "$log"
  status=${PIPESTATUS[0]}
  set -e
  emit ""
  emit "# sweep context=$context exit status: $status"
  emit "# load average after the sweep: $(cat /proc/loadavg)"
  emit ""
  return "$status"
}

run_sweep route
run_sweep none

# --- the route's own workspace harness, same session -------------------------
emit "## the route's workspace harness (same session, same kernel flags)"
if ! lean_gate; then
  emit "SETUP: refused to run the workspace harness"
  exit 2
fi
wswork=$(mktemp -d "${TMPDIR:-/tmp}/json-cost-workspace.XXXXXX")
set +e
WORKSPACE_DIR=$wswork bash "$repo/probes/json/route/workspace.sh" \
  --rounds "$rounds" --reps "$reps" --core "$core" >>"$log" 2>&1
ws_status=$?
set -e
emit "# workspace exit status: $ws_status; build directory: $wswork"
grep -E -A1 '^syn-strings-64k +fresh' "$log" | tail -2 | while IFS= read -r line; do emit "$line"; done
emit ""

# --- placement: the same code at the route harness's kernel addresses --------
if [ "$placement" = 1 ]; then
  emit "## the placement measurement"
  if [ ! -x "$wswork/workspace" ]; then
    emit "placement: skipped (the workspace binary is absent)"
  else
    target=$(nm "$wswork/workspace" |
      awk '/ T leanllvm_json_pipeline$/{print $1}')
    emit "placement: route harness leanllvm_json_pipeline at $target"
    natdir=$build/placement-natural
    if ! FILLER_N=0 BUILD_DIR=$natdir CORPUS=$doc \
           bash "$here/build.sh" >>"$log" 2>&1; then
      emit "placement: natural build failed"
      exit 2
    fi
    natural=$(nm "$natdir/cost-profile" |
      awk '/ T leanllvm_json_pipeline$/{print $1}')
    filler=$(( 0x$target - 0x$natural ))
    aldir=$build/placement-aligned
    if [ "$filler" -gt 0 ]; then
      if ! FILLER_N=$filler BUILD_DIR=$aldir CORPUS=$doc \
             bash "$here/build.sh" >>"$log" 2>&1; then
        emit "placement: aligned build failed"
        exit 2
      fi
      aligned=$(nm "$aldir/cost-profile" |
        awk '/ T leanllvm_json_pipeline$/{print $1}')
      emit "placement: natural=$natural aligned=$aligned filler=$filler"\
" target=$target"
      for d in "$natdir" "$aldir"; do
        lean_gate || exit 2
        set +e
        taskset -c "$core" "$d/cost-profile" --doc "$doc" --arm 2 \
          --context route --rounds "$rounds" --reps "$reps" 2>&1 |
          tee -a "$log"
        pstatus=${PIPESTATUS[0]}
        set -e
        emit "# placement $(basename "$d") exit status: $pstatus"
        emit ""
      done
    else
      emit "placement: no padding needed (natural=$natural target=$target)"
    fi
  fi
fi

# --- the cross-check --------------------------------------------------------
field() { printf '%s\n' "$1" | tr ' ' '\n' | sed -n "s/^$2=//p" | head -1; }
ref_line=$(grep '^reference doc=' "$log" | head -1)
cons_line=$(grep '^consumer ' "$log" | head -1)
fail=0
for f in verdict ndst nev; do
  a=$(field "$ref_line" "$f")
  b=$(field "$route_row" "$f")
  if [ -n "$b" ] && [ "$a" != "$b" ]; then
    emit "cross-check: $f: instrument=$a route=$b"
    fail=1
  fi
done
for f in tokens values foldsum walked; do
  a=$(field "$cons_line" "$f")
  b=$(field "$route_row" "$f")
  if [ -n "$b" ] && [ "$a" != "$b" ]; then
    emit "cross-check: consumer $f: instrument=$a route=$b"
    fail=1
  fi
done
emit ""
if [ -z "$route_row" ]; then
  emit "cross-check: skipped (no route row); the instrument's own gates held"
elif [ "$fail" -eq 0 ]; then
  emit "cross-check: ok (verdict, ndst, nev, tokens, values, foldsum, walked)"
else
  emit "cross-check: FAILED"
  exit 3
fi
emit ""
emit "transcript: $log"
