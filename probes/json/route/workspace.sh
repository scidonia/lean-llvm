#!/usr/bin/env bash
# The composed route's four intervals with a fresh and a reused workspace, on
# the three accepted 64 KiB documents, beside simdjson 5.0.5's full parse.
#
#   nix develop -c bash probes/json/route/workspace.sh [--rounds N] [--reps N] [--core N]
#
# What is measured.  `probes/json/route/workspace.cc` runs the route's four
# stages over the same bytes: the two-phase admission, the caller's staging in
# the record's shape, the adapter's copy-in, `leanllvm_json_pipeline` and the
# result's copy-out, and the consumer's values reading with the header decode
# in the interval.  Each act is measured twice:
#
#   fresh   the window and the thirteen buffers are allocated and zeroed per
#           call, as `RouteMain.lean`'s `stage` does, and the adapter's copies
#           are allocated and freed per call, as `shim.c` does;
#   reused  one allocation of the same capacities: staging copies the document
#           into the window and resets the five cursor words and the two
#           carries, and the pipeline writes the caller's own buffers, so the
#           adapter's protective copy is absent.  (That folds the hand-over
#           measure into reuse; the report says so.)
#
# The reused arm alternates the three documents, in a rotated order, inside
# every round, so a call inherits the previous document's bytes.  The `stale`
# row is the affirmative control for that: it counts the event bytes the
# previous document left past the current one's `nev`, and requires at least
# one nonzero tail.  Every act, timed or not, must reproduce the reference
# observation's header words, arena bytes, event bytes, token count, value
# count and both checksums; a disagreement exits 3.
#
# The reference observation is cross-checked against the route binary's own
# `--consume-events` row for the same document, so the C harness's reading and
# the Lean route's reading are compared and not assumed equal.
#
# Corpus.  The five 65,536-byte documents of `tests/json-units-bench/
# transcript.txt` live in the units' corpus directory; the three synthetic ones
# are the measured set, and `route-s1-64k` is the untimed refusal control.  The
# script checks every file against the size and sha256 that transcript records.
#
# Exit status: 0 when every row was measured and every gate held; 2 on a setup
# problem (absent corpus, compiler, simdjson store output or route binary); 3
# when a measurement gate failed.
set -euo pipefail
export LC_ALL=C

cap_bytes=6442450944
swap_bytes=1073741824

if [ -z "${OMP_BENCH_CAPPED:-}" ]; then
  self=$(realpath "$0")
  if ! command -v systemd-run >/dev/null 2>&1; then
    echo "workspace: systemd-run is absent; run this script inside a memory cap" >&2
    exit 2
  fi
  export OMP_BENCH_CAPPED=1
  exec systemd-run --user --scope \
    -p MemoryMax="$cap_bytes" -p MemorySwapMax="$swap_bytes" --quiet \
    bash "$self" "$@"
fi

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
work=${WORKSPACE_DIR:-$here/build/workspace}
corpus=${BENCH_CORPUS:-$repo/tests/json-units-bench/build/corpus}
route=${ROUTE_BIN:-$here/build/leanllvm-json-route}
cc=clang
cxx=clang++
rounds=15
reps=21
core=0

while [ "$#" -gt 0 ]; do
  case "$1" in
    --rounds) shift; rounds=${1:-} ;;
    --rounds=*) rounds=${1#--rounds=} ;;
    --reps) shift; reps=${1:-} ;;
    --reps=*) reps=${1#--reps=} ;;
    --core) shift; core=${1:-} ;;
    --core=*) core=${1#--core=} ;;
    *) echo "workspace: unknown argument $1" >&2; exit 2 ;;
  esac
  shift
done

die() { printf 'SETUP: %s\n' "$*" >&2; exit 2; }

for tool in "$cc" "$cxx" sha256sum taskset; do
  command -v "$tool" >/dev/null 2>&1 || die "no $tool on PATH; run under nix develop"
done
[ -x "$route" ] || die "absent route binary: $route
  build it with: nix develop -c bash probes/json/route/build.sh"
[ -d "$corpus" ] || die "absent corpus '$corpus'
  generate it with: nix develop -c bash tests/json-units-bench/bench.sh"

dev=${SIMDJSON_DEV:-/nix/store/m2i8165bayxxgzj3fbvdg6gihz6na93d-simdjson-5.0.5-dev}
lib=${SIMDJSON_LIB:-/nix/store/jglxdk9y0yfk3mc9dbr675pfmv42a89y-simdjson-5.0.5}
header=$dev/include/simdjson.h
solib=$lib/lib/libsimdjson.so.34.0.0
[ -f "$header" ] || die "absent: $header
  realise it with: nix build --no-link --print-out-paths 'nixpkgs#simdjson.dev'"
[ -f "$solib" ] || die "absent: $solib
  realise it with: nix build --no-link --print-out-paths 'nixpkgs#simdjson'"
ver=$(sed -n 's/^#define SIMDJSON_VERSION "\(.*\)"/\1/p' "$header" | head -1)
[ "$ver" = "5.0.5" ] || die "header is simdjson '$ver', not 5.0.5"

# Size and sha256 as `tests/json-units-bench/transcript.txt` records them.
expected="route-s1-64k.json 65536 41f918853d55dad0e05d3ec03682e037925759031632f045a755db5a5173535c
syn-dense-64k.json 65536 3d9e0237ec66adb2d77848a24f1998fa4b56b4dbe77a11431b02176fcd162995
syn-strings-64k.json 65536 bd007090d7a5ab09a1fc69c0b96879f101dbf8b3f13a300d7d3e46127d26fb12
syn-utf8-64k.json 65536 f95f4aeaac083d5d97ff98f9ad6aa09e4ed8c905d89e1bf3a3177179533400a4"
while read -r name size sha; do
  [ -n "$name" ] || continue
  [ -f "$corpus/$name" ] || die "absent $corpus/$name"
  [ "$(stat -c %s "$corpus/$name")" = "$size" ] ||
    die "$corpus/$name is not $size bytes"
  [ "$(sha256sum "$corpus/$name" | cut -d' ' -f1)" = "$sha" ] ||
    die "$corpus/$name does not hash $sha"
done <<<"$expected"

[ -n "$work" ] && [ "$work" != "/" ] || die "refusing work directory '$work'"
rm -rf "$work"
mkdir -p "$work"

kflags=(-O2 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
        -falign-functions=64 -I "$repo/kernel/json")
for f in pipeline s1_block entry escape utf8 stage2; do
  "$cc" "${kflags[@]}" -c "$repo/kernel/json/$f.c" -o "$work/$f.o"
done
"$cc" -c "$repo/tests/v16/depth_count.ll" -o "$work/depth_count.o"
"$cc" "${kflags[@]}" -I "$here" -c "$here/policy.c" -o "$work/policy.o"

"$cxx" -O3 -march=x86-64-v3 -mpclmul -std=c++17 -falign-loops=64 \
  -falign-functions=64 -I "$dev/include" -I "$repo/kernel/json" -I "$here" \
  "$here/workspace.cc" "$work/pipeline.o" "$work/s1_block.o" "$work/entry.o" \
  "$work/escape.o" "$work/utf8.o" "$work/stage2.o" "$work/depth_count.o" \
  "$work/policy.o" -L "$lib/lib" -Wl,-rpath,"$lib/lib" -lsimdjson \
  -o "$work/workspace"

printf 'command: nix develop -c bash probes/json/route/workspace.sh --rounds %s --reps %s --core %s\n' \
  "$rounds" "$reps" "$core"
printf 'harness: probes/json/route/workspace.cc sha256=%s\n' \
  "$(sha256sum "$here/workspace.cc" | cut -d' ' -f1)"
printf 'script: probes/json/route/workspace.sh sha256=%s\n' \
  "$(sha256sum "$here/workspace.sh" | cut -d' ' -f1)"
printf 'admission source: probes/json/route/admission.h sha256=%s\n' \
  "$(sha256sum "$here/admission.h" | cut -d' ' -f1)"
printf 'guard source: probes/json/route/escape_guard.h sha256=%s\n' \
  "$(sha256sum "$here/escape_guard.h" | cut -d' ' -f1)"
printf 'policy source: probes/json/route/policy.c sha256=%s\n' \
  "$(sha256sum "$here/policy.c" | cut -d' ' -f1)"
printf 'simdjson: %s; dev: %s\n' "$ver" "$dev"
printf 'simdjson lib: %s sha256=%s\n' "$(basename "$solib")" \
  "$(sha256sum "$solib" | cut -d' ' -f1)"
printf 'header: simdjson.h sha256=%s\n' "$(sha256sum "$header" | cut -d' ' -f1)"
printf 'route binary: %s sha256=%s mtime=%s\n' "$route" \
  "$(sha256sum "$route" | cut -d' ' -f1)" "$(stat -c %y "$route")"
printf 'compiler: %s (%s)\n' "$cxx" "$("$cxx" --version | head -1)"
printf 'kernel flags: %s\n' "${kflags[*]}"
printf 'harness flags: -O3 -march=x86-64-v3 -mpclmul -std=c++17 -falign-loops=64 -falign-functions=64\n'
printf 'host: %s\n' "$(uname -srm)"
printf 'cpu: %s\n' "$(awk -F: '/^model name/ { sub(/^ /, "", $2); print $2; exit }' /proc/cpuinfo)"
printf 'cpus online: %s; pinned to: cpu%s\n' "$(nproc)" "$core"
printf 'scaling governor: %s\n' "$(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null || echo unknown)"
printf 'load average at start: %s\n' "$(cat /proc/loadavg)"
printf 'rounds: %s; repetitions per arm per round: %s\n' "$rounds" "$reps"
printf 'build directory: %s\n' "$work"
printf '\ncorpus: %s\n' "$corpus"
printf '%-22s %8s %s\n' file bytes sha256
for name in syn-dense-64k syn-strings-64k syn-utf8-64k; do
  printf '%-22s %8s %s\n' "$name.json" "$(wc -c <"$corpus/$name.json")" \
    "$(sha256sum "$corpus/$name.json" | cut -d' ' -f1)"
done
printf '%-22s %8s %s\n' route-s1-64k.json \
  "$(wc -c <"$corpus/route-s1-64k.json")" \
  "$(sha256sum "$corpus/route-s1-64k.json" | cut -d' ' -f1)"
printf '\n'

# --- the route binary's own reading, for the cross-check --------------------
: >"$work/route-ref.txt"
for name in syn-dense-64k syn-strings-64k syn-utf8-64k; do
  taskset -c "$core" "$route" --consume-events "$corpus/$name.json" 1 2>&1 |
    grep '^row ' >>"$work/route-ref.txt"
done
printf '## the route binary'"'"'s own `--consume-events` rows (unit ns; repetitions: 1,\n'
printf '## for the identities)\n'
cat "$work/route-ref.txt"
printf '\n'

# --- the probe --------------------------------------------------------------
if taskset -c "$core" "$work/workspace" \
  --doc "syn-dense-64k=$corpus/syn-dense-64k.json" \
  --doc "syn-strings-64k=$corpus/syn-strings-64k.json" \
  --doc "syn-utf8-64k=$corpus/syn-utf8-64k.json" \
  --refused "route-s1-64k=$corpus/route-s1-64k.json" \
  --rounds "$rounds" --reps "$reps" >"$work/out.txt" 2>"$work/err.txt"; then
  status=0
else
  status=$?
fi
cat "$work/out.txt"
if [ -s "$work/err.txt" ]; then cat "$work/err.txt" >&2; fi
if [ "$status" -ne 0 ]; then
  printf 'FAIL: the probe exited %s\n' "$status" >&2
  exit 3
fi

# --- the cross-check: the C reading against the Lean route's ---------------
field() {
  local row=$1 key=$2
  printf '%s\n' "$row" |
    sed -n "s/^.*[[:space:]]${key}=\([^[:space:]]*\).*$/\1/p"
}
ref_of() { grep "^reference doc=$1 " "$work/out.txt" | head -1; }

printf '\n## the cross-check (the C harness'"'"'s reading against the route binary'"'"'s)\n'
fail=0
for name in syn-dense-64k syn-strings-64k syn-utf8-64k; do
  harness=$(ref_of "$name")
  lean=$(grep " doc=$name.json " "$work/route-ref.txt" | head -1)
  [ -n "$harness" ] || { echo "FAIL: no harness reference row for $name" >&2; fail=1; continue; }
  [ -n "$lean" ] || { echo "FAIL: no route row for $name" >&2; fail=1; continue; }
  for key in verdict ndst nev tokens values foldsum valuessum; do
    a=$(field "$harness" "$key")
    b=$(field "$lean" "$key")
    if [ "$a" != "$b" ]; then
      printf 'FAIL: %s %s: harness %s, route %s\n' "$name" "$key" "$a" "$b" >&2
      fail=1
    fi
  done
  printf '%-18s verdict=%s ndst=%s nev=%s tokens=%s values=%s\n' "$name" \
    "$(field "$harness" verdict)" "$(field "$harness" ndst)" \
    "$(field "$harness" nev)" "$(field "$harness" tokens)" \
    "$(field "$harness" values)"
done
if [ "$fail" -ne 0 ]; then
  printf 'FAIL: the harness reading and the route reading differ\n' >&2
  exit 3
fi

printf '\nload average after the sweep: %s\n' "$(cat /proc/loadavg)"
printf 'ok: the paired run completed; the reference observation and the route binary agree\n'
