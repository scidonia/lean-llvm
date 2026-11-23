#!/usr/bin/env bash
# Build and run the stage-2 escape cost probe on `syn-strings-64k`: the list
# arm (2) and the shipping list-free arm (0), in one binary and one session.
#
#   nix develop -c bash probes/json/route/lazy-stage2/run.sh
#   nix develop -c bash probes/json/route/lazy-stage2/run.sh --rounds 21 --reps 31 --core 2
#
# The kernel objects are compiled at the route's own line
# (`-O2 -march=x86-64-v3 -mpclmul -falign-loops=64 -falign-functions=64`) and
# the instrument at the harness line (`-O3`, same target flags).  The script
# builds into a private temporary directory, runs the binary (pinned with
# `taskset` when it is available) and writes the transcript beside itself.
#
# The document is the route's `syn-strings-64k`, regenerated from
# `tests/json-units-bench/gen.c` when the corpus is absent; its size and sha256
# are checked against the recorded document either way.
set -euo pipefail
export LC_ALL=C

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../../.." && pwd)
doc=$repo/tests/json-units-bench/build/corpus/syn-strings-64k.json
log=$here/transcript.txt
rounds=15
reps=21
core=0
build=${BUILD_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/json-lazy-stage2.XXXXXX")}
cc=clang

while [ "$#" -gt 0 ]; do
  case "$1" in
    --rounds) shift; rounds=${1:-}; [ -n "$rounds" ] || { echo "--rounds needs a value" >&2; exit 2; } ;;
    --reps) shift; reps=${1:-}; [ -n "$reps" ] || { echo "--reps needs a value" >&2; exit 2; } ;;
    --core) shift; core=${1:-}; [ -n "$core" ] || { echo "--core needs a value" >&2; exit 2; } ;;
    --doc) shift; doc=${1:-}; [ -n "$doc" ] || { echo "--doc needs a value" >&2; exit 2; } ;;
    --help) sed -n '2,22p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "run: unknown argument $1" >&2; exit 2 ;;
  esac
  shift
done

command -v "$cc" >/dev/null 2>&1 ||
  { printf 'SETUP: no %s on PATH; run under nix develop\n' "$cc" >&2; exit 2; }

if [ ! -f "$doc" ]; then
  printf 'SETUP: absent document %s; generating it with gen.c\n' "$doc" >&2
  mkdir -p "$(dirname "$doc")" "$repo/tests/json-units-bench/build/bin"
  "$cc" -O2 -std=gnu11 -o "$repo/tests/json-units-bench/build/bin/gen" \
    "$repo/tests/json-units-bench/gen.c"
  "$repo/tests/json-units-bench/build/bin/gen" --shape strings --size 65536 \
    --out "$doc"
fi
size=$(stat -c %s "$doc")
sha=$(sha256sum "$doc" | cut -d' ' -f1)
[ "$size" = 65536 ] || { printf 'SETUP: %s is %s bytes, not 65536\n' "$doc" "$size" >&2; exit 2; }
[ "$sha" = bd007090d7a5ab09a1fc69c0b96879f101dbf8b3f13a300d7d3e46127d26fb12 ] ||
  { printf 'SETUP: %s sha256=%s, not the recorded document\n' "$doc" "$sha" >&2; exit 2; }

kflags=(-O2 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
        -falign-functions=64 -I "$repo/kernel/json")
hflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
        -falign-functions=64 -I "$repo/kernel/json")

mkdir -p "$build"
for f in pipeline s1_block entry escape utf8 stage2; do
  "$cc" "${kflags[@]}" -c "$repo/kernel/json/$f.c" -o "$build/$f.o"
done
"$cc" "${hflags[@]}" -c "$here/lazy-bench.c" -o "$build/lazy-bench.o"
"$cc" "$build/lazy-bench.o" "$build/pipeline.o" "$build/s1_block.o" \
  "$build/entry.o" "$build/escape.o" "$build/utf8.o" "$build/stage2.o" \
  -o "$build/lazy-bench"
"$cc" "${hflags[@]}" -o "$build/verdict-probe" "$here/verdict-probe.c" \
  "$build/pipeline.o" "$build/s1_block.o" "$build/entry.o" "$build/escape.o" \
  "$build/utf8.o" "$build/stage2.o"

{
  printf '# command: %s %s\n' "$0" "$*"
  printf '# install: %s\n' "$(uname -srm)"
  printf '# cpu: %s\n' "$(awk -F: '/^model name/ { sub(/^ /, "", $2); print $2; exit }' /proc/cpuinfo)"
  printf '# cpus online: %s; pinned to: cpu%s\n' "$(nproc)" "$core"
  printf '# load average: %s\n' "$(cat /proc/loadavg)"
  printf '# document: %s size=%s sha256=%s\n' "$doc" "$size" "$sha"
  printf '# build: %s\n\n' "$build"
  for f in "$repo"/kernel/json/{pipeline,s1_block,entry,escape,utf8,stage2}.c \
           "$here/lazy-bench.c"; do
    printf '#   %-60s %s\n' "${f#"$repo"/}" "$(sha256sum "$f" | cut -d' ' -f1)"
  done
  printf '\n'
  if command -v taskset >/dev/null 2>&1; then
    taskset -c "$core" "$build/lazy-bench" --doc "$doc" --rounds "$rounds" \
      --reps "$reps" --core "$core"
  else
    "$build/lazy-bench" --doc "$doc" --rounds "$rounds" --reps "$reps" \
      --core "$core"
  fi
  printf '\n# the verdict control: the same walk with the escape list withheld\n'
  if command -v taskset >/dev/null 2>&1; then
    taskset -c "$core" "$build/verdict-probe"
  else
    "$build/verdict-probe"
  fi
} | tee "$log"

printf '\nok: %s\n' "$log"
