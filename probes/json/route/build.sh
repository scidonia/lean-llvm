#!/usr/bin/env bash
# Build the JSON pipeline's Lean call route and its native adapter.
#
#   nix develop -c bash probes/json/route/build.sh
#
# The kernel is outside Lake (kernel/json/README.md), so this script is the link
# step: it compiles the six kernel translation units, the C adapter, and the
# standalone Lean program, then links them with `leanc`.  It asserts that the
# adapter imports `leanllvm_json_pipeline` and that the executable defines it,
# so a build that silently lost the call is a failure rather than a pass.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
build=${BUILD_DIR:-"$here/build"}

rm -rf "$build"
mkdir -p "$build"

cflags=(-O2 -march=x86-64-v3 -mpclmul -std=gnu11
        -falign-loops=64 -falign-functions=64 -I "$repo/kernel/json")

for f in pipeline s1_block entry escape utf8 stage2; do
  clang "${cflags[@]}" -c "$repo/kernel/json/$f.c" -o "$build/$f.o"
done

clang "${cflags[@]}" $(leanc --print-cflags) -c "$here/shim.c" -o "$build/shim.o"

(cd "$here" && lean -c "$build/RouteMain.c" RouteMain.lean)
leanc -c "$build/RouteMain.c" -o "$build/RouteMain.o"

if [ "$(nm -u "$build/shim.o" | grep -c 'leanllvm_json_pipeline')" -eq 0 ]; then
  echo "build: the adapter does not import leanllvm_json_pipeline" >&2
  exit 1
fi

leanc "$build/RouteMain.o" "$build/shim.o" \
  "$build/pipeline.o" "$build/s1_block.o" "$build/entry.o" \
  "$build/escape.o" "$build/utf8.o" "$build/stage2.o" \
  -o "$build/leanllvm-json-route"

if [ "$(nm "$build/leanllvm-json-route" | grep -c ' T leanllvm_json_pipeline$')" -eq 0 ]; then
  echo "build: the executable does not define leanllvm_json_pipeline" >&2
  exit 1
fi

clang "${cflags[@]}" "$here/driver.c" \
  "$build/pipeline.o" "$build/s1_block.o" "$build/entry.o" \
  "$build/escape.o" "$build/utf8.o" "$build/stage2.o" -o "$build/driver"

echo "ok: $build/leanllvm-json-route"
