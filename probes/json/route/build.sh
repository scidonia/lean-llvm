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

# The decision and the fallback are the library's, so the program imports the
# domain module and the reference parser.  Their Lean modules are built by Lake,
# and the emitted C is what links: the input must be inside the Lake project so
# the module prefix resolves, and `-I` is the emitted C's own include root.
cone_ir=("$repo/.lake/build/ir/LeanLLVM/JsonKernelDomain.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/ByteString.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Bytes.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Utf8.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Spec.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Scan.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Tape.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Parse.c")
for f in "${cone_ir[@]}"; do
  [ -f "$f" ] || {
    echo "build: absent: $f" >&2
    echo "build: build the route's Lean modules first:" >&2
    echo "  nix develop -c bash probes/install/lake-locked.sh build LeanLLVM.JsonKernelDomain LeanLLVM.JSON.Parse" >&2
    exit 1
  }
done

(cd "$repo" && lake env lean -c "$build/RouteMain.c" probes/json/route/RouteMain.lean)
leanc -c "$build/RouteMain.c" -I "$repo/.lake/build/ir" -o "$build/RouteMain.o"

if [ "$(nm -u "$build/shim.o" | grep -c 'leanllvm_json_pipeline')" -eq 0 ]; then
  echo "build: the adapter does not import leanllvm_json_pipeline" >&2
  exit 1
fi

# The adapter's setup fills the entry unit's POS8 table before the call; a
# build that lost that call leaves the table zero and every container refused.
if [ "$(nm -u "$build/shim.o" | grep -c 'leanllvm_json_entry_table')" -eq 0 ]; then
  echo "build: the adapter does not import leanllvm_json_entry_table" >&2
  exit 1
fi

leanc "$build/RouteMain.o" "$build/shim.o" \
  "${cone_ir[@]}" \
  "$build/pipeline.o" "$build/s1_block.o" "$build/entry.o" \
  "$build/escape.o" "$build/utf8.o" "$build/stage2.o" \
  -I "$repo/.lake/build/ir" -o "$build/leanllvm-json-route"

if [ "$(nm "$build/leanllvm-json-route" | grep -c ' T leanllvm_json_pipeline$')" -eq 0 ]; then
  echo "build: the executable does not define leanllvm_json_pipeline" >&2
  exit 1
fi
if [ "$(nm "$build/leanllvm-json-route" | grep -c ' T leanllvm_json_entry_table$')" -eq 0 ]; then
  echo "build: the executable does not define leanllvm_json_entry_table" >&2
  exit 1
fi

clang "${cflags[@]}" "$here/driver.c" \
  "$build/pipeline.o" "$build/s1_block.o" "$build/entry.o" \
  "$build/escape.o" "$build/utf8.o" "$build/stage2.o" -o "$build/driver"

echo "ok: $build/leanllvm-json-route"
