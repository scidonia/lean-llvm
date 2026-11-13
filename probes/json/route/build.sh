#!/usr/bin/env bash
# Build the JSON pipeline's Lean call route and its native adapter.
#
#   nix develop -c bash probes/json/route/build.sh
#
# The kernel is outside Lake (kernel/json/README.md), so this script is the link
# step: it compiles the six kernel translation units, the proved stage-1 depth
# counter (`tests/v16/depth_count.ll`, at the same `clang -c` line the install
# uses for the unit), the probe's native character-policy scan (`policy.c`), the
# C adapter, and the standalone Lean program, then links them with `leanc`.  It
# asserts that the adapter imports the units it calls -- `leanllvm_json_pipeline`,
# `leanllvm_json_entry_table`, the mask unit, the depth counter and the policy
# scan -- and that the executable defines each of them, so a build that silently
# lost a call is a failure rather than a pass.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
build=${BUILD_DIR:-"$here/build"}

rm -rf "$build"
mkdir -p "$build"

# The kernel object's optimisation level and the adapter's stage instrument are
# the two build knobs; both default to the build the route ships.  `OPT` names
# the level the six kernel units are compiled at (the route's object); `TIMING=1`
# makes the adapter record its three stage intervals for `--stages`.  Everything
# else is held fixed, so an `OPT` pair differs in the optimisation level alone.
opt=${OPT:--O2}
timing=${TIMING:-0}
base=(-march=x86-64-v3 -mpclmul -std=gnu11
      -falign-loops=64 -falign-functions=64 -I "$repo/kernel/json")
kflags=("$opt" "${base[@]}")
shim_flags=(-O2 "${base[@]}")
if [ "$timing" = 1 ]; then
  shim_flags+=(-DROUTE_TIMING=1)
fi

printf 'flags: kernel=%s adapter=-O2 timing=%s\n' "$opt" "$timing"

for f in pipeline s1_block entry escape utf8 stage2; do
  clang "${kflags[@]}" -c "$repo/kernel/json/$f.c" -o "$build/$f.o"
done

# The depth counter is the census fixture's text, compiled at the line the
# install uses for it (`probes/install/build.sh`), so the object the route runs
# is the object `depth_count_refines` is about.
clang -c "$repo/tests/v16/depth_count.ll" -o "$build/depth_count.o"

clang "${shim_flags[@]}" $(leanc --print-cflags) -I "$here" -c "$here/policy.c" \
  -o "$build/policy.o"
clang "${shim_flags[@]}" $(leanc --print-cflags) -c "$here/shim.c" -o "$build/shim.o"

# The instrument is a compile-time gate, so its cost in the ordinary adapter is
# checkable rather than asserted: an uninstrumented build must not reference the
# clock at all, and an instrumented one must.
clock_refs=$(nm -u "$build/shim.o" | grep -c 'clock_gettime' || true)
if [ "$timing" = 1 ]; then
  if [ "$clock_refs" -lt 1 ]; then
    echo "build: TIMING=1 but the adapter does not read the clock" >&2
    exit 1
  fi
else
  if [ "$clock_refs" -ne 0 ]; then
    echo "build: the ordinary adapter references clock_gettime; the gate is off" >&2
    exit 1
  fi
fi

# The decision and the fallback are the library's, so the program imports the
# domain module and the reference parser.  Their Lean modules are built by Lake,
# and the emitted C is what links: the input must be inside the Lake project so
# the module prefix resolves, and `-I` is the emitted C's own include root.
#
# `admission`'s depth clause folds `deltaZ` (`DepthCountRefine`), so the domain
# module's link carries that module and the eight-module cone its emitted C
# names: the three the initialiser chain reaches (`Memory`, `Parser`, `Semantics`)
# and the four they in turn reach (`Basic`, `Syntax`, `Binary64`, `Printer`).  A
# module absent from this list is an undefined `deltaZ` at link, not a green
# build: the list is what the emitted C names, not a choice.
cone_ir=("$repo/.lake/build/ir/LeanLLVM/JsonKernelDomain.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/ByteString.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Bytes.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Utf8.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Spec.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Scan.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Tape.c"
         "$repo/.lake/build/ir/LeanLLVM/JSON/Parse.c"
         "$repo/.lake/build/ir/LeanLLVM/Refinement/DepthCountRefine.c"
         "$repo/.lake/build/ir/LeanLLVM/Basic.c"
         "$repo/.lake/build/ir/LeanLLVM/Binary64.c"
         "$repo/.lake/build/ir/LeanLLVM/Memory.c"
         "$repo/.lake/build/ir/LeanLLVM/Parser.c"
         "$repo/.lake/build/ir/LeanLLVM/Printer.c"
         "$repo/.lake/build/ir/LeanLLVM/Semantics.c"
         "$repo/.lake/build/ir/LeanLLVM/Syntax.c")
for f in "${cone_ir[@]}"; do
  [ -f "$f" ] || {
    echo "build: absent: $f" >&2
    echo "build: build the route's Lean modules first:" >&2
    echo "  nix develop -c bash probes/install/lake-locked.sh build LeanLLVM.JsonKernelDomain LeanLLVM.JSON.Parse" >&2
    exit 1
  }
done

(cd "$repo" && lake env lean -c "$build/RouteMain.c" "$here/RouteMain.lean")
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

# Phase one of the admission is the depth walk, and its lane list goes through
# the proved depth counter: an adapter that stopped calling the counter would
# still build and would report a maximum with no second arithmetic beside it.
# The mask unit is not on this path -- the walk reads the bytes it folds, because
# the classifier's in-string mask is a different reading of a string from the
# reference scan's (see `shim.c`'s depth section) -- so it is checked where it is
# defined, by the object, and not here.
if [ "$(nm -u "$build/shim.o" | grep -c ' depth_count$')" -eq 0 ]; then
  echo "build: the adapter does not import depth_count" >&2
  exit 1
fi
if [ "$(nm -u "$build/shim.o" | grep -c ' leanllvm_route_body_stop$')" -eq 0 ]; then
  echo "build: the adapter does not import leanllvm_route_body_stop" >&2
  exit 1
fi
# Phase two of the admission is this scan: an adapter that stopped calling it
# would build, would still answer every document, and would be reading the
# reference's rule from nowhere, so the import is checked like the pipeline's.
if [ "$(nm -u "$build/shim.o" | grep -c ' leanllvm_route_policy_scan$')" -eq 0 ]; then
  echo "build: the adapter does not import leanllvm_route_policy_scan" >&2
  exit 1
fi

leanc "$build/RouteMain.o" "$build/shim.o" "$build/policy.o" \
  "${cone_ir[@]}" \
  "$build/pipeline.o" "$build/s1_block.o" "$build/entry.o" \
  "$build/escape.o" "$build/utf8.o" "$build/stage2.o" "$build/depth_count.o" \
  -I "$repo/.lake/build/ir" -o "$build/leanllvm-json-route"

if [ "$(nm "$build/leanllvm-json-route" | grep -c ' T leanllvm_json_pipeline$')" -eq 0 ]; then
  echo "build: the executable does not define leanllvm_json_pipeline" >&2
  exit 1
fi
if [ "$(nm "$build/leanllvm-json-route" | grep -c ' T leanllvm_json_entry_table$')" -eq 0 ]; then
  echo "build: the executable does not define leanllvm_json_entry_table" >&2
  exit 1
fi
if [ "$(nm "$build/leanllvm-json-route" | grep -c ' T leanllvm_json_s1_masks$')" -eq 0 ]; then
  echo "build: the executable does not define leanllvm_json_s1_masks" >&2
  exit 1
fi
if [ "$(nm "$build/leanllvm-json-route" | grep -c ' T depth_count$')" -eq 0 ]; then
  echo "build: the executable does not define depth_count" >&2
  exit 1
fi
if [ "$(nm --defined-only "$build/leanllvm-json-route" | grep -c ' leanllvm_route_policy_scan$')" -eq 0 ]; then
  echo "build: the executable does not define leanllvm_route_policy_scan" >&2
  exit 1
fi

clang "${kflags[@]}" "$here/driver.c" \
  "$build/pipeline.o" "$build/s1_block.o" "$build/entry.o" \
  "$build/escape.o" "$build/utf8.o" "$build/stage2.o" -o "$build/driver"

echo "ok: $build/leanllvm-json-route"
