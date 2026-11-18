#!/usr/bin/env bash
# Build the C-only cost profile of the route's native interval.
#
#   nix develop -c bash probes/json/route/cost-profile/build.sh
#   BUILD_DIR=/tmp/x bash probes/json/route/cost-profile/build.sh
#
# The six kernel translation units are compiled at the route's own line
# (`-O2 -march=x86-64-v3 -mpclmul -falign-loops=64 -falign-functions=64`), the
# same one `probes/json/route/workspace.sh` uses, and the instrument is compiled
# at the harness line `workspace.cc` is compiled at (`-O3`, same target flags).
# C only: there is no Lean, `leanc`, or C++ input.  Outputs go to a private
# directory (a fresh `mktemp -d` unless BUILD_DIR names one).
#
# The build asserts what the report depends on: the binary defines the pipeline
# and the escape expander, and the instrument object references the expander, so
# the direct-expand act cannot have been optimised into something else.
set -euo pipefail
export LC_ALL=C

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../../.." && pwd)
build=${BUILD_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/json-cost-profile.XXXXXX")}
corpus=${CORPUS:-$repo/tests/json-units-bench/build/corpus/syn-strings-64k.json}
cc=clang

command -v "$cc" >/dev/null 2>&1 ||
  { printf 'SETUP: no %s on PATH; run under nix develop\n' "$cc" >&2; exit 2; }

if [ -f "$corpus" ]; then
  size=$(stat -c %s "$corpus")
  sha=$(sha256sum "$corpus" | cut -d' ' -f1)
  [ "$size" = 65536 ] ||
    { printf 'SETUP: %s is %s bytes, not 65536\n' "$corpus" "$size" >&2; exit 2; }
  [ "$sha" = bd007090d7a5ab09a1fc69c0b96879f101dbf8b3f13a300d7d3e46127d26fb12 ] ||
    { printf 'SETUP: %s sha256=%s, not the recorded document\n' "$corpus" \
        "$sha" >&2; exit 2; }
else
  printf 'SETUP: absent corpus %s; generate it with ' "$corpus" >&2
  printf 'nix develop -c bash tests/json-units-bench/bench.sh\n' >&2
  exit 2
fi

mkdir -p "$build"

kflags=(-O2 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
        -falign-functions=64 -I "$repo/kernel/json" -I "$repo/probes/json/route")
hflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
        -falign-functions=64 -I "$repo/kernel/json" -I "$repo/probes/json/route")

printf 'build: %s\n' "$build"
printf 'kernel flags: %s\n' "${kflags[*]}"
printf 'harness flags: %s\n' "${hflags[*]}"
printf 'compiler: %s (%s)\n' "$cc" "$("$cc" --version | head -1)"

for f in pipeline s1_block entry escape utf8 stage2; do
  "$cc" "${kflags[@]}" -c "$repo/kernel/json/$f.c" -o "$build/$f.o"
done

# The route-shaped context needs the same admission the workspace runs: its
# policy scan (C, the route's own source) and the committed depth-counter
# fixture, compiled at the line `probes/json/route/build.sh` compiles it.  The
# fixture is LLVM IR that ships in the tree; no Lean and no Lean output is read.
"$cc" "${kflags[@]}" -c "$repo/probes/json/route/policy.c" -o "$build/policy.o"
"$cc" -c "$repo/tests/v16/depth_count.ll" -o "$build/depth_count.o"

"$cc" "${hflags[@]}" -c "$here/cost-profile.c" -o "$build/cost-profile.o"

# Optional link-order padding, for the placement measurement in README.md: a
# filler object placed before the kernel objects moves their code addresses
# without changing a byte of their code.
filler_n=${FILLER_N:-0}
extra=()
if [ "$filler_n" -gt 0 ]; then
  "$cc" -O2 -DFILLER_N="$filler_n" -c "$here/filler.c" -o "$build/filler.o"
  extra=("$build/filler.o")
fi
printf 'filler: %s byte(s)\n' "$filler_n"

# The direct-expand act must reach out of line: the instrument object has to
# reference the unit's ABI entry point, and the binary has to define it.
if [ "$(nm -u "$build/cost-profile.o" | grep -c ' leanllvm_json_escape_expand$')" -eq 0 ]; then
  printf 'BUILD: cost-profile.o does not reference leanllvm_json_escape_expand\n' >&2
  exit 2
fi

"$cc" "$build/cost-profile.o" "${extra[@]}" \
  "$build/pipeline.o" "$build/s1_block.o" "$build/entry.o" \
  "$build/escape.o" "$build/utf8.o" "$build/stage2.o" \
  "$build/policy.o" "$build/depth_count.o" \
  -o "$build/cost-profile"

for sym in leanllvm_json_pipeline leanllvm_json_escape_expand \
           leanllvm_json_escape_list leanllvm_json_stage2 \
           leanllvm_json_s1_masks leanllvm_json_entry_pos8 \
           leanllvm_json_utf8 leanllvm_route_policy_scan_ws depth_count; do
  if [ "$(nm --defined-only "$build/cost-profile" | grep -c " T $sym\$")" -eq 0 ]; then
    printf 'BUILD: the binary does not define %s\n' "$sym" >&2
    exit 2
  fi
done

printf '\nsource digests:\n'
for f in "$repo"/kernel/json/{pipeline,s1_block,entry,escape,utf8,stage2}.c \
         "$repo/probes/json/route/policy.c" "$repo/tests/v16/depth_count.ll" \
         "$here/cost-profile.c" "$here/build.sh" "$here/run.sh"; do
  [ -f "$f" ] || continue
  printf '  %-60s %s\n' "${f#"$repo"/}" "$(sha256sum "$f" | cut -d' ' -f1)"
done
printf 'object digests:\n'
for f in "$build"/{pipeline,s1_block,entry,escape,utf8,stage2,policy,depth_count}.o; do
  printf '  %-60s %s\n' "$(basename "$f")" "$(sha256sum "$f" | cut -d' ' -f1)"
done
printf 'binary: %s sha256=%s\n' "$build/cost-profile" \
  "$(sha256sum "$build/cost-profile" | cut -d' ' -f1)"
printf 'ok: %s\n' "$build/cost-profile"
