#!/usr/bin/env bash
# Build the entry-opt harness: the installed stage-1 units at the route's own
# compiler line, plus the two other entry-emitter shapes, plus the instrument.
#
#   nix develop -c bash probes/json/route/entry-opt/build.sh
#   BUILD_DIR=/tmp/eo bash probes/json/route/entry-opt/build.sh
#
# The six kernel translation units are compiled at
# `-O2 -march=x86-64-v3 -mpclmul -falign-loops=64 -falign-functions=64`, the
# same line `probes/json/route/cost-profile/build.sh` uses; the instrument is
# compiled at the harness line `-O3` with the same target flags.  C only.
set -euo pipefail
export LC_ALL=C

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../../.." && pwd)
build=${BUILD_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/json-entry-opt.XXXXXX")}
corpus=${CORPUS:-$repo/tests/json-units-bench/build/corpus/syn-strings-64k.json}
pinned=$repo/tests/json-units-bench/build/corpus/syn-strings-64k.json
cc=clang

command -v "$cc" >/dev/null 2>&1 ||
  { printf 'SETUP: no %s on PATH; run under nix develop\n' "$cc" >&2; exit 2; }

if [ -f "$corpus" ]; then
  size=$(stat -c %s "$corpus")
  sha=$(sha256sum "$corpus" | cut -d' ' -f1)
  if [ "$corpus" = "$pinned" ]; then
    [ "$size" = 65536 ] ||
      { printf 'SETUP: %s is %s bytes, not 65536\n' "$corpus" "$size" >&2; exit 2; }
    [ "$sha" = bd007090d7a5ab09a1fc69c0b96879f101dbf8b3f13a300d7d3e46127d26fb12 ] ||
      { printf 'SETUP: %s sha256=%s, not the recorded document\n' "$corpus" \
          "$sha" >&2; exit 2; }
  else
    printf 'corpus: %s size=%s sha256=%s (not the pinned document)\n' \
      "$corpus" "$size" "$sha"
  fi
else
  printf 'SETUP: absent corpus %s; generate it with ' "$corpus" >&2
  printf 'nix develop -c bash tests/json-units-bench/bench.sh\n' >&2
  exit 2
fi

mkdir -p "$build"

kflags=(-O2 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
        -falign-functions=64 -I "$repo/kernel/json")
hflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
        -falign-functions=64 -I "$repo/kernel/json")
warn=(-Wall -Wextra -Werror)

printf 'build: %s\n' "$build"
printf 'kernel flags: %s\n' "${kflags[*]}"
printf 'harness flags: %s\n' "${hflags[*]}"
printf 'compiler: %s (%s)\n' "$cc" "$("$cc" --version | head -1)"

for f in pipeline s1_block entry escape utf8 stage2; do
  "$cc" "${kflags[@]}" -c "$repo/kernel/json/$f.c" -o "$build/$f.o"
done

"$cc" "${kflags[@]}" "${warn[@]}" -c "$here/entry_variants.c" \
  -o "$build/entry_variants.o"
"$cc" "${hflags[@]}" "${warn[@]}" -c "$here/entry-opt.c" -o "$build/entry-opt.o"

# The variants' table must be the installed unit's, not a second copy of the
# rule: the object has to reference the installed table copier.
if [ "$(nm -u "$build/entry_variants.o" |
        grep -c ' leanllvm_json_entry_table$')" -eq 0 ]; then
  printf 'BUILD: entry_variants.o does not reference leanllvm_json_entry_table\n' >&2
  exit 2
fi
# And the instrument must reach every shape out of line, so a call is a call.
for sym in eo_entry_pos8_skip eo_entry_sparse leanllvm_json_entry_pos8; do
  if [ "$(nm -u "$build/entry-opt.o" | grep -c " $sym\$")" -eq 0 ]; then
    printf 'BUILD: entry-opt.o does not reference %s\n' "$sym" >&2
    exit 2
  fi
done

"$cc" "$build/entry-opt.o" "$build/entry_variants.o" \
  "$build/pipeline.o" "$build/s1_block.o" "$build/entry.o" \
  "$build/escape.o" "$build/utf8.o" "$build/stage2.o" \
  -o "$build/entry-opt"

# The untimed shape report: one document's entry words under the route's
# stage-1 prologue, in the words the report's `shape` lines use.
"$cc" "${kflags[@]}" "${warn[@]}" -c "$here/shape.c" -o "$build/shape.o"
"$cc" "$build/shape.o" "$build/s1_block.o" -o "$build/entry-opt-shape"

for sym in leanllvm_json_pipeline leanllvm_json_s1_masks \
           leanllvm_json_entry_pos8 leanllvm_json_entry_b8 \
           leanllvm_json_entry_table leanllvm_json_escape_list \
           leanllvm_json_stage2 leanllvm_json_utf8 eo_entry_pos8_skip \
           eo_entry_sparse; do
  if [ "$(nm --defined-only "$build/entry-opt" | grep -c " T $sym\$")" -eq 0 ]; then
    printf 'BUILD: the binary does not define %s\n' "$sym" >&2
    exit 2
  fi
done

printf '\nsource digests:\n'
for f in "$repo"/kernel/json/{pipeline,s1_block,entry,escape,utf8,stage2}.c \
         "$here/entry-opt.c" "$here/entry_variants.c" "$here/shape.c" \
         "$here/build.sh" "$here/run.sh"; do
  [ -f "$f" ] || continue
  printf '  %-60s %s\n' "${f#"$repo"/}" "$(sha256sum "$f" | cut -d' ' -f1)"
done
printf 'binary: %s sha256=%s\n' "$build/entry-opt" \
  "$(sha256sum "$build/entry-opt" | cut -d' ' -f1)"
printf 'binary: %s sha256=%s\n' "$build/entry-opt-shape" \
  "$(sha256sum "$build/entry-opt-shape" | cut -d' ' -f1)"
printf 'ok: %s\n' "$build/entry-opt"
printf 'ok: %s\n' "$build/entry-opt-shape"
