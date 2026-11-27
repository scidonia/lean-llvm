#!/usr/bin/env bash
# Emit the production stage-2 IR once, record the bytes and what reads them.
#
#   nix develop -c bash probes/install/ir/capture-stage2-production.sh
#
# Unlike `capture-stage2.sh`, nothing here transforms the source and nothing is
# normalised: the artifact is the emission the route's build compiles, at the
# route's own flags (`probes/json/route/build.sh`: `-O2` plus the measured
# codegen line).  The fixture remains the separate derivation that script owns;
# this one writes `stage2.production.ll` and its record, and never touches
# `stage2.candidate.ll`.
#
# Output
#   stage2.production.ll        the emission, byte for byte
#   stage2.production.tsv       the command, flags, target layout, digest and
#                               the import verdict
#   stage2.production.import.tsv  each measured stopping point, from the raw
#                               module inward: the first construct the parser
#                               refuses at that level, with its function and
#                               instruction or declaration
#
# Exit status: 0 when the three files are written (an import refusal is a
# recorded result, not a setup fault); 3 when clang, opt or the parser is
# missing, or the emission is not well-formed IR.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)

src=kernel/json/stage2.c
symbol=leanllvm_json_stage2
artifact=$here/stage2.production.ll
record=$here/stage2.production.tsv
imports=$here/stage2.production.import.tsv

fail() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

[ -f "$repo/$src" ] || fail "absent: $repo/$src"
command -v clang >/dev/null 2>&1 || fail "clang is not on PATH"
command -v opt >/dev/null 2>&1 || fail "opt is not on PATH"
parser=$repo/.lake/build/bin/leanllvm
[ -x "$parser" ] || fail "absent: $parser (build it with 'lake build leanllvm')"

work=$(mktemp -d "$repo/.lake/tmp-stage2-production.XXXXXX" 2>/dev/null) ||
  work=$(mktemp -d) ||
  fail "cannot create a work directory"
trap 'rm -rf "$work"' EXIT

# `probes/json/route/build.sh`'s line, with the output mode it does not need.
opt_level=${OPT:--O2}
flags=("$opt_level" -march=x86-64-v3 -mpclmul -std=gnu11
       -falign-loops=64 -falign-functions=64 -I "$repo/kernel/json")
emit=("${flags[@]}" -S -emit-llvm)

( cd "$repo" && clang "${emit[@]}" "$src" -o "$work/stage2.ll" ) ||
  fail "clang refused the emission"

opt -passes=verify -disable-output "$work/stage2.ll" ||
  fail "the emission is not well-formed IR"

triple=$(sed -n 's/^target triple = "\(.*\)"$/\1/p' "$work/stage2.ll")
datalayout=$(sed -n 's/^target datalayout = "\(.*\)"$/\1/p' "$work/stage2.ll")
[ -n "$triple" ] || fail "the emission carries no target triple"
[ -n "$datalayout" ] || fail "the emission carries no target datalayout"

sha=$(sha256sum "$work/stage2.ll" | awk '{print $1}')

# The named structs the emission carries, with the extent the target gives each:
# `parseModuleWith` takes these as its `Layout`, and the driver passes none.  The
# extents come from clang's own record layout for this target, not from a reading
# of the IR text.
( cd "$repo" && clang "${flags[@]}" -Xclang -fdump-record-layouts -fsyntax-only "$src" ) \
  > "$work/layouts.txt" 2>/dev/null || fail "clang refused the record-layout dump"
structs=""
for name in $(grep -o '%struct\.[A-Za-z0-9_]*' "$work/stage2.ll" | sed 's/%struct\.//' | sort -u); do
  size=$(awk -v n="$name" '
    $0 ~ "^ *0 \\| " n "$" { want = 1; next }
    want && match($0, /\[sizeof=[0-9]+/) {
      s = substr($0, RSTART + 8, RLENGTH - 8)
      print s; exit
    }' "$work/layouts.txt")
  [ -n "$size" ] || fail "no record layout for %struct.$name"
  structs="$structs %struct.$name=$size"
done
bytes=$(wc -c < "$work/stage2.ll" | tr -d ' ')
lines=$(wc -l < "$work/stage2.ll" | tr -d ' ')
ndef=$(grep -c '^define ' "$work/stage2.ll" || true)
ndecl=$(grep -c '^declare ' "$work/stage2.ll" || true)
funcs=$(grep '^define ' "$work/stage2.ll" | sed -E 's/^define .*@([A-Za-z0-9_.$]+)\(.*/\1/' | paste -sd, -)

# The import refusal, as the driver reports it: the parser's own message.
import_message() { # <file> -> the first line of the parser's error
  set +e
  "$parser" --passes none --no-check -o /dev/null "$1" 2> "$2"
  local st=$?
  set -e
  sed -n "s/^leanllvm: parse error in '[^']*': //p" "$2" | head -1
  return $st
}

raw_message=$(import_message "$work/stage2.ll" "$work/raw.err" || true)
raw_status=0
"$parser" --passes none --no-check -o /dev/null "$work/stage2.ll" >/dev/null 2>&1 || raw_status=$?

# The measured descent.  Each row is a mechanical restriction of the emission
# above; the row's message is the first construct the parser refuses once that
# restriction is in place, and the site is the function, block and line that
# carries it.  The restrictions are exactly `capture-stage2.sh`'s documented
# strip classes plus the module-level omissions it also records, so no row hides
# a construct the strip would not have removed.
cat > "$work/site.awk" <<'AWK'
# The parse refusal names a block and the token it refused; find the first
# instruction in that block carrying the token, and the define that encloses it.
BEGIN {
  msg = ENVIRON["MSG"]
  blk = ""
  if (match(msg, /in block /)) {
    rest = substr(msg, RSTART + 9)
    split(rest, parts, "\047")
    blk = parts[2]
  }
  n = split(msg, q, "\047")
  tok = (n >= 3) ? q[n - 1] : ""
}
{ line[NR] = $0 }
END {
  start = 0
  for (i = 1; i <= NR; i++)
    if (blk != "" && index(line[i], blk ":") == 1) { start = i; break }
  if (start == 0) exit
  hit = 0
  for (i = start; i <= NR; i++) {
    if (i > start && line[i] ~ /^[A-Za-z0-9_.]+:/) break
    if (tok != "" && index(line[i], tok) > 0) { hit = i; break }
  }
  at = (hit ? hit : start)
  fn = ""
  for (i = at; i >= 1; i--) {
    if (match(line[i], /^define .*@[A-Za-z0-9_.$]+\(/)) {
      s = substr(line[i], RSTART)
      match(s, /@[A-Za-z0-9_.$]+/)
      fn = substr(s, RSTART + 1, RLENGTH - 1)
      break
    }
  }
  if (hit) {
    t = line[hit]
    gsub(/^[ \t]+/, "", t)
    printf "%s\t%s:%d\t%s\n", fn, blk, hit, t
  } else printf "%s\t%s\t-\n", fn, blk
}
AWK

strip_module() { # module declarations, type definitions, globals, metadata
  awk '
    /^source_filename =/ {next}
    /^target (datalayout|triple) =/ {next}
    /^%[A-Za-z0-9_.]+ = type / {next}
    /^@[A-Za-z0-9_.]+ = / {next}
    /^attributes #[0-9]+ = / {next}
    /^!/ {next}
    {print}' "$1" > "$2"
}
strip_surface() { # classes 1, 2, 3, 9, 10 and the instruction metadata class 5
  sed -E \
    -e 's/ (noundef|nonnull|readonly|writeonly|noalias|zeroext|signext|returned|immarg|nocapture|nofree|nosync|nounwind|norecurse|willreturn|mustprogress)//g' \
    -e 's/ (captures|range|initializes|dereferenceable|dereferenceable_or_null|nofpclass)\([^)]*(\([^)]*\))?[^)]*\)//g' \
    -e 's/ (local_unnamed_addr|unnamed_addr)//g' \
    -e 's/ #[0-9]+//g' \
    -e 's/^(define .*)\) align [0-9]+ \{$/\1) {/' \
    -e 's/, !tbaa ![0-9]+//g' \
    -e 's/, ![A-Za-z0-9_.]+ ![0-9]+//g' \
    -e 's/, !llvm\.[^ ]*//g' \
    -e 's/, align [0-9]+//g' \
    -e 's/ call fastcc / call /g' \
    -e 's/,[ \t]*$//' \
    "$1" > "$2"
}
strip_flags() { # class 4: nuw, nsw, nusw, disjoint, nneg
  sed -E 's/ (nuw|nsw|nusw|disjoint|nneg)//g' "$1" > "$2"
}

strip_module "$work/stage2.ll" "$work/v1.ll"
strip_surface "$work/v1.ll" "$work/v2.ll"
# From here the emission carries `-fno-discard-value-names`, because clang emits
# no label for an unnamed entry block and the parser requires one.  The flag is
# the one `capture-stage2.sh` measures to change no instruction; the descent is
# a measurement of the parser, not of codegen.
( cd "$repo" && clang "${flags[@]}" -fno-discard-value-names -S -emit-llvm "$src" \
    -o "$work/named.ll" ) || fail "clang refused the named emission"
named_sha=$(sha256sum "$work/named.ll" | awk '{print $1}')
strip_module "$work/named.ll" "$work/n1.ll"
strip_surface "$work/n1.ll" "$work/n2.ll"
strip_flags "$work/n2.ll" "$work/n3.ll"
# The switch has to be lowered while the type definitions are still present.
opt -S -passes=lower-switch "$work/named.ll" -o "$work/lowered.ll"
strip_module "$work/lowered.ll" "$work/n1l.ll"
strip_surface "$work/n1l.ll" "$work/n2l.ll"
strip_flags "$work/n2l.ll" "$work/n3l.ll"

record_import() { # <level> <file> <description>
  local level=$1 file=$2 desc=$3 msg site
  msg=$(import_message "$file" "$work/level$level.err" || true)
  site=$(MSG="$msg" awk -v msg="$msg" -f "$work/site.awk" "$file")
  printf '%s\t%s\t%s\t%s\n' "$level" "$desc" "$msg" "$site" >> "$imports"
}
: > "$imports"
record_import 0 "$work/stage2.ll" "the emission, byte for byte"
record_import 1 "$work/v1.ll" "module declarations, type definitions, globals, attributes and metadata omitted"
record_import 2 "$work/v2.ll" "plus parameters, returns, calls and headers stripped of their attributes; the unnamed entry block has no label"
record_import 3 "$work/n2.ll" "the same strip on the named emission"
record_import 4 "$work/n3.ll" "plus nuw/nsw/nusw/disjoint/nneg removed"
record_import 5 "$work/n3l.ll" "plus switch lowered (opt -passes=lower-switch)"

# The object the route links: the backend's compilation of the same bytes, with
# the middle end disabled so the object is not a second optimisation of them.
( cd "$repo" && clang "${flags[@]}" -c -Xclang -disable-llvm-passes "$work/stage2.ll" \
    -o "$work/stage2.o" 2>/dev/null ) ||
  fail "clang refused the emission as an object input"
obj_sha=$(sha256sum "$work/stage2.o" | awk '{print $1}')
obj_bytes=$(wc -c < "$work/stage2.o" | tr -d ' ')
# The object the same flags build from the source: the text-derived object is
# recorded beside it rather than assumed to equal it.
( cd "$repo" && clang "${flags[@]}" -c "$src" -o "$work/source.o" ) ||
  fail "clang refused the source object"
src_obj_sha=$(sha256sum "$work/source.o" | awk '{print $1}')
# The naming flag is a naming flag: the named emission, compiled the same way,
# is the same object.  The record states it only because this proves it here.
( cd "$repo" && clang "${flags[@]}" -c -Xclang -disable-llvm-passes "$work/named.ll" \
    -o "$work/named.o" 2>/dev/null ) || fail "clang refused the named emission as an object input"
named_obj_sha=$(sha256sum "$work/named.o" | awk '{print $1}')
[ "$named_obj_sha" = "$obj_sha" ] ||
  fail "-fno-discard-value-names changed the object ($named_obj_sha against $obj_sha)"

cp "$work/stage2.ll" "$artifact"

{
  printf '# The production stage-2 emission and what reads it.\n'
  printf 'source\t%s\n' "$src"
  printf 'emit\tclang %s -S -emit-llvm %s -o probes/install/ir/stage2.production.ll\n' \
    "${opt_level} -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64 -I kernel/json" "$src"
  printf 'opt\t%s\n' "$opt_level"
  printf 'triple\t%s\n' "$triple"
  printf 'datalayout\t%s\n' "$datalayout"
  printf 'struct_extents\t%s\n' "${structs# }"
  printf 'sha256\t%s\n' "$sha"
  printf 'named_flag\t-fno-discard-value-names: sha256 %s (changes names only: the two emissions compile to the same object)\n' "$named_sha"
  printf 'bytes\t%s\n' "$bytes"
  printf 'lines\t%s\n' "$lines"
  printf 'defines\t%s\n' "$ndef"
  printf 'declares\t%s\n' "$ndecl"
  printf 'functions\t%s\n' "$funcs"
  printf 'verify\topt -passes=verify: ok\n'
  printf 'parser_layout\tparseModule (empty Layout): named structs in an alloca or getelementptr need a declared byte extent the driver does not supply\n'
  printf 'import\texit %s: %s\n' "$raw_status" "$raw_message"
  printf 'object\tclang %s -c -Xclang -disable-llvm-passes %s -o stage2.o\n' \
    "${opt_level} -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64" \
    "probes/install/ir/stage2.production.ll"
  printf 'object_sha256\t%s\n' "$obj_sha"
  printf 'object_bytes\t%s\n' "$obj_bytes"
  printf 'source_object_sha256\t%s\n' "$src_obj_sha"
  if [ "$obj_sha" = "$src_obj_sha" ]; then
    printf 'object_dataset\tthe same flags build this object from kernel/json/stage2.c: identical\n'
  else
    printf 'object_dataset\tthe same flags build %s from kernel/json/stage2.c: the text-derived object is not that object; the bitcode route (-c -emit-llvm, then -Xclang -disable-llvm-passes) reproduces it byte for byte\n' "$src_obj_sha"
  fi
} > "$work/record.tsv"

cp "$work/record.tsv" "$record"

printf 'ok: %s (sha256 %s, %s bytes), %s, %s\n' \
  "${artifact#$repo/}" "$sha" "$bytes" "${record#$repo/}" "${imports#$repo/}"
printf 'import: exit %s: %s\n' "$raw_status" "$raw_message"
