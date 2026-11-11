#!/usr/bin/env bash
# The stage-2 artifact correspondence the route relies on.
#
#   nix develop -c bash probes/json/route/correspondence.sh
#
# The proofs run `probes/install/ir/stage2.candidate.ll`: the -O3 emission of
# `kernel/json/stage2.c` with `noinline` on every helper except `s2_walk`, its
# switch lowered, the emitted attributes stripped and the eight staging objects
# flattened to parameters.  The route links an object built from the same
# `stage2.c` at `build.sh`'s flags, which use -O2 and no source transform.
# `stage2.candidate.ll`'s own header says in one line that it is "NOT the
# measured object's text", and a shared source filename is not a
# correspondence: this script derives and prints the relation that is actually
# relied on, and fails when a structural claim in it stops holding.
#
# What it asserts, and therefore what a stale record cannot hide:
#
#   - the two flag lines differ in the optimisation level alone: every other
#     token matches, `-O2` against `-O3`, ignoring the output-mode flags, the
#     include path and the naming flag;
#   - the source transform is the one `capture-stage2.sh` describes: two
#     `always_inline` occurrences (the comment's and `s2_walk`'s) and eleven
#     `noinline` helpers;
#   - `-fno-discard-value-names` changes no instruction at the route's own flag
#     line, measured with and without it;
#   - the eleven helpers are calls in the transformed emission and in the
#     committed fixture, and no calls at all in the untransformed emission at
#     either level, so the gap between the fixture and the object is the
#     transform's call composition and not the optimisation level.
#
# It measures, and prints for the record:
#
#   - which helper bodies are identical between the transformed -O2 and -O3
#     emissions after the recorded normalisation (register names replaced,
#     block labels and metadata dropped, the emitted attributes stripped);
#   - whether the walk's own body is identical under the same treatment;
#   - the call counts above, per symbol.
#
# Exit status: 0 when every asserted relation holds, 1 when one does not, 3 when
# a fixture is absent.
set -euo pipefail
export LC_ALL=C

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
stage2=$repo/kernel/json/stage2.c
capture=$repo/probes/install/ir/capture-stage2.sh
fixture=$repo/probes/install/ir/stage2.candidate.ll
symbol=leanllvm_json_stage2

for path in "$stage2" "$capture" "$fixture"; do
  [ -f "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done

work=$(mktemp -d "$repo/.lake/tmp-route-correspondence.XXXXXX" 2>/dev/null) ||
  work=$(mktemp -d) ||
  { echo "SETUP: cannot create a work directory" >&2; exit 3; }
trap 'rm -rf "$work"' EXIT

fail() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }

# ---------------------------------------------------------------------------
# The two flag lines
# ---------------------------------------------------------------------------

flag_line() { # <script> <array name>
  tr '\n' ' ' <"$1" | sed -n "s/.*[^A-Za-z0-9_]$2=(\([^)]*\)).*/\1/p"
}

build_flags=$(flag_line "$here/build.sh" cflags)
capture_flags=$(flag_line "$capture" flags)
[ -n "$build_flags" ] || fail "build.sh has no cflags=(...) line"
[ -n "$capture_flags" ] || fail "capture-stage2.sh has no flags=(...) line"

# The codegen tokens: the output-mode flags (the capture emits .ll, the route
# compiles .o), the include path and the naming flag are not code generation.
codegen_tokens() {
  local -a t
  read -r -a t <<<"$1"
  local i=0
  while [ "$i" -lt "${#t[@]}" ]; do
    case "${t[$i]}" in
      -I) i=$((i + 2)); continue ;;
      -I*) i=$((i + 1)); continue ;;
      -S|-emit-llvm|-fno-discard-value-names) i=$((i + 1)); continue ;;
      *) printf '%s\n' "${t[$i]}" ;;
    esac
    i=$((i + 1))
  done | sort -u
}

codegen_tokens "$build_flags" >"$work/build.flags"
codegen_tokens "$capture_flags" >"$work/capture.flags"
comm -23 "$work/build.flags" "$work/capture.flags" >"$work/only-build"
comm -13 "$work/build.flags" "$work/capture.flags" >"$work/only-capture"
comm -12 "$work/build.flags" "$work/capture.flags" >"$work/common"
[ -s "$work/common" ] || fail "the two flag lines share no codegen flag"
only_build=$(paste -sd' ' "$work/only-build")
only_capture=$(paste -sd' ' "$work/only-capture")
[ "$only_build" = "-O2" ] ||
  fail "build.sh carries '$only_build' beyond the capture's flags; the relation is not -O2 against -O3 alone"
[ "$only_capture" = "-O3" ] ||
  fail "capture-stage2.sh carries '$only_capture' beyond build.sh's flags; the relation is not -O2 against -O3 alone"
common_flags=$(paste -sd' ' "$work/common")

# ---------------------------------------------------------------------------
# The source transform, applied exactly as capture-stage2.sh applies it
# ---------------------------------------------------------------------------

sed -e 's/__attribute__((always_inline)) static inline/__attribute__((noinline)) static inline/g' \
    -e 's/#define EL_ENTRY __attribute__((always_inline)) static inline/#define EL_ENTRY __attribute__((noinline)) static inline/' \
    "$stage2" >"$work/step1.c"

awk '{ if (hold) { print "__attribute__((always_inline)) static inline uint64_t"; hold = 0 }
       if ($0 == "__attribute__((noinline)) static inline uint64_t") { hold = 1; next }
       print }
     END { if (hold) exit 1 }' "$work/step1.c" >"$work/noinline.c" ||
  fail "the s2_walk attribute was not restored"

n_al=$(grep -c 'always_inline' "$work/noinline.c" || true)
n_ni=$(grep -c '__attribute__((noinline))' "$work/noinline.c" || true)
[ "$n_al" -eq 2 ] ||
  fail "the transformed source carries $n_al 'always_inline' occurrences, not 2"
# Twelve occurrences: eleven function definitions and the `EL_ENTRY` macro line.
[ "$n_ni" -eq 12 ] ||
  fail "the transformed source carries $n_ni 'noinline' occurrences, not 12"
grep -A1 '^__attribute__((always_inline)) static inline uint64_t$' "$work/noinline.c" |
  grep -q '^s2_walk(' ||
  fail "the one forced-inline function is not s2_walk"

# The eleven functions the transform takes out of line.  A `#` line is skipped
# rather than joined: the `EL_ENTRY` macro carries the attribute too but is not
# a function, and a continued `static inline void` header's name is on the next
# line.
awk '/__attribute__\(\(noinline\)\)/ {
       if ($0 ~ /^#/) next
       line = $0
       sub(/.*__attribute__\(\(noinline\)\)/, "", line)
       while (line !~ /\(/) {
         if ((getline nxt) <= 0) exit 1
         if (nxt ~ /^#/) continue
         line = line " " nxt
       }
       if (match(line, /[A-Za-z_][A-Za-z0-9_]*\(/))
         print substr(line, RSTART, RLENGTH - 1)
     }' "$work/noinline.c" | sort -u >"$work/helpers"
[ "$(wc -l <"$work/helpers" | tr -d ' ')" -eq 11 ] ||
  fail "read a helper list that is not eleven function names: $(paste -sd' ' "$work/helpers")"

# ---------------------------------------------------------------------------
# The emissions
# ---------------------------------------------------------------------------

base=(-march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)
compile() { ( cd "$repo" && clang -I kernel/json "$@" ); }

compile -S -emit-llvm -O2 "${base[@]}" -fno-discard-value-names "$work/noinline.c" -o "$work/o2.ll"
compile -S -emit-llvm -O3 "${base[@]}" -fno-discard-value-names "$work/noinline.c" -o "$work/o3.ll"
compile -S -emit-llvm -O2 "${base[@]}" "$work/noinline.c" -o "$work/o2.plain.ll"
compile -S -emit-llvm -O2 "${base[@]}" "$stage2" -o "$work/fused-o2.ll"
compile -S -emit-llvm -O3 "${base[@]}" "$stage2" -o "$work/fused-o3.ll"
opt -S -passes=lower-switch "$work/o2.ll" -o "$work/o2.lowered.ll"
opt -S -passes=lower-switch "$work/o3.ll" -o "$work/o3.lowered.ll"

# The naming flag's claim, at the route's own optimisation level: the same
# source, with and without the flag, is the same instructions after register
# names and block labels are neutralised.
normalise_surface() {
  sed -E -e 's/%[A-Za-z0-9_.$-]+/%r/g' |
    awk '!/^[A-Za-z0-9_.$-]+:/ && !/^[ \t]*$/ && !/^(!|attributes #|target |source_filename)/'
}
normalise_surface <"$work/o2.ll" >"$work/o2.named.norm"
normalise_surface <"$work/o2.plain.ll" >"$work/o2.plain.norm"
cmp -s "$work/o2.named.norm" "$work/o2.plain.norm" ||
  fail "-fno-discard-value-names changed an instruction at -O2; it is not a naming flag there"

# ---------------------------------------------------------------------------
# The body comparison: the capture's token strip, then neutral naming
# ---------------------------------------------------------------------------

block_of() { # <file> <symbol>
  awk -v sym="$2" '
    $0 ~ "^define .*@" sym "\\(" { on = 1 }
    on { print }
    on && $0 == "}" { exit }' "$1"
}

# `capture-stage2.sh`'s strip, in its two passes, so the two emissions are
# compared after the same surface removal the fixture records.
strip_surface() {
  sed -E \
    -e 's/ (noundef|nonnull|readonly|writeonly|noalias|zeroext|signext|returned|immarg|nocapture|nofree|nosync|nounwind|norecurse|willreturn|mustprogress)//g' \
    -e 's/ (captures|range|initializes|dereferenceable|dereferenceable_or_null|nofpclass)\([^)]*(\([^)]*\))?[^)]*\)//g' \
    -e 's/ (local_unnamed_addr|unnamed_addr)//g' \
    -e 's/ (nuw|nsw|nusw|disjoint|nneg)//g' \
    -e 's/ align [0-9]+//g' \
    -e 's/ #[0-9]+//g' \
    -e 's/^define ([^@]*)@/define \1@/' |
    sed -E -e 's/^(define .*)\) align [0-9]+ \{$/\1) {/' \
      -e 's/, align [0-9]+//g' -e 's/, !tbaa ![0-9]+//g' \
      -e 's/, ![A-Za-z0-9_.]+ ![0-9]+//g' \
      -e 's/, !llvm\.[^ ]*//g' -e 's/ call fastcc / call /g' -e 's/,[ \t]*$//'
}

normalised_block() { # <file> <symbol>
  block_of "$1" "$2" | strip_surface | normalise_surface
}

# ---------------------------------------------------------------------------
# The call counts
# ---------------------------------------------------------------------------

calls_in_block() { # <file> <symbol> <callee>
  awk -v sym="$2" -v fn="$3" '
    $0 ~ "^define .*@" sym "\\(" { on = 1 }
    on && index($0, "@" fn "(") { n++ }
    on && $0 == "}" { exit }
    END { printf "%d", n + 0 }' "$1"
}

count_calls() { # <file> <names file>
  local total=0 h
  while IFS= read -r h; do
    total=$((total + $(calls_in_block "$1" "$symbol" "$h")))
  done <"$2"
  printf '%s' "$total"
}

fixture_calls=$(count_calls "$fixture" "$work/helpers")
o2_calls=$(count_calls "$work/o2.lowered.ll" "$work/helpers")
o3_calls=$(count_calls "$work/o3.lowered.ll" "$work/helpers")
fused_o2_calls=$(count_calls "$work/fused-o2.ll" "$work/helpers")
fused_o3_calls=$(count_calls "$work/fused-o3.ll" "$work/helpers")

[ "$fixture_calls" -gt 0 ] ||
  fail "the committed fixture has no call to any of the eleven helpers; the noinline transform is not the fixture's"
[ "$o2_calls" -eq "$fixture_calls" ] ||
  fail "the transformed -O2 emission has $o2_calls helper call(s), the fixture has $fixture_calls"
[ "$o3_calls" -eq "$fixture_calls" ] ||
  fail "the transformed -O3 emission has $o3_calls helper call(s), the fixture has $fixture_calls"
[ "$fused_o2_calls" -eq 0 ] ||
  fail "the untransformed -O2 emission keeps $fused_o2_calls helper call(s); the helpers are always_inline, so the call composition is the transform's"
[ "$fused_o3_calls" -eq 0 ] ||
  fail "the untransformed -O3 emission keeps $fused_o3_calls helper call(s); the helpers are always_inline, so the call composition is the transform's"

# ---------------------------------------------------------------------------
# Which bodies are identical under the transform
# ---------------------------------------------------------------------------

identical=()
differing=()
o2_only=()
o3_only=()
absent=()
for h in $(cat "$work/helpers"); do
  block_of "$work/o2.lowered.ll" "$h" >"$work/h.o2.ll"
  block_of "$work/o3.lowered.ll" "$h" >"$work/h.o3.ll"
  if [ ! -s "$work/h.o2.ll" ] || [ ! -s "$work/h.o3.ll" ]; then
    if [ ! -s "$work/h.o2.ll" ] && [ ! -s "$work/h.o3.ll" ]; then
      absent+=("$h")
    elif [ ! -s "$work/h.o2.ll" ]; then
      o2_only+=("$h")
    else
      o3_only+=("$h")
    fi
    continue
  fi
  normalised_block "$work/o2.lowered.ll" "$h" >"$work/h.o2.norm"
  normalised_block "$work/o3.lowered.ll" "$h" >"$work/h.o3.norm"
  if cmp -s "$work/h.o2.norm" "$work/h.o3.norm"; then
    identical+=("$h")
  else
    differing+=("$h")
  fi
done

normalised_block "$work/o2.lowered.ll" "$symbol" >"$work/walk.o2.norm"
normalised_block "$work/o3.lowered.ll" "$symbol" >"$work/walk.o3.norm"
if cmp -s "$work/walk.o2.norm" "$work/walk.o3.norm"; then
  walk=identical
else
  walk=differs
fi
walk_o2_lines=$(wc -l <"$work/walk.o2.norm" | tr -d ' ')
walk_o3_lines=$(wc -l <"$work/walk.o3.norm" | tr -d ' ')
fixture_body_lines=$(awk '/^define /{on=1} on && !/^(define|declare)/ && !/^[ \t]*;/ {n++} END{printf "%d", n+0}' "$fixture")
object_body_lines=$(wc -l <"$work/walk.o2.norm" | tr -d ' ')

# ---------------------------------------------------------------------------
# The record
# ---------------------------------------------------------------------------

printf '## The two artifact paths\n\n'
printf '| | flags | source | derivation |\n'
printf '|---|---|---|---|\n'
printf '| the proofs'"'"' body (`probes/install/ir/stage2.candidate.ll`) | `%s` | `kernel/json/stage2.c`, `noinline` on eleven helpers, `s2_walk` forced inline | `opt -passes=lower-switch`, the recorded token strip, eight staging allocas flattened to parameters, callees reduced to declarations |\n' "$(printf '%s' "$capture_flags" | sed 's/  */ /g')"
printf '| the route'"'"'s object (`probes/json/route/build.sh`) | `%s` | the same file, untransformed | none: `clang -c` |\n\n' "$(printf '%s' "$build_flags" | sed 's/  */ /g')"

printf '## The flag relation\n\n'
printf 'The codegen token sets are equal except for the optimisation level:\n\n'
printf -- '- common: `%s`\n' "$common_flags"
printf -- '- `build.sh` alone: `%s`\n' "$only_build"
printf -- '- `capture-stage2.sh` alone: `%s`\n' "$only_capture"
printf -- '- ignored as non-codegen: `-S -emit-llvm` (output mode), `-I` and its path (include path), `-fno-discard-value-names` (naming)\n\n'
printf 'The naming flag changes no instruction at the route'"'"'s own -O2 line: the emission with and without it is identical after register names and block labels are neutralised.\n\n'

printf '## The normalisation steps\n\n'
printf 'The fixture is derived, not transcribed.  In order: (1) the source transform above, whose counts are two `always_inline` occurrences (the comment'"'"'s and `s2_walk`'"'"'s) and eleven `noinline` helper functions, plus the `EL_ENTRY` macro line; (2) `opt -passes=lower-switch`; (3) the token strip, by the classes `capture-stage2.sh` records in `stage2.strip.tsv`; (4) the eight staging allocas `%%d.i %%c.i %%ctype.i %%cst.i %%t352.i %%s %%z %%e` appended as `ptr` parameters (`stage2.staging.tsv`); (5) the three instruction rewrites and the callee definitions replaced by declarations (`stage2.rewrites.tsv`).  The comparison below applies steps (1)–(3) to both emissions and then replaces every virtual register with one placeholder and drops block labels, so the two texts are compared instruction by instruction.\n\n'

printf '## What is identical, and what is not\n\n'
printf 'The eleven helpers, as emitted under the transform at each level:\n\n'
printf -- '- identical after the normalisation (%s): `%s`\n' "${#identical[@]}" "$(printf '%s ' "${identical[@]}")"
if [ "${#differing[@]}" -gt 0 ]; then
  printf -- '- differing (%s): `%s`\n' "${#differing[@]}" "$(printf '%s ' "${differing[@]}")"
else
  printf -- '- differing: none\n'
fi
if [ "${#o2_only[@]}" -gt 0 ] || [ "${#o3_only[@]}" -gt 0 ]; then
  printf -- '- emitted at one level only: `%s %s`\n' "${o2_only[*]:-}" "${o3_only[*]:-}"
fi
if [ "${#absent[@]}" -gt 0 ]; then
  printf -- '- not emitted at either level (a `static` function this translation unit no longer references once the callers are out of line): `%s`\n' "${absent[*]}"
fi
printf '\nThe walk'"'"'s own body (`@%s` with `s2_walk` inlined): %s after the same normalisation, %s lines at -O2 against %s at -O3.\n\n' \
  "$symbol" "$walk" "$walk_o2_lines" "$walk_o3_lines"

printf 'The helper calls the fixture keeps, per emission of the wrapper block: `%s` in the committed fixture, `%s` in the transformed -O2 emission, `%s` in the transformed -O3 emission, and `%s`/`%s` in the untransformed -O2/-O3 emissions.  Every helper is `always_inline` before the transform, so the untransformed object has none: the distance between the fixture and the object is the call composition of the transform, not the optimisation level.\n\n' \
  "$fixture_calls" "$o2_calls" "$o3_calls" "$fused_o2_calls" "$fused_o3_calls"

printf '## The relation relied on, and its residual\n\n'
printf 'The correspondence between the proof'"'"'s body and the route'"'"'s object is these five statements and no more:\n\n'
printf '1. both artifacts are emitted from `kernel/json/stage2.c`; this is necessary and not sufficient, and it is all that the shared filename gives;\n'
printf '2. their codegen flags differ in the optimisation level alone (`%s` against `%s`), measured above, and the naming flag is not an instruction change, measured above;\n' "$only_build" "$only_capture"
printf '3. of the eleven helper bodies, %s are identical between the two levels under the transform after the recorded normalisation, %s differ, and %s are not emitted at either level; the walk'"'"'s body %s;\n' \
  "${#identical[@]}" "${#differing[@]}" "${#absent[@]}" "$walk"
printf '4. the fixture keeps %s helper call site(s) where the untransformed emissions keep %s, so the object inlines every helper the fixture leaves out of line;\n' \
  "$fixture_calls" "$fused_o2_calls"
printf '5. the object'"'"'s walk text is therefore not the fixture'"'"'s text: the fixture'"'"'s body is %s instruction line(s) against the object'"'"'s normalised %s.\n\n' \
  "$fixture_body_lines" "$object_body_lines"
printf 'So the object is not the fixture'"'"'s function by these measurements: the fixture is the walk'"'"'s text with the helpers it takes out of line as callees, and the object at -O2 has none of them out of line and a different instruction selection inside the walk.  What the record establishes is the shape of the gap — same source, same code-generating flags but the level, a known transform, and a measured body-by-body difference — so a claim that the linked object computes the fixture'"'"'s function has to carry the compiler/backend trust row and the helper-contract transfer for the bodies that differ here.  It cannot be inferred from the source filename, and the probe does not claim it.\n\n'
printf 'Unification was not taken: linking the fixture would make the route call a twenty-one-argument body while the driver calls the thirteen-argument ABI, so the two callers would stop being comparable, and the fixture'"'"'s callees are declarations the proof'"'"'s environment resolves rather than objects the probe links.\n'

exit 0
