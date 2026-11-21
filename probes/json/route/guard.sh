#!/usr/bin/env bash
# The escape-list arm's scenario: stage 2 with the list against stage 2 without.
#
#   nix develop -c bash probes/json/route/guard.sh
#
# The route passes the pipeline's arm word; bit 1 is the escape-list gate.  The
# shipping arm is 0 on every document: stage 1 emits no list and stage 2
# classifies each string body by scanning its own span.  Bit 1 is still
# available, and this script is the equivalence gate between the two arms —
# `escape_guard.h` remains the document fact the admission reports, and the
# pipeline's consumer-observable output must not depend on which arm supplied
# the decoder's input.
#
# What it asserts, over every document it feeds:
#
#   1. the two arms agree on every consumer-observable field.  For each document
#      the pipeline is called twice on the same bytes with the same staging —
#      arm 2 (the stage-1 list) and arm 0 (no list; stage 2 rescans) — and the
#      verdict, the entry cursor, the error offset, the arena and event extents,
#      and both payloads are compared.  The escape-list count is stage 1's
#      output and is reported, not compared.
#   2. the guard's claim is still the list's emptiness: on every document the
#      guard fires on, the arm-2 list's count is zero.
#   3. the control is a defect build, not a property of the corpus.  A copy of
#      `kernel/json/stage2.c` whose list-free arm takes the old form (a) — the
#      body is its own materialisation and nothing is validated — must make arm
#      0 disagree with arm 2 on at least one document whose arm-2 list is not
#      empty.  A comparison that cannot see that build differ would be an
#      equality over nothing.
#
# The documents, and where they come from:
#
#   * `tests/json/corpus/*.json` — the route's own corpus, 130 documents,
#     including the rows that carry a raw control byte inside a string and no
#     backslash (`raw-lf.json` and its siblings), which are the rows the defect
#     control must catch;
#   * `tests/json-escape/corpus.tsv` — the escape unit's 21 committed rows, in
#     its own `<label> <hex> <n>` form, decoded by the probe's `--hex` mode;
#   * the bench's documents.  The nine that `probes/json/route/bench.sh` and
#     `probes/json/core-shape/shape.sh` generate are written here from the same
#     commands (bench.sh:141-149, shape.sh's corpus block), and the four
#     committed `probes/bench/json/*.json` are read in place.
#
# Exit status: 0 when every row holds and the defect control diverges, 1 when a
# row fails or the control agrees, 3 on a setup fault (no `clang`, an absent
# corpus or kernel source, a build that failed).
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
kernel=$repo/kernel/json
cc=clang

command -v "$cc" >/dev/null 2>&1 || { printf 'SETUP: no clang on PATH\n' >&2; exit 3; }
for path in "$repo/tests/json/corpus" "$repo/tests/json-escape/corpus.tsv" \
            "$kernel/pipeline.c" "$kernel/stage2.c" "$here/guard_check.c" \
            "$here/escape_guard.h"; do
  [ -e "$path" ] || { printf 'SETUP: absent: %s\n' "$path" >&2; exit 3; }
done

work=$(mktemp -d "${TMPDIR:-/tmp}/json-guard.XXXXXX") || {
  printf 'SETUP: cannot create a work directory\n' >&2; exit 3; }
trap 'rm -rf "$work"' EXIT

# The route's kernel line (`build.sh`'s `kflags`, `OPT` defaulting to -O2).
kflags=(-O2 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
        -falign-functions=64 -I "$kernel")
for u in pipeline s1_block entry escape utf8 stage2; do
  if ! "$cc" "${kflags[@]}" -c "$kernel/$u.c" -o "$work/$u.o" \
       2>"$work/build.err"; then
    printf 'SETUP: %s did not compile\n' "$kernel/$u.c" >&2
    awk 'NR <= 40' "$work/build.err" >&2
    exit 3
  fi
done
if ! "$cc" "${kflags[@]}" "$here/guard_check.c" \
      "$work/pipeline.o" "$work/s1_block.o" "$work/entry.o" \
      "$work/escape.o" "$work/utf8.o" "$work/stage2.o" \
      -o "$work/guard_check" 2>"$work/build.err"; then
  printf 'SETUP: the probe did not build\n' >&2
  awk 'NR <= 40' "$work/build.err" >&2
  exit 3
fi

# The defect build: the list branch of `s2_string_body` is made unconditional,
# so a list-free call (`nxp == 0`) takes form (a) and decodes and validates
# nothing -- the behaviour this change removes.  The substitution is asserted to
# apply exactly once; a rewritten branch is a setup fault, not a control that
# silently stops biting.
if [ "$(grep -c '^    if (nxp) {$' "$kernel/stage2.c")" -ne 1 ]; then
  printf 'SETUP: the list branch is not the one line the defect expects\n' >&2
  exit 3
fi
sed '0,/^    if (nxp) {$/s//    if (1) {/' "$kernel/stage2.c" \
  >"$work/stage2.defect.c"
if cmp -s "$kernel/stage2.c" "$work/stage2.defect.c"; then
  printf 'SETUP: the defect substitution changed nothing\n' >&2
  exit 3
fi
if ! "$cc" "${kflags[@]}" -c "$work/stage2.defect.c" -o "$work/stage2.defect.o" \
      2>"$work/build.err"; then
  printf 'SETUP: the defect stage 2 did not compile\n' >&2
  awk 'NR <= 40' "$work/build.err" >&2
  exit 3
fi
if ! "$cc" "${kflags[@]}" "$here/guard_check.c" \
      "$work/pipeline.o" "$work/s1_block.o" "$work/entry.o" \
      "$work/escape.o" "$work/utf8.o" "$work/stage2.defect.o" \
      -o "$work/guard_check_defect" 2>"$work/build.err"; then
  printf 'SETUP: the defect probe did not build\n' >&2
  awk 'NR <= 40' "$work/build.err" >&2
  exit 3
fi

# The bench's documents, generated from bench.sh's own commands.
bench=$work/bench
mkdir -p "$bench"
awk 'BEGIN{n=683;   printf "["; for(i=0;i<n;i++){if(i)printf ",";printf "12345"}; printf "]"}' >"$bench/fast-nums-4096.json"
awk 'BEGIN{n=2731;  printf "["; for(i=0;i<n;i++){if(i)printf ",";printf "12345"}; printf "]"}' >"$bench/fast-nums-16384.json"
awk 'BEGIN{n=10923; printf "["; for(i=0;i<n;i++){if(i)printf ",";printf "12345"}; printf "]"}' >"$bench/fast-nums-65536.json"
awk 'BEGIN{printf "["; printf "\""; for(i=0;i<1000;i++)printf "\\n"; printf "\"]"}' >"$bench/fast-esc.json"
awk 'BEGIN{printf "["; printf "\""; for(i=0;i<1000;i++)printf "\\\""; printf "\"]"}' >"$bench/fast-esc-quotes.json"
awk 'BEGIN{printf "["; printf "\""; for(i=0;i<500;i++)printf "\\u00e9"; printf "\"]"}' >"$bench/fast-esc-u.json"
awk 'BEGIN{printf "["; printf "\""; for(i=0;i<250;i++)printf "\\uD83D\\uDE00"; printf "\"]"}' >"$bench/fast-surrogate.json"
awk 'BEGIN{printf "["; printf "\""; for(i=0;i<1000;i++)printf "\303\251"; printf "\"]"}' >"$bench/fast-utf8.json"
cp "$repo/probes/bench/json/scale-4096.json" "$bench/scale-4096.json"

rows=$work/rows.txt
diag=$work/diag.txt
: >"$rows"
: >"$diag"
status=0

feed() { # <source> <file>
  if ! "$work/guard_check" "$2" 2>>"$diag" | sed "s/^file /$1 /" >>"$rows"; then
    status=1
  fi
}
feed_hex() { # <label> <hex-or->
  if ! "$work/guard_check" --hex "$1" "$2" 2>>"$diag" |         sed 's/^hex /escape /' >>"$rows"; then
    status=1
  fi
}

# 1. the route's corpus, then 2. the escape unit's committed rows.
for f in "$repo"/tests/json/corpus/*.json; do feed corpus "$f"; done
while IFS=$'\t' read -r label hex n; do
  [ -n "${label:-}" ] || continue
  feed_hex "$label" "$hex"
done <"$repo/tests/json-escape/corpus.tsv"

# 3. the bench documents: the generated nine and the four committed ones.
for f in "$bench"/*.json; do feed bench "$f"; done
for f in "$repo"/probes/bench/json/*.json; do feed bench "$f"; done

# The row transcript is the relation: one line per document, and the source
# column names which corpus it came from.
awk '{ print "  " $0 }' "$rows"

# The aggregates, from the transcript's own fields.  `fired` counts the rows the
# guard fires on, `agree` the rows that read identical=1, and `list` the rows
# whose arm-2 list is not empty.
read -r compared fired agree list < <(awk '{
  n++; g = 0; s = 0;
  for (i = 3; i <= NF; i++) {
    split($i, p, "=");
    if (p[1] == "guard") g = p[2] + 0;
    if (p[1] == "identical") s = p[2] + 0;
    if (p[1] == "nxp" && p[2] + 0 > 0) l++;
  }
  if (s == 1) a++;
  if (g == 1) f++;
} END { printf "%d %d %d %d\n", n, f, a, l }' "$rows")

# The defect control: the same comparison against a stage 2 whose list-free arm
# validates nothing.  At least one row whose arm-2 list is not empty must read
# identical=0; the correct build above must read identical=1 on every row.
defect_rows=$work/defect.txt
: >"$defect_rows"
while IFS=$'\t' read -r label hex n; do
  [ -n "${label:-}" ] || continue
  "$work/guard_check_defect" --hex "$label" "$hex" 2>/dev/null >>"$defect_rows" || true
done <"$repo/tests/json-escape/corpus.tsv"
read -r defect_compared defect_diverged < <(awk '{
  n++; x = 0; s = 1;
  for (i = 3; i <= NF; i++) {
    split($i, p, "=");
    if (p[1] == "nxp") x = p[2] + 0;
    if (p[1] == "identical") s = p[2] + 0;
  }
  if (s == 0 && x > 0) d++;
} END { printf "%d %d\n", n + 0, d + 0 }' "$defect_rows")

printf '\n'
printf 'rows compared        %s, of them identical %s (required: all)\n' \
  "${compared:-0}" "${agree:-0}"
printf 'guard fired          %s, arm-2 list non-empty %s\n' \
  "${fired:-0}" "${list:-0}"
printf 'defect rows          %s, diverged with a non-empty list %s (required: >0)\n' \
  "${defect_compared:-0}" "${defect_diverged:-0}"

failed=0
[ "${compared:-0}" -gt 0 ] || { echo 'FAIL: no row was compared'; failed=1; }
[ "${fired:-0}" -gt 0 ] || { echo 'FAIL: the guard fired on no row'; failed=1; }
[ "${list:-0}" -gt 0 ] || {
  echo 'FAIL: no row carried an arm-2 escape list'; failed=1; }
[ "${agree:-0}" -eq "${compared:-0}" ] || {
  echo 'FAIL: a row does not read identical=1'; failed=1; }
[ "${defect_compared:-0}" -gt 0 ] || {
  echo 'FAIL: the defect control compared no row'; failed=1; }
[ "${defect_diverged:-0}" -gt 0 ] || {
  echo 'FAIL: the defect build agrees with arm 2 on every row, so the comparison cannot bite'; failed=1; }
[ "$status" -eq 0 ] || { echo 'FAIL: a row did not hold (diagnostics above)'; failed=1; }

if [ "$failed" -ne 0 ]; then
  cat "$diag" >&2
  exit 1
fi
printf 'ok: arm 0 (rescan) and arm 2 (list) agree on every consumer-observable\n'
printf '    field on %s row(s), and the defect build diverges on %s of its %s\n' \
  "$compared" "$defect_diverged" "$defect_compared"
printf '    row(s) whose arm-2 list is not empty\n'
exit 0
