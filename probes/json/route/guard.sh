#!/usr/bin/env bash
# The escape-list guard's scenario.
#
#   nix develop -c bash probes/json/route/guard.sh
#
# The route passes the pipeline's arm word, and bit 1 of it is the escape-list
# gate: with it set `leanllvm_json_escape_list` runs on every 64-byte block even
# where its output is empty.  `escape_guard.h` states the guard — no backslash
# byte and no byte at or below `0x1F` — and `RouteMain.lean`'s fast path takes
# the arm from it.  This script checks the claim the guard rests on and prices
# nothing: `probes/json/core-shape/shape.sh` is the timing instrument.
#
# What it asserts, over every document it feeds:
#
#   1. the two arms agree byte for byte.  For each document the pipeline is
#      called twice on the same bytes with the same staging — arm 2, and the arm
#      the guard selects — and the verdict, the four cursors, the error offset,
#      the arena bytes and the event bytes are compared.  Where the guard does
#      not fire the two calls are the same call by construction (the arm words
#      are equal), so the comparison is the guard's own work there.
#   2. the guard's claim is the list's emptiness, not a coincidence of the two
#      arms' reporting: on every document the guard fires on, the arm-2 list's
#      count is zero.  A guard that fired on a document whose list is not empty
#      would be a red here even if the two outputs happened to agree.
#   3. the control fires.  On a document whose arm-2 list is not empty, forcing
#      bit 1 clear must change the observable result; a forced arm that agreed
#      would mean the guard's decision is not the claim under test.  The
#      documents that exercise it are named in the transcript, and at least one
#      is required.
#
# The documents, and where they come from:
#
#   * `tests/json/corpus/*.json` — the route's own corpus, 130 documents,
#     including the rows that carry a raw control byte inside a string and no
#     backslash (`raw-lf.json` and its siblings), which is exactly the class a
#     backslash-only guard would miss;
#   * `tests/json-escape/corpus.tsv` — the escape unit's 21 committed rows, in
#     its own `<label> <hex> <n>` form, decoded by the probe's `--hex` mode;
#   * the bench's documents.  The nine that `probes/json/route/bench.sh` and
#     `probes/json/core-shape/shape.sh` generate are written here from the same
#     commands (bench.sh:141-149, shape.sh's corpus block), and the four
#     committed `probes/bench/json/*.json` are read in place.
#
# Exit status: 0 when every row holds and all three controls are non-empty, 1
# when a row or a control fails, 3 on a setup fault (no `clang`, an absent
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
# guard fires on, `fire_identical` those of them that read identical=1, `list`
# the rows whose arm-2 list is not empty (the control set), and `controls` the
# rows a forced arm 0 actually changed.
read -r compared fired fire_identical list controls < <(awk '{
  n++; g = 0; s = 0;
  for (i = 3; i <= NF; i++) {
    split($i, p, "=");
    if (p[1] == "guard") g = p[2] + 0;
    if (p[1] == "identical") s = p[2] + 0;
    if (p[1] == "nxp" && p[2] + 0 > 0) l++;
    if (p[1] == "control" && p[2] == "fired") c++;
  }
  if (g == 1) { f++; if (s == 1) fi++; }
} END { printf "%d %d %d %d %d\n", n, f, fi, l, c }' "$rows")

printf '\n'
printf 'rows compared        %s\n' "${compared:-0}"
printf 'guard fired          %s, of them identical %s (required: equal)\n' \
  "${fired:-0}" "${fire_identical:-0}"
printf 'arm-2 list non-empty %s (the control set)\n' "${list:-0}"
printf 'controls fired       %s\n' "${controls:-0}"

failed=0
[ "${compared:-0}" -gt 0 ] || { echo 'FAIL: no row was compared'; failed=1; }
[ "${fired:-0}" -gt 0 ] || { echo 'FAIL: the guard fired on no row'; failed=1; }
[ "${list:-0}" -gt 0 ] || {
  echo 'FAIL: no row carried an arm-2 escape list, so the control set is empty'; failed=1; }
[ "${controls:-0}" -gt 0 ] || {
  echo 'FAIL: the forced-arm control fired on no row'; failed=1; }
[ "${fire_identical:-0}" -eq "${fired:-0}" ] || {
  echo 'FAIL: a row the guard fired on does not read identical=1'; failed=1; }
[ "$status" -eq 0 ] || { echo 'FAIL: a row did not hold (diagnostics above)'; failed=1; }

if [ "$failed" -ne 0 ]; then
  cat "$diag" >&2
  exit 1
fi
printf 'ok: the guard and arm 2 agree on every row it fires on, and the control\n'
printf '    fires on the %s rows whose arm-2 list is not empty\n' "$list"
exit 0
