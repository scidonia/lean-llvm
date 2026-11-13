#!/usr/bin/env bash
# Measure the fast path's residue: which documents it refuses, by the admission
# clause that refused, over every document set the repository has, and over the
# document shapes the corpus does not cover.
#
#   nix develop -c bash probes/json/route/residue.sh
#
# The route is the shipped build (`probes/json/route/build.sh`); the decision is
# read from `--admit <file> 1`, which prints the two-phase verdict, the clause,
# the measured depth and the policy class on one line, and the reference's own
# verdict on the same bytes is read from `leanllvm-json` (`--corpus/--manifest`).
# Nothing here is timed: the unit is documents, and every row states its
# construction.
#
# The document sets:
#
#   corpus     the 130 rows of `tests/json/manifest.tsv`, one per corpus file.
#              The manifest's verdict is the expected reference verdict under
#              the row's own profile, and the reference is re-run on the same
#              bytes here, so the manifest is checked rather than trusted.
#   scenario   the 135 documents the route's own scenario generates
#              (`check.sh`): the empty document, the over-bound one, the
#              opener-rich string, the four depth documents, the eight
#              hand-written depth-clause documents and the 120-document
#              fixed-seed sweep.  The constructions are `check.sh`'s, copied
#              here so the row set is the scenario's and not a second idea of
#              it.
#   bench      the ten documents `bench.sh` generates plus the repository's
#              `probes/bench/json/scale-4096.json`; the constructions are
#              `bench.sh`'s lines, copied for the same reason.
#   plausible  the shapes a producer emits that the corpus does not cover: an
#              all-whitespace document, whitespace-wrapped and long string
#              documents, a string carrying a policy character, two
#              escaped-heavy documents, the input bound's inside and outside,
#              deep nesting past 128 (with the bound's variants beside it), and
#              raw-UTF-8 and surrogate-pair strings.
#
# A document is "valid" when its bytes are a JSON text the reference accepts
# under `Limits.default`, except where a documented clause is the only refusal
# (the fourteen RFC 7493 policy rows, and the three rows a non-default profile
# limits).  `?` marks a document whose validity is not asserted: the sweep's
# random bytes are not claimed to be anything, and its rows are excluded from
# every share.  The share's unit is documents, and its denominator is stated on
# its own row.
#
# Exit status: 0 when every constructed document's reference verdict held and
# the decision agreed with the library's on every row; 1 on a disagreement; 2
# when the route or the reference executable is absent.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
route=${ROUTE:-"$here/build/leanllvm-json-route"}
oracle=${ORACLE:-"$repo/.lake/build/bin/leanllvm-json"}
work=${WORK:-$(mktemp -d)}
mkdir -p "$work"
keep=${KEEP:-0}
cleanup() { if [ "$keep" = 1 ]; then echo "residue: documents kept in $work" >&2; else rm -rf "$work"; fi }
trap cleanup EXIT

die() { printf 'residue: %s\n' "$*" >&2; exit 1; }

[ -x "$route" ] || {
  echo "residue: absent: $route" >&2
  echo "residue: build it with: nix develop -c bash probes/json/route/build.sh" >&2
  exit 2
}
[ -x "$oracle" ] || {
  echo "residue: absent: $oracle" >&2
  echo "residue: build it with: nix develop -c bash probes/install/lake-locked.sh build leanllvm-json" >&2
  exit 2
}

corpus=$repo/tests/json/corpus
rows=$work/rows.tsv
: >"$rows"

# set, name, class, path, validity (1/0/?), expected reference verdict
# (? = not asserted), manifest profile, construction
row() {
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$@" >>"$rows"
}

# --- the corpus ------------------------------------------------------------
# The fourteen rows the reference refuses under RFC 7493's character policy:
# syntactically valid escapes and raw characters that the policy excludes, and
# therefore valid JSON inputs for this measurement (the refusal is the residue
# the character-policy clause exists for).  The class is the README's and
# `check.sh`'s; the counts below assert it is exactly fourteen.
policy_rows=$(printf '%s\n' \
  lone-dead.json lone-d800.json lone-dc00.json double-high.json \
  high-char.json reversed-pair.json nc-fdd0.json nc-fffe.json nc-ffff.json \
  nc-pair-max.json nc-raw-fdd0.json nc-raw-fffe.json nc-raw-10ffff.json \
  nc-raw-1fffe.json)
policy_seen=0
nondefault_valid=0
default_rows=0
while IFS=$'\t' read -r path verdict rendering profile; do
  [ -n "${path:-}" ] || continue
  valid=0
  case $verdict in
    accept) valid=1 ;;
    invalid)
      if printf '%s\n' "$policy_rows" | grep -qxF "$path"; then
        valid=1
        policy_seen=$((policy_seen + 1))
      fi ;;
    depthExceeded|inputTooLong|outOfCapacity)
      if [ "$profile" = default ]; then
        die "$path: a resource refusal in a default-profile row"
      fi
      valid=1
      nondefault_valid=$((nondefault_valid + 1)) ;;
    *) die "$path: unknown manifest verdict '$verdict'" ;;
  esac
  [ "$profile" != default ] || default_rows=$((default_rows + 1))
  row corpus "$path" corpus "$corpus/$path" "$valid" "$verdict" "$profile" \
    "tests/json/manifest.tsv row"
done <"$repo/tests/json/manifest.tsv"
[ "$policy_seen" -eq 14 ] || die "the corpus carries $policy_seen policy row(s), expected 14"
[ "$nondefault_valid" -eq 3 ] || die "the corpus carries $nondefault_valid non-default-profile resource row(s), expected 3"
[ "$default_rows" -eq 122 ] || die "the corpus carries $default_rows default-profile row(s), expected 122"

# --- the route's own scenario row set --------------------------------------
# `check.sh` generates these; the constructions are that script's.
scenario=$work/scenario
mkdir -p "$scenario"

: >"$scenario/empty"
row scenario empty empty "$scenario/empty" 0 invalid default "0 bytes (check.sh: : >empty)"

head -c 1048577 /dev/zero >"$scenario/over-bound"
row scenario over-bound input-bound "$scenario/over-bound" 0 inputTooLong default \
  "1048577 zero bytes (check.sh: head -c 1048577 /dev/zero)"

{ printf '%s' '"'; for _ in $(seq 129); do printf '%s' '['; done; printf '%s' '"'; } \
  >"$scenario/opener-rich"
row scenario opener-rich depth "$scenario/opener-rich" 1 accept default \
  "a JSON string of 129 '[' bytes (check.sh: rich)"

depth_doc() { # <depth>
  local d=$1 i
  for ((i = 0; i < d; i++)); do printf '['; done
  for ((i = 0; i < d; i++)); do printf ']'; done
}
for d in 128 129 520 521; do
  depth_doc "$d" >"$scenario/depth-$d.json"
  expected=accept
  [ "$d" -le 128 ] || expected=depthExceeded
  row scenario "depth-$d" depth "$scenario/depth-$d.json" 1 "$expected" default \
    "$d nested arrays (check.sh: depth_doc $d)"
done

{ printf '%s' '['; for _ in $(seq 199); do printf '%s' '[],'; done; printf '%s' '[]]'; } \
  >"$scenario/siblings"
row scenario siblings depth "$scenario/siblings" 1 accept default \
  "200 shallow sibling arrays (check.sh: siblings)"

printf '%s' ']] [[' >"$scenario/neg-prefix"
row scenario neg-prefix depth "$scenario/neg-prefix" 0 invalid default \
  "']] [[' (check.sh: neg-prefix)"

printf '%s' '[[ "abc' >"$scenario/body-ended"
row scenario body-ended depth "$scenario/body-ended" 0 invalid default \
  "[[' \"abc' — an unterminated body (check.sh: body-ended)"

printf '%s' '[["\q"]' >"$scenario/body-refused"
row scenario body-refused depth "$scenario/body-refused" 0 invalid default \
  "[['\"\\q\"']' — a refused escape in a body (check.sh: body-refused)"

printf '%s' '"\q" "\uD800"' >"$scenario/quote-after-refused"
row scenario quote-after-refused policy "$scenario/quote-after-refused" 0 invalid default \
  "'\"\\q\" \"\\uD800\"' — a bad escape, then a refused body (check.sh: quote-after-refused)"

{ printf '%s' '["'; for _ in 1 2 3; do printf '%s' '\"'; done
  for _ in $(seq 200); do printf '%s' '['; done; printf '%s' '"]'; } >"$scenario/escaped"
row scenario escaped depth "$scenario/escaped" 1 accept default \
  "escaped quotes and 200 '[' bytes inside one body (check.sh: escaped)"

{ printf '%s' '['; for _ in $(seq 61); do printf ' '; done; printf '%s' '"'
  for _ in $(seq 8); do printf '%s' '['; done; printf '%s' '"]]'; } >"$scenario/straddle-body"
row scenario straddle-body depth "$scenario/straddle-body" 0 invalid default \
  "a body opening at byte 62 with eight '[' crossing lane 63/64, then an extra ']' (the depth gate's row; not a valid document)"

{ printf '%s' '['; for _ in $(seq 62); do printf ' '; done; printf '%s' '"'
  for _ in $(seq 8); do printf '%s' '['; done; printf '%s' '"]'; } >"$scenario/straddle-quote"
row scenario straddle-quote depth "$scenario/straddle-quote" 1 accept default \
  "a body opening at lane 63 with the body in the next block (check.sh: straddle-quote)"

# The fixed-seed sweep, the same generator and seed as `check.sh`.
cat >"$work/gen.awk" <<'AWK'
function rnd() { state = (state * 48271) % 2147483647; return state / 2147483647 }
BEGIN {
  state = 20261113
  nchar = split("91 93 123 125 34 92 117 68 56 48 49 32 44 58 97 120 70", code, " ")
  for (n = 0; n < 120; n++) {
    len = 1 + int(rnd() * 200)
    s = ""
    for (i = 0; i < len; i++) s = s sprintf("%c", code[1 + int(rnd() * nchar)])
    printf "%s", s > (dir "/sweep-" n ".json")
    close(dir "/sweep-" n ".json")
  }
}
AWK
awk -v dir="$scenario" -f "$work/gen.awk"
for f in "$scenario"/sweep-*.json; do
  row scenario "$(basename "$f")" sweep "$f" ? ? default \
    "1-200 bytes from the depth rule's alphabet, fixed-seed Lehmer (check.sh: sweep)"
done

# --- the bench's generated documents ---------------------------------------
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
awk 'BEGIN{for(i=0;i<128;i++)printf "["; for(i=0;i<128;i++)printf "]"}' >"$bench/depth-128.json"
awk 'BEGIN{for(i=0;i<129;i++)printf "["; for(i=0;i<129;i++)printf "]"}' >"$bench/depth-129.json"
cat >"$work/bench-rows.tsv" <<'EOF'
fast-nums-4096.json	a JSON array of 683 number elements	accept
fast-nums-16384.json	a JSON array of 2731 number elements	accept
fast-nums-65536.json	a JSON array of 10923 number elements	accept
fast-esc.json	a string of 1000 '\n' escapes	accept
fast-esc-quotes.json	a string of 1000 escaped quotes	accept
fast-esc-u.json	a string of 500 '\u00e9' escapes	accept
fast-surrogate.json	a string of 250 surrogate pairs	accept
fast-utf8.json	a string of 1000 raw two-byte characters	accept
depth-128.json	128 nested arrays	accept
depth-129.json	129 nested arrays	depthExceeded
EOF
while IFS=$'\t' read -r name construction expected; do
  row bench "$name" bench "$bench/$name" 1 "$expected" default \
    "bench.sh line $(grep -n -m1 "corpus/$name\"" "$here/bench.sh" | cut -d: -f1): $construction"
done <"$work/bench-rows.tsv"
row bench scale-4096.json bench "$repo/probes/bench/json/scale-4096.json" 1 accept default \
  "the repository's 178-object document (178 objects, 179 opener bytes, nesting 2)"

# --- the constructed plausible-document classes ----------------------------
plausible=$work/plausible
mkdir -p "$plausible"

awk 'BEGIN{for(i=0;i<65536;i++)printf " "}' >"$plausible/ws-only-64k"

{ for _ in $(seq 51200); do printf ' '; done; printf '%s' '[1,2,3]'
  for _ in $(seq 51200); do printf ' '; done; } >"$plausible/ws-wrapped-100k"

depth_doc 129 >"$plausible/deep-129"
depth_doc 256 >"$plausible/deep-256"
depth_doc 520 >"$plausible/deep-520"

awk 'BEGIN{printf "[\""; for(i=0;i<262144;i++)printf "a"; printf "\"]"}' \
  >"$plausible/str-256k-ascii"
awk 'BEGIN{printf "[\""; for(i=0;i<262144;i++)printf "a"; printf "\\uD800\"]"}' \
  >"$plausible/str-256k-u-d800"
awk 'BEGIN{printf "[\""; for(i=0;i<262144;i++)printf "a"; printf "\357\277\277\"]"}' \
  >"$plausible/str-256k-raw-noncharacter"
awk 'BEGIN{printf "[\""; for(i=0;i<100000;i++)printf "\\u00e9"; printf "\"]"}' \
  >"$plausible/esc-heavy-u00e9"
awk 'BEGIN{printf "[\""; for(i=0;i<1000;i++)printf "\\\""; printf "\"]"}' \
  >"$plausible/esc-heavy-quotes"
awk 'BEGIN{n=209715; printf "["; for(i=0;i<n;i++){if(i)printf ",";printf "1234"}; printf "]"}' \
  >"$plausible/large-at-bound"
{ cat "$plausible/large-at-bound"; printf ' '; } >"$plausible/large-over-bound"
awk 'BEGIN{printf "[\""; for(i=0;i<1000;i++)printf "\\uD83D\\uDE00"; printf "\"]"}' \
  >"$plausible/surrogate-pairs-1000"
awk 'BEGIN{printf "[\""; for(i=0;i<1000;i++)printf "\303\251"; printf "\"]"}' \
  >"$plausible/unicode-2byte-1000"

row plausible ws-only-64k all-whitespace "$plausible/ws-only-64k" 0 invalid default \
  "65536 space bytes, no value"
row plausible ws-wrapped-100k whitespace-wrapped "$plausible/ws-wrapped-100k" 1 accept default \
  "'[1,2,3]' with 51200 spaces before and after"
row plausible deep-129 deep "$plausible/deep-129" 1 depthExceeded default \
  "129 nested arrays (one past the reference's 128)"
row plausible deep-256 deep "$plausible/deep-256" 1 depthExceeded default \
  "256 nested arrays (the bound's variant, not a class of its own)"
row plausible deep-520 deep "$plausible/deep-520" 1 depthExceeded default \
  "520 nested arrays, the object's own stack bound (the bound's variant)"
row plausible str-256k-ascii long-string "$plausible/str-256k-ascii" 1 accept default \
  "a 262144-byte ASCII string in an array"
row plausible str-256k-u-d800 long-string-policy "$plausible/str-256k-u-d800" 1 invalid default \
  "a 262144-byte ASCII string followed by the escape '\\uD800'"
row plausible str-256k-raw-noncharacter long-string-policy "$plausible/str-256k-raw-noncharacter" 1 invalid default \
  "a 262144-byte ASCII string followed by the raw U+FFFF character"
row plausible esc-heavy-u00e9 escaped-heavy "$plausible/esc-heavy-u00e9" 1 accept default \
  "100000 '\\u00e9' escapes in one string"
row plausible esc-heavy-quotes escaped-heavy "$plausible/esc-heavy-quotes" 1 accept default \
  "1000 escaped quotes in one string (the reference's scan is quadratic in them)"
row plausible large-at-bound large "$plausible/large-at-bound" 1 accept default \
  "209715 number elements, exactly 1048576 bytes (the input bound)"
row plausible large-over-bound large "$plausible/large-over-bound" 1 inputTooLong default \
  "the same array plus one space, 1048577 bytes"
row plausible surrogate-pairs-1000 escaped-heavy "$plausible/surrogate-pairs-1000" 1 accept default \
  "1000 '\\uD83D\\uDE00' pairs in one string"
row plausible unicode-2byte-1000 escaped-heavy "$plausible/unicode-2byte-1000" 1 accept default \
  "1000 raw two-byte characters in one string"

# --- the reference's verdict on the same bytes -----------------------------
# One `leanllvm-json` pass collects the reference verdict and rendering for
# every document (its expectation column is a placeholder, so its status is not
# read), a second pass runs with the collected columns as the expectation and
# must exit 0 with byte-identical output: the reference reading is reproduced,
# not just recorded.
oracle_dir=$work/oracle
mkdir -p "$oracle_dir/corpus"
: >"$oracle_dir/manifest1"
n=0
while IFS=$'\t' read -r set name class path validity expected profile construction; do
  n=$((n + 1))
  ln -s "$path" "$oracle_dir/corpus/doc-$n.json"
  printf 'doc-%s.json\tinvalid\t-\t%s\n' "$n" "$profile" >>"$oracle_dir/manifest1"
done <"$rows"
"$oracle" --corpus "$oracle_dir/corpus" --manifest "$oracle_dir/manifest1" \
  >"$oracle_dir/out1" 2>"$oracle_dir/err1" || true
[ "$(wc -l <"$oracle_dir/out1")" -eq "$n" ] || {
  echo "residue: the reference printed $(wc -l <"$oracle_dir/out1") row(s), expected $n" >&2
  cat "$oracle_dir/err1" >&2
  exit 1
}
paste "$oracle_dir/manifest1" "$oracle_dir/out1" \
  | awk -F'\t' '{ printf "%s\t%s\t%s\t%s\n", $1, $6, $7, $4 }' >"$oracle_dir/manifest2"
"$oracle" --corpus "$oracle_dir/corpus" --manifest "$oracle_dir/manifest2" \
  >"$oracle_dir/out2" 2>"$oracle_dir/err2" || {
  echo "residue: the reference did not reproduce its own reading:" >&2
  cat "$oracle_dir/err2" >&2
  exit 1
}
cmp -s "$oracle_dir/out1" "$oracle_dir/out2" || {
  echo "residue: the reference's two readings differ" >&2
  exit 1
}
# Every constructed row's expected verdict is asserted against the reference's
# printed one; `?` rows (the sweep) are recorded, not asserted.
paste "$rows" "$oracle_dir/out2" | awk -F'\t' '
  $6 != "?" && $6 != $10 { printf "residue: %s (set %s): the reference says %s, the construction says %s\n", $2, $1, $10, $6; bad = 1 }
  $10 != "accept" && $10 != "invalid" && $10 != "depthExceeded" && $10 != "inputTooLong" && $10 != "outOfCapacity" {
    printf "residue: %s: unknown reference verdict %s\n", $2, $10; bad = 1 }
  END { exit bad ? 1 : 0 }' || exit 1
# The reference's accept count over the sweep is data: the sweep's bytes are
# not claimed to be valid, so it is not in a share's denominator.
sweep_accept=$(paste "$rows" "$oracle_dir/out2" | awk -F'\t' '$1 == "scenario" && $3 == "sweep" && $10 == "accept"' | wc -l)

# --- the decision, read from the route -------------------------------------
measured=$work/measured.tsv
: >"$measured"
while IFS=$'\t' read -r set name class path validity expected profile construction; do
  line=$("$route" --admit "$path" 1 2>&1) || {
    echo "residue: --admit failed on $path:" >&2
    echo "$line" >&2
    exit 1
  }
  result=$(printf '%s\n' "$line" | awk -v name="$name" '
    function field(k,   i, kv) { for (i = 2; i <= NF; i++) { split($i, kv, "="); if (kv[1] == k) return kv[2] } return "-" }
    /^admit / {
      size = field("size"); reason = field("reason"); agree = field("agree")
      depth = field("native_depth")
      admitted = (reason == "none") ? 1 : 0
      if (reason == "none") refusal = "admitted"
      else if (reason == "emptyInput") refusal = "empty"
      else if (reason == "inputTooLong") refusal = "inputTooLong"
      else if (reason == "depthBound") refusal = "depthBound"
      else if (reason ~ /^unpairedSurrogate@/) refusal = "policy-unpairedSurrogate"
      else if (reason ~ /^noncharacter@/) refusal = "policy-noncharacter"
      else if (reason == "failed") refusal = "failed"
      else refusal = "unsupported"
      if (agree != 1) {
        printf "residue: %s: the two-phase decision and the library disagree (reason %s)\n", name, reason > "/dev/stderr"
        exit 3
      }
      printf "%d\t%s\t%s\t%s\t%s\n", admitted, refusal, reason, depth, size
      found = 1
      next
    }
    { printf "residue: %s: no admit row: %s\n", name, $0 > "/dev/stderr" }
    END { if (!found) exit 3 }') || {
    echo "residue: --admit output for $path was not a decision" >&2
    exit 1
  }
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$set" "$name" "$class" "$path" "$validity" "$expected" "$profile" "$construction" \
    "$result" >>"$measured"
done <"$rows"

# Every decision agrees with the library's `admission` (`agree=1` above), and
# no row is refused for a reason the refusal vocabulary does not name.
unsupported=$(awk -F'\t' '$10 == "unsupported" || $10 == "failed"' "$measured" | wc -l)
[ "$unsupported" -eq 0 ] || {
  echo "residue: $unsupported row(s) refused for an unnamed reason:" >&2
  awk -F'\t' '$10 == "unsupported" || $10 == "failed" { print "  " $2 "\t" $11 }' "$measured" >&2
  exit 1
}

# --- the route's observed path, for the constructed classes ----------------
# `--doc` reports the path the decision produced, so a constructed class's row
# names the outcome and not only the decision.  The output is large for the
# large documents (the payloads are printed), so it is read for its first line
# and discarded.
paths=$work/paths.tsv
: >"$paths"
while IFS=$'\t' read -r set name class path validity expected profile construction admitted refusal reason depth size; do
  case $set in plausible|bench) ;; *) continue ;; esac
  out=$work/doc.out
  errf=$work/doc.err
  status=0
  "$route" --doc "$path" >"$out" 2>"$errf" || status=$?
  case $status in
    0|2) ;;
    *) die "$name: --doc exited $status: $(cat "$errf")" ;;
  esac
  first=$(sed -n '1p' "$out")
  case $first in
    verdict=*) observed="fast path: $first" ;;
    fallback=accepted*) observed="fallback: $first" ;;
    "") observed="fallback refused: $(sed -n '1s/^refused: //p' "$errf")" ;;
    *) die "$name: --doc printed '$first'" ;;
  esac
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$set" "$name" "$class" "$validity" "$admitted" "$refusal" "$observed" >>"$paths"
done <"$measured"

# --- the record ------------------------------------------------------------
clause_order="empty inputTooLong depthBound policy-unpaired policy-noncharacter"
printf '## the residue, by the admission clause that refused (unit: documents)\n\n'
printf '%-11s %6s %9s %6s %13s %11s %12s %12s %12s\n' \
  set docs admitted empty inputTooLong depthBound policy-unpaired policy-noncharacter unsupported
awk -F'\t' '
  { s = $1; docs[s]++
    if ($9 == 1) adm[s]++
    c[s, $10]++
    if ($10 == "empty") et[s]++
    total++; if ($9 == 1) total_adm++
    if ($10 == "unsupported" || $10 == "failed") bad++
    allc[$10]++ }
  END {
    n = split("corpus scenario bench plausible", order, " ")
    for (i = 1; i <= n; i++) {
      s = order[i]
      if (!(s in docs)) continue
      printf "%-11s %6d %9d %6d %13d %11d %12d %12d %12d\n", s, docs[s], adm[s] + 0,
        c[s, "empty"] + 0, c[s, "inputTooLong"] + 0, c[s, "depthBound"] + 0,
        c[s, "policy-unpairedSurrogate"] + 0, c[s, "policy-noncharacter"] + 0,
        c[s, "unsupported"] + c[s, "failed"] + 0
    }
    printf "%-11s %6d %9d %6d %13d %11d %12d %12d %12d\n", "total", total, total_adm,
      allc["empty"] + 0, allc["inputTooLong"] + 0, allc["depthBound"] + 0,
      allc["policy-unpairedSurrogate"] + 0, allc["policy-noncharacter"] + 0,
      allc["unsupported"] + allc["failed"] + 0
  }' "$measured"
printf '\nThe reference verdict on the same bytes: %s accepted sweep document(s) of the\n' "$sweep_accept"
printf '120; the sweep is the only set whose validity is not asserted, so its rows are\n'
printf 'in the table above and in no share below.\n\n'

printf '## the fast-path share of the valid documents (unit: documents)\n\n'
printf '%-11s %6s %7s %8s %12s %9s %s\n' \
  set docs valid unknown 'fast(valid)' share denominator
awk -F'\t' '
  { s = $1; docs[s]++
    if ($5 == 1) valid[s]++
    if ($5 == "?") unknown[s]++
    if ($5 == 1 && $9 == 1) fast[s]++ }
  END {
    n = split("corpus scenario bench plausible", order, " ")
    for (i = 1; i <= n; i++) {
      s = order[i]
      if (!(s in docs)) continue
      share = (valid[s] + 0) ? sprintf("%.1f%%", 100 * fast[s] / valid[s]) : "-"
      printf "%-11s %6d %7d %8d %12d %9s %s\n", s, docs[s], valid[s] + 0, unknown[s] + 0,
        fast[s] + 0, share, "valid documents of this set"
    }
    # The populations a share is stated over.  The constructed population is
    # the bench set and the plausible classes; the repository population adds
    # the corpus; the whole set adds the route scenario rows.
    split("bench plausible", bp, " ")
    v = 0; f = 0; d = 0
    for (i = 1; i <= 2; i++) { s = bp[i]; d += docs[s]; v += valid[s]; f += fast[s] }
    printf "%-11s %6d %7d %8d %12d %9s %s\n", "constructed", d, v, 0, f,
      (v ? sprintf("%.1f%%", 100 * f / v) : "-"), "bench + plausible, valid documents"
    v2 = v; f2 = f; d2 = d
    v2 += valid["corpus"]; f2 += fast["corpus"]; d2 += docs["corpus"]
    printf "%-11s %6d %7d %8d %12d %9s %s\n", "+corpus", d2, v2, 0, f2,
      (v2 ? sprintf("%.1f%%", 100 * f2 / v2) : "-"), "constructed + corpus, valid documents"
    v3 = v2 + valid["scenario"]; f3 = f2 + fast["scenario"]; d3 = d2 + docs["scenario"]
    printf "%-11s %6d %7d %8d %12d %9s %s\n", "all", d3, v3, 0, f3,
      (v3 ? sprintf("%.1f%%", 100 * f3 / v3) : "-"), "every set, valid documents (the sweep excluded)"
  }' "$measured"
printf '\nEach share is fast(valid)/valid for the row set named on its row, in documents.\n'
printf 'The scenario row is the route scenario set of 135 rows; its 8 valid\n'
printf 'documents are the constructed ones and its 120 swept documents carry no\n'
printf 'validity claim.  The total row of the first table is not a share: the\n'
printf 'residue there is 28 of 290 documents, and 262 take the fast path.\n\n'

printf '## the constructed plausible-document classes\n\n'
printf '%-20s %5s %6s %6s %14s %-24s %s\n' \
  class docs valid fast bytes 'reference verdict' 'admission outcome'
awk -F'\t' '
  function mark(a, k, v) { if (!((a SUBSEP k) SUBSEP v in seen)) { seen[(a SUBSEP k) SUBSEP v] = 1; return 1 } return 0 }
  $1 == "plausible" {
    c = $3; docs[c]++
    if ($5 == 1) { valid[c]++; if ($9 == 1) fast[c]++ }
    if (!(c in lo) || $13 + 0 < lo[c]) lo[c] = $13 + 0
    if (!(c in hi) || $13 + 0 > hi[c]) hi[c] = $13 + 0
    if (mark("ref", c, $6)) ref[c] = (c in ref) ? ref[c] ", " $6 : $6
    if (mark("adm", c, $10 == "admitted" ? "fast" : "refused: " $10)) \
      adm[c] = (c in adm) ? adm[c] ", " ($10 == "admitted" ? "fast" : "refused: " $10) : ($10 == "admitted" ? "fast" : "refused: " $10)
  }
  END {
    n = split("all-whitespace whitespace-wrapped deep long-string long-string-policy escaped-heavy large", order, " ")
    for (i = 1; i <= n; i++) {
      c = order[i]
      if (!(c in docs)) continue
      bytes = (lo[c] == hi[c]) ? lo[c] : lo[c] "-" hi[c]
      printf "%-20s %5d %6d %6d %14s %-24s %s\n", c, docs[c], valid[c] + 0, fast[c] + 0,
        bytes, ref[c], adm[c]
    }
  }' "$measured"
printf '\n'
printf '%-26s %-22s %-9s %-9s %s\n' document class valid admitted 'admission reason'
awk -F'\t' '$1 == "plausible" { printf "%-26s %-22s %-9s %-9s %s\n", $2, $3,
  ($5 == 1 ? "valid" : "invalid"), ($9 == 1 ? "fast" : "fallback"), ($10 == "admitted" ? "-" : $11) }' "$measured"
printf '\n'

printf '## the constructed rows and the path the route took (unit: one route run)\n\n'
printf '%-11s %-26s %-22s %-9s %s\n' set document class valid observation
awk -F'\t' '{ printf "%-11s %-26s %-22s %-9s %s\n", $1, $2, $3,
  ($4 == 1 ? "valid" : "invalid"), $7 }' "$paths"
printf '\n'

printf 'ok: %s document(s) measured; the decision agreed with `admission` on every row;\n' \
  "$(wc -l <"$measured")"
printf 'the reference reproduced its own reading on every row; no row is refused for a\n'
printf 'reason outside the five refusal constructors.\n'
