#!/usr/bin/env bash
# The native parse core's per-stage cost in the shape the route calls it.
#
#   nix develop -c bash probes/json/core-shape/shape.sh
#   nix develop -c bash probes/json/core-shape/shape.sh --corpus <manifest> --rounds 21 --core 3
#   nix develop -c bash probes/json/core-shape/shape.sh --corpus-out <dir> --rounds 31 --core 3
#
# With no --corpus, the nine documents `probes/json/route/bench.sh` times are
# generated from the same commands (the three scalar arrays, the five escape
# documents, and `probes/bench/json/scale-4096.json`), into the work directory
# or into --corpus-out when that is given; the manifest it writes is the one
# `kernel/json/bench/profile-pipeline.sh --corpus` reads, so the two instruments
# time the same bytes with the same digests.
#
# What it measures, from `shape.cc`'s header: the whole pipeline with a
# 64-byte-aligned window and reused buffers (`site`), with the route's
# three-byte window offset (`off3`), with fresh per-call buffers in the route's
# staging shape (`fresh3`), the same with 64-byte-aligned buffers (`fresh+64`)
# and with an aligned window (`fresh0`), simdjson 4.6.11 On-Demand over the same
# document (`reference`) and its padded-copy staging (`pad`), and the six
# stages separately in the `site` shape.
#
# Every variant is checked before the clock: it must return the same nk, nxp,
# ndst, nev, err, event bytes and arena bytes as `site`.  A variant that parses
# differently is a setup fault, not a timing row.
#
# Exit status: 0 when every document is measured and every pre-clock check
# passed; 3 on a setup fault (absent document, manifest digest mismatch,
# reference or tool, a variant disagreement).
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
kernel=$repo/kernel/json
cc=clang
cc_cxx=g++
cflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
        -falign-functions=64 -falign-functions=4096)
reference_version=4.6.11
simdjson_lib=${SIMDJSON_LIB:-}
simdjson_dev=${SIMDJSON_DEV:-}
corpus=""
corpus_out=""
rounds=21
cores=()

usage() {
  awk 'NR > 1 && /^set -/ { exit } NR > 1 { print }' "$0" | sed 's/^# \{0,1\}//'
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --corpus) shift; corpus=${1:-}; [ -n "$corpus" ] || { printf 'shape: --corpus needs a value\n' >&2; exit 3; } ;;
    --corpus=*) corpus=${1#--corpus=} ;;
    --rounds) shift; rounds=${1:-}; [ -n "$rounds" ] || { printf 'shape: --rounds needs a value\n' >&2; exit 3; } ;;
    --rounds=*) rounds=${1#--rounds=} ;;
    --core) shift; cores+=("${1:-}"); [ -n "${1:-}" ] || { printf 'shape: --core needs a value\n' >&2; exit 3; } ;;
    --core=*) cores+=("${1#--core=}") ;;
    --corpus-out) shift; corpus_out=${1:-}; [ -n "$corpus_out" ] || { printf 'shape: --corpus-out needs a value\n' >&2; exit 3; } ;;
    --corpus-out=*) corpus_out=${1#--corpus-out=} ;;
    -h|--help) usage; exit 0 ;;
    *) printf 'shape: unknown argument %s\n' "$1" >&2; exit 3 ;;
  esac
  shift
done

for tool in "$cc" "$cc_cxx" sha256sum; do
  command -v "$tool" >/dev/null 2>&1 || { printf 'SETUP: no %s on PATH\n' "$tool" >&2; exit 3; }
done
if [ "${#cores[@]}" -gt 0 ]; then
  command -v taskset >/dev/null 2>&1 || { printf 'SETUP: --core needs taskset on PATH\n' >&2; exit 3; }
fi

if [ -z "$simdjson_lib" ]; then
  simdjson_lib=$(ls -d /nix/store/*-simdjson-"$reference_version" 2>/dev/null | head -n 1)
fi
if [ -z "$simdjson_dev" ]; then
  simdjson_dev=$(ls -d /nix/store/*-simdjson-"$reference_version"-dev 2>/dev/null | head -n 1)
fi
if [ -z "$simdjson_lib" ] || [ ! -f "$simdjson_lib/lib/libsimdjson.so" ]; then
  printf 'SETUP: absent: the pinned reference library simdjson %s\n' "$reference_version" >&2
  exit 3
fi
if [ -z "$simdjson_dev" ] || [ ! -f "$simdjson_dev/include/simdjson.h" ]; then
  printf 'SETUP: absent: the pinned reference headers simdjson %s\n' "$reference_version" >&2
  exit 3
fi
ref_version=$(sed -n 's/^#define SIMDJSON_VERSION "\(.*\)"/\1/p' \
                "$simdjson_dev/include/simdjson.h" | head -n 1)
if [ "$ref_version" != "$reference_version" ]; then
  printf 'SETUP: the reference header is simdjson %s, not the pinned %s\n' \
    "$ref_version" "$reference_version" >&2
  exit 3
fi

mkdir -p "$repo/.lake" || { printf 'SETUP: cannot create %s/.lake\n' "$repo" >&2; exit 3; }
work=$(mktemp -d "$repo/.lake/tmp-core-shape.XXXXXX" 2>/dev/null) || {
  printf 'SETUP: cannot create a work directory under %s/.lake\n' "$repo" >&2
  exit 3
}
trap 'rm -rf "$work"' EXIT

# The default corpus is the one `probes/json/route/bench.sh` times, generated
# here from the same commands so the default run needs no input file to exist
# beforehand.  A supplied manifest is used as it stands (digest-checked).
if [ -z "$corpus" ]; then
  if [ -n "$corpus_out" ]; then
    mkdir -p "$corpus_out/corpus" || exit 3
    c=$corpus_out/corpus
  else
    mkdir -p "$work/corpus"
    c="$work/corpus"
  fi
  awk 'BEGIN{n=683;   printf "["; for(i=0;i<n;i++){if(i)printf ",";printf "12345"}; printf "]"}' >"$c/fast-nums-4096.json"
  awk 'BEGIN{n=2731;  printf "["; for(i=0;i<n;i++){if(i)printf ",";printf "12345"}; printf "]"}' >"$c/fast-nums-16384.json"
  awk 'BEGIN{n=10923; printf "["; for(i=0;i<n;i++){if(i)printf ",";printf "12345"}; printf "]"}' >"$c/fast-nums-65536.json"
  awk 'BEGIN{printf "["; printf "\""; for(i=0;i<1000;i++)printf "\\n"; printf "\"]"}' >"$c/fast-esc.json"
  awk 'BEGIN{printf "["; printf "\""; for(i=0;i<1000;i++)printf "\\\""; printf "\"]"}' >"$c/fast-esc-quotes.json"
  awk 'BEGIN{printf "["; printf "\""; for(i=0;i<500;i++)printf "\\u00e9"; printf "\"]"}' >"$c/fast-esc-u.json"
  awk 'BEGIN{printf "["; printf "\""; for(i=0;i<250;i++)printf "\\uD83D\\uDE00"; printf "\"]"}' >"$c/fast-surrogate.json"
  awk 'BEGIN{printf "["; printf "\""; for(i=0;i<1000;i++)printf "\303\251"; printf "\"]"}' >"$c/fast-utf8.json"
  cp "$repo/probes/bench/json/scale-4096.json" "$c/scale-4096.json"
  if [ -n "$corpus_out" ]; then corpus=$corpus_out/corpus.tsv; else corpus=$work/corpus.tsv; fi
  printf 'name\tarm_E\tarm_P\trecord_E\trecord_P\tsha256\tpath\n' >"$corpus"
  for f in "$c"/*.json; do
    printf '%s\t2\t2\t0\t0\t%s\t%s\n' "$(basename "$f" .json)" \
      "$(sha256sum "$f" | cut -d' ' -f1)" "$f" >>"$corpus"
  done
fi
[ -f "$corpus" ] || { printf 'SETUP: absent: corpus manifest %s\n' "$corpus" >&2; exit 3; }

build() { # <output> <args...>
  local out=$1
  shift
  if ! "$cc" "$@" -o "$out" 2>"$work/build.err"; then
    printf 'SETUP: %s did not build\n' "$out" >&2
    awk 'NR <= 40' "$work/build.err" >&2
    exit 3
  fi
}

mkdir -p "$work/native" || exit 3
for u in s1_block entry utf8 escape stage2 pipeline; do
  build "$work/native/$u.o" "${cflags[@]}" -I "$kernel" -c "$kernel/$u.c"
done

if ! "$cc_cxx" -O3 -march=x86-64-v3 -std=c++17 -I "$kernel" \
      -I "$simdjson_dev/include" "$here/shape.cc" \
      "$work/native/pipeline.o" "$work/native/s1_block.o" "$work/native/entry.o" \
      "$work/native/utf8.o" "$work/native/escape.o" "$work/native/stage2.o" \
      -L "$simdjson_lib/lib" -lsimdjson -Wl,-rpath,"$simdjson_lib/lib" \
      -o "$work/shape" 2>"$work/build.err"; then
  printf 'SETUP: the harness did not build\n' >&2
  awk 'NR <= 40' "$work/build.err" >&2
  exit 3
fi

printf 'binary        %s\n' "$work/shape"
printf 'binary sha256 %s\n' "$(sha256sum "$work/shape" | cut -d' ' -f1)"
for u in pipeline s1_block entry utf8 escape stage2; do
  printf 'obj sha256 %-9s %s\n' "$u.o" \
    "$(sha256sum "$work/native/$u.o" | cut -d' ' -f1)"
done
printf 'compiler      %s %s, %s %s\n' "$cc" "$($cc -dumpversion)" \
  "$cc_cxx" "$($cc_cxx -dumpversion)"
printf 'compiler-line %s %s\n' "$cc" "${cflags[*]}"
printf 'harness-line  %s -O3 -march=x86-64-v3 -std=c++17\n' "$cc_cxx"
printf 'reference     simdjson %s (%s/lib/libsimdjson.so)\n' \
  "$reference_version" "$simdjson_lib"
printf 'corpus        %s\n' "$corpus"

if [ "${#cores[@]}" -eq 0 ]; then
  printf 'note          no --core: the rows are not pinned\n'
  "$work/shape" --corpus "$corpus" --rounds "$rounds"
  exit $?
fi

status=0
for c in "${cores[@]}"; do
  printf '\n== pinned to CPU %s\n' "$c"
  if ! taskset -c "$c" "$work/shape" --corpus "$corpus" --rounds "$rounds" --core "$c"; then
    status=3
  fi
done
exit "$status"
