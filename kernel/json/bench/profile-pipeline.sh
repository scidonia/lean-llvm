#!/usr/bin/env bash
# Arm D: the assembled pipeline's per-stage cost profile beside the reference.
#
#   nix develop -c bash kernel/json/bench/profile-pipeline.sh
#   nix develop -c bash kernel/json/bench/profile-pipeline.sh --rounds 21 --core 2
#   nix develop -c bash kernel/json/bench/profile-pipeline.sh --corpus <manifest>
#
# What it measures, from `profile-pipeline.cc`'s header:
#
#   masks, entry, escape, utf8   the separate classification/entry pass
#   stage2                       the walk over the precomputed entry stream
#   pipeline                     the whole staged body (`leanllvm_json_pipeline`)
#   reference                    simdjson On-Demand, the reference arm's act
#   numbers, num-measured        the same number tokens through the extracted
#                                `num_fast_el1` and through the measured
#                                `measured/numf_el1.h`, with both outputs checked
#   refnum                       the reference walk minus the same walk with
#                                `get_double` removed
#   ratio                        the paired pipeline/reference ratio, the row
#                                `paired.sh --unit reference` reports
#
# Each round times each act once per document in rotated order; the report is
# the median of each act.  The second table is the decomposition
# `margin = stage1 - (reference - walk) - overlap`, computed from those medians.
#
# One binary holds the six staged objects the reference arm links (the measured
# clang line, 4 KiB function alignment), the driver at the reference build's
# own g++ line, and the pinned simdjson.  The timed stage2 is the unmodified
# object; the counted copy (stage2.c with its wrapper renamed and one number
# loop and the tier accessors appended) is used only for the census and the
# extracted number loop, and the script checks that the copy is stage2.c plus
# exactly that appended block.
#
# Before the clock, for every document: the entry stream is checked byte-
# identical against `leanllvm_json_pipeline`'s own output, both arms accept,
# the extracted and measured number loops return the same values, and the
# measured third tier is unreached.  The corpus digests are checked first, so
# a row names the artefact the record names.
#
# Cost to run: about five seconds to build; 21 rounds over the seven documents
# is about two seconds on the measurement host, five when the host is busy.
#
# Exit status: 0 when every document is measured and every pre-clock check
# passed; 3 on a setup fault (absent corpus row, reference or tool, a digest or
# version mismatch, a stream or number disagreement).  A ratio above 1.0 is a
# result, not a failure -- this instrument has no pass/fail claim.
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
measured=$repo/kernel/json/measured
kernel_dir=$repo/kernel/json
cc=clang
cc_cxx=g++
cflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
        -falign-functions=64 -falign-functions=4096)

reference_version=4.6.11
simdjson_lib=${SIMDJSON_LIB:-}
simdjson_dev=${SIMDJSON_DEV:-}

corpus=$here/reference-corpus.tsv
rounds=""
cores=()
build_id="profile/$(cd "$repo" && git rev-parse --short=12 HEAD 2>/dev/null || printf unstated)"

usage() {
  awk 'NR > 1 && /^set -/ { exit } NR > 1 { print }' "$0" | sed 's/^# \{0,1\}//'
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --corpus) shift; corpus=${1:-}; [ -n "$corpus" ] || { printf 'profile: --corpus needs a value\n' >&2; exit 3; } ;;
    --corpus=*) corpus=${1#--corpus=} ;;
    --rounds) shift; rounds=${1:-}; [ -n "$rounds" ] || { printf 'profile: --rounds needs a value\n' >&2; exit 3; } ;;
    --rounds=*) rounds=${1#--rounds=} ;;
    --core) shift; cores+=("${1:-}"); [ -n "${1:-}" ] || { printf 'profile: --core needs a value\n' >&2; exit 3; } ;;
    --core=*) cores+=("${1#--core=}") ;;
    -h|--help) usage; exit 0 ;;
    *) printf 'profile: unknown argument %s\n' "$1" >&2; exit 3 ;;
  esac
  shift
done
[ -n "$rounds" ] || rounds=21

for tool in "$cc" "$cc_cxx" sha256sum; do
  command -v "$tool" >/dev/null 2>&1 || { printf 'SETUP: no %s on PATH\n' "$tool" >&2; exit 3; }
done
if [ "${#cores[@]}" -gt 0 ]; then
  command -v taskset >/dev/null 2>&1 || { printf 'SETUP: --core needs taskset on PATH\n' >&2; exit 3; }
fi

# The pinned reference: the release the record's ratios were taken against.
# The version is checked against the header here and against the header's enum
# again at run time, so a row is never compared against an unnamed reference.
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
ref_major=$(sed -n 's/.*SIMDJSON_VERSION_MAJOR = \([0-9][0-9]*\).*/\1/p' \
              "$simdjson_dev/include/simdjson.h" | head -n 1)
ref_minor=$(sed -n 's/.*SIMDJSON_VERSION_MINOR = \([0-9][0-9]*\).*/\1/p' \
              "$simdjson_dev/include/simdjson.h" | head -n 1)
ref_revision=$(sed -n 's/.*SIMDJSON_VERSION_REVISION = \([0-9][0-9]*\).*/\1/p' \
                 "$simdjson_dev/include/simdjson.h" | head -n 1)
if [ "$ref_major.$ref_minor.$ref_revision" != "$reference_version" ]; then
  printf 'SETUP: the reference header is simdjson %s.%s.%s, not the pinned %s\n' \
    "$ref_major" "$ref_minor" "$ref_revision" "$reference_version" >&2
  exit 3
fi

[ -f "$corpus" ] || { printf 'SETUP: absent: corpus manifest %s\n' "$corpus" >&2; exit 3; }
[ -f "$here/profile-pipeline.cc" ] || { printf 'SETUP: absent: profile-pipeline.cc\n' >&2; exit 3; }
[ -f "$here/profile-num-oracle.c" ] || { printf 'SETUP: absent: profile-num-oracle.c\n' >&2; exit 3; }
[ -f "$here/profile-num-slow.c" ] || { printf 'SETUP: absent: profile-num-slow.c\n' >&2; exit 3; }
[ -f "$measured/numf_el1.h" ] || { printf 'SETUP: absent: measured/numf_el1.h\n' >&2; exit 3; }

# The manifest names the document, its arm per core class, the record's ratio
# and the bytes' digest.  A missing or substituted document is refused before
# anything is measured.
while IFS=$'\t' read -r name arm_e arm_p rec_e rec_p sha path; do
  case "$name" in ''|'#'*|name) continue ;; esac
  [ -n "$path" ] && [ -n "$sha" ] || {
    printf 'SETUP: corpus row %s is not seven columns\n' "$name" >&2
    exit 3
  }
  [ -f "$path" ] || {
    printf 'SETUP: absent: document %s (%s, sha256 %s)\n' "$name" "$path" "$sha" >&2
    exit 3
  }
  got=$(sha256sum "$path" | cut -d' ' -f1)
  [ "$got" = "$sha" ] || {
    printf 'SETUP: %s: digest %s, the manifest names %s\n' "$name" "$got" "$sha" >&2
    exit 3
  }
done < "$corpus"

mkdir -p "$repo/.lake" || { printf 'SETUP: cannot create %s/.lake\n' "$repo" >&2; exit 3; }
work=$(mktemp -d "$repo/.lake/tmp-profile-bench.XXXXXX" 2>/dev/null) || {
  printf 'SETUP: cannot create a work directory under %s/.lake\n' "$repo" >&2
  exit 3
}
trap 'rm -rf "$work"' EXIT

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
for u in s1_block entry utf8 escape stage2; do
  build "$work/native/$u.o" "${cflags[@]}" -I "$kernel_dir" -c "$kernel_dir/$u.c"
done
build "$work/native/pipeline.o" "${cflags[@]}" -I "$kernel_dir" -c "$kernel_dir/pipeline.c"

# The counted copy: stage2.c with its wrapper renamed, then one appended block
# (the extracted number loop and the tier accessors).  The timed pipeline uses
# the unmodified object above; this copy is only the census and the extracted
# number loop, and the diff below is the statement that the appended block is
# all that separates it from the unit.
counted=$work/stage2-counted.c
cp "$kernel_dir/stage2.c" "$counted" || exit 3
cat >> "$counted" <<'EOF'

/* ---- appended by profile-pipeline.sh; the walk above is unchanged -------- */
typedef struct { uint32_t pos, len; } profile_tok;

uint64_t profile_num_loop_extracted(const uint8_t *doc, const profile_tok *t,
                                    uint64_t nt, volatile double *sink) {
    double acc = 0.0;
    uint64_t ok = 0, h = 0;
    size_t err = 0;
    for (uint64_t j = 0; j < nt; j++) {
        double d = 0.0;
        if (num_fast_el1(doc + t[j].pos, t[j].len, &d, &err)) {
            uint64_t u;
            memcpy(&u, &d, 8);
            h = (h ^ u) * 0x9E3779B97F4A7C15ULL;
            acc += d;
            ok++;
        }
    }
    *sink = acc;
    return ok ^ h;
}
uint64_t profile_tier_el(void) { return g_nume1_el; }
uint64_t profile_tier_slow(void) { return g_nume1_slow; }
uint64_t profile_tier_window(void) { return g_el_window; }
uint64_t profile_tier_undec(void) { return g_el_undec; }
EOF
head -n "$(wc -l < "$kernel_dir/stage2.c")" "$counted" > "$work/stage2-prefix.c" || exit 3
if ! cmp -s "$work/stage2-prefix.c" "$kernel_dir/stage2.c"; then
  printf 'SETUP: the counted copy is not stage2.c plus the appended block\n' >&2
  exit 3
fi
build "$work/native/stage2-counted.o" "${cflags[@]}" \
  -Dleanllvm_json_stage2=profile_stage2_extracted \
  -I "$kernel_dir" -c "$counted"

build "$work/native/num-oracle.o" "${cflags[@]}" -I "$measured" \
  -c "$here/profile-num-oracle.c"
build "$work/native/num-slow.o" "${cflags[@]}" -c "$here/profile-num-slow.c"

build_cxx() { # <output> <args...>
  local out=$1
  shift
  if ! "$cc_cxx" "$@" -o "$out" 2>"$work/build.err"; then
    printf 'SETUP: %s did not build\n' "$out" >&2
    awk 'NR <= 40' "$work/build.err" >&2
    exit 3
  fi
}
build_cxx "$work/profile" -O3 -march=x86-64-v3 -std=c++17 \
  -I "$kernel_dir" -I "$simdjson_dev/include" "$here/profile-pipeline.cc" \
  "$work/native/pipeline.o" "$work/native/s1_block.o" "$work/native/entry.o" \
  "$work/native/utf8.o" "$work/native/escape.o" "$work/native/stage2.o" \
  "$work/native/stage2-counted.o" "$work/native/num-oracle.o" \
  "$work/native/num-slow.o" \
  -L "$simdjson_lib/lib" -lsimdjson -Wl,-rpath,"$simdjson_lib/lib"

cc_version=$("$cc" -dumpversion 2>/dev/null || printf unknown)
cc_target=$("$cc" -dumpmachine 2>/dev/null || printf unknown)
cxx_version=$("$cc_cxx" -dumpversion 2>/dev/null || printf unknown)
printf 'binary        %s\n' "$work/profile"
printf 'binary sha256 %s\n' "$(sha256sum "$work/profile" | cut -d' ' -f1)"
for u in pipeline s1_block entry utf8 escape stage2 stage2-counted num-oracle num-slow; do
  printf 'obj sha256 %-13s %s\n' "$u.o" \
    "$(sha256sum "$work/native/$u.o" | cut -d' ' -f1)"
done
printf 'compiler      %s %s, %s %s\n' "$cc" "$cc_version" "$cc_cxx" "$cxx_version"
printf 'compiler-line %s %s\n' "$cc" "${cflags[*]}"
printf 'harness-line  %s -O3 -march=x86-64-v3 -std=c++17\n' "$cc_cxx"
printf 'reference     simdjson %s (%s/lib/libsimdjson.so)\n' \
  "$reference_version" "$simdjson_lib"
printf 'corpus        %s\n' "$corpus"
printf 'target        %s\n' "$cc_target"

status=0
if [ "${#cores[@]}" -eq 0 ]; then
  printf '\nunpinned run\n'
  "$work/profile" --corpus "$corpus" --rounds "$rounds" --build "$build_id" || status=$?
else
  for core in "${cores[@]}"; do
    printf '\n== pinned to CPU %s\n' "$core"
    taskset -c "$core" "$work/profile" --corpus "$corpus" --rounds "$rounds" \
      --build "$build_id" || status=$?
  done
fi

if [ "$status" -eq 0 ]; then
  printf '\nthe rows above name their core class, their reference version and their\n'
  printf 'corpus; every pre-clock check passed (entry stream identity, both arms\n'
  printf 'accept, extracted/measured number identity, measured third tier unreached),\n'
  printf 'and the decomposition closes from the printed medians.\n'
fi
exit "$status"
