#!/usr/bin/env bash
# The JSON route's per-stage timings, the object's -O2/-O3 pair, the fallback's
# price, and the reference arm, over a generated corpus.
#
#   nix develop -c bash probes/json/route/bench.sh [reps]
#
# Every row names its unit: all times are nanoseconds, `ns` in the field name.
# A row's construction is the field set it carries (`stage` rows carry one field
# per stage and the `reps` their medians were taken over); a ratio row carries
# its unit and its construction on the row itself.
#
# ## What is measured, and how
#
# * `stage` rows come from `leanllvm-json-route --stages <file> <reps>`: one
#   process, `reps` repetitions, the document re-read inside every repetition so
#   no stage's input is shared between repetitions, and each field is that
#   stage's median.  The stages are admission, staging, the adapter's copy-in,
#   the native call, the adapter's copy-out (which closes after the staging
#   copies are freed), and outcome handling (the tagged result decoded and the
#   observation and payloads printed).  The admission stage is the two-phase
#   decision: `admission_ns` is both phases and `admission_native_ns` and
#   `admission_policy_ns` split it, the second present only on the rows whose
#   masks saw a policy candidate (`admission_candidate`).
# * `admit` rows come from `leanllvm-json-route --admit <file> <reps>` on the
#   production build: the two-phase decision, the proved depth counter, and the
#   library's `admission` on the same bytes, with each one's own median.  They
#   are what the two-phase admission table divides, and they are the same rows
#   `check.sh` asserts agreement on.  `adapter_wall_ns` is the interval the
#   caller saw around the adapter; `copyin + native + copyout` less it is the
#   precondition checks and the two clock reads the adapter's intervals are
#   divided by.  `total_ns` is admission's start to the end of outcome handling,
#   so the file read is in `read_ns` and not in any stage; `summed_stage_ns` is
#   the per-repetition sum of the six stages, and `total - summed` is the glue
#   between them.
# * `stage` rows are taken from a `TIMING=1` build: the ordinary adapter reads
#   no clock at all (`build.sh` asserts that with `nm`), so it cannot report
#   these intervals and `--stages` refuses to print a row instead of printing
#   zeros.  The instrument's own cost is two clock reads inside copy-in and two
#   in copy-out, which land in those stages.
# * `process_wall` rows are the same executable's ordinary `--doc` mode, one
#   fresh process per repetition, from `date +%s%N`, with stdout to /dev/null:
#   process start, the file read, the route, and the printing of the hex
#   payloads.  They are the artifact a shell sees, and they are measured on the
#   uninstrumented build for both levels.
# * `consume` rows come from `leanllvm-json-route --consume <file> <reps>` on
#   the production build: the fast path run once per repetition, its result read
#   without printing -- the header through indexing and the event stream record
#   by record -- with a fold that keeps no per-token object and a reading that
#   materialises one event record per token.  The dissection section prices the
#   outcome stage's five parts against them; the mode exits 5 if its two
#   readings disagree.
# * `simdjson` rows come from `bench/simdjson-baseline.cc`: `pad_ns` is one
#   `padded_string` construction (simdjson's staging: allocate, copy, pad) and
#   `parse_ns` is one `iterate` plus the full value traversal, the parser staged
#   before the clock as `kernel/json/bench/paired-reference.cc` stages its arm.
#   They are the reference for the `staging+copyin` and `native` stages
#   respectively; `pad_plus_parse_ns` is the sum comparable with the route's
#   `total_ns`.  The reference is compiled from the local simdjson 4.6.11 source
#   and refuses to report a row unless the header and the active implementation
#   name that release.
#
# ## The -O2/-O3 pair
#
# The pair is the route's object -- the six kernel translation units -- built at
# each level with the adapter and everything else held fixed (`build.sh`'s
# `OPT`).  This is the optimisation-level gap
# `docs/json-route-artifact-correspondence.md` records between the route's -O2
# object and the proofs' -O3 emission, priced for the route's use of the object.
# The fallback rows are the control: they never call the object, so their pair
# must be unchanged, and a fallback row that moves with `OPT` means the pair is
# measuring something other than the object.
#
# ## The memory cap
#
# Every compile, build and run happens inside a systemd scope with a 6 GiB hard
# limit and 1 GiB of swap, directly or through `nix develop -c`.  If this script
# is not already inside such a scope it re-executes itself in one, so the record
# it prints is reproducible from a plain shell:
#
#   systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
#     nix develop -c bash probes/json/route/bench.sh 21
#
# `BENCH_DIR` keeps the build and corpus directories; `BENCH_CPU` selects the
# CPU every arm is pinned to (default 3); `SIMDJSON_SRC` names the simdjson
# source tree holding `singleheader/`.  Absent simdjson, the reference rows are
# reported absent rather than substituted, and the route's absolute numbers
# stand alone.
set -euo pipefail

cap_bytes=6442450944
swap_bytes=1073741824

# --- re-exec under the cap ------------------------------------------------
if [ -z "${OMP_BENCH_CAPPED:-}" ]; then
  self=$(realpath "$0")
  if ! command -v systemd-run >/dev/null 2>&1; then
    echo "bench: systemd-run is absent; run this script inside a memory cap" >&2
    exit 2
  fi
  export OMP_BENCH_CAPPED=1
  exec systemd-run --user --scope \
    -p MemoryMax="$cap_bytes" -p MemorySwapMax="$swap_bytes" --quiet \
    bash "$self" "$@"
fi

# The cap this run actually has, read back rather than assumed.
cgroup_dir=/sys/fs/cgroup$(awk -F: '$1=="0"{print $3}' /proc/self/cgroup)
cap_seen=$(cat "$cgroup_dir/memory.max" 2>/dev/null || echo unknown)

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
reps=${1:-21}
cpu=${BENCH_CPU:-3}
work=${BENCH_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/json-route-bench.XXXXXX")}
mkdir -p "$work"

pin=()
if command -v taskset >/dev/null 2>&1; then pin=(taskset -c "$cpu"); fi

# --- corpus ---------------------------------------------------------------
# Every fast-path document stays inside `admission`: one opener byte, so the
# opener-count clause holds, and shapes whose arena and event streams fit the
# record's capacities.  The two depth documents are the boundary pair: 128
# openers are admitted, 129 are outside the domain and the fallback answers.
corpus="$work/corpus"
mkdir -p "$corpus"
awk 'BEGIN{n=683;   printf "["; for(i=0;i<n;i++){if(i)printf ",";printf "12345"}; printf "]"}' >"$corpus/fast-nums-4096.json"
awk 'BEGIN{n=2731;  printf "["; for(i=0;i<n;i++){if(i)printf ",";printf "12345"}; printf "]"}' >"$corpus/fast-nums-16384.json"
awk 'BEGIN{n=10923; printf "["; for(i=0;i<n;i++){if(i)printf ",";printf "12345"}; printf "]"}' >"$corpus/fast-nums-65536.json"
awk 'BEGIN{printf "["; printf "\""; for(i=0;i<1000;i++)printf "\\n"; printf "\"]"}' >"$corpus/fast-esc.json"
awk 'BEGIN{for(i=0;i<128;i++)printf "["; for(i=0;i<128;i++)printf "]"}' >"$corpus/depth-128.json"
awk 'BEGIN{for(i=0;i<129;i++)printf "["; for(i=0;i<129;i++)printf "]"}' >"$corpus/depth-129.json"

fast_docs=("$corpus/fast-nums-4096.json" "$corpus/fast-nums-16384.json"
           "$corpus/fast-nums-65536.json" "$corpus/fast-esc.json")
depth_docs=("$corpus/depth-128.json" "$corpus/depth-129.json")
# A document the repository already ships that the domain does not admit: its
# objects open a container per element, so the opener count exceeds the bound.
repo_fallback=("$repo/probes/bench/json/scale-4096.json")

# --- machine --------------------------------------------------------------
printf '## the machine\n\n'
printf '%-14s %s\n' "cpu" "$(lscpu | sed -n 's/^Model name: *//p' | head -1)"
printf '%-14s %s\n' "cpus" "$(nproc)"
printf '%-14s %s\n' "kernel" "$(uname -srm)"
printf '%-14s %s\n' "memory" "$(awk '/MemTotal/{printf "%.1f GiB", $2/1048576}' /proc/meminfo)"
printf '%-14s %s\n' "memory cap" "$cap_bytes bytes hard, $swap_bytes bytes swap; read back from cgroup: $cap_seen"
printf '%-14s %s\n' "pinned cpu" "${BENCH_CPU:-3}"
printf '%-14s %s\n' "clang" "$(nix develop -c clang --version 2>/dev/null | grep -m1 'clang version')"
printf '%-14s %s\n' "lean" "$(nix develop -c lean --version | sed -n 's/^Lean (version \([^,]*\).*/\1/p')"
printf '%-14s %s\n' "nix" "$(nix --version)"
printf '%-14s %s\n' "reps" "$reps"
printf '\n'

# --- corpus table ---------------------------------------------------------
printf '## the corpus\n\n'
printf '%-22s %8s  %s\n' doc bytes sha256
for doc in "${fast_docs[@]}" "${depth_docs[@]}" "${repo_fallback[@]}"; do
  printf '%-22s %8s  %s\n' "$(basename "$doc")" "$(stat -c %s "$doc")" \
    "$(sha256sum "$doc" | cut -d' ' -f1)"
done
printf '\n'

# --- builds ---------------------------------------------------------------
build() { # <dir> <opt> <timing>
  local dir=$1 opt=$2 timing=$3
  BUILD_DIR="$work/$dir" OPT="$opt" TIMING="$timing" \
    nix develop -c bash "$here/build.sh" >"$work/$dir.log" 2>&1 || {
      echo "bench: build $dir failed:" >&2
      tail -20 "$work/$dir.log" >&2
      exit 1
    }
  sed -n 's/^flags:/flags:/p' "$work/$dir.log"
}

printf '## the builds\n\n'
printf '$ BUILD_DIR=<dir> OPT=-O2 TIMING=1 bash probes/json/route/build.sh\n'
printf '  %s\n' "$(build o2t -O2 1)"
printf '$ BUILD_DIR=<dir> OPT=-O3 TIMING=1 bash probes/json/route/build.sh\n'
printf '  %s\n' "$(build o3t -O3 1)"
printf '$ BUILD_DIR=<dir> OPT=-O2 TIMING=0 bash probes/json/route/build.sh\n'
printf '  %s\n' "$(build o2 -O2 0)"
printf '$ BUILD_DIR=<dir> OPT=-O3 TIMING=0 bash probes/json/route/build.sh\n'
printf '  %s\n' "$(build o3 -O3 0)"
printf '\nThe ordinary builds contain no clock read: build.sh asserts with nm\n'
printf 'that clock_gettime is absent from the TIMING=0 adapter and present in the\n'
printf 'TIMING=1 one.  Each build above passed that assertion or the script exited.\n\n'

# --- rows -----------------------------------------------------------------
field() { # <row> <name>
  printf '%s\n' "$1" | tr ' ' '\n' | sed -n "s/^$2=//p" | head -1
}

ratio() { # <a> <b>
  awk -v a="$1" -v b="$2" 'BEGIN{ if (b+0 == 0) print "n/a"; else printf "%.3f", a/b }'
}

stage_row() { # <build dir> <file> <expected path> [reps] -> row on stdout
  local out status row r=${4:-$reps}
  set +e
  out=$("${pin[@]}" "$work/$1/leanllvm-json-route" --stages "$2" "$r" \
          2>&1 >/dev/null)
  status=$?
  set -e
  # The fallback reports a refusal as exit 2; the row is printed either way, so
  # both statuses are expected and the path field is what is checked.
  case $status in
    0 | 2) ;;
    *)
      echo "bench: $(basename "$2") exited $status under --stages in $1:" >&2
      printf '%s\n' "$out" >&2
      exit 1
      ;;
  esac
  row=$(printf '%s\n' "$out" | grep '^row ')
  if [ "$(field "$row" path)" != "$3" ]; then
    echo "bench: $(basename "$2") took path=$(field "$row" path), expected $3" >&2
    exit 1
  fi
  printf '%s\n' "$row"
}

median_lines() { sort -n "$1" | awk '{a[NR]=$1} END{ if (NR) print a[int((NR+1)/2)]; else print 0 }'; }

wall_row() { # <build dir> <file> -> row on stdout
  local f="$work/wall.$$.txt" i t0 t1 status
  : >"$f"
  for ((i = 0; i < reps; i++)); do
    t0=$(date +%s%N)
    set +e
    "${pin[@]}" "$work/$1/leanllvm-json-route" --doc "$2" >/dev/null 2>&1
    status=$?
    set -e
    # A document the domain does not admit is a fallback refusal, exit 2; the
    # wall time of that answer is a row like any other.
    case $status in
      0 | 2) ;;
      *)
        echo "bench: $2 exited $status in $1" >&2
        exit 1
        ;;
    esac
    t1=$(date +%s%N)
    printf '%s\n' $((t1 - t0)) >>"$f"
  done
  printf 'row doc=%s size=%s build=%s process_wall_ns=%s reps=%s\n' \
    "$(basename "$2")" "$(stat -c %s "$2")" "$1" "$(median_lines "$f")" "$reps"
  rm -f "$f"
}

consumer_row() { # <build dir> <file> [reps] -> row on stdout
  local out status row r=${3:-$reps}
  set +e
  out=$("${pin[@]}" "$work/$1/leanllvm-json-route" --consume "$2" "$r" \
          2>&1 >/dev/null)
  status=$?
  set -e
  # The consumer's two readings must agree, or the mode exits 5 and this is a
  # failure rather than a row.  A document outside the domain has no fast-path
  # result to read and is not a consumer row, so any non-zero status is a
  # failure of the row this function was asked for.
  case $status in
    0) ;;
    *)
      echo "bench: $(basename "$2") exited $status under --consume in $1:" >&2
      printf '%s\n' "$out" >&2
      exit 1
      ;;
  esac
  row=$(printf '%s\n' "$out" | grep '^row ')
  if [ "$(field "$row" path)" != fast ]; then
    echo "bench: $(basename "$2") took path=$(field "$row" path) under --consume" >&2
    exit 1
  fi
  printf '%s\n' "$row"
}

printf '## the rows (ns)\n\n'
printf 'stage rows   <build>/leanllvm-json-route --stages <file> %s\n' "$reps"
printf 'wall rows    <build>/leanllvm-json-route --doc <file>, one process each\n'
printf 'reference    bench/simdjson-baseline <file> %s\n\n' "$reps"

o2_rows="$work/o2-fast.rows"; o3_rows="$work/o3-fast.rows"
: >"$o2_rows"; : >"$o3_rows"

row_d128=$(stage_row o2t "${depth_docs[0]}" fast)
row_d129=$(stage_row o2t "${depth_docs[1]}" fallback)
row_rs4096=$(stage_row o2t "${repo_fallback[0]}" fallback)
row_d128_o3=$(stage_row o3t "${depth_docs[0]}" fast)
row_d129_o3=$(stage_row o3t "${depth_docs[1]}" fallback)
row_rs4096_o3=$(stage_row o3t "${repo_fallback[0]}" fallback)

for doc in "${fast_docs[@]}"; do
  row=$(stage_row o2t "$doc" fast)
  printf '%s\n' "$row" | tee -a "$o2_rows"
done
printf '%s\n%s\n%s\n' "$row_d128" "$row_d129" "$row_rs4096"
printf '\n'
for doc in "${fast_docs[@]}"; do
  row=$(stage_row o3t "$doc" fast)
  printf '%s\n' "$row" | tee -a "$o3_rows"
done
printf '%s\n%s\n%s\n' "$row_d128_o3" "$row_d129_o3" "$row_rs4096_o3"
printf '\n'

for doc in "${fast_docs[@]}"; do
  for b in o2 o3; do printf '%s\n' "$(wall_row "$b" "$doc")"; done
done
for doc in "${depth_docs[@]}" "${repo_fallback[@]}"; do
  printf '%s\n' "$(wall_row o2 "$doc")"
done
printf '\n'

# --- the consumer's rows --------------------------------------------------
# `--consume` reads the fast path's result without printing: the header through
# indexing and the event stream record by record, counted and checksummed.  It
# is driven on the production build, so nothing in its row comes from the
# adapter's instrument; the mode exits 5 if its two readings disagree.
printf 'consume rows  <build>/leanllvm-json-route --consume <file> %s\n\n' "$reps"
cons_rows="$work/cons-fast.rows"
: >"$cons_rows"
for doc in "${fast_docs[@]}"; do
  printf '%s\n' "$(consumer_row o2 "$doc")" | tee -a "$cons_rows"
done
printf '\n'

# --- the outcome stage, dissected ----------------------------------------
pct() { # <a> <b> -> a as a percent of b
  awk -v a="$1" -v b="$2" 'BEGIN{ if (b+0 == 0) print "-"; else printf "%.2f", 100*a/b }'
}
per() { # <numerator> <denominator> -> the quotient, three decimals
  awk -v a="$1" -v b="$2" 'BEGIN{ if (b+0 == 0) print "-"; else printf "%.2f", a/b }'
}
sum5() { # five numbers -> their sum
  awk -v a="$1" -v b="$2" -v c="$3" -v d="$4" -v e="$5" \
    'BEGIN{ printf "%d", a+b+c+d+e }'
}

printf '## the outcome stage dissected (unit: ns; medians of %s reps, OPT=-O2 TIMING=1 build)\n\n' "$reps"
printf '%-22s %9s %7s %8s %7s %10s %10s %10s %11s %7s\n' \
  doc decode header slice arena events outcome hex_arena hex_events tokens
for doc in "${fast_docs[@]}"; do
  name=$(basename "$doc")
  row=$(grep " doc=$name " "$o2_rows")
  cons=$(grep " doc=$name " "$cons_rows")
  printf '%-22s %9s %7s %8s %7s %10s %10s %10s %11s %7s\n' "$name" \
    "$(field "$row" outcome_decode_ns)" "$(field "$row" outcome_header_ns)" \
    "$(field "$row" outcome_slice_ns)" "$(field "$row" outcome_arena_ns)" \
    "$(field "$row" outcome_events_ns)" "$(field "$row" outcome_ns)" \
    "$(field "$row" hex_arena_ns)" "$(field "$row" hex_events_ns)" \
    "$(field "$cons" tokens)"
done
printf '\nconstruction: the five parts are the outcome stage itself, in its own\n'
printf 'order.  decode is `decodeResult`: the tagged header, the length check and\n'
printf 'the seven header words; header is the observation line built and written;\n'
printf 'slice is the two payloads cut out of the result; arena and events are each\n'
printf 'payload line built and written.  outcome is the per-repetition sum of the\n'
printf 'five, so the five clock reads that divide them are inside the stage and\n'
printf 'nothing outside it is.  hex_arena and hex_events rebuild the same two lines\n'
printf 'with the write removed, after the stage timed window: the difference between\n'
printf 'a payload part and its hex figure is that line write.  tokens is the event\n'
printf 'count the consumer row above reports for the same document.\n\n'

printf 'share of outcome (unit: percent; each part median divided by the outcome\n'
printf 'median from the same --stages row; the parts are medians of per-repetition\n'
printf 'sums, so they need not add to exactly 100)\n\n'
printf '%-22s %8s %7s %8s %7s %9s %8s\n' doc decode header slice arena events parts
for doc in "${fast_docs[@]}"; do
  name=$(basename "$doc")
  row=$(grep " doc=$name " "$o2_rows")
  out=$(field "$row" outcome_ns)
  parts=$(sum5 "$(field "$row" outcome_decode_ns)" "$(field "$row" outcome_header_ns)" \
    "$(field "$row" outcome_slice_ns)" "$(field "$row" outcome_arena_ns)" \
    "$(field "$row" outcome_events_ns)")
  printf '%-22s %8s %7s %8s %7s %9s %8s\n' "$name" \
    "$(pct "$(field "$row" outcome_decode_ns)" "$out")" \
    "$(pct "$(field "$row" outcome_header_ns)" "$out")" \
    "$(pct "$(field "$row" outcome_slice_ns)" "$out")" \
    "$(pct "$(field "$row" outcome_arena_ns)" "$out")" \
    "$(pct "$(field "$row" outcome_events_ns)" "$out")" \
    "$(pct "$parts" "$out")"
done
printf '\n'

printf 'per-unit costs (each column states its numerator, its denominator and its\n'
printf 'unit; the denominators are the same stage row and the consumer row above)\n\n'
printf '%-22s %7s %12s %11s %16s %15s %13s\n' \
  doc tokens result_bytes decode/byte hex_events/byte events_write printed/event
for doc in "${fast_docs[@]}"; do
  name=$(basename "$doc")
  row=$(grep " doc=$name " "$o2_rows")
  cons=$(grep " doc=$name " "$cons_rows")
  rb=$((80 + $(field "$row" ndst) + $(field "$row" nev)))
  wr=$(($(field "$row" outcome_events_ns) - $(field "$row" hex_events_ns)))
  printf '%-22s %7s %12s %11s %16s %15s %13s\n' "$name" \
    "$(field "$cons" tokens)" "$rb" \
    "$(per "$(field "$row" outcome_decode_ns)" "$rb")" \
    "$(per "$(field "$row" hex_events_ns)" "$(field "$row" nev)")" \
    "$wr" \
    "$(per "$(field "$row" outcome_ns)" "$(field "$cons" tokens)")"
done
printf '\nUnits and construction: result_bytes is 80 header bytes plus ndst plus nev,\n'
printf 'the extent of the array decodeResult walks; decode/byte divides the decode\n'
printf 'median by it (ns per result byte); hex_events/byte divides the hex rebuild\n'
printf 'median by nev (ns per event-stream byte); events_write is the events part\n'
printf 'less its hex rebuild, in ns per document (the write of one events line);\n'
printf 'printed/event divides the outcome median by the consumer token count (ns\n'
printf 'per event, the printed path).\n\n'

printf '## what a consumer pays (unit: ns; the same documents, the consumer rows above)\n\n'
printf '%-22s %7s %6s %7s %8s %8s %14s %16s %10s %12s\n' \
  doc tokens ndst nev fold values fold/event values/event fold/byte values/byte
for doc in "${fast_docs[@]}"; do
  name=$(basename "$doc")
  cons=$(grep " doc=$name " "$cons_rows")
  t=$(field "$cons" tokens)
  b=$(( $(field "$cons" ndst) + $(field "$cons" nev) ))
  printf '%-22s %7s %6s %7s %8s %8s %14s %16s %10s %12s\n' "$name" "$t" \
    "$(field "$cons" ndst)" "$(field "$cons" nev)" \
    "$(field "$cons" consume_fold_ns)" "$(field "$cons" consume_values_ns)" \
    "$(per "$(field "$cons" consume_fold_ns)" "$t")" \
    "$(per "$(field "$cons" consume_values_ns)" "$t")" \
    "$(per "$(field "$cons" consume_fold_ns)" "$b")" \
    "$(per "$(field "$cons" consume_values_ns)" "$b")"
done
printf '\nconstruction: fold and values are the two readings the consumer mode\n'
printf 'prices, medians over the same repetition count, alternating which goes\n'
printf 'first so neither always pays the cold pass; both include one indexed header\n'
printf 'decode and the arena read.  fold keeps no per-token object; values\n'
printf 'materialises one event record per token and folds the array, so its price\n'
printf 'carries the per-token allocation.  fold/event and values/event divide each\n'
printf 'median by the event count (ns per event); fold/byte and values/byte divide\n'
printf 'it by ndst plus nev instead (ns per payload byte).\n\n'

printf 'printed against consumed (unit: multiplier; the printed path outcome median\n'
printf 'divided by the consumer values median, same document and session, outcome\n'
printf 'from the TIMING=1 build and consumed from the production build; per-event\n'
printf 'costs are those two medians divided by the same token count)\n\n'
printf '%-22s %12s %16s %14s %18s\n' \
  doc printed/event consumed/event printed/consumed decoded/printed
for doc in "${fast_docs[@]}"; do
  name=$(basename "$doc")
  row=$(grep " doc=$name " "$o2_rows")
  cons=$(grep " doc=$name " "$cons_rows")
  t=$(field "$cons" tokens)
  out=$(field "$row" outcome_ns)
  cv=$(field "$cons" consume_values_ns)
  dec=$(field "$row" outcome_decode_ns)
  printf '%-22s %12s %16s %14s %18s\n' "$name" \
    "$(per "$out" "$t")" "$(per "$cv" "$t")" "$(per "$out" "$cv")" \
    "$(pct "$dec" "$out")"
done
printf '\nconstruction: printed/consumed is the outcome median over the consumer\n'
printf 'values median, both per document (a multiplier, not a percentage);\n'
printf 'decoded/printed is the decode part percent of the outcome, the same figure\n'
printf 'the share table carries, repeated here beside the consumer number.\n\n'

# --- the reference arm ----------------------------------------------------
printf '## the reference arm\n\n'
src=${SIMDJSON_SRC:-}
if [ -z "$src" ]; then
  hit=$(find /nix/store -maxdepth 3 -path '*/singleheader/simdjson.h' -print -quit 2>/dev/null || true)
  if [ -n "$hit" ]; then
    proj=$(dirname "$(dirname "$hit")")
    if grep -q 'SIMDJSON_VERSION "4.6.11"' "$hit"; then src=$proj; fi
  fi
fi
if [ -n "$src" ] && [ -f "$src/singleheader/simdjson.cpp" ]; then
  printf 'source      %s/singleheader, simdjson %s\n' "$src" \
    "$(sed -n 's/^#define SIMDJSON_VERSION "\(.*\)"/\1/p' "$src/singleheader/simdjson.h" | head -1)"
  printf 'lineage     no simdjson checkout and no -dev headers exist on this machine; the\n'
  printf '            arm is compiled from the local source archive the pinned release\n'
  printf '            ships as (singleheader/simdjson.{h,cpp}), and its runtime refuses a\n'
  printf '            row unless that header and the active implementation name 4.6.11\n'
  printf 'build       clang++ -O3 -std=c++17 -march=x86-64-v3 -mpclmul -I <src>/singleheader\\\n'
  printf '              bench/simdjson-baseline.cc <src>/singleheader/simdjson.cpp\n\n'
  nix develop -c clang++ -O3 -std=c++17 -march=x86-64-v3 -mpclmul \
    -I "$src/singleheader" "$here/bench/simdjson-baseline.cc" \
    "$src/singleheader/simdjson.cpp" -o "$work/simdjson-baseline" \
    >"$work/simdjson-build.log" 2>&1 || {
      echo "bench: the reference arm did not compile:" >&2
      tail -20 "$work/simdjson-build.log" >&2
      exit 1
    }
  ref_rows="$work/simdjson.rows"; : >"$ref_rows"
  for doc in "${fast_docs[@]}"; do
    printf '%s\n' "$("${pin[@]}" "$work/simdjson-baseline" "$doc" "$reps")" | tee -a "$ref_rows"
  done
  printf '\n'
else
  printf 'absent      no local simdjson 4.6.11 source with singleheader/ was found and no\n'
  printf '            row is substituted; the route rows above stand alone.\n\n'
fi

# --- ratios ---------------------------------------------------------------
# Each ratio row names its unit and the two medians it divides, so the number
# cannot be read as another unit or another construction.
# The pair and its control are interleaved, not taken from the two tables
# above: a shared machine's per-run medians drifted by more than a fifth within
# this session (the control column), so two separate runs of two builds cannot
# carry a claim about OPT.  Each round runs both builds on the same document and
# alternates which goes first, and the same build is run a third time in the
# round as the drift control; the row is the median of the per-round ratios and
# its range, so the spread is visible beside the number.
rounds=${BENCH_ROUNDS:-9}
pair_reps=${BENCH_PAIR_REPS:-5}
pair_tsv="$work/pair.tsv"
: >"$pair_tsv"
printf '## the -O2/-O3 pair, paired (unit: ratio of ns medians; %s rounds of %s reps)\n\n' \
  "$rounds" "$pair_reps"
progress() { printf 'bench: paired round %s/%s for %s\r' "$1" "$rounds" "$2" >&2; }
for doc in "${fast_docs[@]}"; do
  name=$(basename "$doc")
  for ((r = 0; r < rounds; r++)); do
    progress "$((r + 1))" "$name"
    if ((r % 2 == 0)); then
      row_a=$(stage_row o2t "$doc" fast "$pair_reps")
      row_b=$(stage_row o3t "$doc" fast "$pair_reps")
    else
      row_b=$(stage_row o3t "$doc" fast "$pair_reps")
      row_a=$(stage_row o2t "$doc" fast "$pair_reps")
    fi
    row_c=$(stage_row o2t "$doc" fast "$pair_reps")
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$name" \
      "$(ratio "$(field "$row_b" native_ns)" "$(field "$row_a" native_ns)")" \
      "$(ratio "$(field "$row_b" total_ns)" "$(field "$row_a" total_ns)")" \
      "$(ratio "$(field "$row_c" native_ns)" "$(field "$row_a" native_ns)")" \
      "$(ratio "$(field "$row_c" total_ns)" "$(field "$row_a" total_ns)")" \
      "$(field "$row_a" native_ns)" >>"$pair_tsv"
  done
done
printf '\n\n'

stats() { # <file of numbers> -> "median min max"
  sort -n "$1" | awk '{a[NR]=$1} END{
    if (!NR) { print "n/a n/a n/a"; exit }
    printf "%.3f %.3f %.3f", a[int((NR+1)/2)], a[1], a[NR] }'
}
printf '%-22s %-21s %-21s %-21s\n' doc 'O3/O2 native' 'O3/O2 total' 'control native'
printf '%-22s %-21s %-21s %-21s\n' '' 'med min max' 'med min max' 'med min max'
for doc in "${fast_docs[@]}"; do
  name=$(basename "$doc")
  for col in 2 3 4; do
    awk -F'\t' -v n="$name" -v c="$col" '$1==n{print $c}' "$pair_tsv" >"$work/col.txt"
    case $col in
      2) nat=$(stats "$work/col.txt") ;;
      3) tot=$(stats "$work/col.txt") ;;
      4) ctl=$(stats "$work/col.txt") ;;
    esac
  done
  printf '%-22s %-21s %-21s %-21s\n' "$name" "$nat" "$tot" "$ctl"
done
printf '\nconstruction: O3/O2 native divides the -O3 build native-call stage by the\n'
printf '%s\n' '-O2 build same stage in the same round, alternated so the drift cancels;'
printf 'O3/O2 total is the same for admission-to-print; control native divides a\n'
printf 'second -O2 run by the first in the same round, so its range is what the\n'
printf 'machine contributes with no OPT change at all.  A pair whose median sits\n'
printf 'inside the control range is not a difference OPT produced.\n\n'

printf '## the fallback price (unit: ns; medians of %s reps, OPT=-O2 build)\n\n' "$reps"
printf '%-22s %9s %10s %10s %10s %10s %11s\n' doc path admission staging native outcome total
for row in "$row_d128" "$row_d129" "$row_rs4096"; do
  printf '%-22s %9s %10s %10s %10s %10s %11s\n' "$(field "$row" doc)" \
    "$(field "$row" path)" "$(field "$row" admission_ns)" \
    "$(field "$row" staging_ns)" "$(field "$row" native_ns)" \
    "$(field "$row" outcome_ns)" "$(field "$row" total_ns)"
done
printf '\nratio depth-129/depth-128 total = %s (unit: ns per document; the documents\n' \
  "$(ratio "$(field "$row_d129" total_ns)" "$(field "$row_d128" total_ns)")"
printf 'differ by one bracket pair, and by which path answers them)\n'
printf 'ratio scale-4096/fast-nums-4096 total = %s (unit: ns per document; the\n' \
  "$(ratio "$(field "$row_rs4096" total_ns)" "$(field "$(grep ' doc=fast-nums-4096.json ' "$o2_rows")" total_ns)")"
printf 'documents differ in shape as well as in path)\n\n'

# --- the two-phase admission ----------------------------------------------
# The admission stage the route runs is the two-phase decision; these rows put
# it beside the predicate it replaced, on the same documents in the same
# session, and beside the proved depth counter, which is measured and gates
# nothing.  `certified_ns` is the library's `admission` -- the opener count over
# `doc.data.toList` and the per-quote policy scan -- and `two_phase_ns` is what
# the route now pays: the native facts, then the policy scan only where the masks
# saw a candidate.
admit_row() { # <file> [native depth] -> the row on stderr
  local out status row
  set +e
  out=$("${pin[@]}" "$work/o2/leanllvm-json-route" --admit "$1" "$reps" ${2:-} \
          2>&1 >/dev/null)
  status=$?
  set -e
  if [ "$status" -ne 0 ]; then
    echo "bench: $(basename "$1") exited $status under --admit:" >&2
    printf '%s\n' "$out" >&2
    exit 1
  fi
  row=$(printf '%s\n' "$out" | grep '^admit ')
  if [ -z "$row" ]; then
    echo "bench: $(basename "$1") printed no admission row" >&2
    exit 1
  fi
  printf '%s\n' "$row"
}

adm_rows="$work/admit.rows"
: >"$adm_rows"
all_docs=("${fast_docs[@]}" "${depth_docs[@]}" "${repo_fallback[@]}")
for doc in "${all_docs[@]}"; do
  admit_row "$doc" | tee -a "$adm_rows" >/dev/null
done

printf '## the two-phase admission (unit: ns; medians of %s reps, OPT=-O2 production build)\n\n' "$reps"
printf '%-22s %8s %9s %12s %10s %10s %12s %10s %10s\n' \
  doc openers candidate certified_ns phase1_ns policy_ns two_phase_ns 'two_phase/certified' depth_ns
for doc in "${all_docs[@]}"; do
  name=$(basename "$doc")
  row=$(grep " doc=$name " "$adm_rows")
  printf '%-22s %8s %9s %12s %10s %10s %12s %10s %10s\n' "$name" \
    "$(field "$row" openers)" "$(field "$row" candidate)" \
    "$(field "$row" certified_ns)" "$(field "$row" phase1_ns)" \
    "$(field "$row" policy_ns)" "$(field "$row" two_phase_ns)" \
    "$(ratio "$(field "$row" two_phase_ns)" "$(field "$row" certified_ns)")" \
    "$(field "$row" depth_ns)"
done
printf '\nconstruction: certified_ns is the library'"'"'s `admission`: the empty and\n'
printf 'length clauses, the opener count over `doc.data.toList`, and the per-quote\n'
printf 'policy scan.  phase1_ns is the adapter'"'"'s native call (the mask unit over\n'
printf 'the document, the delimiter lanes counted, the candidate flag), including\n'
printf 'the Lean extern call and the header decode.  policy_ns is phase two, the\n'
printf 'reference'"'"'s own `policyRefusal`, and is `-` where the masks saw no\n'
printf 'candidate: two_phase_ns is phase one plus phase two, so a `-` row differs\n'
printf 'from certified_ns alone.  two_phase/certified is a multiplier (the new\n'
printf 'cost divided by the old, same document and session).  depth_ns is the\n'
printf 'proved depth counter run over the same delimiter lanes: it is a balance\n'
printf 'and a prefix-depth sum, neither of which is the opener count the clause\n'
printf 'states, so it is reported and gates nothing.\n\n'

cand=0
ran=0
for doc in "${all_docs[@]}"; do
  row=$(grep " doc=$(basename "$doc") " "$adm_rows")
  [ "$(field "$row" candidate)" = 1 ] && cand=$((cand + 1))
  [ "$(field "$row" policy)" = 1 ] && ran=$((ran + 1))
done
printf 'policy candidate on %s of %s rows (the fraction of documents whose masks\n' \
  "$cand" "${#all_docs[@]}"
printf 'show a byte the policy scan can report at: a quote or a backslash); the\n'
printf 'scan itself ran on %s, the rows that candidate flag did not spare by a\n' "$ran"
printf 'native clause refusing first.  A document with quotes and no escapes pays\n'
printf 'the whole scan, which is the number that decides whether the policy check\n'
printf 'needs its own native unit.\n\n'

if [ -x "$work/simdjson-baseline" ]; then
  # Paired for the same reason the -O2/-O3 pair is: the two arms are separate
  # binaries, this host's per-run medians drift by a tenth or more, and a
  # cross-binary comparison taken from two separate runs would attribute that
  # drift to the code (docs/json-pipeline-performance.md §7.2).  Each round runs
  # both arms on the same document, alternating which goes first, and the row is
  # the median and range of the per-round ratios.
  ref_tsv="$work/ref-pair.tsv"
  : >"$ref_tsv"
  printf '## the reference comparison, paired (unit: ratio of ns medians; %s rounds of %s reps)\n\n' \
    "$rounds" "$pair_reps"
  for doc in "${fast_docs[@]}"; do
    name=$(basename "$doc")
    for ((r = 0; r < rounds; r++)); do
      printf 'bench: reference round %s/%s for %s\r' "$((r + 1))" "$rounds" "$name" >&2
      if ((r % 2 == 0)); then
        row_a=$(stage_row o2t "$doc" fast "$pair_reps")
        ref=$("${pin[@]}" "$work/simdjson-baseline" "$doc" "$pair_reps")
      else
        ref=$("${pin[@]}" "$work/simdjson-baseline" "$doc" "$pair_reps")
        row_a=$(stage_row o2t "$doc" fast "$pair_reps")
      fi
      o2=$(field "$row_a" outcome_ns)
      core=$(($(field "$row_a" total_ns) - o2))
      printf '%s\t%s\t%s\t%s\t%s\n' "$name" \
        "$(ratio "$(field "$row_a" native_ns)" "$(field "$ref" parse_ns)")" \
        "$(ratio "$core" "$(field "$ref" pad_plus_parse_ns)")" \
        "$(field "$row_a" native_ns)" "$(field "$ref" parse_ns)" >>"$ref_tsv"
    done
  done
  printf '\n\n'
  printf '%-22s %-21s %-21s\n' doc 'native/parse' 'core/pad+parse'
  printf '%-22s %-21s %-21s\n' '' 'med min max' 'med min max'
  for doc in "${fast_docs[@]}"; do
    name=$(basename "$doc")
    for col in 2 3; do
      awk -F'\t' -v n="$name" -v c="$col" '$1==n{print $c}' "$ref_tsv" >"$work/col.txt"
      case $col in
        2) np=$(stats "$work/col.txt") ;;
        3) cp=$(stats "$work/col.txt") ;;
      esac
    done
    printf '%-22s %-21s %-21s\n' "$name" "$np" "$cp"
  done
  printf '\nnative/parse divides the route native-call stage by simdjson iterate plus\n'
  printf 'the full value traversal; core/pad+parse divides the route total less\n'
  printf 'outcome handling (admission, staging, copy-in, native, copy-out) by simdjson\n'
  printf 'padded-copy plus parse.  Both are ratios of ns medians over the same document\n'
  printf 'in the same round; one pass per arm, no repeated work in either.  The arms are\n'
  printf 'two binaries, so the alternation cancels drift but not the difference between\n'
  printf 'two address spaces.  The escape-heavy document is the one shape where the\n'
  printf 'reference traversal, which unescapes every string, exceeds the route native\n'
  printf 'stage.  The route total over the same figure is not shown: it is the hex\n'
  printf 'printing of both payloads, which is the outcome stage and is reported on\n'
  printf 'its own above, in the outcome dissection.\n\n'
fi

printf '## the record\n\n'
printf 'build and corpus directory: %s\n' "$work"
printf 'every command above ran under MemoryMax=%s with MemorySwapMax=%s, pinned to CPU %s.\n' \
  "$cap_bytes" "$swap_bytes" "$cpu"
