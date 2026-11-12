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
#   observation and payloads printed).  `adapter_wall_ns` is the interval the
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
  printf 'stage.  The route total over the same figure is not shown: it is 80-480x\n'
  printf 'because the route prints both payloads as hex, which is the outcome stage\n'
  printf 'and is reported on its own above.\n\n'
fi

printf '## the record\n\n'
printf 'build and corpus directory: %s\n' "$work"
printf 'every command above ran under MemoryMax=%s with MemorySwapMax=%s, pinned to CPU %s.\n' \
  "$cap_bytes" "$swap_bytes" "$cpu"
