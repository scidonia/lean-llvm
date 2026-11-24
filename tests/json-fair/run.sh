#!/usr/bin/env bash
# Measure the fair comparison on the pinned corpus, one CPU at a time.
#
#   nix develop -c bash tests/json-fair/run.sh
#   nix develop -c bash tests/json-fair/run.sh --short
#
# What is measured.  Every document is read once and gated (the writer's event
# and arena bytes equal `leanllvm_json_pipeline`'s, the same C consumer reads
# both, and the direct sum equals that consumer's fold) and only then timed,
# under `taskset` on one CPU from `BENCH_CPUS`.  The arms are, in this order
# (the order rotates at every trial, so each arm is first and last equally
# often):
#
#   parse   simdjson 5.0.5's full traversal, no output
#   pw      traversal + the equal-output writer (event and arena bytes)
#   pwc     pw + the consumer fold
#   ps      traversal + the direct consumer sum, no event buffer
#   rp      this tree's pipeline call (`leanllvm_json_pipeline`)
#   rpc     rp + the consumer fold
#   rpn     the no-event pipeline's returned reading, no event buffer and no
#           consumer walk (only when built with the no-event objects)
#
# `ps` and `rpn` are the two sides of the consumer-boundary claim: both answer
# the consumer's reading without materialising an event buffer.  `parse` is not
# that comparison and a `parse` quotient is not reported as one.
#
# Discipline.  Each document gets one warm pass of every arm outside the clock;
# each row is `BENCH_REPS` repetitions and the trial's value is their median;
# the whole set runs `BENCH_TRIALS` times.  Every quotient is taken within one
# trial on one CPU and then reduced across the trials, so a drift between
# trials never becomes a quotient.  The per-document table is written to
# `build/per-document.tsv`.
#
# The counts, when the no-event arm is present, are over the `rpn/ps` quotient:
#
#   faster   the quotient is below 1.0
#   in band  1.0 <= quotient <= 1.10 (at parity or at most 10% over)
#   over     the quotient is above 1.10
#
# The three partition the documents.  The majority condition is "faster on
# more than half of the corpus", and it is printed with its denominator; it is
# not a statement about `parse`.
#
# Environment: BENCH_CPUS (default 0), BENCH_TRIALS (3), BENCH_REPS (51),
# BENCH_DIR, FAIR_CORPUS, FAIR_REGENERATE=1 (regenerate the corpus rather than
# verify it), FAIR_NOEVENT=1 (link and time the no-event arm), BENCH_CXX
# (clang++), FAIR_CC (clang), SIMDJSON_DEV, SIMDJSON_LIB.
#
# Exit status: 0 when every gate held and every document was measured, 1 when a
# gate or the corpus assertion failed, 3 when an arm is not usable (an absent
# compiler, store output, corpus, `gen.c` or `taskset`).
set -uo pipefail
export LC_ALL=C

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
work=${BENCH_DIR:-$here/build}
bin=$work/bin
cpus=${BENCH_CPUS:-0}
short=0
for arg in "$@"; do
  case "$arg" in
    --short) short=1 ;;
    -h|--help) sed -n '2,58p' "$0"; exit 0 ;;
    *) printf 'SETUP: unknown argument %s\n' "$arg" >&2; exit 3 ;;
  esac
done
if [ "$short" = 1 ]; then
  trials=${BENCH_TRIALS:-1}
  reps=${BENCH_REPS:-3}
else
  trials=${BENCH_TRIALS:-3}
  reps=${BENCH_REPS:-51}
fi
cxx=${BENCH_CXX:-clang++}
cc=${FAIR_CC:-clang}
dev=${SIMDJSON_DEV:-/nix/store/m2i8165bayxxgzj3fbvdg6gihz6na93d-simdjson-5.0.5-dev}
lib=${SIMDJSON_LIB:-/nix/store/jglxdk9y0yfk3mc9dbr675pfmv42a89y-simdjson-5.0.5}
corpus=${FAIR_CORPUS:-$here/corpus}
regenerate=${FAIR_REGENERATE:-0}
noevent=${FAIR_NOEVENT:-0}

die() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

cxxflags=(-O3 -march=x86-64-v3 -mpclmul -std=c++17 -falign-loops=64 -falign-functions=64)
kbase=(-march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64
       -I "$repo/kernel/json")
kflags=(-O2 "${kbase[@]}")

[ -n "$work" ] && [ "$work" != "/" ] || die "refusing work directory '$work'"
command -v "$cxx" >/dev/null 2>&1 || die "no $cxx on PATH; run this under nix develop"
command -v "$cc" >/dev/null 2>&1 || die "no $cc on PATH; run this under nix develop"
command -v taskset >/dev/null 2>&1 || die "no taskset on PATH"
case "$regenerate" in 0|1) ;; *) die "FAIR_REGENERATE is '$regenerate', not 0 or 1" ;; esac
case "$noevent" in 0|1) ;; *) die "FAIR_NOEVENT is '$noevent', not 0 or 1" ;; esac

header=$dev/include/simdjson.h
solib=$lib/lib/libsimdjson.so.34.0.0
[ -f "$header" ] || die "absent: $header
  realise it with: nix build --no-link --print-out-paths 'nixpkgs#simdjson.dev'"
[ -f "$solib" ] || die "absent: $solib
  realise it with: nix build --no-link --print-out-paths 'nixpkgs#simdjson'"
ver=$(sed -n 's/^#define SIMDJSON_VERSION "\(.*\)"/\1/p' "$header" | head -1)
[ "$ver" = "5.0.5" ] || die "header is simdjson '$ver', not 5.0.5"

# --- Corpus -----------------------------------------------------------------
[ -f "$here/manifest.tsv" ] || die "absent: tests/json-fair/manifest.tsv"
if [ "$regenerate" = 1 ] || [ ! -d "$corpus" ]; then
  bash "$here/generate.sh" --out="$corpus" || die "corpus generation failed"
else
  bash "$here/generate.sh" --verify --out="$corpus" || die "corpus verification failed"
fi

# --- Build ------------------------------------------------------------------
rm -rf "$work"
mkdir -p "$bin" || die "cannot create $work"

objs=()
for f in pipeline s1_block entry escape utf8 stage2; do
  "$cc" "${kflags[@]}" -c "$repo/kernel/json/$f.c" -o "$bin/$f.o" 2>"$work/$f.cc.err" ||
    { cat "$work/$f.cc.err" >&2; die "kernel/json/$f.c did not build"; }
  objs+=("$bin/$f.o")
done

noevflag=()
if [ "$noevent" = 1 ]; then
  for f in stage2_noevent pipeline_noevent; do
    "$cc" "${kflags[@]}" -c "$repo/kernel/json/$f.c" -o "$bin/$f.o" 2>"$work/$f.cc.err" ||
      { cat "$work/$f.cc.err" >&2; die "kernel/json/$f.c did not build"; }
    objs+=("$bin/$f.o")
  done
  noevflag=(-DFAIR_NOEVENT=1)
fi

"$cxx" "${cxxflags[@]}" "${noevflag[@]}" -I "$dev/include" -I "$repo/kernel/json" \
  -I "$repo/probes/json/route" -c "$here/fair.cc" -o "$bin/fair.o" 2>"$work/fair.cc.err" ||
  { cat "$work/fair.cc.err" >&2; die "fair.cc did not build"; }

"$cxx" "$bin/fair.o" "${objs[@]}" -L "$lib/lib" -Wl,-rpath,"$lib/lib" \
  -lsimdjson -o "$bin/fair" 2>"$work/link.err" ||
  { cat "$work/link.err" >&2; die "the fair harness did not link"; }

# --- Host and build record ---------------------------------------------------
printf 'command: nix develop -c bash tests/json-fair/run.sh%s\n' \
  "$([ "$short" = 1 ] && echo ' --short')"
printf 'harness: run.sh sha256=%s\n' "$(sha256sum "$0" | cut -d' ' -f1)"
printf 'generator: gen.py sha256=%s\n' "$(sha256sum "$here/gen.py" | cut -d' ' -f1)"
printf 'manifest: sha256=%s rows=%s\n' "$(sha256sum "$here/manifest.tsv" | cut -d' ' -f1)" \
  "$(awk 'END { print NR - 1 }' "$here/manifest.tsv")"
printf 'writer: fair.cc sha256=%s\n' "$(sha256sum "$here/fair.cc" | cut -d' ' -f1)"
printf 'simdjson: %s (header); dev: %s\n' "$ver" "$dev"
printf 'simdjson lib: %s; %s sha256=%s\n' "$lib" "$(basename "$solib")" \
  "$(sha256sum "$solib" | cut -d' ' -f1)"
printf 'provenance: nix build --no-link --print-out-paths '\''nixpkgs#simdjson.dev'\''\n'
printf 'provenance: nix build --no-link --print-out-paths '\''nixpkgs#simdjson'\''\n'
printf 'compiler: %s (%s); kernel: %s (%s)\n' "$cxx" "$("$cxx" --version | head -1)" \
  "$cc" "$("$cc" --version | head -1)"
printf 'kernel flags: %s\n' "${kflags[*]}"
printf 'harness flags: %s\n' "${cxxflags[*]}"
printf 'no-event arm: %s\n' "$([ "$noevent" = 1 ] && echo linked || echo absent)"
printf 'host: %s\n' "$(uname -srm)"
printf 'cpu: %s\n' "$(awk -F: '/^model name/ { sub(/^ /, "", $2); print $2; exit }' /proc/cpuinfo)"
printf 'cpus online: %s; pinned to: %s\n' "$(nproc)" "$cpus"
printf 'scaling governor: %s\n' "$(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null || echo unknown)"
printf 'load average at start: %s\n' "$(cat /proc/loadavg)"
printf 'trials: %s; reps in every row: %s\n' "$trials" "$reps"
printf 'corpus: %s (%s documents)\n' "$corpus" \
  "$(awk 'END { print NR - 1 }' "$here/manifest.tsv")"
printf '\n'

# --- Measure ----------------------------------------------------------------
docs=()
while IFS=$'\t' read -r file rest; do
  [ "$file" = file ] && continue
  docs+=(--doc "$corpus/$file")
done < "$here/manifest.tsv"

raw=$work/rows.tsv
: >"$raw"
status=0
for cpu in $cpus; do
  if ! taskset -c "$cpu" "$bin/fair" --reps "$reps" --trials "$trials" "${docs[@]}" \
      2>"$work/fair.$cpu.err" | awk -v c="$cpu" '{ print c "\t" $0 }' >>"$raw"; then
    status=1
  fi
  cat "$work/fair.$cpu.err" >&2
done
[ "$status" = 0 ] || { printf '\nFAIL: a gate failed; the rows above are not a measurement\n' >&2; exit 1; }
printf 'load average after the sweep: %s\n\n' "$(cat /proc/loadavg)"

# --- Aggregate ---------------------------------------------------------------
# The per-document table: each arm's median of the trial medians, and (when the
# no-event arm is present) the no-event quotient as the median of the per-trial
# quotients.  A trial missing an arm is a failure, not a shorter average.
awk -v trials="$trials" -v noevent="$noevent" '
  function sortn(a, n,   i, j, t) { for (i = 2; i <= n; i++) { t = a[i]; for (j = i - 1; j >= 1 && a[j] > t; j--) a[j+1] = a[j]; a[j+1] = t } }
  function med(a, n) { if (n % 2) return a[(n + 1) / 2]; return 0.5 * (a[n / 2] + a[n / 2 + 1]) }
  BEGIN {
    printf "# per-document fair comparison; times are ns (median of the %d trial medians),\n", trials
    printf "# rpn/ps is the median of the per-trial quotients.  `parse` is not the fair denominator.\n"
    printf "cpu\tdoc\tbytes\tparse\tpw\tpwc\tps\trp\trpc%s\n", (noevent ? "\trpn\trpn/ps" : "")
  }
  $2 == "GATE" {
    if ($4 != "pass") { printf "FAIL: gate %s/%s %s\n", $1, $3, $4 > "/dev/stderr"; bad = 1 }
    next
  }
  $2 == "ROW" {
    cpu = $1; doc = $3; key = cpu SUBSEP doc
    bytes[key] = $4; arm = $5; t = $6 + 0; ns = $7
    if (!(key in seen)) { seen[key] = 1; order[++n] = key }
    A[arm] = 1
    if ((key SUBSEP arm SUBSEP t) in V) {
      printf "FAIL: %s/%s trial %d twice\n", key, arm, t > "/dev/stderr"; bad = 1
    }
    V[key SUBSEP arm SUBSEP t] = ns
    next
  }
  END {
    narm = 0; for (a in A) narm++
    want = 6 + (noevent ? 1 : 0)
    if (narm != want) { printf "FAIL: %d arm(s), not %d\n", narm, want > "/dev/stderr"; bad = 1 }
    for (k = 1; k <= n; k++) {
      key = order[k]; split(key, p, SUBSEP); cpu = p[1]; doc = p[2]
      for (a in A) for (ti = 0; ti < trials; ti++) {
        if (!((key SUBSEP a SUBSEP ti) in V)) {
          printf "FAIL: %s has no %s trial %d\n", key, a, ti > "/dev/stderr"; bad = 1
        }
      }
      for (ti = 0; ti < trials; ti++) {
        q[ti] = 0
        if (noevent && ((key SUBSEP "ps" SUBSEP ti) in V) &&
            ((key SUBSEP "rpn" SUBSEP ti) in V)) {
          pns = V[key SUBSEP "ps" SUBSEP ti]
          if (pns > 0) q[ti] = V[key SUBSEP "rpn" SUBSEP ti] / pns
        }
      }
      line = ""
      split("parse pw pwc ps rp rpc", arms, " ")
      for (ai = 1; ai <= 6; ai++) {
        a = arms[ai]; m = 0
        for (ti = 0; ti < trials; ti++) s[++m] = V[key SUBSEP a SUBSEP ti] + 0
        sortn(s, m); line = line "\t" sprintf("%.0f", med(s, m)); split("", s)
      }
      if (noevent) {
        m = 0; for (ti = 0; ti < trials; ti++) s[++m] = V[key SUBSEP "rpn" SUBSEP ti] + 0
        sortn(s, m); rm = med(s, m); split("", s)
        m = 0; for (ti = 0; ti < trials; ti++) s[++m] = q[ti]
        sortn(s, m); qm = med(s, m); split("", s)
        line = line "\t" sprintf("%.0f", rm) "\t" sprintf("%.4f", qm)
        Q[key] = qm
        canon = (doc ~ /^syn-/)
        N++; if (!canon) N148++
        if (qm < 1.0) { F++; if (!canon) F148++ }
        else if (qm <= 1.10) { B++; if (!canon) B148++ }
        else { O++; if (!canon) O148++ }
      }
      printf "%s\t%s\t%d%s\n", cpu, doc, bytes[key], line
    }
    if (bad) exit 1
    if (noevent) {
      m = 0; for (k in Q) s[++m] = Q[k]
      sortn(s, m); qmed = med(s, m)
      printf "\n## the consumer boundary (rpn/ps; median of per-document within-trial quotients)\n"
      printf "  median quotient over %d documents: %.4f\n", N, qmed
      printf "  faster (<1.0): %d/%d; in band [1.0,1.10]: %d/%d; over 10%%: %d/%d\n", \
        F, N, B, N, O, N
      printf "  the 148 heterogeneous documents: faster %d/%d; in band %d/%d; over %d/%d\n", \
        F148, N148, B148, N148, O148, N148
      printf "  majority-faster (strictly faster on more than half): %s (denominator %d)\n", \
        (F * 2 > N ? "MET" : "NOT MET"), N
    } else {
      printf "\n## the no-event arm is absent: this run builds the certified set only and\n"
      printf "## measures no consumer-boundary row.  Link it with FAIR_NOEVENT=1.\n"
    }
  }
' "$raw" > "$work/per-document.tsv"
agg=$?
if [ "$agg" -ne 0 ]; then cat "$work/per-document.tsv" >&2; exit 1; fi

cat "$work/per-document.tsv"

printf '\nrows: %s\n' "$raw"
printf 'per-document table: %s\n' "$work/per-document.tsv"
exit 0
