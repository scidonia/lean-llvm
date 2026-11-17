#!/usr/bin/env bash
# The route's cost on the units harness's corpus.
#
#   nix develop -c bash tests/json-units-bench/bench.sh      # corpus + units floor
#   TIMING=1 nix develop -c bash probes/json/route/build.sh  # the stage instrument
#   nix develop -c bash probes/json/route/bench-corpus.sh
#
# Corpus.  The documents `tests/json-units-bench/bench.sh` generates, under
# `tests/json-units-bench/build/corpus`: the tiled route documents
# (`route-s1-64k`, `route-u8-64k`), and the synthetic `syn-{dense,strings,utf8}`
# documents at 65,536 and 4,194,304 bytes from that harness's seed.  This script
# generates nothing of its own, so the two measurements describe the same bytes.
#
# Instrument.  The route's own `--stages` and `--consume` modes: the stage split
# is the code the route runs, and the consumer row is the caller's reader.  The
# stage rows need a `TIMING=1` build; the consumer rows do not, but the frozen
# object must be one build for the two to describe one artifact.
#
# Discipline.  `BENCH_TRIALS` trials of `BENCH_REPS` repetitions per document,
# each trial pinned with `taskset` to one CPU from `BENCH_CPUS`, and the summary
# reports the trial medians' median, their min and max, and the median of the
# within-row p90-p10 spread -- the units harness's own row shape.
#
# What the rows mean.  A document the route's admission admits takes the fast
# path and the object runs; its row carries `path=fast` and the stage split.  A
# document the domain does not admit takes the fallback: the reference parser
# answers it, the object is not called, and the row carries `path=fallback`, its
# refusal (`door`), and the admission stage alone.  The 4 MiB documents are of
# that class because the route's input bound is one mebibyte
# (`LeanLLVM.JSON.Limits.default`), which is a property of this route rather
# than of the units: the units' rows measure 4 MiB, the route's rows record that
# it refuses them.
set -uo pipefail
export LC_ALL=C

repo=$(cd "$(dirname "$0")/../../.." && pwd)
work=${BENCH_DIR:-$repo/tests/json-units-bench/build}
corpus=$work/corpus
bin=$repo/probes/json/route/build/leanllvm-json-route
cpus=${BENCH_CPUS:-"0 4"}
trials=${BENCH_TRIALS:-3}
reps=${BENCH_REPS:-21}
out=${BENCH_OUT:-$work/route}

die() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

[ -d "$corpus" ] || die "absent corpus '$corpus'; run tests/json-units-bench/bench.sh first"
[ -x "$bin" ] || die "absent route binary '$bin'; run probes/json/route/build.sh first"
command -v taskset >/dev/null 2>&1 || die "no taskset on PATH; run this under nix develop"
[ -n "$out" ] && [ "$out" != "/" ] || die "refusing output directory '$out'"
rm -rf "$out"
mkdir -p "$out" || die "cannot create $out"

docs=()
for f in "$corpus"/*.json; do
  [ -f "$f" ] || die "no documents under $corpus"
  docs+=("$f")
done

# The stage instrument is a compile-time gate: an ordinary build refuses to
# print a row, and a script that took that refusal as a measurement would report
# zeros.  Probe the documents once, and require at least one fast-path row with
# a staging interval before the sweep.
instrumented=0
for f in "${docs[@]}"; do
  probe=$("$bin" --stages "$f" 1 2>&1)
  case $probe in
    *"path=fast"*"staging_ns="[0-9]*) instrumented=1; break ;;
  esac
done
[ "$instrumented" = 1 ] ||
  die "the route binary printed no fast-path stage row; build it with TIMING=1"

printf 'command: nix develop -c bash probes/json/route/bench-corpus.sh\n'
printf 'binary: %s\n' "$bin"
printf 'binary sha256: %s\n' "$(sha256sum "$bin" | cut -d' ' -f1)"
printf 'corpus: %s\n' "$corpus"
printf 'host: %s; cpu: %s\n' "$(uname -srm)" \
  "$(awk -F: '/^model name/ { sub(/^ /, "", $2); print $2; exit }' /proc/cpuinfo)"
printf 'cpus: %s; trials: %s; reps: %s\n' "$cpus" "$trials" "$reps"
printf 'governor: %s\n\n' \
  "$(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null || echo unknown)"

printf '%-18s %10s %s\n' file bytes sha256
for f in "${docs[@]}"; do
  printf '%-18s %10s %s\n' "$(basename "$f")" "$(wc -c < "$f")" \
    "$(sha256sum "$f" | cut -d' ' -f1)"
done
printf '\n'

status=0
for cpu in $cpus; do
  for trial in $(seq 1 "$trials"); do
    for f in "${docs[@]}"; do
      name=$(basename "$f" .json)
      # One file per mode: the modes print their row on stderr and, for a fast
      # path, the observation on stdout, so the two are merged and the row is
      # the line the summary reads.
      set +e
      # The row is written on stderr and the fast path's observation on stdout;
      # the observation is the last repetition's printed output, not a measure-
      # ment, so it is discarded rather than kept.
      taskset -c "$cpu" "$bin" --stages "$f" "$reps" \
        >/dev/null 2>"$out/stages.$cpu.$trial.$name.log"
      st=$?
      taskset -c "$cpu" "$bin" --consume "$f" "$reps" \
        >/dev/null 2>"$out/consume.$cpu.$trial.$name.log"
      ct=$?
      set -e
      # The modes do not name the device or the trial in their rows; the
      # harness knows both, so it writes them into the row rather than letting
      # a reader infer them from the file name.
      sed -i "s/^row /row cpu=$cpu trial=$trial /" \
        "$out/stages.$cpu.$trial.$name.log" "$out/consume.$cpu.$trial.$name.log"
      # A document the domain refuses never reaches the object, so the stage
      # mode's refusal exit (2) and the consumer mode's are the route's
      # documented refusal, not a failed measurement.  A fast row that is
      # missing, or a mode that exited nonzero on an admitted document, is a
      # failure.
      if grep -q '^row .*path=fast' "$out/stages.$cpu.$trial.$name.log"; then
        [ "$st" = 0 ] || { printf 'FAIL: --stages %s exited %s with a fast row\n' "$name" "$st" >&2; status=1; }
        case $ct in 0|5) : ;; *) printf 'FAIL: --consume %s exited %s on a fast row\n' "$name" "$ct" >&2; status=1 ;; esac
      else
        case $st in 0|2) : ;; *) printf 'FAIL: --stages %s exited %s without a fast row\n' "$name" "$st" >&2; status=1 ;; esac
        case $ct in 0|2|5) : ;; *) printf 'FAIL: --consume %s exited %s\n' "$name" "$ct" >&2; status=1 ;; esac
      fi
    done
  done
done

# The stage rows, one per trial: the per-trial medians, verbatim.
printf '## the stage rows (unit: ns, medians of %s reps; one row per document, cpu and trial)\n' "$reps"
grep -h '^row ' "$out"/stages.*.log
printf '\n'

# The summary: one row per (cpu, document), from the trials' medians.
printf '## the summary (unit: ns; the medians of the trial medians; ns/byte at the document; spread is the median within-row (p90-p10)/median, percent)\n'
awk '
  function kv(   i, a) { delete f; for (i = 2; i <= NF; i++) { split($i, a, "="); f[a[1]] = a[2] } }
  function num(x) { return (x == "-" || x == "" ? -1 : x + 0) }
  function sortn(a, n,   i, j, t) { for (i = 2; i <= n; i++) { t = a[i]; for (j = i - 1; j >= 1 && a[j] > t; j--) a[j+1] = a[j]; a[j+1] = t } }
  function med(a, n) { if (n % 2) return a[(n+1)/2]; return 0.5 * (a[n/2] + a[n/2+1]) }
  $1 == "row" {
    kv()
    key = f["cpu"] SUBSEP f["doc"]
    if (!(key in n)) { n[key] = 0; order[++nk] = key }
    t = ++n[key]
    total[key, t] = num(f["total_ns"])
    staging[key, t] = num(f["staging_ns"])
    copyin[key, t] = num(f["copyin_ns"])
    native[key, t] = num(f["native_ns"])
    copyout[key, t] = num(f["copyout_ns"])
    outcome[key, t] = num(f["outcome_ns"])
    admit[key, t] = num(f["admission_ns"])
    size[key] = f["size"] + 0
    path[key] = f["path"]
    ndst[key, t] = f["ndst"]
    nev[key, t] = f["nev"]
    rt = f["rep_total_ns"]; gsub(/^\[|\]$/, "", rt)
    m = split(rt, rs, ",")
    sortn(rs, m)
    spread[key, t] = (med(rs, m) > 0 ? 100.0 * (rs[int((m-1)*0.9)+1] - rs[int((m-1)*0.1)+1]) / med(rs, m) : 0)
    next
  }
  END {
    printf "%-6s %-18s %8s %-9s %10s %10s %12s %8s %10s %12s %9s %7s\n",
      "cpu", "doc", "bytes", "path", "admission", "staging", "call+copyin", "copyout", "outcome", "total", "ns/byte", "spread"
    for (k = 1; k <= nk; k++) {
      key = order[k]; m = n[key]
      for (i = 1; i <= m; i++) {
        ta[i] = total[key, i]; ad[i] = admit[key, i]; st[i] = staging[key, i]
        ci[i] = copyin[key, i]; na[i] = native[key, i]; co[i] = copyout[key, i]
        ou[i] = outcome[key, i]; sp[i] = spread[key, i]
      }
      sortn(ta, m); sortn(ad, m); sortn(st, m); sortn(ci, m); sortn(na, m)
      sortn(co, m); sortn(ou, m); sortn(sp, m)
      split(key, p, SUBSEP)
      printf "%-6s %-18s %8d %-9s %10d %10s %12s %8s %10s %12d %9.2f %7.1f\n",
        p[1], p[2], size[key], path[key], med(ad, m),
        (st[m] < 0 ? "-" : sprintf("%d", med(st, m))),
        (ci[m] < 0 ? "-" : sprintf("%d", med(ci, m) + med(na, m))),
        (co[m] < 0 ? "-" : sprintf("%d", med(co, m))),
        (ou[m] < 0 ? "-" : sprintf("%d", med(ou, m))), med(ta, m),
        med(ta, m) / size[key], med(sp, m)
    }
  }
' <(sed 's/, /,/g' "$out"/stages.*.log)
printf '\n'

# The consumer rows: the fast path read without printing.  A `verdict=0` row is
# the object's own refusal: its event stream is empty and no token is owed.
printf '## the consumer rows (unit: ns, medians of %s reps; tokens = the event stream decoded record by record)\n' "$reps"
grep -h '^row ' "$out"/consume.*.log
printf '\n'

if [ "$status" -ne 0 ]; then
  printf 'FAIL: a row did not complete; the summary above is over the rows that did\n' >&2
  exit 1
fi
printf 'ok: %s document(s) x %s cpu(s) x %s trial(s) at %s repetition(s)\n' \
  "${#docs[@]}" "$(printf '%s' "$cpus" | wc -w)" "$trials" "$reps"
printf 'note: the stage rows are a TIMING=1 build; the two clock reads in copy-in and two in copy-out are inside those stages\n'
