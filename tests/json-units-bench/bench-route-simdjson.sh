#!/usr/bin/env bash
# The composed route against simdjson 5.0.5's stage 1 and full parse, over the
# corpus the three proved stage-1 units are measured on.
#
#   nix develop -c bash tests/json-units-bench/bench-route-simdjson.sh
#
# What is measured.  Two arms, both pinned to one CPU, over the same documents,
# in the same trial, alternating which arm goes first so a drift inside the
# trial cancels in the quotient:
#
#   route     the composed route from this tree, `leanllvm-json-route
#             --consume-events <doc> <reps>`.  The row's fields are its own
#             stages: `admission_ns` (the two-phase domain decision), `staging_ns`,
#             `route_ns` (the native call `leanllvm_json_pipeline`), and
#             `consume_values_ns` (a consumer that materialises one event record
#             per token).  The document read is `read_ns` and is in no stage.
#   simdjson  `simdjson-baseline --reps <reps> --doc <name>=<path>...`, built
#             here at the units' compiler line from `simdjson-baseline.cc`:
#             `stage1` (one classification/structural-index pass), `parse`
#             (one on-demand `iterate` plus the full value traversal), and `pad`
#             (one `padded_string` staging).
#
# What each row is work-wise, and what is not like-for-like.  `route_ns` is not
# a stage-1 row.  `leanllvm_json_pipeline` runs classification, the entry
# emitter, escape positions, UTF-8 validity and stage 2 in one call
# (`kernel/json/pipeline.c` has no stage-1 stop), so `native ÷ stage1` is an
# **upper bound**: the whole composed pipeline's cost against the cost of
# simdjson's first stage.  It is not a stage ratio and is labelled so in the
# report.  The like-for-like pair is `route_ns` against `parse`, the two full
# parses of the same bytes, and `staging_ns` against `pad`, the two stagings.
# The end-to-end pair is admission + staging + native + the consumer's read
# against `pad + parse`; the route's admission is work simdjson does not do and
# the row states it rather than folding it away.  The stage-for-stage figure for
# stage 1 is not this harness's subject and is not re-measured here: it is the
# units' composite against `stage1` in `docs/json-pipeline-performance.md`
# §"The simdjson row, measured".
#
# Corpus and domain.  The eight documents of `tests/json-units-bench/
# transcript.txt`, byte for byte: five at 65,536 bytes and three at 4,194,304,
# from `gen.c` at seed 0x243F6A8885A308D3 and the route corpora tiled.  Every
# file is checked against the size and sha256 that transcript records.  The
# route admits the five 65,536-byte documents; the three 4 MiB documents are
# refused at admission because the route's input bound is one mebibyte
# (`LeanLLVM.JSON.Limits.default`), so they have no route stage to compare and
# are recorded as refusals, not timed.  simdjson is measured on all eight.
#
# Discipline.  `taskset` pins each process to one CPU from `BENCH_CPUS`; each
# document is warmed once outside the clock before its trial; each row is
# `BENCH_REPS` repetitions; the whole pair runs `BENCH_TRIALS` times per CPU.
# The report gives the median of the trial medians with their minimum and
# maximum, and each quotient as the median of the per-trial quotients with its
# minimum and maximum.  The simdjson arm calibrates its core clock before every
# row; the route's `--consume-events` row carries no clock, so GB/s and the quotients
# are wall-time figures and no cycles-per-byte figure is derived for the route.
#
# Provenance.  The simdjson dev output and library are the realised nix builds
# of nixpkgs' 5.0.5:
#
#   nix build --no-link --print-out-paths 'nixpkgs#simdjson.dev'
#   nix build --no-link --print-out-paths 'nixpkgs#simdjson'
#
# A store that has garbage-collected them refuses to run until they are
# realised again; this script does not fetch, it verifies.  The route binary is
# the one `probes/json/route/build.sh` produces; this script does not build it
# (the link needs Lean) and refuses if it is absent.
#
# Environment: BENCH_CPUS (default "0 4"), BENCH_TRIALS (3), BENCH_REPS (51),
# BENCH_DIR, BENCH_CORPUS, BENCH_CXX (clang++), ROUTE_BIN, SIMDJSON_DEV,
# SIMDJSON_LIB.
#
# Exit status: 0 when every row was measured and the gates held, 1 when a gate
# failed, 3 when an arm is not usable (absent compiler, store output, corpus
# document, route binary or `taskset`).
set -uo pipefail
export LC_ALL=C

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
work=${BENCH_DIR:-$repo/tests/json-units-bench/build-route-simdjson}
bin=$work/bin
cpus=${BENCH_CPUS:-"0 4"}
ncpu=$(set -- $cpus; echo $#)
trials=${BENCH_TRIALS:-3}
reps=${BENCH_REPS:-51}
cxx=${BENCH_CXX:-clang++}
dev=${SIMDJSON_DEV:-/nix/store/m2i8165bayxxgzj3fbvdg6gihz6na93d-simdjson-5.0.5-dev}
lib=${SIMDJSON_LIB:-/nix/store/jglxdk9y0yfk3mc9dbr675pfmv42a89y-simdjson-5.0.5}
route=${ROUTE_BIN:-$repo/probes/json/route/build/leanllvm-json-route}

die() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

cxxflags=(-O3 -march=x86-64-v3 -mpclmul -std=c++17 -falign-loops=64 -falign-functions=64)

[ -n "$work" ] && [ "$work" != "/" ] || die "refusing work directory '$work'"
[ -f "$here/simdjson-baseline.cc" ] || die "absent: tests/json-units-bench/simdjson-baseline.cc"
command -v "$cxx" >/dev/null 2>&1 || die "no $cxx on PATH; run this under nix develop"
command -v taskset >/dev/null 2>&1 || die "no taskset on PATH"
[ -x "$route" ] || die "absent route binary: $route
  build it with: nix develop -c bash probes/json/route/build.sh"

header=$dev/include/simdjson.h
solib=$lib/lib/libsimdjson.so.34.0.0
[ -f "$header" ] || die "absent: $header
  realise it with: nix build --no-link --print-out-paths 'nixpkgs#simdjson.dev'"
[ -f "$solib" ] || die "absent: $solib
  realise it with: nix build --no-link --print-out-paths 'nixpkgs#simdjson'"

ver=$(sed -n 's/^#define SIMDJSON_VERSION "\(.*\)"/\1/p' "$header" | head -1)
[ "$ver" = "5.0.5" ] || die "header is simdjson '$ver', not 5.0.5"

# --- Corpus -----------------------------------------------------------------
# Size and sha256 as `tests/json-units-bench/transcript.txt` records them.
expected="route-s1-64k.json 65536 41f918853d55dad0e05d3ec03682e037925759031632f045a755db5a5173535c
route-u8-64k.json 65536 d14a6a6842610aaaf2bdd13a292730f156cf5c6c5724eddae93effa9b697f18c
syn-dense-4m.json 4194304 243e8f36f14e1acb5694d8c873c18f46a86a073c768944abaa94cfb57883accd
syn-dense-64k.json 65536 3d9e0237ec66adb2d77848a24f1998fa4b56b4dbe77a11431b02176fcd162995
syn-strings-4m.json 4194304 3ce71d559eef1d11e83272b999fe944f49cb5bef656b5ec863044ed8f1b5cd27
syn-strings-64k.json 65536 bd007090d7a5ab09a1fc69c0b96879f101dbf8b3f13a300d7d3e46127d26fb12
syn-utf8-4m.json 4194304 2091fc28bf071e8a7311f43754d8bb82cb2ddef54360be8570c46b7a94d298f2
syn-utf8-64k.json 65536 f95f4aeaac083d5d97ff98f9ad6aa09e4ed8c905d89e1bf3a3177179533400a4"

# The units' corpus order, so a later reader can line the rows up with
# `transcript.txt` without re-sorting.
names=(route-s1-64k route-u8-64k syn-dense-4m syn-dense-64k \
       syn-strings-4m syn-strings-64k syn-utf8-4m syn-utf8-64k)
admitted=(route-s1-64k route-u8-64k syn-dense-64k syn-strings-64k syn-utf8-64k)

corpus=${BENCH_CORPUS:-$repo/tests/json-units-bench/build/corpus}
[ -d "$corpus" ] || die "absent corpus '$corpus'
  generate it with: nix develop -c bash tests/json-units-bench/bench.sh
  or name another directory with BENCH_CORPUS"

corpus_ok() {
  local name size sha
  while read -r name size sha; do
    [ -n "$name" ] || continue
    [ -f "$corpus/$name" ] || { printf 'SETUP: absent %s\n' "$corpus/$name" >&2; return 1; }
    [ "$(stat -c %s "$corpus/$name")" = "$size" ] ||
      { printf 'SETUP: %s is not %s bytes\n' "$corpus/$name" "$size" >&2; return 1; }
    [ "$(sha256sum "$corpus/$name" | cut -d' ' -f1)" = "$sha" ] ||
      { printf 'SETUP: %s does not hash %s\n' "$corpus/$name" "$sha" >&2; return 1; }
  done <<<"$expected"
}
corpus_ok || die "BENCH_CORPUS does not hold the units' eight documents"

[ -n "$work" ] && [ "$work" != "/" ] || die "refusing work directory '$work'"
rm -rf "$work"
mkdir -p "$bin" || die "cannot create $work"

# --- Build ------------------------------------------------------------------
"$cxx" "${cxxflags[@]}" -I "$dev/include" "$here/simdjson-baseline.cc" \
  -L "$lib/lib" -Wl,-rpath,"$lib/lib" -lsimdjson -o "$bin/simdjson-baseline" \
  2>"$work/simdjson.cc.err" ||
  { cat "$work/simdjson.cc.err" >&2; die "simdjson-baseline did not build"; }

# --- Host and build record ---------------------------------------------------
printf 'command: nix develop -c bash tests/json-units-bench/bench-route-simdjson.sh\n'
printf 'harness: bench-route-simdjson.sh sha256=%s\n' "$(sha256sum "$0" | cut -d' ' -f1)"
printf 'baseline source: simdjson-baseline.cc sha256=%s\n' \
  "$(sha256sum "$here/simdjson-baseline.cc" | cut -d' ' -f1)"
printf 'simdjson: %s (header); dev: %s\n' "$ver" "$dev"
printf 'simdjson lib: %s; %s sha256=%s\n' "$lib" "$(basename "$solib")" \
  "$(sha256sum "$solib" | cut -d' ' -f1)"
printf 'header: simdjson.h sha256=%s\n' "$(sha256sum "$header" | cut -d' ' -f1)"
printf 'provenance: nix build --no-link --print-out-paths '\''nixpkgs#simdjson.dev'\''\n'
printf 'provenance: nix build --no-link --print-out-paths '\''nixpkgs#simdjson'\''\n'
printf 'compiler: %s (%s)\n' "$cxx" "$("$cxx" --version | head -1)"
printf 'harness flags: %s\n' "${cxxflags[*]}"
printf 'library note: the shared library is the realised nix build, not recompiled at\n'
printf '              these flags; stage1 is the library'"'"'s code, the traversal in\n'
printf '              parse is compiled here at the flags above.\n'
printf 'route binary: %s\n' "$route"
printf 'route sha256: %s; mtime: %s\n' "$(sha256sum "$route" | cut -d' ' -f1)" \
  "$(stat -c %y "$route")"
printf 'route note: the binary is `probes/json/route/build.sh`'"'"'s default build\n'
printf '            (TIMING=0); `--stages` needs TIMING=1 and is not used, so the\n'
printf '            adapter'"'"'s copy-in/copy-out slots are absent and the route rows\n'
printf '            carry its own staging, native and consumer intervals.\n'
printf 'host: %s\n' "$(uname -srm)"
printf 'cpu: %s\n' "$(awk -F: '/^model name/ { sub(/^ /, "", $2); print $2; exit }' /proc/cpuinfo)"
printf 'cpus online: %s; pinned to: %s\n' "$(nproc)" "$cpus"
printf 'scaling governor: %s\n' "$(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null || echo unknown)"
printf 'load average at start: %s\n' "$(cat /proc/loadavg)"
printf 'trials: %s; reps in every row: %s\n' "$trials" "$reps"
for c in $cpus; do
  printf 'cpu%s Cpus_allowed_list under the pin: %s\n' "$c" \
    "$(taskset -c "$c" sh -c 'grep -m1 Cpus_allowed_list /proc/self/status' 2>/dev/null || echo '?')"
done
printf '\ncorpus: %s\n' "$corpus"
printf '%-18s %10s %s\n' file bytes sha256
for name in "${names[@]}"; do
  printf '%-18s %10s %s\n' "$name.json" "$(wc -c <"$corpus/$name.json")" \
    "$(sha256sum "$corpus/$name.json" | cut -d' ' -f1)"
done
printf '\n'

# --- The refusal rows --------------------------------------------------------
# The route's domain refuses the 4 MiB documents before the pipeline is called.
# One probe each records the refusal; they are not timed and not compared.
for name in "${names[@]}"; do
  case " ${admitted[*]} " in *" $name "*) continue ;; esac
  out=$(taskset -c "${cpus%% *}" "$route" --consume-events "$corpus/$name.json" 1 2>&1)
  st=$?
  printf 'refusal %s exit=%s %s\n' "$name" "$st" "$out"
  case $out in
    *"path=fallback"*) : ;;
    *) printf 'FAIL: %s was not refused by the route\n' "$name" >&2; exit 1 ;;
  esac
done
printf '\n'

# --- Measure ----------------------------------------------------------------
rt=$work/route.tsv
sj=$work/simdjson.tsv
: >"$rt"
: >"$sj"

rfield() { # <row> <key>
  local row=$1 k=$2 v
  v=$(printf '%s\n' "$row" | sed -n "s/^.*[[:space:]]${k}=\([^[:space:]]*\).*$/\1/p")
  printf '%s' "${v:--}"
}

for cpu in $cpus; do
  for trial in $(seq 1 "$trials"); do
    printf 'trial cpu=%s trial=%s/%s\n' "$cpu" "$trial" "$trials"
    # Alternate which arm goes first: an odd trial measures the route first, an
    # even trial simdjson first, and both are in the same trial on the same CPU.
    if [ $((trial % 2)) -eq 1 ]; then order="route sj"; else order="sj route"; fi
    for arm in $order; do
      if [ "$arm" = route ]; then
        for name in "${admitted[@]}"; do
          # One warm pass per document, outside the clock of the measured row.
          taskset -c "$cpu" "$route" --consume-events "$corpus/$name.json" 1 \
            >/dev/null 2>&1
          out=$(taskset -c "$cpu" "$route" --consume-events "$corpus/$name.json" "$reps" 2>&1)
          st=$?
          printf '%s\n' "$out" >"$work/route.$cpu.$trial.$name.out"
          if [ "$st" -ne 0 ]; then
            printf 'FAIL: the route exited %s on %s cpu %s trial %s\n' \
              "$st" "$name" "$cpu" "$trial" >&2
            printf '%s\n' "$out" >&2
            exit 1
          fi
          case $out in
            row\ *) : ;;
            *) printf 'FAIL: the route printed no row for %s on cpu %s trial %s\n' \
                 "$name" "$cpu" "$trial" >&2; exit 1 ;;
          esac
          printf 'route cpu=%s trial=%s doc=%s bytes=%s path=%s verdict=%s admission=%s staging=%s native=%s consume=%s tokens=%s values=%s foldsum=%s valuessum=%s\n' \
            "$cpu" "$trial" "$name" "$(rfield "$out" size)" "$(rfield "$out" path)" \
            "$(rfield "$out" verdict)" "$(rfield "$out" admission_ns)" \
            "$(rfield "$out" staging_ns)" "$(rfield "$out" route_ns)" \
            "$(rfield "$out" consume_values_ns)" "$(rfield "$out" tokens)" \
            "$(rfield "$out" values)" "$(rfield "$out" foldsum)" \
            "$(rfield "$out" valuessum)" >>"$rt"
        done
      else
        docargs=()
        for name in "${names[@]}"; do
          docargs+=(--doc "$name=$corpus/$name.json")
        done
        out=$(taskset -c "$cpu" "$bin/simdjson-baseline" --reps "$reps" \
              "${docargs[@]}" 2>"$work/simdjson.$cpu.$trial.err")
        st=$?
        printf '%s\n' "$out" >>"$work/simdjson.$cpu.$trial.out"
        if [ "$st" -ne 0 ]; then
          printf 'FAIL: simdjson-baseline exited %s on cpu %s trial %s\n' \
            "$st" "$cpu" "$trial" >&2
          [ -s "$work/simdjson.$cpu.$trial.err" ] &&
            cat "$work/simdjson.$cpu.$trial.err" >&2
          exit 1
        fi
        observed=$(awk '$1 == "instrument" {
            for (i = 2; i <= NF; i++) { split($i, a, "="); if (a[1] == "cpu") print a[2] }
          }' <<<"$out")
        if [ "$observed" != "$cpu" ]; then
          printf 'FAIL: pin asked for cpu%s, simdjson observed cpu%s\n' \
            "$cpu" "$observed" >&2
          exit 1
        fi
        awk -v cpu="$cpu" -v trial="$trial" '
          $1 == "row" {
            for (i = 2; i <= NF; i++) { split($i, a, "="); f[a[1]] = a[2] }
            printf "sj cpu=%s trial=%s doc=%s arm=%s bytes=%s ns=%s status=%s checksum=%s ghz=%s\n",
              cpu, trial, f["doc"], f["arm"], f["bytes"], f["median_ns"],
              f["status"], f["checksum"], f["core_ghz"]
            delete f
          }' <<<"$out" >>"$sj"
      fi
    done
  done
done
printf '\nload average after the sweep: %s\n\n' "$(cat /proc/loadavg)"

# --- Aggregate --------------------------------------------------------------
# One summary per (cpu, document, arm): the median of the trial medians and
# their minimum and maximum.  Every quotient is taken inside one trial on the
# same CPU, then reduced across the trials, so a drift between trials does not
# become a quotient.  Checksums and identities are asserted before anything is
# reported.
awk -v trials="$trials" -v ncpu="$ncpu" '
  function kv(   i, a) { delete F; for (i = 2; i <= NF; i++) { split($i, a, "="); F[a[1]] = a[2] } }
  function sortn(a, n,   i, j, t) { for (i = 2; i <= n; i++) { t = a[i]; for (j = i - 1; j >= 1 && a[j] > t; j--) a[j+1] = a[j]; a[j+1] = t } }
  function med(a, n) { if (n % 2) return a[(n + 1) / 2]; return 0.5 * (a[n / 2] + a[n / 2 + 1]) }
  function gbps(ns, bytes) { return (ns > 0 ? bytes / ns : 0) }
  $1 == "route" {
    kv()
    key = F["cpu"] SUBSEP F["doc"]
    if (!(key in rseen)) { rorder[++nr] = key; rseen[key] = 1 }
    t = F["trial"] + 0
    if (t > rmax[key]) rmax[key] = t
    R[key, t] = F["native"] + 0
    ADM[key, t] = F["admission"] + 0
    STG[key, t] = F["staging"] + 0
    CON[key, t] = F["consume"] + 0
    E2E[key, t] = ADM[key, t] + STG[key, t] + R[key, t] + CON[key, t]
    RBYTES[key] = F["bytes"] + 0
    RPATH[key] = F["path"]
    RVER[key] = F["verdict"]
    RID[key, F["path"] "|" F["verdict"] "|" F["tokens"] "|" F["values"] "|" F["foldsum"] "|" F["valuessum"]] = 1
    next
  }
  $1 == "sj" {
    kv()
    key = F["cpu"] SUBSEP F["doc"]
    if (!(key in sseen)) { sorder[++ns] = key; sseen[key] = 1 }
    t = F["trial"] + 0
    if (t > smax[key]) smax[key] = t
    S[key, F["arm"], t] = F["ns"] + 0
    SSTAT[key, F["arm"]] = F["status"]
    SBYTES[key] = F["bytes"] + 0
    SID[key, F["arm"], F["status"] "|" F["checksum"]] = 1
    ARMS[F["arm"]] = 1
    GHZ[key, t] = F["ghz"] + 0
    next
  }
  END {
    bad = 0
    narm = 0; for (a in ARMS) narm++
    if (narm != 3) {
      printf "FAIL: %d simdjson arm(s), not 3 (pad, stage1, parse)\n", narm > "/dev/stderr"
      bad = 1
    }
    if (nr != 5 * ncpu) {
      printf "FAIL: %d route (cpu, document) row(s), not 5 documents x %d CPU(s)\n", nr, ncpu > "/dev/stderr"
      bad = 1
    }
    if (ns != 8 * ncpu) {
      printf "FAIL: %d simdjson (cpu, document) row(s), not 8 documents x %d CPU(s)\n", ns, ncpu > "/dev/stderr"
      bad = 1
    }
    for (k = 1; k <= nr; k++) {
      key = rorder[k]
      if (rmax[key] != trials) {
        printf "FAIL: %s has %d route trial(s), not %d\n", key, rmax[key], trials > "/dev/stderr"
        bad = 1
      }
    }
    for (k = 1; k <= ns; k++) {
      key = sorder[k]
      if (smax[key] != trials) {
        printf "FAIL: %s has %d simdjson trial(s), not %d\n", key, smax[key], trials > "/dev/stderr"
        bad = 1
      }
    }
    # A route row must be the fast path on every trial and CPU, or there is no
    # stage to report; and every (cpu, document, arm) identity must be stable.
    for (k = 1; k <= nr; k++) {
      key = rorder[k]
      split(key, p, SUBSEP)
      if (RPATH[key] != "fast") {
        printf "FAIL: %s/%s is %s, not the fast path\n", p[1], p[2], RPATH[key] > "/dev/stderr"
        bad = 1
      }
      cnt = 0
      for (v in RID) {
        split(v, q, SUBSEP)
        if ((q[1] SUBSEP q[2]) == key) cnt++
      }
      if (cnt != 1) {
        printf "FAIL: %s/%s printed %d distinct path/verdict/token identities\n", p[1], p[2], cnt > "/dev/stderr"
        bad = 1
      }
    }
    for (v in SID) {
      split(v, q, SUBSEP)
      sub_key = q[1] SUBSEP q[2]
      delete cs
      for (w in SID) {
        split(w, z, SUBSEP)
        if ((z[1] SUBSEP z[2] SUBSEP z[3]) == (sub_key SUBSEP q[3])) cs[z[4]] = 1
      }
      cnt = 0; for (x in cs) cnt++
      if (cnt != 1) {
        printf "FAIL: %s/%s printed %d distinct status/checksum pairs\n", q[1], q[2], cnt > "/dev/stderr"
        bad = 1
      }
    }

    printf "## the composed route (unit: ns; median of the three trial medians, min-max of those medians)\n"
    printf "%-6s %-18s %8s %4s %7s %10s %10s %10s %12s %12s %9s %8s\n", \
      "cpu", "doc", "bytes", "path", "verdict", "admission", "staging", "native", "consume", "end2end", "ns/byte", "GB/s"
    for (k = 1; k <= nr; k++) {
      key = rorder[k]
      split(key, p, SUBSEP)
      m = rmax[key]
      for (i = 1; i <= m; i++) { na[i] = R[key, i]; ad[i] = ADM[key, i]; st[i] = STG[key, i]; cn[i] = CON[key, i]; e2[i] = E2E[key, i] }
      sortn(na, m); sortn(ad, m); sortn(st, m); sortn(cn, m); sortn(e2, m)
      printf "%-6s %-18s %8d %4s %7s %6d-%-6d %6d-%-6d %6d-%-6d %6d-%-6d %6d-%-6d %9.2f %8.3f\n", \
        p[1], p[2], RBYTES[key], RPATH[key], (RVER[key] == "1" ? "accept" : "refuse"), \
        ad[1], ad[m], st[1], st[m], \
        na[1], na[m], cn[1], cn[m], e2[1], e2[m], \
        med(e2, m) / RBYTES[key], gbps(med(e2, m), RBYTES[key])
    }

    printf "\n## simdjson 5.0.5 (same discipline; GB/s at the median of the trial medians)\n"
    printf "%-6s %-18s %-7s %8s %11s %12s %9s %8s %-8s\n", \
      "cpu", "doc", "arm", "bytes", "ns_median", "ns_min-max", "ns/byte", "GB/s", "status"
    for (k = 1; k <= ns; k++) {
      key = sorder[k]
      split(key, p, SUBSEP)
      m = smax[key]
      for (aa = 1; aa <= 3; aa++) {
        a = (aa == 1 ? "pad" : (aa == 2 ? "stage1" : "parse"))
        if (!((key SUBSEP a SUBSEP 1) in S)) continue
        for (i = 1; i <= m; i++) sv[i] = S[key, a, i]
        sortn(sv, m)
        stt = SSTAT[key, a]
        printf "%-6s %-18s %-7s %8d %11d %6d-%-6d %9.3f %8.3f %-8s\n", \
          p[1], p[2], a, SBYTES[key], med(sv, m), sv[1], sv[m], \
          med(sv, m) / SBYTES[key], gbps(med(sv, m), SBYTES[key]), stt
      }
    }

    printf "\n## the comparison (unit: a multiplier; per-trial quotients, median with min-max)\n"
    printf "Each quotient is one arm over the other inside one trial, both on the same CPU and\n"
    printf "bytes.  A value above 1 means the route costs more.  A cell is `-` when the\n"
    printf "simdjson arm it divides by is not `ok` for that document: a `rejected` stage 1 or\n"
    printf "a `refused` parse times an error, not the stage, and prices a different amount of\n"
    printf "work.\n\n"
    printf "%-6s %-18s %18s %16s %14s %20s %8s\n", \
      "cpu", "doc", "native/stage1", "native/parse", "staging/pad", "end2end/(pad+parse)", "route"
    for (k = 1; k <= nr; k++) {
      key = rorder[k]
      split(key, p, SUBSEP)
      m = rmax[key]
      n1 = 0; n2 = 0; n3 = 0; n4 = 0
      s1ok = (SSTAT[key, "stage1"] == "ok")
      spok = (SSTAT[key, "parse"] == "ok")
      for (i = 1; i <= m; i++) {
        s1 = S[key, "stage1", i]; sp = S[key, "parse", i]; pd = S[key, "pad", i]
        if (s1ok && s1 > 0 && R[key, i] > 0) r1[++n1] = R[key, i] / s1
        if (spok && sp > 0 && R[key, i] > 0) r2[++n2] = R[key, i] / sp
        if (pd > 0 && STG[key, i] > 0) r3[++n3] = STG[key, i] / pd
        if (spok && pd + sp > 0 && E2E[key, i] > 0) r4[++n4] = E2E[key, i] / (pd + sp)
      }
      sortn(r1, n1); sortn(r2, n2); sortn(r3, n3); sortn(r4, n4)
      printf "%-6s %-18s", p[1], p[2]
      printf " %s", (n1 ? sprintf("%.2f (%.2f-%.2f)", med(r1, n1), r1[1], r1[n1]) : "-")
      printf " %s", (n2 ? sprintf("%.2f (%.2f-%.2f)", med(r2, n2), r2[1], r2[n2]) : "-")
      printf " %s", (n3 ? sprintf("%.2f (%.2f-%.2f)", med(r3, n3), r3[1], r3[n3]) : "-")
      printf " %s", (n4 ? sprintf("%.2f (%.2f-%.2f)", med(r4, n4), r4[1], r4[n4]) : "-")
      printf " %8s\n", (RVER[key] == "1" ? "accept" : "refuse")
      split("", r1); split("", r2); split("", r3); split("", r4)
    }
    exit bad
  }
' "$rt" "$sj"
status=$?
if [ "$status" -ne 0 ]; then
  printf 'FAIL: the aggregation gates did not hold\n' >&2
  exit 1
fi

printf '\n'
printf 'ok: %d document(s) x %d CPU(s) x %s trial(s) at %s repetition(s) for the route;\n' \
  5 "$ncpu" "$trials" "$reps"
printf '    the same documents and discipline for simdjson, with the three 4 MiB\n'
printf '    documents refused at the route'"'"'s admission and recorded above\n'
printf 'note: `native/stage1` is an upper bound, not a stage ratio: the route'"'"'s native\n'
printf '      call runs stage 1 and stage 2 in one function\n'
printf 'note: `native/parse` is the like-for-like full-parse pair; `parse` rows whose\n'
printf '      status is `refused` time a refusal and are not full-parse figures, so the\n'
printf '      quotient cells that divide by them are `-`\n'
printf 'note: a route row whose verdict is `refuse` (the route corpora, which simdjson\n'
printf '      also refuses) prices the pipeline up to its refusal, not an accepted run;\n'
printf '      the route column of the comparison states it\n'
printf 'note: the route rows carry no calibrated core clock, so GB/s is wall time per\n'
printf '      byte and no cycles-per-byte figure is derived for them\n'
