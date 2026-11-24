#!/usr/bin/env bash
# Contract check for the fair comparison's corpus, gates and report.
#
#   nix develop -c bash tests/json-fair/check.sh
#
# Three properties are asserted, each against an external actor, and each with
# an affirmative control in the same run:
#
#   NF1  `tests/json-fair/generate.sh` regenerates the 151-document corpus into
#        a private directory; every manifest row's size and sha256 equal the
#        generated file's, the document set is the manifest's, and the count is
#        148 `hetero-*` plus 3 `syn-*`.  One byte of one document is changed in
#        a copy and the same `--verify` detector must reject it; the unchanged
#        directory passes it.
#
#   NF2  `tests/json-fair/run.sh` gates every document before it times it: the
#        writer's event and arena bytes equal `leanllvm_json_pipeline`'s, the
#        same C consumer reads both streams and agrees, the direct sum equals
#        that fold, and the no-event arm's reading equals the certified fold.
#        The uncut run exits 0 with one gate-pass line per manifest document.
#        A throwaway copy of the tree whose `fair.cc` declares one fewer payload
#        byte in every key and string record must compile, then exit 1 at that
#        gate: the failure is the writer's event bytes (`writer=1 ev=0
#        arena=1`), a failed document is not timed, and the same document
#        passed in the uncut run.
#
#   NF3  The report recounts from its own rows.  Each arm cell in
#        `build/per-document.tsv` is recomputed as the median of that arm's
#        trial medians in `build/rows.tsv`; each `rpn/ps` cell is recomputed as
#        the median of the document's per-trial `rpn/ps` quotients; the
#        summary's faster, in-band and over-10% counts must partition the
#        corpus with the denominator stated, for all 151 documents and for the
#        148 heterogeneous ones; the median quotient is the median of the
#        per-document quotients; and a copy of the summary with one count
#        incremented fails the same recount.
#
#   NF4  The body-bound attribution.  It has no instrument at this revision, so
#        this check runs nothing for it; `tests/json-fair.contract.md` records
#        the stub's actor, boundary and outcome, and the ablation instrument is
#        `tests/json-fair/ablate.sh` when it lands.
#
# The corpus is regenerated into a private directory and the harness's build
# and per-document table live beside it; the staged cut is compiled in a
# throwaway copy of the tree.  Nothing in the repository is written.
#
# Environment: CHECK_TRIALS (3), CHECK_REPS (3), FAIR_CC, BENCH_CXX, and the
# simdjson store variables `run.sh` reads.  The trials and reps are small on
# purpose: this check asserts the report's arithmetic, not a performance row.
#
# Exit status: 0 when every assertion holds, 1 when one fails, 3 when the route
# is not usable (an absent source or tool, a corpus the generator cannot
# materialise, a harness that is not usable, or a staged cut that does not
# apply), so a setup fault is never read as an assertion result.
set -uo pipefail
export LC_ALL=C

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
manifest=$here/manifest.tsv
generator=$here/generate.sh
harness=$here/run.sh
faircc=$here/fair.cc
trials=${CHECK_TRIALS:-3}
reps=${CHECK_REPS:-3}

setup() { printf 'SETUP: %s\n' "$1" >&2; exit 3; }
fail() { printf 'FAIL: %s\n' "$1" >&2; exit 1; }

for path in "$manifest" "$generator" "$harness" "$faircc" "$here/gen.py" \
            "$repo/tests/json-units-bench/gen.c" \
            "$repo/kernel/json/pipeline.c" "$repo/kernel/json/pipeline.h" \
            "$repo/kernel/json/stage2.c" "$repo/kernel/json/stage2.h" \
            "$repo/kernel/json/stage2_noevent.c" \
            "$repo/kernel/json/stage2_noevent.h" \
            "$repo/kernel/json/pipeline_noevent.c" \
            "$repo/probes/json/route/escape_guard.h"; do
  [ -e "$path" ] || setup "absent: $path"
done
for tool in python3 clang clang++ sha256sum stat taskset mktemp; do
  command -v "$tool" >/dev/null 2>&1 || setup "no $tool on PATH; run this under nix develop"
done

work=$(mktemp -d "${TMPDIR:-/tmp}/json-fair-check.XXXXXX") ||
  setup "cannot create a temporary directory"
trap 'rm -rf "$work"' EXIT

rows_n=$(awk 'END { print NR - 1 }' "$manifest")
[ "$rows_n" = 151 ] || setup "the manifest has $rows_n rows, not 151"
[ "$(head -1 "$manifest")" = "$(printf 'file\tstyle\ttarget_bytes\trecords\tbytes\tsha256\troot\tseed\tmax_depth\tseed_index')" ] ||
  setup "the manifest's header is not the fair corpus header"

# --------------------------------------------------------------- 1. NF1 ----
#
# The actor materialises the corpus into a private directory.  The per-row
# verification below is the check's own: it reads the manifest's bytes and
# sha256 and compares them with the generated files, so a manifest and a
# generator that drifted apart together are not a pass.  The generator's own
# `--verify` is the same detector the control below drives, and it also
# compares `gen.py`'s manifest with the committed 148 rows.

corpus=$work/corpus
bash "$generator" --out="$corpus" >"$work/generate.log" 2>&1
status=$?
if [ "$status" -ne 0 ]; then
  [ "$status" -eq 3 ] && setup "generate.sh is not usable (exit 3)"
  printf 'FAIL: generate.sh did not materialise the corpus\n' >&2
  cat "$work/generate.log" >&2
  exit 1
fi

declare -A seen
checked=0
hetero=0
canonical=0
while IFS=$'\t' read -r file style target records bytes sha root seed depth si; do
  [ "$file" = file ] && continue
  [ -n "$file" ] || fail "the manifest has a blank row"
  [ -z "${seen[$file]-}" ] || fail "the manifest names $file twice"
  seen[$file]=1
  [ -f "$corpus/$file" ] || fail "the generator did not write $file"
  got_bytes=$(stat -c %s "$corpus/$file") ||
    setup "cannot read $corpus/$file"
  [ "$got_bytes" = "$bytes" ] ||
    fail "$file is $got_bytes bytes, the manifest pins $bytes"
  got_sha=$(sha256sum "$corpus/$file" | cut -d' ' -f1)
  [ "$got_sha" = "$sha" ] ||
    fail "$file has sha256 $got_sha, the manifest pins $sha"
  case $file in
    hetero-*) hetero=$((hetero + 1)) ;;
    syn-*) canonical=$((canonical + 1)) ;;
    *) fail "the manifest names $file outside the two corpus groups" ;;
  esac
  checked=$((checked + 1))
done <"$manifest"
[ "$checked" = 151 ] || fail "checked $checked manifest rows, not 151"
[ "$hetero" = 148 ] || fail "the corpus has $hetero heterogeneous rows, not 148"
[ "$canonical" = 3 ] || fail "the corpus has $canonical canonical rows, not 3"

present=$(find "$corpus" -mindepth 1 -maxdepth 1 -type f -name '*.json' -printf '%f\n' |
  LC_ALL=C sort)
manifest_set=$(awk -F '\t' 'NR > 1 { print $1 }' "$manifest" | LC_ALL=C sort)
present_n=$(printf '%s\n' "$present" | awk 'NF { n++ } END { print n + 0 }')
[ "$present_n" = 151 ] || fail "the corpus holds $present_n documents, not 151"
if [ "$present" != "$manifest_set" ]; then
  printf 'FAIL: the generated document set is not the manifest set\n' >&2
  diff <(printf '%s\n' "$present") <(printf '%s\n' "$manifest_set") | awk 'NR <= 20' >&2
  exit 1
fi
printf 'ok: the generator materialised 151 documents (148 hetero + 3 canonical); every size and sha256 is the manifest'"'"'s\n'

# The affirmative control: one byte changed in a copy of one document.  The
# same `--verify` must pass the unchanged directory and reject the mutated one.
if ! bash "$generator" --verify --out="$corpus" >"$work/verify.log" 2>&1; then
  printf 'FAIL: generate.sh --verify rejected the corpus it just generated\n' >&2
  cat "$work/verify.log" >&2
  exit 1
fi

mutant=$work/mutant
cp -a "$corpus" "$mutant" || setup "cannot copy the corpus for the mutation control"
mutant_file=$(awk -F '\t' 'NR == 2 { print $1 }' "$manifest")
[ -n "$mutant_file" ] || setup "the manifest has no first data row"
mutant_before=$(sha256sum "$mutant/$mutant_file" | cut -d' ' -f1)
mutant_size_before=$(stat -c %s "$mutant/$mutant_file")
python3 - "$mutant/$mutant_file" <<'PY' || setup "cannot mutate the control document"
import sys
path = sys.argv[1]
b = bytearray(open(path, "rb").read())
if not b:
    raise SystemExit("empty control document")
b[0] ^= 0xFF
open(path, "wb").write(b)
PY
mutant_after=$(sha256sum "$mutant/$mutant_file" | cut -d' ' -f1)
mutant_size_after=$(stat -c %s "$mutant/$mutant_file")
[ "$mutant_after" != "$mutant_before" ] ||
  setup "the mutation control did not change the document's digest"
[ "$mutant_size_after" = "$mutant_size_before" ] ||
  setup "the mutation control changed the document's size, not only a byte"

mutant_status=0
bash "$generator" --verify --out="$mutant" >"$work/mutant.log" 2>&1 ||
  mutant_status=$?
if [ "$mutant_status" -eq 3 ]; then
  printf 'SETUP: generate.sh --verify is not usable on the mutated copy (exit 3)\n' >&2
  cat "$work/mutant.log" >&2
  exit 3
fi
[ "$mutant_status" -eq 1 ] ||
  fail "generate.sh --verify exited $mutant_status on a one-byte mutation, and a rejected row exits 1"
grep -q 'corpus disagrees with the manifest' "$work/mutant.log" ||
  fail "the one-byte mutation was rejected without the manifest disagreement"
grep -q "$mutant_file" "$work/mutant.log" ||
  fail "the one-byte mutation was rejected without naming $mutant_file"
grep -q 'sha256' "$work/mutant.log" ||
  fail "the one-byte mutation was rejected without the digest it computed"
printf '   rejected: %s\n' "$(grep -m1 'sha256' "$work/mutant.log" | sed 's/^ *//')"
printf 'ok: a one-byte mutation of %s is rejected by the same detector; the unchanged corpus passes\n' \
  "$mutant_file"

# ------------------------------------------------------- 2. the uncut run ----
#
# One run serves NF2's control and NF3's rows.  The no-event arm is linked
# because NF3's quotient needs it; the gates cover the writer, the consumer and
# the certified reading either way.  Three trials make the per-document
# quotient a median of three within-trial quotients rather than a copy of one.

control_build=$work/control-build
FAIR_NOEVENT=1 BENCH_TRIALS="$trials" BENCH_REPS="$reps" \
  BENCH_DIR="$control_build" FAIR_CORPUS="$corpus" \
  bash "$harness" --short >"$work/control.out" 2>"$work/control.err"
control_status=$?
if [ "$control_status" -eq 3 ]; then
  printf 'SETUP: the fair harness is not usable (exit 3)\n' >&2
  cat "$work/control.err" >&2
  exit 3
fi
[ "$control_status" -eq 0 ] || {
  printf 'FAIL: the uncut harness exited %s on the pinned corpus\n' "$control_status" >&2
  cat "$work/control.err" >&2
  exit 1
}
[ -x "$control_build/bin/fair" ] || fail "the uncut harness built no binary"
grep -Fxq "fair: 0 gate failures over 151 documents" "$work/control.err" ||
  fail "the uncut harness did not report zero gate failures over 151 documents"

control_rows=$control_build/rows.tsv
control_tsv=$control_build/per-document.tsv
[ -f "$control_rows" ] || fail "the uncut harness wrote no rows.tsv"
[ -f "$control_tsv" ] || fail "the uncut harness wrote no per-document.tsv"

manifest_stems=$(awk -F '\t' 'NR > 1 { sub(/\.json$/, "", $1); print $1 }' "$manifest" |
  LC_ALL=C sort)

# Every document was gated and passed.  The pass line is produced only for a
# document whose writer bytes, arena bytes and consumer reading all agreed, so
# its presence per document is the gate's per-document outcome, not a summary.
gate_pass=$(awk -F '\t' '$2 == "GATE" && $4 == "pass" { print $3 }' "$control_rows" |
  LC_ALL=C sort)
gate_pass_n=$(printf '%s\n' "$gate_pass" | awk 'NF { n++ } END { print n + 0 }')
[ "$gate_pass_n" = 151 ] ||
  fail "the uncut harness printed $gate_pass_n gate-pass lines, not 151"
if [ "$gate_pass" != "$manifest_stems" ]; then
  printf 'FAIL: the gate-pass documents are not the manifest documents\n' >&2
  diff <(printf '%s\n' "$gate_pass") <(printf '%s\n' "$manifest_stems") | awk 'NR <= 20' >&2
  exit 1
fi
if awk -F '\t' '$2 == "GATE" && $4 != "pass" { found = 1 } END { exit(found ? 0 : 1) }' "$control_rows"; then
  fail "the uncut harness printed a gate failure"
fi
# The consumer's fold is the same on both sides: the pass line carries the
# certified fold's reading, whose token and value counters are one per record.
bad_counts=$(awk -F '\t' '
  $2 == "GATE" && $4 == "pass" {
    tok = val = ""; sum = ""
    for (i = 5; i <= NF; i++) {
      if ($i ~ /^tokens=/) { tok = substr($i, 8) }
      else if ($i ~ /^values=/) { val = substr($i, 8) }
      else if ($i ~ /^sum=/) { sum = substr($i, 5) }
    }
    if (tok == "" || val == "" || sum == "") { bad++; next }
    if (tok != val || tok !~ /^[0-9]+$/ || sum !~ /^[0-9]+$/) bad++
  }
  END { print bad + 0 }' "$control_rows")
[ "$bad_counts" = 0 ] ||
  fail "a gate-pass line carries no agreeing consumer reading"
printf 'ok: every one of the 151 documents passed the writer, arena, consumer and no-event gates before timing\n'

# NF2's cut: a throwaway copy of the tree whose writer declares one fewer
# payload byte in every key and string record.  The cut is in `fair.cc`'s
# `ev_rec`, which runs for every such record on the writer's boundary path; it
# changes no production byte and no other gate's input.
cut=$work/cut
mkdir -p "$cut/tests/json-fair" "$cut/tests/json-units-bench" \
         "$cut/kernel" "$cut/probes/json" ||
  setup "cannot create the cut tree"
cp "$here/gen.py" "$here/manifest.tsv" "$here/generate.sh" "$here/run.sh" \
   "$here/fair.cc" "$cut/tests/json-fair/" || setup "cannot copy the harness into the cut tree"
cp "$repo/tests/json-units-bench/gen.c" "$cut/tests/json-units-bench/" ||
  setup "cannot copy the canonical generator into the cut tree"
cp -a "$repo/kernel/json" "$cut/kernel/json" ||
  setup "cannot copy the kernel into the cut tree"
cp -a "$repo/probes/json/route" "$cut/probes/json/route" ||
  setup "cannot copy the route headers into the cut tree"

awk '
  /^  p\[1\] = \(uint8_t\)len; p\[2\] = \(uint8_t\)\(len >> 8\);$/ {
    sub(/p\[1\] = \(uint8_t\)len;/, "p[1] = (uint8_t)(len - (len != 0));")
    hit = 1
  }
  { print }
  END { exit(hit ? 0 : 1) }
' "$here/fair.cc" >"$cut/tests/json-fair/fair.cc" ||
  setup "the dropped-payload-byte cut did not apply"
cmp -s "$here/fair.cc" "$cut/tests/json-fair/fair.cc" &&
  setup "the dropped-payload-byte cut did not change fair.cc"

cut_build=$work/cut-build
FAIR_NOEVENT=1 BENCH_TRIALS="$trials" BENCH_REPS="$reps" \
  BENCH_DIR="$cut_build" FAIR_CORPUS="$corpus" \
  bash "$cut/tests/json-fair/run.sh" --short >"$work/cut.out" 2>"$work/cut.err"
cut_status=$?
if [ "$cut_status" -eq 3 ]; then
  printf 'FAIL: the cut tree did not build or verify (exit 3)\n' >&2
  cat "$work/cut.err" >&2
  exit 1
fi
[ -x "$cut_build/bin/fair" ] || fail "the cut tree did not build its harness"
[ "$cut_status" -eq 1 ] ||
  fail "the cut harness exited $cut_status, and a gate failure exits 1"
grep -q 'FAIL: a gate failed' "$work/cut.err" ||
  fail "the cut harness failed without the gate-failure line"
cut_rows=$cut_build/rows.tsv
[ -f "$cut_rows" ] || fail "the cut harness wrote no rows.tsv"

cut_fail=$(awk -F '\t' '$2 == "GATE" && $4 == "FAIL" { print $3 }' "$cut_rows" |
  LC_ALL=C sort)
cut_fail_n=$(printf '%s\n' "$cut_fail" | awk 'NF { n++ } END { print n + 0 }')
[ "$cut_fail_n" -gt 0 ] || fail "the cut fired no gate failure"
cut_pass_n=$(awk -F '\t' '$2 == "GATE" && $4 == "pass"' "$cut_rows" | wc -l)
[ $((cut_fail_n + cut_pass_n)) = 151 ] ||
  fail "the cut run gated $((cut_fail_n + cut_pass_n)) documents, not 151"

# The first failed document's own line must show the writer's event bytes
# differing while the arena still agrees, and the same document must have
# passed the uncut run.
cut_first=$(printf '%s\n' "$cut_fail" | head -1)
cut_line=$(awk -F '\t' -v d="$cut_first" '$2 == "GATE" && $3 == d && $4 == "FAIL" { print; exit }' "$cut_rows")
printf '%s\n' "$cut_line" | grep -q 'writer=1 ev=0 arena=1' ||
  fail "the cut's first failure is not the writer's event gate with the arena agreeing"
printf '%s\n' "$cut_line" | grep -q 'consumer=0' ||
  fail "the cut's failing line does not show the consumer reading differing"
evlens=$(printf '%s\n' "$cut_line" | sed -n 's/.*evlen=\([0-9][0-9]*\)\/\([0-9][0-9]*\).*/\1 \2/p')
[ -n "$evlens" ] || fail "the cut's failing line carries no event lengths"
read -r cut_ev_route cut_ev_writer <<< "$evlens"
[ "$cut_ev_route" = "$cut_ev_writer" ] ||
  fail "the cut changed the event stream's length, not a record's payload byte"
cut_at=$(printf '%s\n' "$cut_line" | sed -n 's/.*at=\([0-9][0-9]*\).*/\1/p')
[ -n "$cut_at" ] || fail "the cut's failing line carries no differing offset"
[ "$cut_at" -lt "$cut_ev_route" ] ||
  fail "the cut's differing offset is not inside the event stream"
awk -F '\t' -v d="$cut_first" '$2 == "GATE" && $3 == d && $4 == "pass" { found = 1 } END { exit(found ? 0 : 1) }' \
  "$control_rows" ||
  fail "the first document the cut failed did not pass the uncut run"
awk -F '\t' -v d="$cut_first" '$2 == "ROW" && $3 == d { found = 1 } END { exit(found ? 0 : 1) }' \
  "$cut_rows" &&
  fail "a document the cut failed was timed anyway"
timed_fail=$(awk -F '\t' '
  $2 == "GATE" && $4 == "FAIL" { failed[$3] = 1 }
  $2 == "ROW" && ($3 in failed) { n++ }
  END { print n + 0 }' "$cut_rows")
[ "$timed_fail" = 0 ] ||
  fail "$timed_fail rows were timed for documents the cut failed"
printf '   firing assertion: %s\n' "$(printf '%s\n' "$cut_line" | cut -f2-)"
printf 'ok: the cut tree compiled; declaring one fewer payload byte fired the writer gate on %d documents (%s first, %s bytes, first difference at %s), and that document passed uncut\n' \
  "$cut_fail_n" "$cut_first" "$cut_ev_route" "$cut_at"

# --------------------------------------------------------------- 3. NF3 ----
#
# Every derived number is recomputed from `rows.tsv`, which carries one median
# per document, arm and trial.  The table's cells and the summary's counts are
# then compared with those recomputations; the same function rejects a summary
# whose faster count is incremented.

recount() { # tsv rows trials -> RECOUNT line on stdout, mismatches on stderr
  awk -F '\t' -v trials="$3" '
    function sortn(a, n,   i, j, t) {
      for (i = 2; i <= n; i++) { t = a[i]; for (j = i - 1; j >= 1 && a[j] > t; j--) a[j+1] = a[j]; a[j+1] = t }
    }
    function med(a, n) {
      if (n % 2) return a[(n + 1) / 2]
      return 0.5 * (a[n / 2] + a[n / 2 + 1])
    }
    FNR == NR {
      if ($1 !~ /^[0-9]+$/) next
      d = $2; n++; order[n] = d
      ta[d, "parse"] = $4 + 0; ta[d, "pw"] = $5 + 0; ta[d, "pwc"] = $6 + 0
      ta[d, "ps"] = $7 + 0; ta[d, "rp"] = $8 + 0; ta[d, "rpc"] = $9 + 0
      ta[d, "rpn"] = $10 + 0; tq[d] = $11 + 0
      next
    }
    $2 == "ROW" {
      d = $3; a = $5; t = $6 + 0; ns = $7 + 0
      if (t < 0 || t >= trials) { printf "%s/%s carries trial %d outside 0..%d\n", d, a, t, trials - 1 > "/dev/stderr"; bad = 1 }
      k = d SUBSEP a SUBSEP t
      if (k in V) { printf "%s/%s trial %d appears twice\n", d, a, t > "/dev/stderr"; bad = 1 }
      V[k] = ns
      if (!(d in seen)) { seen[d] = 1; rn++ }
      next
    }
    END {
      if (rn != n) { printf "the rows name %d documents, the table %d\n", rn, n > "/dev/stderr"; bad = 1 }
      split("parse pw pwc ps rp rpc rpn", arms, " ")
      for (i = 1; i <= n; i++) {
        d = order[i]
        for (ai = 1; ai <= 7; ai++) {
          a = arms[ai]; m = 0
          for (t = 0; t < trials; t++) {
            k = d SUBSEP a SUBSEP t
            if (!(k in V)) { printf "%s has no %s trial %d\n", d, a, t > "/dev/stderr"; bad = 1; continue }
            s[++m] = V[k]
          }
          if (m == trials) {
            sortn(s, m)
            got = sprintf("%.0f", med(s, m)); want = sprintf("%.0f", ta[d, a])
            if (got != want) { printf "%s %s is %s, the rows give %s\n", d, a, want, got > "/dev/stderr"; bad = 1 }
          }
          split("", s)
        }
        m = 0
        for (t = 0; t < trials; t++) {
          kp = d SUBSEP "ps" SUBSEP t; kr = d SUBSEP "rpn" SUBSEP t
          if ((kp in V) && (kr in V) && V[kp] > 0) q[t] = V[kr] / V[kp]
          else { printf "%s has no positive ps/rpn pair in trial %d\n", d, t > "/dev/stderr"; bad = 1; q[t] = 0 }
          s[++m] = q[t]
        }
        sortn(s, m); qm = med(s, m)
        if (sprintf("%.4f", qm) != sprintf("%.4f", tq[d])) {
          printf "%s rpn/ps is %.4f, the rows give %.4f\n", d, tq[d], qm > "/dev/stderr"; bad = 1
        }
        Q[i] = qm
        if (qm < 1.0) F++
        else if (qm <= 1.10) B++
        else O++
        if (d !~ /^syn-/) {
          N148++
          if (qm < 1.0) F148++
          else if (qm <= 1.10) B148++
          else O148++
        }
      }
      sortn(Q, n); qmed = med(Q, n)
      printf "RECOUNT\t%d\t%d\t%d\t%d\t%.4f\t%d\t%d\t%d\t%d\t%d\n", \
        n, F, B, O, qmed, N148, F148, B148, O148, bad
      exit(bad ? 1 : 0)
    }
  ' "$1" "$2"
}

recount_line=$(recount "$control_tsv" "$control_rows" "$trials" 2>"$work/recount.err")
recount_status=$?
if [ "$recount_status" -ne 0 ]; then
  printf 'FAIL: the report does not recount from its rows\n' >&2
  awk 'NR <= 20' "$work/recount.err" >&2
  exit 1
fi
read -r _ N F B O QMED N148 F148 B148 O148 bad < <(printf '%s\n' "$recount_line")
[ "$N" = 151 ] || fail "the table holds $N documents, not 151"
[ $((F + B + O)) = "$N" ] ||
  fail "faster $F + in band $B + over 10% $O is not the corpus size $N"
[ "$N148" = 148 ] || fail "the heterogeneous group holds $N148 documents, not 148"
[ $((F148 + B148 + O148)) = "$N148" ] ||
  fail "the heterogeneous counts do not partition their group"

# The table's byte column and its document set are the manifest's.
table_set=$(awk -F '\t' '$1 !~ /^[0-9]+$/ { next } { print $2 }' "$control_tsv" |
  LC_ALL=C sort)
if [ "$table_set" != "$manifest_stems" ]; then
  printf 'FAIL: the per-document table is not the manifest document set\n' >&2
  diff <(printf '%s\n' "$table_set") <(printf '%s\n' "$manifest_stems") | awk 'NR <= 20' >&2
  exit 1
fi
manifest_bytes_ok=$(awk -F '\t' '
  NR == FNR { if ($1 != "file") want[$1] = $5; next }
  $1 !~ /^[0-9]+$/ { next }
  { f = $2 ".json"; if (!(f in want) || want[f] != $3) bad++ }
  END { print bad + 0 }' "$manifest" "$control_tsv")
[ "$manifest_bytes_ok" = 0 ] ||
  fail "a per-document row's byte count is not the manifest's"

# The summary's every count, denominator and median must be the recount's.
check_summary() { # summary file -> 0 when every stated number is the recount's
  local sum=$1 line n m f fd b bd o od state denom want
  line=$(sed -n 's/^  median quotient over \([0-9][0-9]*\) documents: \([0-9.]*\)$/\1 \2/p' "$sum")
  [ -n "$line" ] || { printf 'the summary states no median quotient\n' >&2; return 1; }
  n=${line%% *}; m=${line#* }
  [ "$n" = "$N" ] ||
    { printf 'the summary names %s documents, the rows %s\n' "$n" "$N" >&2; return 1; }
  awk -v a="$m" -v b="$QMED" 'BEGIN { d = a - b; if (d < 0) d = -d; exit !(d <= 0.00005) }' ||
    { printf 'the summary median is %s, the rows give %s\n' "$m" "$QMED" >&2; return 1; }
  line=$(sed -n 's/^  faster (<1\.0): \([0-9][0-9]*\)\/\([0-9][0-9]*\); in band \[1\.0,1\.10\]: \([0-9][0-9]*\)\/\([0-9][0-9]*\); over 10%: \([0-9][0-9]*\)\/\([0-9][0-9]*\)$/\1 \2 \3 \4 \5 \6/p' "$sum")
  [ -n "$line" ] || { printf 'the summary states no partition of the corpus\n' >&2; return 1; }
  read -r f fd b bd o od <<< "$line"
  [ "$f" = "$F" ] ||
    { printf 'the summary faster count is %s, the rows give %s\n' "$f" "$F" >&2; return 1; }
  [ "$b" = "$B" ] ||
    { printf 'the summary in-band count is %s, the rows give %s\n' "$b" "$B" >&2; return 1; }
  [ "$o" = "$O" ] ||
    { printf 'the summary over-10%% count is %s, the rows give %s\n' "$o" "$O" >&2; return 1; }
  [ "$fd" = "$N" ] && [ "$bd" = "$N" ] && [ "$od" = "$N" ] ||
    { printf 'the summary denominators are %s/%s/%s, the corpus is %s\n' "$fd" "$bd" "$od" "$N" >&2; return 1; }
  line=$(sed -n 's/^  the 148 heterogeneous documents: faster \([0-9][0-9]*\)\/\([0-9][0-9]*\); in band \([0-9][0-9]*\)\/\([0-9][0-9]*\); over \([0-9][0-9]*\)\/\([0-9][0-9]*\)$/\1 \2 \3 \4 \5 \6/p' "$sum")
  [ -n "$line" ] || { printf 'the summary states no heterogeneous group\n' >&2; return 1; }
  read -r f fd b bd o od <<< "$line"
  [ "$f" = "$F148" ] && [ "$b" = "$B148" ] && [ "$o" = "$O148" ] ||
    { printf 'the summary heterogeneous counts are %s/%s/%s, the rows give %s/%s/%s\n' \
        "$f" "$b" "$o" "$F148" "$B148" "$O148" >&2; return 1; }
  [ "$fd" = "$N148" ] && [ "$bd" = "$N148" ] && [ "$od" = "$N148" ] ||
    { printf 'the summary heterogeneous denominators are %s/%s/%s, the group is %s\n' \
        "$fd" "$bd" "$od" "$N148" >&2; return 1; }
  state=$(awk -F ': ' '/^  majority-faster / { sub(/ \(denominator.*/, "", $2); print $2 }' "$sum")
  denom=$(awk '/^  majority-faster / { sub(/.*\(denominator /, ""); sub(/\)$/, ""); print }' "$sum")
  [ "$state" = MET ] || [ "$state" = "NOT MET" ] ||
    { printf 'the summary states no majority condition\n' >&2; return 1; }
  if [ $((F * 2)) -gt "$N" ]; then want=MET; else want="NOT MET"; fi
  [ "$state" = "$want" ] ||
    { printf 'the summary says the majority is %s, the rows give %s\n' "$state" "$want" >&2; return 1; }
  [ "$denom" = "$N" ] ||
    { printf 'the majority denominator is %s, the corpus is %s\n' "$denom" "$N" >&2; return 1; }
  return 0
}

sed -n '/^## the consumer boundary/,$p' "$control_tsv" >"$work/summary.txt"
[ -s "$work/summary.txt" ] || fail "the per-document table carries no consumer-boundary summary"
if ! check_summary "$work/summary.txt" 2>"$work/summary.err"; then
  printf 'FAIL: the report summary does not recount from its rows\n' >&2
  cat "$work/summary.err" >&2
  exit 1
fi

awk '
  /^  faster \(<1\.0\): / && !hit {
    if (match($0, /faster \(<1\.0\): [0-9]+\//)) {
      head = substr($0, 1, RSTART - 1)
      tok = substr($0, RSTART, RLENGTH)
      tail = substr($0, RSTART + RLENGTH)
      n = tok; sub(/^faster \(<1\.0\): /, "", n); sub(/\/$/, "", n)
      $0 = head "faster (<1.0): " (n + 1) "/" tail
      hit = 1
    }
  }
  { print }
  END { exit(hit ? 0 : 1) }
' "$work/summary.txt" >"$work/summary.tampered" ||
  setup "the summary tamper did not apply"
cmp -s "$work/summary.txt" "$work/summary.tampered" &&
  setup "the summary tamper did not change the summary"
if check_summary "$work/summary.tampered" 2>"$work/tamper.err"; then
  fail "the recount accepted a summary with one faster count incremented"
fi
grep -q 'the summary faster count is' "$work/tamper.err" ||
  fail "the tampered summary failed without naming the count"
printf '   rejected: %s\n' "$(cat "$work/tamper.err")"
printf 'ok: the report recounts from its rows (%d/%d faster, %d/%d in band, %d/%d over; median %s); a tampered count is rejected\n' \
  "$F" "$N" "$B" "$N" "$O" "$N" "$QMED"

# --------------------------------------------------------------- 4. NF4 ----
#
# The body-bound attribution has no instrument at this revision.  Its actor,
# boundary and outcome are recorded in `tests/json-fair.contract.md`; the
# ablation instrument is `tests/json-fair/ablate.sh` when it lands.  Nothing
# here measures a stage, and nothing here should be read as the attribution.

printf 'pending: NF4 has no ablation instrument at this revision; its stub is in tests/json-fair.contract.md\n'
printf 'ok: the corpus is pinned, the harness times equal outputs, and the report recounts from its rows\n'
exit 0
