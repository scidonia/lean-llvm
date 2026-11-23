#!/usr/bin/env bash
# Route check for the no-event stage-2 entry and the no-event pipeline entry.
#
#   nix develop -c bash tests/json-noevent/check.sh
#
# Two boundaries are compared, both through `probes/json/noevent_driver.c` as
# an external process:
#
#   --route stage2    `kernel/json/stage2_noevent.c` against the certified
#                     stage-2 entry `leanllvm_json_stage2` followed by the
#                     unchanged consumer fold
#                     (`probes/json/route/cost-profile/cost-profile.c`'s
#                     `fold_result`, build mode).  Stage 1 is
#                     `leanllvm_json_pipeline`, called only for its entry
#                     stream and escape list; both entries then run on the same
#                     stage-1 output.
#
#   --route pipeline  `leanllvm_json_pipeline_noevent` against
#                     `leanllvm_json_pipeline` plus the same fold.  Each side
#                     runs its own stage 1, so the entry stream's cursor `nk`
#                     and the escape list's count `nxp` are compared as well as
#                     the verdict, the refusal offset and the reading.
#
# The corpus is `tests/json-noevent/corpus`: `documents/` holds the documents,
# `manifest.tsv` records each one's expected row and digest, and `generate.sh`
# with `seed` and `spec.tsv` regenerates both.  The manifest's arm field says
# which route and arms a document belongs to: `both` runs in both arms of both
# routes; `list` carries an escape or a control byte and runs in the `list`
# arm of both routes; `pipeline` is the UTF-8 stage's document-level refusal,
# which only the pipeline route reaches, and it runs in both pipeline arms.
# The `nolist` arm passes `nxp = 0` to both sides and is confined to
# escape-free documents.
#
# What this scenario asserts:
#
#   NE1 — stage-2 entry agreement.  For every document and every arm the
#   manifest assigns the stage-2 route, the driver exits 0, writes nothing to
#   stderr, and prints one row per document in corpus order:
#
#     <path>\t<accept|refuse>\t<1|0>\t<err|->\t<tokens|->\t<values|->\t<sum|->
#
#   The verdict, the refusal offset and the three reading words match the
#   manifest's pinned row.  A disagreement is the driver's `FAIL … reading:`
#   line with both readings and exit 3; the defect object below shows that
#   line fire.
#
#   NE2 — pipeline entry agreement.  For every document and every arm the
#   manifest assigns the pipeline route, the same driver under `--route
#   pipeline` exits 0, writes nothing to stderr, and prints the same seven
#   columns with `nk` and `nxp` appended:
#
#     ...\t<sum>\t<nk>\t<nxp>
#
#   Both stage-1 outputs are compared between the two entries by the driver,
#   so a row is emitted only when they agree; the check additionally requires
#   the two words to be decimal, `nxp` to be zero in the `nolist` arm, and
#   `nxp` to be positive for the escape-bearing (`list`-arm) documents.  On a
#   refusal the slots must hold zero under both refusal classes — the UTF-8
#   stage's document-level one and the walk's.  The defect objects below show
#   the reading and the entry pre-zero firing.
#
#   NE3 — refusal slots.  The driver pre-fills the three reading slots with
#   `0xDEADBEEFDEADBEEF`; on a refusal the entry must write zero to all three
#   and the certified entry's offset to `*err`.  Every refusal class
#   `kernel/json/stage2.h` names (the structural, number, literal and
#   string-body rules and the end-of-stream rules `unclosed`, `no-value`,
#   `unterminated`) has at least one document, and every such row carries its
#   pinned offset and `-` readings.  The defect object below no-ops the refusal
#   stores and shows the sentinel surface as `16045690984833335023`, which is
#   what "wrote zero" and "left untouched" must remain distinguishable by.
#
#   NE6 — dependency census.  The object built from `stage2_noevent.c` defines
#   exactly `leanllvm_json_stage2_noevent` and
#   `leanllvm_json_stage2_noevent_lib` as public symbols and leaves exactly
#   `leanllvm_json_escape_expand` undefined among the project's symbols.  A
#   staged reference to a stage-1 symbol must be reported by the same census.
#
#   NE4 — the current ABI stays byte-identical.  Every protected path's bytes
#   equal `66159e24b93d7f78139d08a8d1794f32ae12e777`'s, and the stage-2 and
#   pipeline identity arms still report their one-symbol census.  The check is
#   a regression guard (it passes trivially at the pre-start state), so its
#   evidence is the positive control: a copy with one byte changed fails the
#   same detector, and an unchanged copy passes it.
#
# The corpus's own integrity is asserted first: every document's digest
# matches the manifest, the document set is exactly the manifest's, and
# `generate.sh` at its fixed seed reproduces both the documents and the
# manifest byte for byte.  An accepted document's sum is below `2 ^ 64`, the
# condition under which the driver's word is the exact sum; the generator
# enforces that bound with a two-limb accumulator and refuses a document whose
# exact sum reaches it.
#
# `clang` compiles the committed kernel sources and the driver into a private
# temporary directory; `CC` is not consulted because the dev shell's `CC` is
# gcc.  The corpus, the generator, the manifest and the driver source are only
# read.  The defect objects and the identity control are built and written
# under that temporary directory, never in the tree.
#
# Exit status: 0 when every assertion holds, 1 when one fails, 3 when the route
# is not usable (an absent corpus, manifest, generator, seed, driver or kernel
# source, no `clang` or `git`, the pinned base revision absent, a corpus the
# generator does not reproduce, or a staged cut that does not apply), so a
# setup fault is never read as an assertion result.
set -uo pipefail

repo=$(cd "$(dirname "$0")/../.." && pwd)
route_rel=tests/json-noevent
corpus=$repo/$route_rel/corpus
docs=$corpus/documents
manifest=$corpus/manifest.tsv
generator=$corpus/generate.sh
spec=$corpus/spec.tsv
seed_file=$corpus/seed
driver_src=$repo/probes/json/noevent_driver.c
base=66159e24b93d7f78139d08a8d1794f32ae12e777
cc=clang

# The measured compiler line (`build49.sh:17`).
cflags=(-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 -falign-functions=64)

# The certifying route's artefact set: the two kernel units the no-event entry
# leaves untouched, their pinned fixtures, and the build list that compiles the
# shipped units.
protected=(
  kernel/json/stage2.c
  kernel/json/stage2.h
  kernel/json/pipeline.c
  kernel/json/pipeline.h
  probes/install/ir/stage2.candidate.ll
  probes/install/ir/json-pipeline.candidate.ll
  probes/json/route/build.sh
)

# The driver's sentinel, `0xDEADBEEFDEADBEEF`, in decimal.
sentinel=16045690984833335023

setup() { printf 'SETUP: %s\n' "$1" >&2; exit 3; }
fail() { printf 'FAIL: %s\n' "$1" >&2; exit 1; }

for path in "$corpus" "$docs" "$manifest" "$generator" "$spec" "$seed_file" \
            "$driver_src" "$repo/kernel/json/stage2_noevent.c" \
            "$repo/kernel/json/stage2_noevent.h" \
            "$repo/kernel/json/stage2.c" "$repo/kernel/json/stage2.h" \
            "$repo/kernel/json/pipeline.c" "$repo/kernel/json/pipeline.h"; do
  [ -e "$path" ] || setup "absent: $path"
done
for unit in s1_block entry utf8 escape stage2 pipeline stage2_noevent pipeline_noevent; do
  [ -f "$repo/kernel/json/$unit.c" ] || setup "absent: kernel/json/$unit.c"
done
command -v "$cc" >/dev/null 2>&1 || setup "no $cc on PATH, and the kernel is C"
command -v git >/dev/null 2>&1 || setup "no git on PATH, and the base comparison needs it"
git -C "$repo" cat-file -e "$base^{commit}" 2>/dev/null ||
  setup "the pinned base $base is not in this repository"

work=$(mktemp -d) || setup "cannot create a temporary directory"
trap 'rm -rf "$work"' EXIT
cd "$repo" || setup "cannot enter $repo"

corpus_rel=$route_rel/corpus

# ------------------------------------------------------------- 0. the corpus --
#
# The manifest is the fixture's pin: every document's digest, the document set,
# and the generator's reproduction of both.  A corpus that drifted from its
# manifest, or a generator that no longer reproduces it, is a setup fault: the
# rows below would be read against bytes nobody pinned.

declare -A M_ARMS M_CLASS M_VERDICT M_ERR M_TOK M_VAL M_SUM M_SHA M_ORIGIN
s2_list_docs=()
s2_nolist_docs=()
pl_list_docs=()
pl_nolist_docs=()
manifest_rows=0
while IFS=$'\t' read -r mpath arms cls verdict errf tok val sumhex sha origin; do
  [ -n "$mpath" ] || continue
  case $mpath in documents/?*) ;; *) fail "a manifest path is not a document: $mpath" ;; esac
  [ -f "$corpus/$mpath" ] || fail "the manifest names an absent document: $mpath"
  got=$(sha256sum "$corpus/$mpath" | cut -d' ' -f1)
  [ "$got" = "$sha" ] || fail "the document's digest is not the manifest's: $mpath"
  M_ARMS[$mpath]=$arms
  M_CLASS[$mpath]=$cls
  M_VERDICT[$mpath]=$verdict
  M_ERR[$mpath]=$errf
  M_TOK[$mpath]=$tok
  M_VAL[$mpath]=$val
  M_SUM[$mpath]=$sumhex
  M_SHA[$mpath]=$sha
  M_ORIGIN[$mpath]=$origin
  case $arms in
    both)
      s2_list_docs+=("$mpath"); s2_nolist_docs+=("$mpath")
      pl_list_docs+=("$mpath"); pl_nolist_docs+=("$mpath")
      ;;
    list)
      s2_list_docs+=("$mpath"); pl_list_docs+=("$mpath")
      ;;
    pipeline)
      pl_list_docs+=("$mpath"); pl_nolist_docs+=("$mpath")
      ;;
    *) fail "the manifest gives $mpath an unknown arm: $arms" ;;
  esac
  manifest_rows=$((manifest_rows + 1))
done <"$manifest"
[ "$manifest_rows" -gt 0 ] || fail "the manifest is empty"

corpus_set=$(find "$docs" -mindepth 1 -maxdepth 1 -type f -printf 'documents/%f\n' | LC_ALL=C sort)
manifest_set=$(awk -F '\t' '{ print $1 }' "$manifest" | LC_ALL=C sort)
if [ "$corpus_set" != "$manifest_set" ]; then
  printf 'FAIL: the document set is not the manifest set\n' >&2
  diff <(printf '%s\n' "$corpus_set") <(printf '%s\n' "$manifest_set") | awk 'NR <= 20' >&2
  exit 1
fi

mkdir -p "$work/gen" || setup "cannot create the generator's output directory"
if ! bash "$generator" "$work/gen" >"$work/gen.log" 2>&1; then
  printf 'FAIL: the corpus generator exited nonzero\n' >&2
  cat "$work/gen.log" >&2
  exit 1
fi
if ! diff -r "$work/gen/documents" "$docs" >"$work/gen.diff" 2>&1; then
  printf 'FAIL: the committed documents are not the generator output at the fixed seed\n' >&2
  awk 'NR <= 20' "$work/gen.diff" >&2
  exit 1
fi
if ! cmp -s "$work/gen/manifest.tsv" "$manifest"; then
  printf 'FAIL: the committed manifest is not the generator output at the fixed seed\n' >&2
  diff -u "$work/gen/manifest.tsv" "$manifest" | awk 'NR <= 40' >&2
  exit 1
fi

# Every refusal class the stage-2 header names has a document.
for cls in structural number literal string-body unclosed no-value unterminated; do
  found=0
  for key in "${!M_CLASS[@]}"; do
    if [ "${M_CLASS[$key]}" = "$cls" ] && [ "${M_VERDICT[$key]}" = refuse ]; then
      found=1
      break
    fi
  done
  [ "$found" -eq 1 ] || fail "the corpus has no refusing $cls document"
done

# The pipeline route's own refusal class: the UTF-8 stage refuses at the
# document's end, so the pinned offset is the document's length.  Such a
# document is `pipeline`-arm only, because stage 2 never sees the gate.
utf8_seen=0
for key in "${!M_CLASS[@]}"; do
  [ "${M_CLASS[$key]}" = utf8-gate ] || continue
  [ "${M_VERDICT[$key]}" = refuse ] ||
    fail "the utf8-gate document $key is not refused"
  [ "${M_ARMS[$key]}" = pipeline ] ||
    fail "the utf8-gate document $key is not pipeline-arm only"
  nbytes=$(wc -c <"$corpus/$key")
  [ "${M_ERR[$key]}" = "$nbytes" ] ||
    fail "the utf8-gate offset for $key is not the document's length"
  utf8_seen=1
done
[ "$utf8_seen" -eq 1 ] || fail "the corpus has no refusing utf8-gate document"

# The corpus holds an accepted number-only and an accepted string-bearing
# document, so the sum cut below is not inert.
has_number=0
has_string=0
for key in "${!M_VERDICT[@]}"; do
  [ "${M_VERDICT[$key]}" = accept ] || continue
  case $key in
    documents/acc-number-* | documents/gen-ws-*) has_number=1 ;;
  esac
  case $key in
    documents/acc-*string* | documents/acc-key-value | documents/repo-string) has_string=1 ;;
  esac
done
[ "$has_number" -eq 1 ] || fail "the corpus has no accepted number document"
[ "$has_string" -eq 1 ] || fail "the corpus has no accepted string document"

# ------------------------------------------------------------- 1. the objects --

for unit in s1_block entry utf8 escape stage2 pipeline stage2_noevent pipeline_noevent; do
  if ! "$cc" "${cflags[@]}" -I "$repo/kernel/json" \
      -c "$repo/kernel/json/$unit.c" -o "$work/$unit.o" 2>"$work/$unit.cc"; then
    printf 'FAIL: kernel/json/%s.c did not compile at the measured flags\n' "$unit" >&2
    awk 'NR <= 20' "$work/$unit.cc" >&2
    exit 1
  fi
done

link_driver() { # $1 output, $2 stage2-noevent object, $3 pipeline-noevent object
  "$cc" -O2 -o "$1" "$driver_src" \
    "$work/s1_block.o" "$work/entry.o" "$work/utf8.o" "$work/escape.o" \
    "$work/stage2.o" "$work/pipeline.o" "$2" "$3"
}

if ! link_driver "$work/driver" "$work/stage2_noevent.o" \
    "$work/pipeline_noevent.o" 2>"$work/link.err"; then
  printf 'FAIL: the driver did not link against the kernel objects\n' >&2
  awk 'NR <= 20' "$work/link.err" >&2
  exit 1
fi

# ----------------------------------------------------------- 2. NE1 and NE3 --
#
# The driver is run once per arm.  Its rows are compared with the manifest's
# pinned rows; the comparison is the assertion, so a row that is merely printed
# is not evidence.

expect_row() { # key path verdict code err tokens values sum -> 0 when it matches
  local key=$1 v=$2 code=$3 errf=$4 tok=$5 val=$6 sum=$7 got
  case ${M_VERDICT[$key]} in
    accept)
      [ "$v" = accept ] || { printf 'its verdict is %s, the manifest pins accept\n' "$v" >&2; return 1; }
      [ "$code" = 1 ] || { printf 'its verdict word is %s, not 1\n' "$code" >&2; return 1; }
      [ "$errf" = - ] || { printf 'it carries a refusal offset on acceptance\n' >&2; return 1; }
      [ "$tok" = "${M_TOK[$key]}" ] || { printf 'tokens %s, the manifest pins %s\n' "$tok" "${M_TOK[$key]}" >&2; return 1; }
      [ "$val" = "${M_VAL[$key]}" ] || { printf 'values %s, the manifest pins %s\n' "$val" "${M_VAL[$key]}" >&2; return 1; }
      [ "$val" = "$tok" ] ||
        { printf 'values %s is not the build-mode token count %s\n' "$val" "$tok" >&2; return 1; }
      got=$(printf '%016x' "$sum" 2>/dev/null) ||
        { printf 'its sum %s is not a 64-bit word\n' "$sum" >&2; return 1; }
      [ "$got" = "${M_SUM[$key]}" ] || { printf 'sum %s, the manifest pins %s\n' "$got" "${M_SUM[$key]}" >&2; return 1; }
      ;;
    refuse)
      [ "$v" = refuse ] || { printf 'its verdict is %s, the manifest pins refuse\n' "$v" >&2; return 1; }
      [ "$code" = 0 ] || { printf 'its verdict word is %s, not 0\n' "$code" >&2; return 1; }
      [ "$errf" = "${M_ERR[$key]}" ] || { printf 'refusal offset %s, the manifest pins %s\n' "$errf" "${M_ERR[$key]}" >&2; return 1; }
      [ "$tok" = - ] && [ "$val" = - ] && [ "$sum" = - ] ||
        { printf 'a refusal carries readings: %s/%s/%s\n' "$tok" "$val" "$sum" >&2; return 1; }
      ;;
    *) printf 'the manifest has no verdict for %s\n' "$key" >&2; return 1 ;;
  esac
  return 0
}

verify_rows() { # file, route, arm, filter(all|accept|refuse), complete(1|0)
  local file=$1 route=$2 arm=$3 filter=$4 complete=$5
  local p v code errf tok val sum nk nxp extra key i=0
  local -a order
  docs_for "$route" "$arm"
  order=("${DOCS[@]}")
  while IFS=$'\t' read -r p v code errf tok val sum nk nxp extra; do
    [ -n "$p" ] || continue
    case $p in "$corpus_rel"/documents/*) ;; *) fail "a $route/$arm row names a path outside the corpus: $p" ;; esac
    key=${p#"$corpus_rel"/}
    [ -n "${M_VERDICT[$key]-}" ] || fail "a $route/$arm row names a document the manifest does not: $key"
    if [ "$route" = pipeline ]; then
      [ -z "$extra" ] || fail "$key: the pipeline row carries more than nine columns"
      case $nk in '' | *[!0-9]*) fail "$key: its nk is not a decimal word: ${nk:-<empty>}" ;; esac
      case $nxp in '' | *[!0-9]*) fail "$key: its nxp is not a decimal word: ${nxp:-<empty>}" ;; esac
      if [ "$arm" = nolist ]; then
        [ "$nxp" -eq 0 ] || fail "$key: the no-list arm reports nxp $nxp"
      else
        case ${M_ARMS[$key]} in
          list) [ "$nxp" -gt 0 ] || fail "$key: an escape-bearing document reports nxp 0" ;;
        esac
      fi
    else
      [ -z "$nk$nxp$extra" ] || fail "$key: a stage-2 row carries a pipeline column"
    fi
    case $filter in
      all) ;;
      accept) [ "${M_VERDICT[$key]}" = accept ] || continue ;;
      refuse) [ "${M_VERDICT[$key]}" = refuse ] || continue ;;
    esac
    if [ "$filter" = all ] && [ "$complete" = 1 ]; then
      [ "$i" -lt "${#order[@]}" ] || fail "the $route/$arm run printed more rows than the arm holds"
      [ "$key" = "${order[$i]}" ] || fail "row $((i + 1)) of the $route/$arm run is $key, expected ${order[$i]}"
    fi
    if ! expect_row "$key" "$v" "$code" "$errf" "$tok" "$val" "$sum"; then
      printf 'FAIL: %s (%s/%s arm) does not match the manifest:\n' "$key" "$route" "$arm" >&2
      exit 1
    fi
    i=$((i + 1))
  done <"$file"
  if [ "$filter" = all ] && [ "$complete" = 1 ] && [ "$i" -ne "${#order[@]}" ]; then
    fail "the $route/$arm run printed $i rows for ${#order[@]} documents"
  fi
}

count_rows() { # route, arm, verdict -> that arm's documents with that verdict
  local route=$1 arm=$2 want=$3 n=0 key
  docs_for "$route" "$arm"
  for key in "${DOCS[@]}"; do
    [ "${M_VERDICT[$key]}" = "$want" ] && n=$((n + 1))
  done
  echo "$n"
}

docs_for() { # route, arm -> DOCS
  case $1:$2 in
    stage2:list) DOCS=("${s2_list_docs[@]}") ;;
    stage2:nolist) DOCS=("${s2_nolist_docs[@]}") ;;
    pipeline:list) DOCS=("${pl_list_docs[@]}") ;;
    pipeline:nolist) DOCS=("${pl_nolist_docs[@]}") ;;
    *) fail "unknown route and arm: $1/$2" ;;
  esac
}

run_arm() { # route, arm, driver, out, err -> exit status
  local route=$1 arm=$2 bin=$3 out=$4 err=$5 key
  local -a args=()
  docs_for "$route" "$arm"
  for key in "${DOCS[@]}"; do args+=("$corpus_rel/$key"); done
  "$bin" --route "$route" --arm "$arm" "${args[@]}" >"$out" 2>"$err"
}

run_boundary() { # route, arm -> asserts exit 0, empty stderr, every pinned row
  local route=$1 arm=$2 status
  run_arm "$route" "$arm" "$work/driver" \
    "$work/$route-$arm.out" "$work/$route-$arm.err"
  status=$?
  if [ "$status" -ne 0 ]; then
    printf 'FAIL: the driver exited %s on the %s/%s route/arm\n' "$status" "$route" "$arm" >&2
    cat "$work/$route-$arm.err" >&2
    exit 1
  fi
  if [ -s "$work/$route-$arm.err" ]; then
    printf 'FAIL: the driver wrote to stderr on %s/%s although it exited 0\n' "$route" "$arm" >&2
    cat "$work/$route-$arm.err" >&2
    exit 1
  fi
  verify_rows "$work/$route-$arm.out" "$route" "$arm" all 1
}

for arm in list nolist; do run_boundary stage2 "$arm"; done
printf 'ok: every document agrees with the certified stage-2 entry in both arms\n'
printf 'ok: every refusal class carries its pinned offset and zeroed readings\n'

for arm in list nolist; do run_boundary pipeline "$arm"; done
printf 'ok: the two pipelines agree end to end, nk and nxp included, in both arms\n'

# --------------------------------------------------------- 3. NE6 census ----

census() { # object -> 0 when the symbol sets are exactly the declared ones
  local obj=$1 defined undef want
  defined=$(nm --defined-only -g "$obj" | awk '{ print $NF }' | LC_ALL=C sort)
  want=$(printf 'leanllvm_json_stage2_noevent\nleanllvm_json_stage2_noevent_lib\n' | LC_ALL=C sort)
  if [ "$defined" != "$want" ]; then
    printf 'the object defines:\n%s\nnot exactly:\n%s\n' "$defined" "$want" >&2
    return 1
  fi
  undef=$(nm -u "$obj" | awk '{ print $NF }' | grep -E '^leanllvm_json_' | LC_ALL=C sort)
  if [ "$undef" != "leanllvm_json_escape_expand" ]; then
    printf 'the object leaves these project symbols undefined:\n%s\n' "${undef:-<none>}" >&2
    return 1
  fi
  return 0
}

if ! census "$work/stage2_noevent.o"; then
  printf 'FAIL: the no-event object'"'"'s symbol census is not the declared one\n' >&2
  exit 1
fi
printf 'ok: the object defines its two entries and leaves only leanllvm_json_escape_expand undefined\n'

# The census control: a staged reference to a stage-1 symbol.  The cut is built
# from a copy of the committed source, so nothing in the tree moves.
cp "$repo/kernel/json/stage2_noevent.c" "$work/stage2_noevent_stage1.c" ||
  setup "cannot stage the census control"
cat >>"$work/stage2_noevent_stage1.c" <<'CUT'

/* The census control: a reference to a stage-1 symbol the entry never calls. */
extern void leanllvm_json_s1_masks(const uint8_t *p, void *carry, void *out);
static void (*volatile ne_cut_stage1_ref)(const uint8_t *, void *, void *)
    __attribute__((used)) = leanllvm_json_s1_masks;
CUT
if cmp -s "$repo/kernel/json/stage2_noevent.c" "$work/stage2_noevent_stage1.c"; then
  setup "the stage-1 reference cut did not apply"
fi
if ! "$cc" "${cflags[@]}" -I "$repo/kernel/json" \
    -c "$work/stage2_noevent_stage1.c" -o "$work/stage2_noevent_stage1.o" \
    2>"$work/stage1.cc"; then
  printf 'FAIL: the staged stage-1 reference did not compile\n' >&2
  awk 'NR <= 20' "$work/stage1.cc" >&2
  exit 1
fi
if census "$work/stage2_noevent_stage1.o" >"$work/stage1.census" 2>&1; then
  printf 'FAIL: the census passed an object that references leanllvm_json_s1_masks\n' >&2
  exit 1
fi
grep -q '^leanllvm_json_s1_masks$' "$work/stage1.census" ||
  fail "the census did not name the staged stage-1 reference"
grep -q '^leanllvm_json_escape_expand$' "$work/stage1.census" ||
  fail "the census's report lost the object's declared undefined symbol"
printf 'ok: the census reports a staged stage-1 reference (leanllvm_json_s1_masks)\n'

# ------------------------------------------------- 4. NE1 defect: the sum ----
#
# The staged cut omits the record payload from the sum accumulator
# (`terms += tag + len`).  It leaves every verdict, refusal offset and refusal
# slot untouched, so accepting rows that carry no string keep their readings
# and every refusing row stays green; the accepted string-bearing rows are the
# ones that move.

awk '
  /\+ \(uint64_t\)\(rf\);/ { sub(/\+ \(uint64_t\)\(rf\);/, ";"); hit = 1 }
  { print }
  END { exit(hit ? 0 : 1) }
' "$repo/kernel/json/stage2_noevent.c" >"$work/stage2_noevent_sum.c" ||
  setup "the sum cut did not apply"
if cmp -s "$repo/kernel/json/stage2_noevent.c" "$work/stage2_noevent_sum.c"; then
  setup "the sum cut did not apply"
fi
if ! "$cc" "${cflags[@]}" -I "$repo/kernel/json" \
    -c "$work/stage2_noevent_sum.c" -o "$work/stage2_noevent_sum.o" \
    2>"$work/sum.cc"; then
  printf 'FAIL: the sum cut did not compile\n' >&2
  awk 'NR <= 20' "$work/sum.cc" >&2
  exit 1
fi
link_driver "$work/driver_sum" "$work/stage2_noevent_sum.o" \
  "$work/pipeline_noevent.o" ||
  fail "the sum-cut driver did not link"

run_arm stage2 list "$work/driver_sum" "$work/sum.out" "$work/sum.err"
status=$?
[ "$status" -eq 3 ] ||
  fail "the sum cut exited $status, and a differential failure exits 3"
grep -q '^FAIL .*reading: reference' "$work/sum.err" ||
  fail "the sum cut did not fire the reading assertion"
grep -q "documents/acc-string" "$work/sum.err" ||
  fail "the sum cut did not fire on an accepted string-bearing document"
if grep -q "documents/acc-number-array" "$work/sum.err"; then
  fail "the sum cut fired on a number-only document, which it cannot change"
fi
grep -q "documents/acc-number-array" "$work/sum.out" ||
  fail "the sum cut lost a number-only document's agreeing row"
verify_rows "$work/sum.out" stage2 list refuse 0
[ "$(awk -F '\t' '$2 == "refuse"' "$work/sum.out" | wc -l)" -eq "$(count_rows stage2 list refuse)" ] ||
  fail "the sum cut lost a refusing document's row"
printf 'ok: omitting the record payload fires the reading assertion on strings only\n'

# --------------------------------------------- 5. NE3 defect: refusal slots --
#
# The staged cut deletes the three refusal stores.  The slots keep their
# sentinel, which is what the driver's refusal message must report; accepting
# rows are unchanged.

awk '
  /\*tokens_out = 0;/ { t_seen = 1; next }
  /\*values_out = 0;/ { v_seen = 1; next }
  /\*sum_out = 0;/ { s_seen = 1; next }
  { print }
  END { exit(t_seen && v_seen && s_seen ? 0 : 1) }
' "$repo/kernel/json/stage2_noevent.c" >"$work/stage2_noevent_slots.c" ||
  setup "the refusal-store cut did not apply"
if cmp -s "$repo/kernel/json/stage2_noevent.c" "$work/stage2_noevent_slots.c"; then
  setup "the refusal-store cut did not apply"
fi
if ! "$cc" "${cflags[@]}" -I "$repo/kernel/json" \
    -c "$work/stage2_noevent_slots.c" -o "$work/stage2_noevent_slots.o" \
    2>"$work/slots.cc"; then
  printf 'FAIL: the refusal-store cut did not compile\n' >&2
  awk 'NR <= 20' "$work/slots.cc" >&2
  exit 1
fi
link_driver "$work/driver_slots" "$work/stage2_noevent_slots.o" \
  "$work/pipeline_noevent.o" ||
  fail "the refusal-store driver did not link"

run_arm stage2 list "$work/driver_slots" "$work/slots.out" "$work/slots.err"
status=$?
[ "$status" -eq 3 ] ||
  fail "the refusal-store cut exited $status, and a differential failure exits 3"
grep -q "^FAIL .*refusal slots: expected zero, got $sentinel/$sentinel/$sentinel" \
  "$work/slots.err" ||
  fail "the refusal-store cut did not report the untouched slots as the sentinel"
verify_rows "$work/slots.out" stage2 list accept 0
[ "$(awk -F '\t' '$2 == "accept"' "$work/slots.out" | wc -l)" -eq "$(count_rows stage2 list accept)" ] ||
  fail "the refusal-store cut lost an accepting document's row"
printf 'ok: no-opping the refusal stores reports the sentinel the pre-fill exists for\n'

# ---------------------------------------- 6. NE2 defects: the pipeline tail --
#
# Two cuts, each built from a copy of the committed pipeline entry, show the
# pipeline comparison binding the two things the stage-2 boundary cannot see:
# the stage-2 tail's escape list and the entry's pre-zero.
#
# Cut A passes `nxp = 0` to the stage-2 tail instead of the stage-1 count.  The
# stage-1 outputs are untouched, so `nk` and `nxp` still agree; an accepted
# escape-bearing document is read as a plain span and its reading moves.

awk '
  /xp, \*nxp,/ { sub(/xp, \*nxp,/, "xp, 0,"); hit = 1 }
  { print }
  END { exit(hit ? 0 : 1) }
' "$repo/kernel/json/pipeline_noevent.c" >"$work/pipeline_noevent_nxp0.c" ||
  setup "the pipeline escape-list cut did not apply"
if cmp -s "$repo/kernel/json/pipeline_noevent.c" "$work/pipeline_noevent_nxp0.c"; then
  setup "the pipeline escape-list cut did not apply"
fi
if ! "$cc" "${cflags[@]}" -I "$repo/kernel/json" \
    -c "$work/pipeline_noevent_nxp0.c" -o "$work/pipeline_noevent_nxp0.o" \
    2>"$work/nxp0.cc"; then
  printf 'FAIL: the pipeline escape-list cut did not compile\n' >&2
  awk 'NR <= 20' "$work/nxp0.cc" >&2
  exit 1
fi
link_driver "$work/driver_nxp0" "$work/stage2_noevent.o" \
  "$work/pipeline_noevent_nxp0.o" ||
  fail "the escape-list-cut driver did not link"

run_arm pipeline list "$work/driver_nxp0" "$work/nxp0.out" "$work/nxp0.err"
status=$?
[ "$status" -eq 3 ] ||
  fail "the escape-list cut exited $status, and a differential failure exits 3"
grep -q '^FAIL .*reading: pipeline' "$work/nxp0.err" ||
  fail "the escape-list cut did not fire the reading assertion"
grep -q "documents/acc-esc-string" "$work/nxp0.err" ||
  fail "the escape-list cut did not fire on an accepted escape-bearing document"
if grep -q '^FAIL .* nxp:' "$work/nxp0.err"; then
  fail "the escape-list cut changed nxp, and it cannot"
fi
if grep -q '^FAIL .* nk:' "$work/nxp0.err"; then
  fail "the escape-list cut changed nk, and it cannot"
fi
while read -r p; do
  [ -n "$p" ] || continue
  key=${p#"$corpus_rel"/}
  [ "${M_ARMS[$key]}" = list ] ||
    fail "the escape-list cut fired on the escape-free $key"
done < <(awk '/^FAIL / { print $2 }' "$work/nxp0.err")
grep -q "documents/acc-number-array" "$work/nxp0.out" ||
  fail "the escape-list cut lost an escape-free document's agreeing row"
verify_rows "$work/nxp0.out" pipeline list all 0
printf 'ok: zeroing the tail beside agreeing nk/nxp fires the reading assertion on escapes only\n'

# Cut B deletes the entry's three pre-zero stores (the post's totality on the
# UTF-8 gate's refusal, which returns before the tail).  The slots keep the
# caller's sentinel, and the check's own corpus carries the document that
# reaches that path.

awk '
  /^[[:space:]]*\*tokens = 0;$/ { t_seen = 1; next }
  /^[[:space:]]*\*values = 0;$/ { v_seen = 1; next }
  /^[[:space:]]*\*sum = 0;$/ { s_seen = 1; next }
  { print }
  END { exit(t_seen && v_seen && s_seen ? 0 : 1) }
' "$repo/kernel/json/pipeline_noevent.c" >"$work/pipeline_noevent_nozero.c" ||
  setup "the entry pre-zero cut did not apply"
if cmp -s "$repo/kernel/json/pipeline_noevent.c" "$work/pipeline_noevent_nozero.c"; then
  setup "the entry pre-zero cut did not apply"
fi
if ! "$cc" "${cflags[@]}" -I "$repo/kernel/json" \
    -c "$work/pipeline_noevent_nozero.c" -o "$work/pipeline_noevent_nozero.o" \
    2>"$work/nozero.cc"; then
  printf 'FAIL: the entry pre-zero cut did not compile\n' >&2
  awk 'NR <= 20' "$work/nozero.cc" >&2
  exit 1
fi
link_driver "$work/driver_nozero" "$work/stage2_noevent.o" \
  "$work/pipeline_noevent_nozero.o" ||
  fail "the pre-zero-cut driver did not link"

run_arm pipeline list "$work/driver_nozero" "$work/nozero.out" "$work/nozero.err"
status=$?
[ "$status" -eq 3 ] ||
  fail "the entry pre-zero cut exited $status, and a differential failure exits 3"
grep -q "^FAIL .*refusal slots: expected zero, got $sentinel/$sentinel/$sentinel" \
  "$work/nozero.err" ||
  fail "the entry pre-zero cut did not report the untouched slots as the sentinel"
grep -q "documents/refuse-utf8-gate" "$work/nozero.err" ||
  fail "the entry pre-zero cut did not fire on the UTF-8 gate's refusal"
[ "$(grep -c 'refusal slots' "$work/nozero.err")" -eq 1 ] ||
  fail "the entry pre-zero cut fired on a refusal path it does not own"
if grep -q '^FAIL .*reading:' "$work/nozero.err"; then
  fail "the entry pre-zero cut changed an accepted reading"
fi
grep -q "documents/acc-number-array" "$work/nozero.out" ||
  fail "the entry pre-zero cut lost an accepting document's row"
grep -q "documents/ref-lit-tru" "$work/nozero.out" ||
  fail "the entry pre-zero cut lost a walk refusal's row"
verify_rows "$work/nozero.out" pipeline list all 0
printf 'ok: deleting the entry pre-zero leaves the sentinel on the UTF-8 gate only\n'

# --------------------------------------------------- 7. NE4 byte identity ---
#
# The detector compares a path's bytes with the pinned base revision's blob.
# Its positive control is one changed byte in a throwaway copy; its affirmative
# control is an unchanged copy of the same bytes.

identity() { # root, path -> 0 when root/path equals the base blob
  local root=$1 path=$2
  [ -f "$root/$path" ] || { printf 'absent: %s\n' "$root/$path" >&2; return 1; }
  git -C "$repo" show "$base:$path" >"$work/base.blob" 2>"$work/base.err" || {
    printf 'the base blob for %s is not readable\n' "$path" >&2
    return 1
  }
  cmp -s "$work/base.blob" "$root/$path" || {
    printf '%s differs from %s\n' "$path" "$base" >&2
    return 1
  }
  return 0
}

for path in "${protected[@]}"; do
  if ! identity "$repo" "$path"; then
    printf 'FAIL: a protected artefact differs from the base revision\n' >&2
    exit 1
  fi
done
printf 'ok: the protected artefact set is byte-identical to %s\n' "$base"

mkdir -p "$work/clean/kernel/json" "$work/tamper/kernel/json" ||
  setup "cannot create the identity control's directories"
cp "$repo/kernel/json/stage2.c" "$work/clean/kernel/json/stage2.c" ||
  setup "cannot stage the identity controls"
cp "$repo/kernel/json/stage2.c" "$work/tamper/kernel/json/stage2.c" ||
  setup "cannot stage the identity controls"
printf '\x00' | dd of="$work/tamper/kernel/json/stage2.c" bs=1 seek=0 \
  conv=notrunc status=none || setup "cannot change the control's one byte"
if identity "$work/clean" kernel/json/stage2.c; then
  :
else
  printf 'FAIL: the identity detector rejects an unchanged copy\n' >&2
  exit 1
fi
if identity "$work/tamper" kernel/json/stage2.c >"$work/identity.tamper" 2>&1; then
  printf 'FAIL: the identity detector passed a copy with one byte changed\n' >&2
  exit 1
fi
grep -q 'differs from' "$work/identity.tamper" ||
  fail "the identity detector failed the changed copy without saying why"
printf 'ok: the identity detector bites one changed byte and passes the unchanged copy (%s)\n' \
  "$(head -n 1 "$work/identity.tamper")"

for unit in stage2 pipeline; do
  if ! bash "$repo/kernel/json/identity/source-identity.sh" --unit "$unit" \
      --arms-only >"$work/identity.$unit.out" 2>&1; then
    printf 'FAIL: the %s identity arm exited nonzero\n' "$unit" >&2
    awk 'NR <= 40' "$work/identity.$unit.out" >&2
    exit 1
  fi
  grep -q '^ok: the unit defines exactly its one ABI symbol$' \
    "$work/identity.$unit.out" ||
    fail "the $unit identity arm did not report its one-symbol census"
  grep -q "^ok: source identity holds ($unit)$" "$work/identity.$unit.out" ||
    fail "the $unit identity arm did not report its source identity"
done
printf 'ok: the stage-2 and pipeline identity arms report their one-symbol censuses\n'

printf 'ok: the no-event entries agree with the certified routes; the sentinel separates refusals; the census and the byte identity are pinned\n'
exit 0
