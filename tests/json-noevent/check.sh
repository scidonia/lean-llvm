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
#   NE12 — the shipped default's dispatch.  One staged document carries the
#   comparison: plain `--consume` prints the same `reading` line as
#   `--consume-noevent` and as `--arm noevent --consume`, so the default
#   spelling is the no-event arm; `--arm events --consume` reaches the
#   certified event consumer and agrees with `--consume-events`, and a `--arm`
#   word that contradicts the mode's spelling exits 1 with the reason.
#
#   NE7 — the route's no-event arm agrees with its C caller and the certified
#   event arm.  Over the corpus's documents the shipped route
#   (`--consume-noevent`) and the C caller (`--noevent`) must print the same
#   `reading` line field for field; the certified event arm is the reference,
#   reached explicitly (`--consume-events`, or `--arm events --consume`).  On
#   the documents the arm is admitted to,
#   that line's verdict, `nk`, `nxp` and `err` equal the event arm's
#   observation and its `tokens`/`values`/`sum` equal the event arm's
#   consumer reading; an acceptance's `tokens` and `values` agree and are
#   non-zero; a refusal carries zero in all three and the certified offset.
#   The route binary is the build step's artefact, so an absent one is a setup
#   fault naming the build command.
#
#   NE8 — the certified event arm is unchanged.  Over all 183 documents the
#   base rows pin, the event arm's exit word, six observation words, arena and
#   event payload digests, document digest and whole-stdout digest must equal
#   `base-event-rows.tsv`'s, which records the base revision and the base
#   binary's digest.  The rows are the fixture; the comparison is per
#   document.
#
#   NE13 — the value arm's decoded reading.  `--value` prints one stdout line
#   per document: `value: verdict=1 value=<hex>` at exit 0 on an acceptance,
#   and `value: refused class=<class> offset=<offset>` at exit 2 on a
#   refusal, where the class is the reference's `parseErrorName` and the
#   offset is its position or `-`.  A reference acceptance whose canonical
#   value cannot be produced is `value: error canon` at exit 5, a form no
#   expected row admits.  The value is the lowercase hex of the UTF-8 bytes of
#   `renderValue (canonValue v)` on the document's own bytes; the expected
#   field of each document is pinned in `tests/json-value/expected.tsv`.  Two
#   controls run first — the field reader over the certified event arm's own
#   row, and the reference's refusal through the fallback on the document the
#   admission declines — so a red below is the arm's absence and not a blind
#   detector.  At the pre-change revision `--value` is not a mode: the
#   invocation exits 1 and prints the usage line, so the probe reds at its own
#   exit-status assertion.
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

# The certifying route's ABI artefact set: the two kernel units the no-event
# entry leaves untouched and their pinned fixtures.  The shipped route's build
# list is not compared: no ABI byte of it is at stake, and the event arm's
# byte identity is NE8's subject.
protected=(
  kernel/json/stage2.c
  kernel/json/stage2.h
  kernel/json/pipeline.c
  kernel/json/pipeline.h
  probes/install/ir/stage2.candidate.ll
  probes/install/ir/json-pipeline.candidate.ll
)

# The driver's sentinel, `0xDEADBEEFDEADBEEF`, in decimal.
sentinel=16045690984833335023

setup() { printf 'SETUP: %s\n' "$1" >&2; exit 3; }
fail() { printf 'FAIL: %s\n' "$1" >&2; exit 1; }

# A hex string as bytes, the conversion the event payloads' digests need.  It
# is `xxd -r -p`'s read without depending on vim's tool: `sed` pairs the
# digits into `\xNN` escapes and `printf` writes them.  An odd trailing nibble
# is dropped, as `xxd -r -p` drops it; the payloads are even-length.
hex_to_bin() {
  local h=$1
  [ -n "$h" ] || return 0
  [ $(( ${#h} % 2 )) -eq 0 ] || h=${h%?}
  printf '%b' "$(printf '%s' "$h" | sed 's/../\\x&/g')"
}

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
# The route binary and its C caller are the shipped build step's artefacts.
# They are not rebuilt here: the build step compiles the Lean program against
# the Lake modules, and a scenario that rebuilt the program would be running a
# different actor from the one the build asserts.
route_bin=${ROUTE:-"$repo/probes/json/route/build/leanllvm-json-route"}
c_driver=${NOEVENT_DRIVER:-"$repo/probes/json/route/build/driver"}
base_rows=$repo/$route_rel/base-event-rows.tsv
[ -f "$base_rows" ] || setup "absent: $base_rows"
if [ ! -x "$route_bin" ]; then
  setup "absent: $route_bin
  build the route with: nix develop -c bash probes/json/route/build.sh"
fi
if [ ! -x "$c_driver" ]; then
  setup "absent: $c_driver
  build the route with: nix develop -c bash probes/json/route/build.sh"
fi
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

# ------------------------- 8. NE12: the shipped default's dispatch --------
#
# The default spelling is the arm a caller gets without naming one, so its
# reading is compared with the arm's spelled-out name and with the `--arm`
# spelling of that arm.  The certified event arm is reached through `--arm
# events` and compared with its own flag, and a `--arm` word that contradicts
# the mode's spelling is refused.  One document carries every invocation, so
# each comparison is made on the same bytes.

# One `name=value` field from a space-separated line: the reading line, the
# event arm's observation line and its consumer row are all that form.
word() { # line, name -> the first value, empty when the name is absent
  printf '%s\n' "$1" | tr ' ' '\n' | sed -n "s/^$2=//p" | head -n 1
}

ne12_doc=$repo/tests/json/corpus/depth-two-ok.json
[ -f "$ne12_doc" ] || setup "absent: $ne12_doc"

"$route_bin" --consume "$ne12_doc" \
  >"$work/ne12.default.out" 2>"$work/ne12.default.err"
ne12_dst=$?
ne12_default=$(cat "$work/ne12.default.out")
"$route_bin" --consume-noevent "$ne12_doc" \
  >"$work/ne12.explicit.out" 2>"$work/ne12.explicit.err"
ne12_est=$?
ne12_explicit=$(cat "$work/ne12.explicit.out")
[ "$ne12_dst" -eq 0 ] && [ "$ne12_est" -eq 0 ] && [ -n "$ne12_default" ] &&
  [ "$ne12_default" = "$ne12_explicit" ] || {
  printf 'FAIL: --consume is not the no-event arm on depth-two-ok.json\n' >&2
  printf '  --consume:         %s (exit %s)\n  --consume-noevent: %s (exit %s)\n' \
    "$ne12_default" "$ne12_dst" "$ne12_explicit" "$ne12_est" >&2
  exit 1
}
case $ne12_default in
  'reading verdict='*) ;;
  *) fail "--consume's line is not the reading form: $ne12_default" ;;
esac

"$route_bin" --arm noevent --consume "$ne12_doc" \
  >"$work/ne12.armnoevent.out" 2>"$work/ne12.armnoevent.err"
st=$?
ne12_armnoevent=$(cat "$work/ne12.armnoevent.out")
[ "$st" -eq 0 ] && [ "$ne12_armnoevent" = "$ne12_default" ] ||
  fail "--arm noevent --consume is not the default reading: '$ne12_armnoevent' (exit $st) against '$ne12_default'"

"$route_bin" --consume-events "$ne12_doc" \
  >"$work/ne12.events.out" 2>"$work/ne12.events.err"
ne12_evst=$?
ne12_eventsrow=$(cat "$work/ne12.events.err")
"$route_bin" --arm events --consume "$ne12_doc" \
  >"$work/ne12.armevents.out" 2>"$work/ne12.armevents.err"
ne12_armst=$?
ne12_armeventsrow=$(cat "$work/ne12.armevents.err")
ne12_same=0
if [ "$ne12_evst" -eq 0 ] && [ "$ne12_armst" -eq 0 ] &&
   [ ! -s "$work/ne12.armevents.out" ] &&
   [ "$(word "$ne12_eventsrow" path)" = fast ] &&
   [ "$(word "$ne12_eventsrow" walked)" = 1 ]; then
  ne12_same=1
  for f in path verdict ndst nev tokens values walked foldsum valuessum; do
    [ "$(word "$ne12_eventsrow" "$f")" = "$(word "$ne12_armeventsrow" "$f")" ] ||
      ne12_same=0
  done
  [ "$(word "$ne12_eventsrow" tokens)" = "$(word "$ne12_default" tokens)" ] ||
    ne12_same=0
  [ "$(word "$ne12_eventsrow" foldsum)" = "$(word "$ne12_default" sum)" ] ||
    ne12_same=0
fi
[ "$ne12_same" -eq 1 ] || {
  printf 'FAIL: --arm events --consume does not reach the certified event consumer on depth-two-ok.json\n' >&2
  printf '  --consume-events:       %s (exit %s)\n  --arm events --consume: %s (exit %s)\n  --consume:              %s\n' \
    "$ne12_eventsrow" "$ne12_evst" "$ne12_armeventsrow" "$ne12_armst" "$ne12_default" >&2
  exit 1
}

while read -r arm mode; do
  "$route_bin" --arm "$arm" "$mode" "$ne12_doc" \
    >"$work/ne12.conflict.out" 2>"$work/ne12.conflict.err"
  st=$?
  [ "$st" -eq 1 ] && [ ! -s "$work/ne12.conflict.out" ] &&
    grep -qx "route: --arm and the mode's spelling name different arms" \
      "$work/ne12.conflict.err" ||
    fail "--arm $arm $mode exited $st without the conflicting-arms reason"
done <<'EOF'
events --consume-noevent
noevent --consume-events
EOF
printf 'ok: --consume is the no-event arm, --arm names that same arm and the certified event arm, and conflicting spellings are refused\n'

# ------------------------------------------------- 9. NE7: the arms agree ----
#
# The shipped route is the third actor.  Its `--consume-noevent` line and the C
# caller's `--noevent` line are compared literally, and the certified event arm
# is the reference for every word they carry: the observation words come from
# the event arm's `--doc` line and the reading words from its `--consume-events`
# row.  The event arm is run on the same document, so the reference cannot
# drift from the document under test.

ne7_docs=0
ne7_read=0
ne7_fallback=0
while IFS=$'\t' read -r key arms cls verdict errf tok val sumhex sha origin; do
  [ -n "$key" ] || continue
  ne7_docs=$((ne7_docs + 1))
  doc=$corpus/$key

  "$route_bin" --consume-noevent "$doc" \
    >"$work/ne7.route.out" 2>"$work/ne7.route.err"
  rst=$?
  if [ "$rst" -ne 0 ]; then
    printf 'FAIL: --consume-noevent exited %s on %s\n' "$rst" "$key" >&2
    awk 'NR <= 5' "$work/ne7.route.err" >&2
    exit 1
  fi

  if [ ! -s "$work/ne7.route.out" ]; then
    # The arm is entered only on a document the admission admits.  The one
    # document it does not enter is the empty one, and the C caller refuses
    # that document at its own entry with the record's reason.
    ne7_fallback=$((ne7_fallback + 1))
    [ "$(wc -c <"$doc")" -eq 0 ] ||
      fail "$key: --consume-noevent printed no reading and the document is not empty"
    grep -q ' path=fallback ' "$work/ne7.route.err" ||
      fail "$key: --consume-noevent printed no reading on an admitted document"
    "$c_driver" --noevent "$doc" \
      >"$work/ne7.driver.out" 2>"$work/ne7.driver.err"
    dst=$?
    [ "$dst" -eq 2 ] ||
      fail "$key: the C caller exited $dst on the empty document, and its entry refuses it at 2"
    grep -q '^refused: empty input' "$work/ne7.driver.err" ||
      fail "$key: the C caller did not report the empty input as its refusal"
    continue
  fi

  ne7_read=$((ne7_read + 1))
  [ "$(wc -l <"$work/ne7.route.out")" -eq 1 ] ||
    fail "$key: --consume-noevent printed $(wc -l <"$work/ne7.route.out") lines"
  rline=$(cat "$work/ne7.route.out")
  case $rline in
    'reading verdict='*) ;;
    *) fail "$key: --consume-noevent did not print a reading line: $rline" ;;
  esac

  "$c_driver" --noevent "$doc" \
    >"$work/ne7.driver.out" 2>"$work/ne7.driver.err"
  dst=$?
  [ "$dst" -eq 0 ] || {
    printf 'FAIL: the C caller exited %s on %s\n' "$dst" "$key" >&2
    awk 'NR <= 5' "$work/ne7.driver.err" >&2
    exit 1
  }
  [ -s "$work/ne7.driver.err" ] &&
    fail "$key: the C caller wrote to stderr although it exited 0"
  dline=$(cat "$work/ne7.driver.out")
  [ "$rline" = "$dline" ] || {
    printf 'FAIL: the route and the C caller print different readings on %s\n' "$key" >&2
    printf '  route:  %s\n  driver: %s\n' "$rline" "$dline" >&2
    exit 1
  }

  # The certified event arm, on the same bytes: the observation and the
  # consumer's reading of the event stream and arena.
  "$route_bin" --consume-events "$doc" \
    >"$work/ne7.consume.out" 2>"$work/ne7.consume.err"
  cst=$?
  if [ "$cst" -ne 0 ]; then
    printf 'FAIL: --consume-events exited %s on %s\n' "$cst" "$key" >&2
    awk 'NR <= 5' "$work/ne7.consume.err" >&2
    exit 1
  fi
  crow=$(cat "$work/ne7.consume.err")
  [ "$(word "$crow" path)" = fast ] ||
    fail "$key: the event arm did not run the fast path beside the arm's evidence"
  [ "$(word "$crow" walked)" = 1 ] ||
    fail "$key: the event arm's consumer did not walk the stream to its end"

  "$route_bin" --doc "$doc" >"$work/ne7.doc.out" 2>"$work/ne7.doc.err"
  est=$?
  [ "$est" -eq 0 ] || {
    printf 'FAIL: --doc exited %s on %s\n' "$est" "$key" >&2
    awk 'NR <= 5' "$work/ne7.doc.err" >&2
    exit 1
  }
  [ -s "$work/ne7.doc.err" ] &&
    fail "$key: the event arm wrote to stderr although it exited 0"
  drow=$(sed -n '1p' "$work/ne7.doc.out")

  rv=$(word "$rline" verdict)
  rnk=$(word "$rline" nk)
  rnxp=$(word "$rline" nxp)
  rerr=$(word "$rline" err)
  rt=$(word "$rline" tokens)
  rval=$(word "$rline" values)
  rs=$(word "$rline" sum)

  dv=$(word "$drow" verdict)
  dnk=$(word "$drow" nk)
  dnxp=$(word "$drow" nxp)
  derr=$(word "$drow" err)

  ct=$(word "$crow" tokens)
  cval=$(word "$crow" values)
  cs=$(word "$crow" foldsum)
  cvs=$(word "$crow" valuessum)
  cverdict=$(word "$crow" verdict)

  # The reference is one arm, so its verdict word must be the same on both of
  # its readings before either is used.  The payload words (`ndst`, `nev`) are
  # not compared between the two halves: the arm's own reading does not carry
  # them, and the event arm's printed `nev` is NE8's subject, not this arm's.
  [ "$dv" = "$cverdict" ] ||
    fail "$key: the event arm's observation says verdict $dv and its consumer $cverdict"

  case ${M_VERDICT[$key]} in
    accept) [ "$rv" = 1 ] || fail "$key: the manifest pins accept and the arm reads verdict $rv" ;;
    refuse) [ "$rv" = 0 ] || fail "$key: the manifest pins refuse and the arm reads verdict $rv" ;;
  esac

  [ "$rv" = "$dv" ] || fail "$key: the arm's verdict $rv, the event arm's $dv"
  [ "$rnk" = "$dnk" ] || fail "$key: the arm's nk $rnk, the event arm's $dnk"
  [ "$rnxp" = "$dnxp" ] || fail "$key: the arm's nxp $rnxp, the event arm's $dnxp"
  [ "$rerr" = "$derr" ] || fail "$key: the arm's err $rerr, the event arm's $derr"

  if [ "$rv" = 1 ]; then
    [ "$rt" = "$ct" ] || fail "$key: the arm's tokens $rt, the event arm's $ct"
    [ "$rval" = "$cval" ] || fail "$key: the arm's values $rval, the event arm's $cval"
    [ "$rs" = "$cs" ] || fail "$key: the arm's sum $rs, the event arm's fold sum $cs"
    [ "$rt" = "$rval" ] ||
      fail "$key: an acceptance's tokens $rt and values $rval disagree"
    [ "$rt" -gt 0 ] || fail "$key: an acceptance carries no token"
    [ "$cs" = "$cvs" ] ||
      fail "$key: the event arm's fold sum $cs and values sum $cvs disagree"
  else
    # A walk refusal leaves the prefix events the object wrote before it failed,
    # so the event arm's consumer still reads them; the no-event entry's
    # refusal semantics are the three zeros, and the offset is the certified one.
    [ "$rt" = 0 ] && [ "$rval" = 0 ] && [ "$rs" = 0 ] ||
      fail "$key: a refusal carries a reading: $rt/$rval/$rs"
    [ "$rerr" = "${M_ERR[$key]}" ] ||
      fail "$key: a refusal's offset $rerr is not the certified ${M_ERR[$key]}"
  fi
done <"$manifest"

[ "$ne7_docs" -gt 0 ] || fail "the manifest is empty"
[ "$ne7_read" -gt 0 ] || fail "the no-event arm printed no reading on the corpus"
printf 'ok: the route and the C caller print one identical reading on all %s admitted documents\n' \
  "$ne7_read"
printf 'ok: every one of those readings equals the event arm (six words, tokens, values, fold sum)\n'
printf 'ok: %s empty document(s) are outside the arm and refused at the driver entry\n' \
  "$ne7_fallback"

# ---------------------------------------- 10. NE8: the event arm is frozen --
#
# The base rows are the fixture: each document's exit word, its six observation
# words, the digests of its arena and event payloads, its own digest, and the
# digest of the base route's whole stdout.  The event arm is run on every row's
# document and compared with the row, so a changed word, a changed payload, a
# changed document or a changed output line is a failure at that document.

grep -qx '# base revision: 691ca12dc1b6afa8e05ff5828003fdadd15c9c1c' "$base_rows" ||
  fail "the base rows do not record the base revision"
grep -qx '# base binary: 86fbb06b3ab8d498e7edc73ee49abae5484ac66f1f12b9345aa2cbf5ac901e40' "$base_rows" ||
  fail "the base rows do not record the base binary"

base_count=$(awk '!/^#/ && NF { n++ } END { print n + 0 }' "$base_rows")
[ "$base_count" -eq 183 ] ||
  fail "the base rows carry $base_count rows, and the record pins 183"
base_dups=$(awk -F '\t' '!/^#/ && NF { print $1 }' "$base_rows" | LC_ALL=C sort | uniq -d)
[ -z "$base_dups" ] ||
  fail "the base rows name a document twice: $(printf '%s' "$base_dups" | head -n 1)"

ne8_rows=0
while IFS=$'\t' read -r p ex pv pnk pnxp pndst pnev perr pash pesh pdsha posha; do
  case $p in '' | '#'*) continue ;; esac
  ne8_rows=$((ne8_rows + 1))
  abspath=$repo/$p
  [ -f "$abspath" ] || fail "a base row names an absent document: $p"
  got=$(sha256sum "$abspath" | cut -d' ' -f1)
  [ "$got" = "$pdsha" ] ||
    fail "$p: the document's digest is not the base row's (the fixture moved)"

  "$route_bin" --doc "$abspath" >"$work/ne8.out" 2>"$work/ne8.err"
  st=$?
  if [ "$st" -ne "$ex" ]; then
    printf 'FAIL: %s: the event arm exited %s, the base row pins %s\n' "$p" "$st" "$ex" >&2
    awk 'NR <= 5' "$work/ne8.err" >&2
    exit 1
  fi
  got=$(sha256sum <"$work/ne8.out" | cut -d' ' -f1)
  [ "$got" = "$posha" ] ||
    fail "$p: the event arm's stdout digest $got is not the base row's $posha"

  line=$(sed -n '1p' "$work/ne8.out")
  want="verdict=$pv nk=$pnk nxp=$pnxp ndst=$pndst nev=$pnev err=$perr"
  [ "$line" = "$want" ] || {
    printf 'FAIL: %s: the event arm observation is not the base row'"'"'s\n' "$p" >&2
    printf '  current: %s\n  base:    %s\n' "$line" "$want" >&2
    exit 1
  }
  arena=$(sed -n 's/^arena=//p' "$work/ne8.out")
  events=$(sed -n 's/^events=//p' "$work/ne8.out")
  got=$(hex_to_bin "$arena" | sha256sum | cut -d' ' -f1)
  [ "$got" = "$pash" ] || fail "$p: the arena's digest $got is not the base row's $pash"
  got=$(hex_to_bin "$events" | sha256sum | cut -d' ' -f1)
  [ "$got" = "$pesh" ] || fail "$p: the event stream's digest $got is not the base row's $pesh"
done <"$base_rows"

[ "$ne8_rows" -eq "$base_count" ] ||
  fail "the base rows yielded $ne8_rows rows of a pinned $base_count"
printf 'ok: the event arm reproduces all %s base rows (exit, six words, both payloads, document and stdout)\n' \
  "$ne8_rows"

# ----------------------------- 11. NE13: the value arm's decoded reading --
#
# `--value` answers a document from the reference path, not the fast path:
#
#   value: verdict=1 value=<hex>              exit 0
#   value: refused class=<class> offset=<n>   exit 2
#   value: error canon                        exit 5
#
# `<hex>` is the lowercase hex of the UTF-8 bytes of `renderValue (canonValue
# v)`, the value the reference path gives (`decodeTape` of `parseBytes`' tape)
# on the document's own bytes.  The line is whitespace-separated, so the value
# travels as hex and a string carrying its own spaces cannot split the line.
# `<class>` is the reference's `parseErrorName` (`invalid:<Reject
# constructor>`, or the limit outcome's own name) and `<n>` its position, or
# `-` where it carries none, so a refusal names the reference's own class and
# offset rather than a normalised corpus class.  `value: error canon` is a
# reference acceptance with no canonical value; no expected row admits it.
#
# The expected rows are `tests/json-value/expected.tsv`: `path`, `verdict`
# (`accept` or `refuse`), the value's hex or `-`, the class or `-`, the offset
# or `-`, and the document's digest.  The table is the oracle's; the route is
# compared against it per document, one line and one status per row.
#
# Two controls run before the arm is probed, so what fails below is the arm's
# absence and not a detector that reads nothing.

# Control (a): the field reader over a line the route prints today.  The
# certified event arm's consumer row carries `walked`, `foldsum` and
# `valuessum`; reading them and requiring the two sums to agree is the same
# reader and comparison the value line's fields use.
ne13_ctl_doc=$repo/tests/json/corpus/depth-two-ok.json
[ -f "$ne13_ctl_doc" ] || setup "absent: $ne13_ctl_doc"
"$route_bin" --consume-events "$ne13_ctl_doc" >/dev/null 2>"$work/ne13.row"
ne13_rst=$?
ne13_row=$(cat "$work/ne13.row")
[ "$ne13_rst" -eq 0 ] && [ "$(word "$ne13_row" path)" = fast ] &&
  [ "$(word "$ne13_row" walked)" = 1 ] &&
  [ -n "$(word "$ne13_row" tokens)" ] &&
  [ "$(word "$ne13_row" foldsum)" = "$(word "$ne13_row" valuessum)" ] || {
  printf 'FAIL: the field reader does not read the certified event arm (exit %s)\n' "$ne13_rst" >&2
  printf '  row: %s\n' "$ne13_row" >&2
  exit 1
}
printf 'ok: the field reader reads walked/foldsum/valuessum from the route today (%s)\n' \
  "$(word "$ne13_row" foldsum)"

# Control (b): the reference's refusal, observed today.  The empty document is
# the corpus's one document the admission declines, so the event arm's
# fallback answers it with the reference parser's own refusal and offset.  The
# value arm's refusal line must name that same refusal, exactly.
ne13_ref_doc=$repo/tests/json-noevent/corpus/documents/repo-empty
[ -f "$ne13_ref_doc" ] || setup "absent: $ne13_ref_doc"
[ ! -s "$ne13_ref_doc" ] || setup "the empty control document is not empty"
"$route_bin" --doc "$ne13_ref_doc" >"$work/ne13.ref.out" 2>"$work/ne13.ref.err"
ne13_rest=$?
ne13_ref=$(cat "$work/ne13.ref.err")
[ "$ne13_rest" -eq 2 ] && [ ! -s "$work/ne13.ref.out" ] &&
  [ "$ne13_ref" = 'refused: invalid: unexpected end at 0' ] || {
  printf 'FAIL: the event arm does not report the reference refusal on the empty document (exit %s)\n' \
    "$ne13_rest" >&2
  printf '  stderr: %s\n' "$ne13_ref" >&2
  exit 1
}
printf 'ok: the reference refusal is observed today: %s\n' "$ne13_ref"

# The arm's absence.  `--value` is not a mode at the pre-change revision, so
# the invocation exits 1 and prints the usage line; this exit-status assertion
# is the scenario's own, reached at the actor's boundary rather than at a
# missing binary or corpus.  An acceptance is the probe: the arm answers it
# with one `value=` line at exit 0.
ne13_probe_doc=$repo/tests/json-noevent/corpus/documents/acc-number-zero-array
[ -f "$ne13_probe_doc" ] || setup "absent: $ne13_probe_doc"
"$route_bin" --value "$ne13_probe_doc" >"$work/ne13.probe.out" 2>"$work/ne13.probe.err"
ne13_pst=$?
if [ "$ne13_pst" -ne 0 ]; then
  printf 'FAIL: --value exited %s on %s; the value arm must exit 0 and print its line on an acceptance\n' \
    "$ne13_pst" "$(basename "$ne13_probe_doc")" >&2
  awk 'NR <= 10' "$work/ne13.probe.err" >&2
  exit 1
fi
[ "$(wc -l <"$work/ne13.probe.out")" -eq 1 ] ||
  fail "--value printed $(wc -l <"$work/ne13.probe.out") lines on an acceptance"
ne13_probe=$(cat "$work/ne13.probe.out")
case $ne13_probe in
  'value: verdict=1 value='*) ;;
  *) fail "--value's line is not the value form: $ne13_probe" ;;
esac
printf 'ok: --value answers an acceptance with its value line\n'

# The per-document comparison.  The corpus and the expected table are the
# arm's fixture: an absent one is a setup fault naming the path, never an
# assertion result.  The table's columns are `path`, `verdict`, the value's
# hex (or `-`), the refusal class (or `-`), the refusal offset (or `-`) and
# the document's digest.
value_corpus=$repo/tests/json-value/corpus
value_expected=$repo/tests/json-value/expected.tsv
[ -d "$value_corpus" ] || setup "absent: $value_corpus"
[ -f "$value_expected" ] || setup "absent: $value_expected"

# The expected stdout line for one row.
ne13_expected_line() { # verdict value class offset
  case $1 in
    accept) printf 'value: verdict=1 value=%s' "$2" ;;
    refuse) printf 'value: refused class=%s offset=%s' "$3" "$4" ;;
    *) return 1 ;;
  esac
}

# One document's comparison: the invocation's status is the row's verdict's,
# its stdout is exactly one line, and that line is the expected one.  The
# comparison is exact string equality, so a token-preserving near-miss fails.
ne13_compare() { # doc verdict value class offset -> 0 when the line matches
  local doc=$1 verdict=$2 value=$3 class=$4 offset=$5
  local want status st got
  want=$(ne13_expected_line "$verdict" "$value" "$class" "$offset") || return 1
  case $verdict in
    accept) status=0 ;;
    refuse) status=2 ;;
    *) return 1 ;;
  esac
  "$route_bin" --value "$doc" >"$work/ne13.value.out" 2>"$work/ne13.value.err"
  st=$?
  if [ "$st" -eq 5 ] &&
     [ "$(cat "$work/ne13.value.out")" = 'value: error canon' ]; then
    printf '  %s: the arm reported no canonical value for a document the reference accepted\n' \
      "$(basename "$doc")" >&2
    return 1
  fi
  if [ "$st" -ne "$status" ]; then
    printf '  %s: --value exited %s, and the row pins %s\n' \
      "$(basename "$doc")" "$st" "$status" >&2
    return 1
  fi
  if [ "$(wc -l <"$work/ne13.value.out")" -ne 1 ]; then
    printf '  %s: --value printed %s lines\n' \
      "$(basename "$doc")" "$(wc -l <"$work/ne13.value.out")" >&2
    return 1
  fi
  got=$(cat "$work/ne13.value.out")
  if [ "$got" != "$want" ]; then
    printf '  %s: the arm'"'"'s line is not the row'"'"'s\n' "$(basename "$doc")" >&2
    printf '    arm:      %s\n    expected: %s\n' "$got" "$want" >&2
    return 1
  fi
  return 0
}

ne13_rows=0
ne13_accept_doc=
ne13_accept_value=
while IFS=$'\t' read -r vpath vverdict vvalue vclass voffset vsha; do
  case $vpath in '' | '#'*) continue ;; esac
  ne13_rows=$((ne13_rows + 1))
  vdoc=$value_corpus/$vpath
  [ -f "$vdoc" ] || fail "$vpath: the expected table names an absent document"
  got=$(sha256sum "$vdoc" | cut -d' ' -f1)
  [ "$got" = "$vsha" ] ||
    fail "$vpath: the document's digest is not the expected table's"
  case $vverdict in
    accept)
      [ -n "$vvalue" ] && [ "$vvalue" != '-' ] &&
        [ "$vclass" = '-' ] && [ "$voffset" = '-' ] ||
        fail "$vpath: an acceptance's row carries a refusal field"
      [ -z "$ne13_accept_doc" ] && ne13_accept_doc=$vdoc && ne13_accept_value=$vvalue
      ;;
    refuse)
      [ "$vvalue" = '-' ] && [ "$vclass" != '-' ] ||
        fail "$vpath: a refusal's row does not carry its class and value"
      case $voffset in
        -) ;;
        '' | *[!0-9]*)
          fail "$vpath: a refusal's offset is neither a position nor '-'"
          ;;
      esac
      ;;
    *) fail "$vpath: the expected row's verdict is neither accept nor refuse: $vverdict" ;;
  esac
  ne13_compare "$vdoc" "$vverdict" "$vvalue" "$vclass" "$voffset" || {
    printf 'FAIL: %s: the value arm is not the reference\n' "$vpath" >&2
    exit 1
  }
done <"$value_expected"

[ "$ne13_rows" -gt 0 ] || fail "the value arm's expected table is empty"
[ -n "$ne13_accept_doc" ] || fail "the value arm's expected table has no acceptance"

# The table and the corpus are one set: each corpus document is named exactly
# once, and the table names no document the corpus does not carry.  Without
# this, a document the table omits would be skipped silently by the loop.
ne13_dups=$(awk -F '\t' '!/^#/ && NF { print $1 }' "$value_expected" |
  LC_ALL=C sort | uniq -d)
[ -z "$ne13_dups" ] ||
  fail "the expected table names a document twice: $(printf '%s' "$ne13_dups" | head -n 1)"
ne13_corpus_set=$(find "$value_corpus" -mindepth 1 -maxdepth 1 -type f \
  -printf '%f\n' | LC_ALL=C sort)
ne13_table_set=$(awk -F '\t' '!/^#/ && NF { print $1 }' "$value_expected" |
  LC_ALL=C sort)
if [ "$ne13_corpus_set" != "$ne13_table_set" ]; then
  printf 'FAIL: the value corpus and the expected table name different documents\n' >&2
  diff <(printf '%s\n' "$ne13_corpus_set") <(printf '%s\n' "$ne13_table_set") |
    awk 'NR <= 20' >&2
  exit 1
fi
ne13_corpus_count=$(printf '%s\n' "$ne13_corpus_set" | grep -c .)
[ "$ne13_corpus_count" -eq "$ne13_rows" ] ||
  fail "the expected table has $ne13_rows rows and the corpus has $ne13_corpus_count documents"

# The comparison's own control: two hex digits appended to an acceptance's
# pinned value is a tampered expectation, and the same comparator must reject
# it.  Without this, a comparator that never compared would pass every row.
if ne13_compare "$ne13_accept_doc" accept "${ne13_accept_value}00" - - \
    2>"$work/ne13.tamper.err"; then
  fail "the comparator passed a tampered expectation"
fi
grep -q 'the arm.s line is not the row.s' "$work/ne13.tamper.err" ||
  fail "the comparator rejected the tampered expectation without saying why"
printf 'ok: the comparator rejects a tampered expectation on %s\n' \
  "$(basename "$ne13_accept_doc")"

printf 'ok: --value carries the reference value or refusal on all %s documents\n' "$ne13_rows"

printf 'ok: the no-event entries agree with the certified routes; the sentinel separates refusals; the census and the byte identity are pinned\n'
exit 0
