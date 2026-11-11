#!/usr/bin/env bash
# Regenerate the escape unit's emitted-IR fixture and its four inventories in
# probes/install/ir/.
#
# Run through the flake, from the repository root:
#
#   nix develop -c bash probes/install/ir/capture-escape.sh
#
# Input
#   kernel/json/escape.c              the escape unit: the escape-position list
#                                     (`xl_lanes`, `xl_batch`, `xl_emit_batch`,
#                                     `xl_emit`) and the list-driven expander
#                                     (`us_dec_x` and its kernels, `UJ_UNESC`,
#                                     `uj_enc_word`), with the two ABI functions
#
# Output (all five in the same run, from the same compilation)
#   json-escape.candidate.ll          the fixture: the four `define` blocks the
#                                     emission holds, in the emission's order,
#                                     with the syntax listed below removed and
#                                     the table read rewritten
#   json-escape.strip.tsv             what the normalisation removed, by class,
#                                     derived by diffing the emission against
#                                     the text this script emits
#   json-escape.rewrites.tsv          what it rewrote rather than removed: the
#                                     `poison` lanes of the two pmadd constants,
#                                     each row with the lane it stood a value in
#                                     for
#   json-escape.table.tsv             the table read and the call that passes
#                                     the base: per site, the text the emission
#                                     wrote and the text the fixture holds
#   json-escape.inventory             the fixture's own opcodes and call targets
#
# `kernel/json/identity/inventory.sh --unit escape` is the gate: it regenerates
# all four inventories and the fixture, compares them byte for byte, parses the
# fixture and fires its controls.  This script only derives; the verdict is
# that gate's.
#
# --- Why this unit's emission is four functions and not one --------------
#
# The list entry point is one `define`; the expander entry point is another, and
# it calls the third, `us_dec_x`, which is `noinline` in the source and stays
# out of line in every build.  The fourth, `xl_batch`, is `static inline` in the
# source but the optimiser does not inline it: it is called from the batch
# loop's back edge and writes eight 4-byte slots, so it is emitted as an
# internal `fastcc` function with its own `range` attributes.  The fixture
# therefore holds all four definitions, because a fixture that dropped two would
# leave calls to definitions it does not contain, and the model would have to
# invent them.
#
# The count is read, not assumed: every `define` block of the module must be one
# of the four named here and no other, in the emission's order.  A fifth
# function is a shape change (an inlined kernel that stopped inlining, a new
# out-of-line helper) and is refused rather than classified.
#
# --- Why the measured compiler line, and the measured `-D` set -----------
#
# The fixture is the emission the *measured* build compiled, not a portable
# re-phrasing of it: the timing arm and the verdict differential compile the
# same C at the same flags, so the body the theorem is about is the body the
# object runs.  The line is `build49.sh:17`'s:
#
#   clang -O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
#         -falign-functions=64
#
# `-fno-discard-value-names` is added to it.  It is a naming flag: it writes the
# source's value names and, because a named entry block is emitted with its
# label, it supplies the block labels the parser requires.  That it changes no
# instruction is checked here rather than asserted: the same source is emitted
# with and without the flag, every register name is replaced by one placeholder
# and label lines are dropped, and the two texts must be identical.
#
# The measured `-D` set (`build49.sh:19-21` plus `-DUS_EMIT4=1`, `:28`) is
# passed because the measured build's translation unit had it, and the identity
# arm compiles both sides with it.  That it changes nothing in *this* unit is
# checked the same way the naming flag is: the source is emitted with and
# without the set, neutralised, and the two texts must be identical.  A
# difference would mean the unit's preprocessed form depends on the set and the
# fixture must say which arm it holds; refusing is the honest response until
# that is decided.
#
# No other compiler or `opt` pass runs between the emission and the fixture: the
# fixture is the blocks clang printed, with the syntax below removed and the
# table read rewritten.  The one `opt` invocation is the check that the result
# is well-formed IR and not only a text the repository's parser reads:
#
#   opt -passes=verify -disable-output json-escape.candidate.ll
#
# It is named in the fixture's provenance comment too, so a reader can repeat
# it, and it runs before any artefact is written.
#
# --- The parameter names: none renamed -----------------------------------
#
# Every parameter of every one of the four functions is the source's own name
# (`bs`/`ctl`/`im`/`blk0`/`xp`/`xn`/`carry`; `b`/`n`/`dst`/`err`/`xp`/`xj`/
# `nxp`/`pos0`; `p`/`n`/`dst`/`err`/`xp`/`xj`/`nxp`/`pos0`; `esc`/`base`/`o`), so
# this capture renames nothing.  The machinery is kept and the names are read
# from the emission, not assumed: for each `define` the capture takes the last
# token of each top-level parameter and requires it to be the name the source
# gives that parameter.  A differing name is a setup fault rather than a silent
# rename, because for this unit a rename would mean the measured text's spelling
# had drifted from the ABI's.
#
# --- The table read: the one rewrite -------------------------------------
#
# The fragment has no module-level globals, so `kernel/json/escape.c`'s
# `UJ_UNESC` — the 256-byte simple-escape map, `static const int8_t[256]` — and
# the one `getelementptr` that names it cannot be represented.  The emitted read
# is
#
#   getelementptr inbounds nuw [256 x i8], ptr @UJ_UNESC, i64 0, i64 %idxprom.i
#
# and it becomes
#
#   getelementptr inbounds i8, ptr %tab, i64 %idxprom.i
#
# with `%tab` appended to the parameter list of the body that reads it.  The
# emitted form addresses `@UJ_UNESC + 0 * 256 + idx * 1` and the rewritten form
# `%tab + idx * 1`, so the byte offset from the base is `idx` on both sides and
# only the base differs — which is exactly what the record's table hypothesis
# supplies.  `nuw` is class 4's removal and is gone before the rewrite; it is
# recorded in json-escape.strip.tsv.
#
# The base is threaded by the call as well as by the read: `us_dec_x` is where
# the read is, and `leanllvm_json_escape_expand` calls it, so the expander takes
# `%tab` and passes it.  The set of functions that take it is computed, not
# listed: a block is a taker when it reads `@UJ_UNESC` or calls a taker, and the
# fixpoint is closed before the rewrite, so a caller added to the unit acquires
# the parameter without this script being edited.  Two checks make the fixpoint
# evidence rather than an assumption: a body that declares `%tab` must use it (a
# parameter that is only declared is an unattributed line), and the fixture must
# verify with `opt -passes=verify`, which refuses a call whose argument count
# disagrees with the definition — the two directions a wrong fixpoint would take.
#
# --- The poison lanes: the one substitution -----------------------------
#
# `us_hex4_pshufb` reads four hex digits and ignores the rest of its 16-byte
# vector, so the four vector constants that follow the digits carry `poison` past
# them, and the emission keeps the lanes as written:
#
#   %17 = and <16 x i8> %11, <i8 15, i8 15, i8 15, i8 15, i8 poison, ...>
#   %18 = select <16 x i1> %cmp, <16 x i8> <i8 9, ...>, <16 x i8> <i8 0, ...>
#   %19 = tail call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %add,
#         <16 x i8> <i8 16, i8 1, i8 16, i8 1, i8 poison, ...>)
#   %20 = tail call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %19,
#         <8 x i16> <i16 256, i16 1, i16 poison, ...>)
#
# Nothing reads past lane 3: the class test takes `_mm_movemask_epi8(...) &
# 0x0F`, and the value is `extractelement <4 x i32> %20, i64 0` masked with
# `0xFFFF` — lane 0 of `%20`, which the defined lanes of `%19`'s first two and
# `%20`'s first two compute.  So the poisoned lanes feed lanes nothing observes,
# the same situation as the entry unit's `poison` operands and handled the same
# way: each poisoned lane is written as the defined lane 0, and every such
# replacement is a row in json-escape.rewrites.tsv.  The substitution is per lane
# and not per vector because the defined lanes' values are what the read lane is
# computed from.
#
# --- What the normalisation removes, and why it is a derivation -----------
#
# The emission at those flags carries syntax the parser refuses by name.  The
# removal is computed, not transcribed: the capture diffs its own clang block
# against the text it emits, groups the removed tokens into contiguous runs, and
# attributes each run to one of the ten classes, writing a row per item with
# the class's reason.  A token that matches no class exits `3`, so syntax cannot
# be stripped silently and the inventory cannot fall behind the emission.  A
# token the parser already accepts and drops (`tail`, `inbounds`, `samesign`,
# `internal`, `fastcc` on a `define`'s header, the written callee type) is never
# removed, so it never appears — the inventory is a record of what was taken
# out, not of what the parser tolerates.
#
# The ten classes.  A token that matches none of them exits `3`.  One of them is
# unexercised by this emission and is kept rather than trimmed, because the
# class list is the capture's vocabulary and a class dropped for one unit is a
# class the next emission arrives without.  Class 10 arrives with this unit:
# the previous three emit no call through an internal function, so no call of
# theirs carries a calling convention, and this one's two internal calls carry
# `fastcc`.
#
#   1. argument, parameter and call-result attributes — `noundef`, `readonly`,
#      `writeonly`, `immarg`, `captures(...)`, a call's `range(...)` and an
#      operand's `range(...)`: a promise about an argument or a result.  This
#      unit's instances are `noundef` and `captures(none)` on every parameter
#      and on every argument of the one internal call, `readonly`/`writeonly`
#      on the pointers, and the `range` clauses of `xl_batch` (its return's
#      `range(i32 1, 9)` and its `%esc`'s `range(i64 1, 0)`) and of the eight
#      `cttz` calls and the `umin` call.
#   2. function-header surface — `unnamed_addr`, `local_unnamed_addr`, `#N`,
#      the function's `align`, and a `declare` line: linkage, code placement and
#      the declaration of a callee the model knows by name, for none of which
#      the model has a semantics.
#   3. attribute-group definitions — `attributes #N = { ... }`: the target
#      feature and memory promise its references carry, removed with them and
#      recorded in PROVENANCE.md.
#   4. instruction flags that constrain — `nuw`, `nsw`, `nusw`, `disjoint`,
#      `nneg`: each excludes inputs, so stripping *widens*; the widening is
#      recorded rather than re-established.  This unit's are `nuw`/`nsw` on the
#      `trunc`s of `xl_batch` and the `lshr`/`shl`/`add`/`getelementptr`s
#      throughout, `disjoint` on the eight `or`s `xl_batch` uses to place a
#      position and on the six of the hex reader's, and `nneg` on the two `zext`s
#      of a value the select made non-negative; `nusw` is unexercised here.
#   5. memory and analysis metadata — `!tbaa`, `!prof` and `!llvm.loop`, and the
#      module's `!N = ...` nodes: the model has no aliasing relation, no branch
#      weight and no loop model to read them with.
#   6. `poison` as a value — the four vector constants of the hex reader whose
#      lanes past the four digits are poisoned, each lane replaced by a defined
#      one and recorded in json-escape.rewrites.tsv.
#   7. `initializes((0, 32))` — `xl_batch`'s `%o`: a promise about which slot
#      bytes the batch writes; the theorem's memory clause is stronger for the
#      bytes it covers.
#   8. module configuration and module-level symbols — `target datalayout`,
#      `target triple`, `source_filename` and the unit's one global.  The
#      configuration values are recorded in the fixture's provenance comment and
#      in PROVENANCE.md; the global becomes `%tab` (json-escape.table.tsv).  A
#      module-level symbol *other than* `UJ_UNESC` is refused rather than
#      classified, because it would mean a second table appeared and the rewrite
#      would have to account for a read this script does not know.
#   9. instruction-level alignment — `load ..., align 1`: the parser's `load` has
#      no alignment field and the model addresses bytes, so the removal is a
#      representation loss and not a semantic one.  Every load and store here
#      carries it, at 1, 4 or 8.
#  10. a call's calling convention — `call fastcc`: the `Calls` environment
#      decides which definition answers and how the call is made, and no calling
#      convention is modelled, so the token is removed before the call.  The
#      parser drops the same token on a `define`'s header (`isHeaderSurface`,
#      `Parser.lean:1571-1589`) and refuses it on a call, which is why the
#      capture removes one and not the other:  `internal fastcc` in a header
#      survives, `call fastcc` cannot.  A call carrying a spelling other than the
#      one this emission writes would not be removed, and the fixture would then
#      fail `opt -passes=verify` rather than be dropped unseen.
#
# Whole lines are removed as lines and carry a class too: `attributes #N = {...}`
# is class 3, a `declare` is class 2, a module metadata node is class 5, and the
# module header and the table's definition are class 8.  Comment lines and
# inline comments are dropped before the diff rather than classified: `tokenize`
# (`LeanLLVM/Parser.lean`) truncates a line at `;` and `tokenLines` drops empty
# lines, so a comment carries no token the parser reads.  The fixture therefore
# holds instruction text and block labels only, and the `preds` lists the
# emission writes after a block label are readable from the `br` that precedes
# the target.
#
# The one rewrite applied before that diff is the `poison` substitution above;
# it is declared to the alignment as a token pair, so a substitution the
# inventory does not carry cannot happen, and every substitution it does make has
# a row.
#
# --- What this capture reports, and what it does not establish -----------
#
# Two verdicts are taken on the fixture and printed on every run, and neither is
# a gate here, because the artefacts are the derivation and the gate's criteria
# are the verdicts:
#
#   opt -passes=verify -disable-output json-escape.candidate.ll
#       clean today: the fixture is well-formed LLVM IR.
#
#   leanllvm --passes none --no-check -o /dev/null json-escape.candidate.ll
#       **red today**, and it is the fragment's gap rather than the fixture's:
#       the emission holds two lane-wise selects —
#
#         %18 = select <16 x i1> %cmp.i190, <16 x i8> <i8 9, ...>,
#               <16 x i8> <i8 0, ...>
#
#       from `_mm_and_si128(isa, _mm_set1_epi8(9))` in `us_hex4_pshufb` — and
#       `LeanLLVM/Parser.lean:1160-1166` refuses a vector condition and a vector
#       value by name.  With those two lines replaced in a throwaway copy, the
#       whole fixture parses, so that is the only form in it the fragment lacks.
#       The capture reports it rather than working around it: a rewrite here
#       would substitute an instruction that carries semantics, which the two
#       rewrites this unit does make (a table base, poison lanes) deliberately do
#       not.  The red is cleared by the slice that widens the fragment with the
#       lane-wise select; until it lands this capture's fixture is well-formed IR
#       that this repository cannot read, and the capture slice is not complete.
#
# The call set is reported the same way and is what the model vocabulary is
# sized from: the fixture's `call @llvm.*` targets are enumerated from the
# inventory, the modelled spellings are extracted from the `Calls` environments
# in `LeanLLVM/Refinement`, and the difference is printed.  That difference is not
# failed on here — the vocabulary's own sufficiency artifact is where an
# unmodelled call fails closed — but it is never recalled: today the fixture
# calls five intrinsic spellings, two are bound (`ctpop.i64`, `cttz.i64`) and
# three are not (`umin.i32`, `sse2.pmadd.wd`, `ssse3.pmadd.ub.sw.128`), and the
# numbers are read off the two lists each run.
#
# Exit status: 0 when the five artefacts are written; 3 when an input is missing
# or the derivation cannot be attributed — the same code the rest of the route
# uses for an unusable input.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)

src=kernel/json/escape.c
# The emission's `define` blocks, in the order they must appear in the fixture.
symbols=(leanllvm_json_escape_list leanllvm_json_escape_expand us_dec_x xl_batch)
# The parameters each `define`'s source gives it, in order.  The table base the
# rewrite appends is not one of them: it names the rewrite, not the unit.
list_names=(bs ctl im blk0 xp xn carry)
expand_names=(b n dst err xp xj nxp pos0)
dec_names=(p n dst err xp xj nxp pos0)
batch_names=(esc base o)
# The table: the symbol the emission reads and the parameter it becomes.
table_symbol=UJ_UNESC
table_param=%tab
fixture=$here/json-escape.candidate.ll
strip=$here/json-escape.strip.tsv
rewrites=$here/json-escape.rewrites.tsv
table=$here/json-escape.table.tsv
inventory=$here/json-escape.inventory

fail() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

# The attribution program, which is also the `--attribute` mode's detector:
# every differing line between a normalised emission block and the text the
# capture emits must be the table read, the call that passes the base, or the
# parameter list.  Rows go to stdout; an unattributable line goes to stderr and
# exits 3.
attribute_program() {
  cat <<'AWK'
BEGIN { rows = 0; bad = 0; nraw = 0; want_tab = 0 }
FILENAME == ARGV[1] { em[FNR] = $0; nem = FNR; next }
FILENAME == ARGV[2] { ca[FNR] = $0; nca = FNR; next }
{ ra[FNR] = $0; nraw = FNR }

END {
    if (nem != nca) {
        printf "SETUP: the emission has %d line(s) and the fixture %d\n", nem, nca > "/dev/stderr"
        exit 3
    }
    if (nem == 0) {
        printf "SETUP: the emission is empty\n" > "/dev/stderr"
        exit 3
    }
    want_tab = index(ca[1], "ptr %" TABP) > 0
    # The parameter list: the rewritten header is the emitted header with the
    # table base appended when the body reads or passes the table, and identical
    # when it does not — a body that names no base and takes the parameter would
    # be a `define` of a different function on no evidence at all.
    want = em[1]
    if (want_tab) {
        if (!sub(/\)[ \t]*\{[ \t]*$/, ", ptr %" TABP ") {", want)) {
            printf "SETUP: the function header '%s' is not a parameter list\n", em[1] > "/dev/stderr"
            exit 3
        }
    }
    if (ca[1] != want) {
        bad++
        if (want_tab)
            printf "SETUP: unattributed: the header changed beyond the appended %%%s\n", TABP > "/dev/stderr"
        else
            printf "SETUP: unattributed: the header takes %%%s, and the body neither reads nor passes the table\n", TABP > "/dev/stderr"
        printf "SETUP:   emitted:  %s\n", em[1] > "/dev/stderr"
        printf "SETUP:   fixture:  %s\n", ca[1] > "/dev/stderr"
    }
    gepkey = "getelementptr inbounds [256 x i8], ptr @" TSYM ", i64 0, i64 "
    for (ln = 2; ln <= nem; ln++) {
        if (em[ln] == ca[ln]) {
            if (index(ca[ln], "%" TABP) > 0) {
                bad++
                printf "SETUP: unattributed: line %d names %%%s and differs from nothing\n", ln, TABP > "/dev/stderr"
            }
            continue
        }
        i = index(em[ln], gepkey)
        if (i > 0) {
            prefix = substr(em[ln], 1, i - 1)
            idx = substr(em[ln], i + length(gepkey))
            if (idx !~ /^%[A-Za-z0-9._$-]+$/) {
                bad++
                printf "SETUP: unattributed: line %d's table GEP has no bare register index\n", ln > "/dev/stderr"
                continue
            }
            want = prefix "getelementptr inbounds i8, ptr %" TABP ", i64 " idx
            if (ca[ln] != want) {
                bad++
                printf "SETUP: unattributed: line %d is a table GEP but the fixture's line is not its rewrite\n", ln > "/dev/stderr"
                printf "SETUP:   emitted:  %s\n", em[ln] > "/dev/stderr"
                printf "SETUP:   fixture:  %s\n", ca[ln] > "/dev/stderr"
                continue
            }
            emitted = (nraw >= ln) ? ra[ln] : em[ln]
            rows++
            printf "gep\t%s\t%s\t%d\t%s\n", emitted, ca[ln], ln, \
              "the unit's table read: base @" TSYM " becomes the caller's %" TABP " and the aggregate [256 x i8] with two indices becomes the indexed i8 with one; both address base + idx"
            continue
        }
        # A call that passes the base: the fixture line is the emitted line with
        # `, ptr %tab` before its closing paren, and nothing else.
        want = em[ln]
        if (sub(/\)[ \t]*$/, ", ptr %" TABP ")", want) && ca[ln] == want) {
            emitted = (nraw >= ln) ? ra[ln] : em[ln]
            rows++
            printf "call\t%s\t%s\t%d\t%s\n", emitted, ca[ln], ln, \
              "the call that passes the table base: the callee reads the table, so the caller hands it on; the argument is appended and nothing else changes"
            continue
        }
        bad++
        printf "SETUP: unattributed: line %d differs and is neither the table read nor the call that passes the base\n", ln > "/dev/stderr"
        printf "SETUP:   emitted:  %s\n", em[ln] > "/dev/stderr"
        printf "SETUP:   fixture:  %s\n", ca[ln] > "/dev/stderr"
    }
    if (!want_tab)
        for (ln = 2; ln <= nem; ln++)
            if (index(ca[ln], "%" TABP) > 0) {
                bad++
                printf "SETUP: unattributed: line %d names %%%s and the header does not take it\n", ln, TABP > "/dev/stderr"
            }
    # A declared base must be used: a parameter only declared is the shape a
    # wrong fixpoint takes in the over-approximating direction, and IR verifies
    # with an unused parameter, so this is the check that sees it.
    if (want_tab) {
        used = 0
        for (ln = 2; ln <= nem; ln++) if (index(ca[ln], "%" TABP) > 0) used = 1
        if (!used) {
            bad++
            printf "SETUP: unattributed: the header takes %%%s and no line of the body uses it\n", TABP > "/dev/stderr"
            printf "SETUP:   header:   %s\n", ca[1] > "/dev/stderr"
        }
    }
    exit (bad > 0)
}
AWK
}

attribute() { # <emitted> <candidate> [<raw>]
  local ws rc
  ws=$(mktemp -d) || fail "cannot create a work directory"
  attribute_program > "$ws/attribute.awk"
  rc=0
  if [ "$#" -ge 3 ] && [ -n "$3" ]; then
    awk -v TSYM="$table_symbol" -v TABP="${table_param#%}" \
      -f "$ws/attribute.awk" "$1" "$2" "$3" || rc=$?
  else
    awk -v TSYM="$table_symbol" -v TABP="${table_param#%}" \
      -f "$ws/attribute.awk" "$1" "$2" || rc=$?
  fi
  rm -rf "$ws"
  return "$rc"
}

if [ "${1:-}" = "--attribute" ]; then
  shift
  [ "$#" -ge 2 ] && [ "$#" -le 3 ] ||
    fail "--attribute needs <emitted> <candidate> [<raw>]"
  for f in "$@"; do
    [ -f "$f" ] || fail "absent: $f"
  done
  attribute "$@"
  exit $?
fi
[ "$#" -eq 0 ] || fail "unknown argument: $1"

[ -f "$repo/$src" ] || fail "absent: $repo/$src"
command -v clang >/dev/null 2>&1 || fail "clang is not on PATH"

mkdir -p "$repo/.lake" || fail "cannot create $repo/.lake"
work=$(mktemp -d "$repo/.lake/tmp-escape-capture.XXXXXX" 2>/dev/null) ||
  work=$(mktemp -d) ||
  fail "cannot create a work directory"
trap 'rm -rf "$work"' EXIT

# --- the emission ---------------------------------------------------------

flags=(-S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11
       -falign-loops=64 -falign-functions=64)
# `build49.sh:19-21`'s measured set plus `-DUS_EMIT4=1` (`:28`), the same set
# `ir-identity.sh --unit escape` compiles both sides with.
defs=(-DSTAGE_PROBE -DS1F_ENT_PROBE=1 -DS1F_DENS=1 -DS1F_TWOPHASE=1
      -DS1F_EXP2=11 -DS1F_DISPATCH=1 -DS1F_UTF8=7 -DS1F_KL_DOC=1 -DPSTAGE=32
      -DPMODE=2 -DS1F_XS=5 -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1
      -DUS_EMIT4=1)

# The source is named relative to the repository root, so `source_filename` in
# the emission does not carry a checkout path.  The include path is the unit's,
# as the identity arm's is.
compile() { ( cd "$repo" && clang -I kernel/json "$@" ); }

compile "${flags[@]}" "$src" -o "$work/plain.ll"
compile "${flags[@]}" -fno-discard-value-names "$src" -o "$work/nodefs.ll"
compile "${flags[@]}" -fno-discard-value-names "${defs[@]}" "$src" -o "$work/named.ll"

# The naming flag's claim, checked: the same source, the same instructions.  The
# flag also *labels* the blocks it emits (the unnamed emission numbers them, and
# writes the numbering as the label), while its `; preds` list is padded to the
# label's length — so a block-label line is dropped from both texts.  A label is
# not an instruction, and the `; preds` list after one carries no token the
# parser reads.
neutralise() {
  sed -E -e 's/%[A-Za-z0-9._$-]+/%N/g' \
         -e 's/^[A-Za-z0-9_.$-]+:/%L:/' \
         -e '/^%L:/d' "$1"
}
neutralise "$work/plain.ll" > "$work/plain.norm.ll"
neutralise "$work/named.ll" > "$work/named.norm.ll"
if ! cmp -s "$work/plain.norm.ll" "$work/named.norm.ll"; then
  diff -u "$work/plain.norm.ll" "$work/named.norm.ll" | awk 'NR <= 40' >&2
  fail "-fno-discard-value-names changed the emission beyond register names"
fi

# The measured `-D` set's claim, checked the same way: this unit's name pass
# does not consult any of the switches, so the set changes no instruction and
# the fixture is the same text either way.  A difference means the unit's
# preprocessed form depends on the configuration, which needs a decision rather
# than a silent pick.
neutralise "$work/nodefs.ll" > "$work/nodefs.norm.ll"
if ! cmp -s "$work/nodefs.norm.ll" "$work/named.norm.ll"; then
  diff -u "$work/nodefs.norm.ll" "$work/named.norm.ll" | awk 'NR <= 40' >&2
  fail "the measured -D set changed this unit's emission; the fixture would have to name which arm it holds"
fi

# The module with comments and blank lines dropped, and with each line cut at
# its comment: the parser's own tokenizer drops both (`tokenize` truncates at
# `;`, `tokenLines` filters empty lines), so a comment carries nothing and is
# not part of the diff.  Cutting inline comments here as well as whole-line ones
# is what makes each block a verbatim contiguous run of this text, so a row's
# `line` is a line of the emission and nothing needs renumbering.
strip_comments() {
  awk '{
    i = index($0, ";")
    if (i > 0) $0 = substr($0, 1, i - 1)
    sub(/[ \t]+$/, "", $0)
    if ($0 == "") next
    print
  }' "$1"
}
strip_comments "$work/named.ll" > "$work/module.ll"

# The `define` block of @<symbol>, verbatim, from the clang emission, as the
# pair of line numbers it occupies in the comment-free module.
block_range() { # <symbol> -> "start end"
  awk -v head='define ' -v sym="@$1(" '
    !inblock && index($0, head) == 1 && index($0, sym) { inblock = 1; start = NR }
    inblock && $0 == "}" { print start, NR; exit }
  ' "$work/module.ll"
}

# Every `define` block of the module, so the line classifier never names a line
# inside a function.  The set is asserted against `symbols` below, so a function
# the fixture does not hold is a setup fault rather than something to classify.
all_block_ranges() {
  awk '
    inblock && $0 == "}" { print start, NR; inblock = 0; next }
    !inblock && index($0, "define ") == 1 { inblock = 1; start = NR }
  ' "$work/module.ll"
}
all_block_ranges > "$work/allranges"
[ -s "$work/allranges" ] || fail "the emission holds no \`define\` block"
nfunc=$(wc -l < "$work/allranges" | tr -d ' ')
[ "$nfunc" -eq "${#symbols[@]}" ] ||
  fail "the emission holds $nfunc \`define\` block(s); the unit is ${#symbols[@]} functions (${symbols[*]})"

: > "$work/ranges"
for sym in "${symbols[@]}"; do
  range=$(block_range "$sym")
  [ -n "$range" ] || fail "the emission has no \`define\` block for @$sym"
  read -r start end <<< "$range"
  sed -n "${start},${end}p" "$work/module.ll" > "$work/block.$sym.ll"
  [ -s "$work/block.$sym.ll" ] || fail "the \`define\` block of @$sym is empty"
  printf '%s %s %s\n' "$start" "$end" "$sym" >> "$work/ranges"
done

# The define set is the fixture's, not a superset of it: every block of the
# module is one of the four, read as a set so a renamed or added function is
# refused rather than classified.
awk '{ print $3 }' "$work/ranges" | LC_ALL=C sort > "$work/want.names"
awk '
  inblock && $0 == "}" { inblock = 0; next }
  !inblock && index($0, "define ") == 1 {
    line = $0
    sub(/^.*@/, "", line)
    sub(/\(.*$/, "", line)
    print line
  }
' "$work/module.ll" | LC_ALL=C sort > "$work/have.names"
if ! cmp -s "$work/want.names" "$work/have.names"; then
  printf 'SETUP: the module defines (%s); the unit is (%s)\n' \
    "$(tr '\n' ' ' < "$work/have.names")" "${symbols[*]}" >&2
  fail "the emission's \`define\` blocks are not the unit's functions"
fi

# The fixture's function order is the emission's, so a reordering cannot pass.
awk '{ if (NR > 1 && $1 <= prev) exit 1; prev = $2 }' "$work/ranges" ||
  fail "the emission's \`define\` blocks are not in the order the fixture holds them"

# --- the parameter names, and the source's spelling of them --------------

# One parameter name per line, from the header's parameter list.
param_names() {
  awk -v sym="@$1(" '
    {
      i = index($0, sym)
      if (i == 0) next
      rest = substr($0, i + length(sym) - 1)
      depth = 0
      chunk = ""
      for (j = 1; j <= length(rest); j++) {
        c = substr(rest, j, 1)
        if (c == "(") {
          depth++
          if (depth == 1) { chunk = "" }
          else { chunk = chunk c }
          continue
        }
        if (c == ")") {
          if (depth == 1) {
            if (!flushparam()) exit 1
            break
          }
          depth--
          chunk = chunk c
          continue
        }
        if (c == "," && depth == 1) {
          if (!flushparam()) exit 1
          continue
        }
        if (depth >= 1) chunk = chunk c
      }
      exit
    }
    function flushparam(   toks, m) {
      m = split(chunk, toks, /[ \t]+/)
      if (m == 0) return 0
      if (substr(toks[m], 1, 1) != "%") {
        printf "SETUP: the parameter chunk '\''%s'\'' does not end in a register\n", chunk > "/dev/stderr"
        return 0
      }
      print toks[m]
      chunk = ""
      return 1
    }
  ' "$2"
}

# names_match <name> ... -- 0 when the names are the expected ones, 1 otherwise.
# The guard is a comparison, so its control is a name that differs: this unit
# records no rename, and "refuses rather than renames" is only evidence if the
# comparison can see a name changed.
names_match() { # <expected...> -- <emitted...>
  local -a want=() have=() emitted=()
  local seen_dd=0 n i
  for n in "$@"; do
    if [ "$seen_dd" -eq 0 ]; then
      if [ "$n" = "--" ]; then seen_dd=1; else want+=("$n"); fi
    else
      emitted+=("$n")
    fi
  done
  [ "${#emitted[@]}" -eq "${#want[@]}" ] || return 1
  for i in "${!want[@]}"; do
    [ "${emitted[$i]#%}" = "${want[$i]}" ] || return 1
  done
  return 0
}

: > "$work/rename.rows"
nrename=0
for sym in "${symbols[@]}"; do
  case "$sym" in
    leanllvm_json_escape_list) want=("${list_names[@]}") ;;
    leanllvm_json_escape_expand) want=("${expand_names[@]}") ;;
    us_dec_x) want=("${dec_names[@]}") ;;
    xl_batch) want=("${batch_names[@]}") ;;
    *) fail "no parameter list for @$sym" ;;
  esac
  param_names "$sym" "$work/block.$sym.ll" > "$work/params.$sym" ||
    fail "cannot read the parameter list of @$sym in the emission"
  mapfile -t emitted_names < "$work/params.$sym"
  if ! names_match "${want[@]}" -- "${emitted_names[@]}"; then
    fail "@$sym's parameters are (${emitted_names[*]-none}); the source names them (${want[*]})"
  fi
done
# The guard's own control: a name that differs by one character must be seen.
if names_match "${list_names[@]}" -- %bs %ctl %im %blk0 %buf %xn %carry; then
  fail "the rename guard does not see a changed parameter name; it is not evidence"
fi
printf 'ok: the emission names the source'"'"'s parameters for all %s functions, and the guard sees a changed one\n' \
  "${#symbols[@]}"

# --- the normalisation ----------------------------------------------------

# Header rules: the function-header surface (2), the parameter attributes and
# the return's `range` (1), and `initializes` (7).  The regexes are written so
# that each matches the token the inventory then attributes: a removal that
# matched inside another token would leave the token diff with something it
# could not name.
normalise_header() {
  sed -E \
    -e 's/ noundef//g' \
    -e 's/ nonnull//g' \
    -e 's/ readonly//g' \
    -e 's/ writeonly//g' \
    -e 's/ captures\(none\)//g' \
    -e 's/ initializes\(\([^)]*\)\)//g' \
    -e 's/ range\(i64 [^)]*\)//g' \
    -e 's/ range\(i32 [^)]*\)//g' \
    -e 's/ unnamed_addr//g' \
    -e 's/ local_unnamed_addr//g' \
    -e 's/ #[0-9]+//g' \
    -e 's/ align [0-9]+//g'
}

# Instruction rules: metadata (5), alignment (9), the constraining flags (4),
# call-argument and call-result attributes (1), `poison` (6), whose lane a
# defined lane replaces, and a call's calling convention (10).
normalise_body() {
  sed -E \
    -e 's/ noundef//g' \
    -e 's/ nonnull//g' \
    -e 's/, !tbaa ![0-9]+//g' \
    -e 's/, !prof ![0-9]+//g' \
    -e 's/, !llvm\.loop ![0-9]+//g' \
    -e 's/, align [0-9]+//g' \
    -e 's/ nuw//g' \
    -e 's/ nsw//g' \
    -e 's/ nusw//g' \
    -e 's/ disjoint//g' \
    -e 's/ nneg//g' \
    -e 's/ range\(i64 [^)]*\)//g' \
    -e 's/ range\(i32 [^)]*\)//g' \
    -e 's/ call fastcc / call /g' \
    -e 's/ poison([ ,>])/ 0\1/g'
}

for sym in "${symbols[@]}"; do
  head -n 1 "$work/block.$sym.ll" | normalise_header > "$work/body.$sym.ll"
  tail -n +2 "$work/block.$sym.ll" | normalise_body >> "$work/body.$sym.ll"
  nemit=$(wc -l < "$work/block.$sym.ll" | tr -d ' ')
  nbody=$(wc -l < "$work/body.$sym.ll" | tr -d ' ')
  [ "$nemit" -eq "$nbody" ] ||
    fail "the normalisation of @$sym changed the line count ($nemit -> $nbody); it removes tokens, not lines"
done

# --- the strip inventory: each block diffed against what it emits ---------

cat > "$work/classify.awk" <<'AWK'
BEGIN {
    seps = " \t,()<>{}"
    c1word["noundef"] = 1; c1word["nonnull"] = 1; c1word["readonly"] = 1
    c1word["writeonly"] = 1; c1word["immarg"] = 1
    c1paren["captures"] = 1; c1paren["range"] = 1
    c2word["local_unnamed_addr"] = 1; c2word["unnamed_addr"] = 1
    c4word["nuw"] = 1; c4word["nsw"] = 1; c4word["nusw"] = 1
    c4word["disjoint"] = 1; c4word["nneg"] = 1
    c7paren["initializes"] = 1
    c10word["fastcc"] = 1
    subst["poison" SUBSEP "0"] = 6
    reason[1] = "argument, parameter and call-result attributes: a promise about an argument or a result, re-established by the theorem's hypotheses; a call's or an operand's range is restated by the model's own definition"
    reason[2] = "function-header surface: linkage, code placement and a callee's declaration, which the model has no semantics for; the Calls environment decides which definition answers"
    reason[3] = "attribute-group definition: the target-feature and memory promise its references carry, recorded in PROVENANCE.md"
    reason[4] = "instruction flag that constrains: it excludes inputs, so stripping widens, and the widening is recorded rather than re-established"
    reason[5] = "memory and analysis metadata: the model has no aliasing relation and no loop model to read it with"
    reason[6] = "poison as a value: no observable reads the lane, so a defined lane stands in"
    reason[7] = "initializes((0, 32)): a promise about which slot bytes are written; the theorem's memory clause is stronger for the bytes it covers"
    reason[8] = "module configuration and module-level symbols: not read by the parser; the configuration is recorded in the fixture's provenance comment and in PROVENANCE.md, and the table becomes the %tab parameter (json-escape.table.tsv)"
    reason[9] = "instruction-level alignment: the parser's load has no alignment field, and the model addresses bytes"
    reason[10] = "a call's calling convention: the Calls environment decides which definition answers and how the call is made, and no calling convention is modelled, so the token is removed before the call; the parser drops the same token on a define header and refuses it on a call"
    rows = 0
    bad = 0
    nsubst = 0
    BIG = 1000000000
}

FILENAME == ARGV[1] { rm[FNR] = $0; nrm = FNR; next }
{ bd[FNR] = $0; nbd = FNR }

END {
    if (nrm != nbd) {
        printf "SETUP: the block has %d line(s) and the emitted body %d\n", nrm, nbd > "/dev/stderr"
        exit 3
    }
    for (ln = 1; ln <= nrm; ln++) {
        curline = ln + ofs
        isheader = (ln == 1)
        nt = tokenize(rm[ln], t, sep)
        no = tokenize(bd[ln], u, usep)
        align(nt, no)
        for (i = 1; i <= nt; i++) {
            if (i in del) { if (ca == 0) ca = i; cb = i; continue }
            flush()
            if (i in subimg) {
                nsubst++
                addrow(subst[t[i] SUBSEP subimg[i]], "substituted",
                       item(i, i), subimg[i], curline)
            }
        }
        flush()
        for (j = 1; j <= no; j++)
            if (j in ins) {
                bad++
                printf "SETUP: line %d emits '%s', which the block does not have\n", curline, u[j] > "/dev/stderr"
            }
    }
    for (k = 1; k <= rows; k++)
        printf "%d\t%s\t%s\t%s\t%d\t%s\n", cls[k], kind[k], it[k], img[k], lnr[k], reason[cls[k]]
    if (nsubstfile != "") printf "%d\n", nsubst > nsubstfile
    exit (bad > 0)
}

function aligned(i, j) {
    return t[i] == u[j] || ((t[i] SUBSEP u[j]) in subst)
}

# Align the block's tokens with the body's.  The cost is lexicographic: an edit
# costs a thousand, and a *run* of deletions costs one more than its length — so
# the alignment that keeps a removed clause whole beats one that reaches into
# the clause for a token equal to a neighbouring survivor, at equal edit count.
# `st` in the DP is whether the previous step deleted, which is how a run is
# counted.  Fills `del`, `ins` and `subimg`.
function align(nt, no,   i, j, best, v, v0, v1, st, oldi) {
    split("", del); split("", ins); split("", subimg)
    split("", d0); split("", d1)
    d0[0, 0] = 0; d1[0, 0] = BIG
    for (i = 1; i <= nt; i++) { d0[i, 0] = BIG; d1[i, 0] = 1001 + (i - 1) * 1000 }
    for (j = 1; j <= no; j++) { d0[0, j] = j * 1000; d1[0, j] = BIG }
    for (i = 1; i <= nt; i++)
        for (j = 1; j <= no; j++) {
            best = BIG
            if (aligned(i, j)) {
                v = d0[i - 1, j - 1]
                if (d1[i - 1, j - 1] < v) v = d1[i - 1, j - 1]
                best = v
            }
            v = d0[i, j - 1]
            if (d1[i, j - 1] < v) v = d1[i, j - 1]
            v += 1000
            if (v < best) best = v
            d0[i, j] = best
            best = d0[i - 1, j] + 1001
            v = d1[i - 1, j] + 1000
            if (v < best) best = v
            d1[i, j] = best
        }
    i = nt; j = no
    st = (d1[i, j] < d0[i, j]) ? 1 : 0
    while (i > 0 || j > 0) {
        if (st == 1) {
            del[i] = 1
            oldi = i
            i--
            if (i >= 0 && d1[i, j] < BIG && d1[i, j] + 1000 == d1[oldi, j]) st = 1
            else st = 0
            continue
        }
        if (i > 0 && j > 0 && aligned(i, j)) {
            v0 = d0[i - 1, j - 1]
            v1 = d1[i - 1, j - 1]
            v = (v1 < v0) ? v1 : v0
            if (d0[i, j] == v) {
                if (t[i] != u[j]) subimg[i] = u[j]
                st = (v1 < v0) ? 1 : 0
                i--; j--
                continue
            }
        }
        ins[j] = 1
        j--
        v0 = d0[i, j]
        v1 = d1[i, j]
        st = (v1 < v0) ? 1 : 0
    }
    ca = 0; cb = 0
}

# Split a line into tokens (runs of characters outside `seps`) and the
# separators after each one; returns the token count.  `sep[k]` is everything
# between token k and token k+1, so a record can be spelled exactly.
function tokenize(s, tk, sp,   n, k, c, cur, inTok) {
    k = 0; cur = ""; inTok = 0; sp[0] = ""
    for (n = 1; n <= length(s); n++) {
        c = substr(s, n, 1)
        if (index(seps, c) > 0) {
            if (inTok) { k++; tk[k] = cur; sp[k] = c; cur = ""; inTok = 0 }
            else { sp[k] = sp[k] c }
        } else { cur = cur c; inTok = 1 }
    }
    if (inTok) { k++; tk[k] = cur }
    return k
}

# The record of tokens a..b, joined by the separators the block had, plus the
# closing brackets the run opened and did not close inside itself (the closing
# `)` of `captures(none)` sits after the last token of the run).
function item(a, b,   s, k, depth, q, m, add, c) {
    s = t[a]
    depth = 0
    for (k = a; k < b; k++) {
        q = sep[k]
        depth += gsub(/\(/, "(", q)
        depth -= gsub(/\)/, ")", q)
        s = s sep[k] t[k + 1]
    }
    if (depth > 0) {
        q = sep[b]
        add = ""
        for (m = 1; m <= length(q); m++) {
            c = substr(q, m, 1)
            if (c == "(") { depth++; add = add c; continue }
            if (c == ")") { depth--; add = add c; if (depth <= 0) break; continue }
            break
        }
        if (depth <= 0) s = s add
    }
    return s
}

function addrow(c, k, s, im, ln) {
    rows++; cls[rows] = c; kind[rows] = k; it[rows] = s; img[rows] = im; lnr[rows] = ln
}

# The index of the token closing the paren group opened after token k, or k when
# no group is opened.
function parenend(k,   depth, c, m, q) {
    depth = 0
    q = sep[k]
    depth += gsub(/\(/, "(", q)
    depth -= gsub(/\)/, ")", q)
    if (depth <= 0) return k
    for (m = k + 1; m <= nt; m++) {
        q = sep[m]
        depth += gsub(/\(/, "(", q)
        depth -= gsub(/\)/, ")", q)
        if (depth <= 0) return m
    }
    return nt
}

function numeric(s) { return s ~ /^-?[0-9]+$/ }

# The last token of the run that class `c` accounts for, starting at `a`, or 0.
function matchclass(c, a, b,   e) {
    if (c == 1) {
        if (t[a] in c1word) return a
        if (t[a] in c1paren) { e = parenend(a); return (e > a) ? e : 0 }
        return 0
    }
    if (c == 2) {
        if (!isheader) return 0
        if (t[a] in c2word) return a
        if (t[a] ~ /^#[0-9]+$/) return a
        if (t[a] == "align" && a + 1 <= b && numeric(t[a + 1])) return a + 1
        return 0
    }
    if (c == 4) return (t[a] in c4word) ? a : 0
    if (c == 5) {
        if (substr(t[a], 1, 1) != "!") return 0
        e = a
        while (e + 1 <= b && substr(t[e + 1], 1, 1) == "!") e++
        return e
    }
    if (c == 6) return (t[a] == "poison") ? a : 0
    if (c == 7) {
        if (t[a] in c7paren) { e = parenend(a); return (e > a) ? e : 0 }
        return 0
    }
    if (c == 9) {
        if (isheader) return 0
        if (t[a] == "align" && a + 1 <= b && numeric(t[a + 1])) return a + 1
        return 0
    }
    if (c == 10) {
        if (isheader) return 0
        return (t[a] in c10word) ? a : 0
    }
    return 0
}

# Attribute the run ca..cb to classes, in class order, by consecutive prefixes.
function flush(   k, c, e, hit) {
    if (ca == 0) return
    k = ca
    while (k <= cb) {
        hit = 0
        for (c = 1; c <= 10; c++) {
            if (c == 3 || c == 8) continue   # whole lines, not tokens
            e = matchclass(c, k, cb)
            if (e > 0) {
                addrow(c, "removed", item(k, e), "", curline)
                k = e + 1
                hit = 1
                break
            }
        }
        if (!hit) {
            bad++
            printf "SETUP: line %d removes '%s', which matches no class\n", curline, t[k] > "/dev/stderr"
            k++
        }
    }
    ca = 0; cb = 0
}
AWK

# Each block's offset inside the comment-free module, so every row's `line` is a
# line of the emission.
nsubst_total=0
: > "$work/rows.strip"
: > "$work/rows.subst"
while read -r start end sym; do
  ofs=$((start - 1))
  awk -v nsubstfile="$work/nsubst.$sym" -v ofs="$ofs" -f "$work/classify.awk" \
    "$work/block.$sym.ll" "$work/body.$sym.ll" > "$work/rows.$sym" ||
    fail "the removal in @$sym could not be attributed to classes (see above)"
  awk -F'\t' '$2 == "substituted"' "$work/rows.$sym" >> "$work/rows.subst"
  awk -F'\t' '$2 != "substituted"' "$work/rows.$sym" >> "$work/rows.strip"
  n=$(cat "$work/nsubst.$sym" 2>/dev/null || printf '0')
  nsubst_total=$((nsubst_total + n))
done < "$work/ranges"

# --- the strip table reconstructs the emission ---------------------------

# The strip table is the fixture's provenance, so the emission must be exactly
# the body with the table's rows read back: each `removed` item deleted from the
# emission line in the table's recorded order, and each `substituted` token left
# where its image stands.  This reads the table rather than the aligner that
# wrote it, so a row whose item text is wrong, a difference no row records, or a
# substitution the table claims and the body does not carry is a failure.  A
# file compared with its own copy is not: that check can never fail.
reconstruct_check() { # <emission-block> <body> <rows> <offset>
  awk -v rowsf="$3" -v ofs="$4" '
    function tokenize(s, tk,   n, k, c, cur, inTok) {
      k = 0; cur = ""; inTok = 0
      for (n = 1; n <= length(s); n++) {
        c = substr(s, n, 1)
        if (index(" \t,()<>{}", c) > 0) {
          if (inTok) { tk[++k] = cur; cur = ""; inTok = 0 }
        } else { cur = cur c; inTok = 1 }
      }
      if (inTok) tk[++k] = cur
      return k
    }
    BEGIN {
      while ((getline r < rowsf) > 0) {
        if (r == "") continue
        split(r, f, "\t")
        ln = f[5] + 0 - ofs
        nrow[ln]++
        kind[ln, nrow[ln]] = f[2]; item[ln, nrow[ln]] = f[3]; image[ln, nrow[ln]] = f[4]
        if (f[2] == "substituted") total_sub++
      }
    }
    FILENAME == ARGV[1] { em[FNR] = $0; ne = FNR; next }
    FILENAME == ARGV[2] { bd[FNR] = $0; nb = FNR; next }
    END {
      bad = 0; seen_sub = 0
      if (ne != nb) {
        printf "the emission block has %d line(s) and the body %d\n", ne, nb > "/dev/stderr"
        bad = 1
      }
      for (ln = 1; ln <= ne && ln <= nb; ln++) {
        text = em[ln]; cursor = 1
        for (r = 1; r <= nrow[ln]; r++) {
          if (kind[ln, r] != "removed") continue
          p = index(substr(text, cursor), item[ln, r])
          if (p == 0) {
            printf "line %d: the strip table removes '\''%s'\'', which the emission does not carry there\n", \
              ln + ofs, item[ln, r] > "/dev/stderr"
            bad = 1
            continue
          }
          pos = cursor + p - 1
          text = substr(text, 1, pos - 1) substr(text, pos + length(item[ln, r]))
          cursor = pos
        }
        nt = tokenize(text, T)
        nu = tokenize(bd[ln], U)
        if (nt != nu) {
          printf "line %d: the emission less the removed items has %d token(s), the body %d\n", \
            ln + ofs, nt, nu > "/dev/stderr"
          bad = 1
          continue
        }
        for (i = 1; i <= nt; i++) {
          if (T[i] == U[i]) continue
          ok = 0
          for (r = 1; r <= nrow[ln]; r++)
            if (kind[ln, r] == "substituted" && item[ln, r] == T[i] && image[ln, r] == U[i]) {
              ok = 1; seen_sub++; break
            }
          if (!ok) {
            printf "line %d: the body has '\''%s'\'' where the emission less the rows has '\''%s'\'', and no row records it\n", \
              ln + ofs, U[i], T[i] > "/dev/stderr"
            bad = 1
            break
          }
        }
      }
      if (seen_sub != total_sub) {
        printf "the strip table records %d substitution(s) and the reconstruction applied %d\n", \
          total_sub, seen_sub > "/dev/stderr"
        bad = 1
      }
      exit (bad ? 1 : 0)
    }
  ' "$1" "$2"
}

: > "$work/perturb.src"
while read -r start end sym; do
  ofs=$((start - 1))
  if ! reconstruct_check "$work/block.$sym.ll" "$work/body.$sym.ll" "$work/rows.$sym" "$ofs"; then
    fail "the strip table is not the emission less its rows, in @$sym"
  fi
  [ -s "$work/perturb.src" ] && continue
  printf '%s %s\n' "$sym" "$ofs" > "$work/perturb.src"
done < "$work/ranges"
printf 'ok: each block is the emission less the strip table'\''s rows, and the substitutions the table records are the ones applied\n'

# The reconstruction is exercised in the same run on a body it must refuse: one
# token deleted is a difference no row records, so a reconstruction that accepts
# it is not evidence about the real pair.
read -r psym pofs <<< "$(cat "$work/perturb.src")"
awk '!done && /^  ret / { sub(/^  ret /, "  "); done = 1 } { print }' \
  "$work/body.$psym.ll" > "$work/body.perturbed.ll"
cmp -s "$work/body.$psym.ll" "$work/body.perturbed.ll" &&
  fail "the reconstruction control did not change the body; it is not evidence"
if reconstruct_check "$work/block.$psym.ll" "$work/body.perturbed.ll" "$work/rows.$psym" "$pofs" \
     > "$work/perturbed.out" 2>&1; then
  fail "the reconstruction accepts a body difference the strip table does not record; it is not evidence"
fi
printf 'ok: the reconstruction refuses an unrecorded change (@%s)\n' "$psym"

# --- the whole-line removals: what the module carries and the fixture does not

classify_lines() {
  awk -v ranges="$work/allranges" -v tabledef="@UJ_UNESC =" '
    BEGIN {
      reason[2] = "function-header surface: linkage, code placement and a callee'"'"'s declaration, which the model has no semantics for; the Calls environment decides which definition answers"
      reason[3] = "attribute-group definition: the target-feature and memory promise its references carry, recorded in PROVENANCE.md"
      reason[5] = "memory and analysis metadata: the model has no aliasing relation and no loop model to read it with"
      reason[8] = "module configuration and module-level symbols: not read by the parser; the configuration is recorded in the fixture'"'"'s provenance comment and in PROVENANCE.md, and the table becomes the %tab parameter (json-escape.table.tsv)"
      n = 0
      while ((getline l < ranges) > 0) {
        n++
        split(l, f, " ")
        rs[n] = f[1] + 0; re[n] = f[2] + 0
      }
      bad = 0
    }
    {
      ln = NR
      inside = 0
      for (i = 1; i <= n; i++) if (ln >= rs[i] && ln <= re[i]) { inside = 1; break }
      if (inside) next
      if ($1 == "attributes") c = 3
      else if ($1 == "declare") c = 2
      else if (substr($1, 1, 1) == "!") c = 5
      else if ($1 == "target" || $1 == "source_filename") c = 8
      else if (substr($0, 1, length(tabledef)) == tabledef) c = 8
      else if (substr($1, 1, 1) == "@") {
        bad++
        printf "SETUP: line %d of the module defines a module-level symbol ('"'"'%s'"'"');\n", ln, $0 > "/dev/stderr"
        printf "SETUP: this unit has one global, the UJ_UNESC table, so a second one means\n" > "/dev/stderr"
        printf "SETUP: the emission has changed shape and the fixture no longer describes the unit\n" > "/dev/stderr"
        next
      }
      else {
        bad++
        printf "SETUP: line %d of the module ('"'"'%s'"'"') matches no class\n", ln, $0 > "/dev/stderr"
        next
      }
      printf "%d\tline\t%s\t\t%d\t%s\n", c, $0, ln, reason[c]
    }
    END { exit (bad > 0) }
  ' "$1"
}

classify_lines "$work/module.ll" > "$work/strip.lines" ||
  fail "the module's whole-line removals could not be attributed to classes (see above)"

if ! grep -q "^@$table_symbol = " "$work/module.ll"; then
  fail "the emission does not define @$table_symbol; the table rewrite has no source"
fi
ntabledef=$(grep -c "^@" "$work/module.ll" || true)
[ "$ntabledef" -eq 1 ] ||
  fail "the module defines $ntabledef module-level symbol(s); the unit's one table is $table_symbol"

# --- the table: which bodies take the base, and the rewrite itself --------

# A body takes the base when it reads the table or calls a body that does.  The
# fixpoint is closed here, over the emission's own text, and its two failure
# directions are caught later by checks that do not share this code: a body that
# declares the base must use it, and the fixture must verify as IR.
takers=" "
for sym in "${symbols[@]}"; do
  if grep -q "ptr @$table_symbol" "$work/body.$sym.ll"; then
    takers="$takers$sym "
  fi
done
changed=1
while [ "$changed" -eq 1 ]; do
  changed=0
  for sym in "${symbols[@]}"; do
    case " $takers " in *" $sym "*) continue ;; esac
    for t in $takers; do
      if grep -q "@$t(" "$work/body.$sym.ll"; then
        takers="$takers$sym "
        changed=1
        break
      fi
    done
  done
done
printf '%s\n' $takers | LC_ALL=C sort > "$work/takers"

: > "$work/table.rows"
for sym in "${symbols[@]}"; do
  takes=0
  grep -qx "$sym" "$work/takers" && takes=1

  # The fixture body is the normalised body with the table read rewritten, the
  # call that passes the base extended, and the parameter list appended.  The
  # rows come from `attribute`, which diffs the two texts it is given, so the set
  # is the difference and not a list kept here.
  awk -v takes="$takes" -v tsym="$table_symbol" -v tparam="${table_param#%}" '
    BEGIN { OFS = "" }
    {
      line = $0
      if (NR > 1) {
        key = "getelementptr inbounds [256 x i8], ptr @" tsym ", i64 0, i64 "
        i = index(line, key)
        if (i > 0) {
          pre = substr(line, 1, i - 1)
          idx = substr(line, i + length(key))
          if (idx ~ /^%[A-Za-z0-9._$-]+$/) line = pre "getelementptr inbounds i8, ptr %" tparam ", i64 " idx
        }
      }
      body[NR] = line
      n = NR
    }
    END {
      # The parameter list gains the table base; only a body that reads or
      # passes the table takes it.
      if (takes && n > 0) sub(/\)[ \t]*\{[ \t]*$/, ", ptr %" tparam ") {", body[1])
      for (k = 1; k <= n; k++) print body[k]
    }
  ' "$work/body.$sym.ll" > "$work/fixture-body.$sym.ll"

  # The call that passes the base: every call to a taker gains the argument.
  if [ "$takes" -eq 1 ]; then
    for t in $(cat "$work/takers"); do
      [ "$t" = "$sym" ] && continue
      awk -v callee="@$t(" -v tparam="${table_param#%}" '
        {
          line = $0
          if (NR > 1 && index(line, callee) > 0 && sub(/\)[ \t]*$/, "", line)) {
            print line ", ptr %" tparam ")"
          } else print
        }
      ' "$work/fixture-body.$sym.ll" > "$work/fixture-body.$sym.tmp"
      mv "$work/fixture-body.$sym.tmp" "$work/fixture-body.$sym.ll"
    done
  fi

  attribute "$work/body.$sym.ll" "$work/fixture-body.$sym.ll" "$work/block.$sym.ll" \
    > "$work/table.$sym" ||
    fail "the table rewrite of @$sym could not be attributed (see above)"
  cat "$work/table.$sym" >> "$work/table.rows"

  # The parameter and the uses stand or fall together: a body that declares the
  # base must use it, and one that does not must not name it.
  if [ "$takes" -eq 1 ]; then
    grep -q "ptr ${table_param})" "$work/fixture-body.$sym.ll" ||
      fail "@$sym takes the table but its fixture header does not declare $table_param"
    tail -n +2 "$work/fixture-body.$sym.ll" | grep -q -- "$table_param" ||
      fail "@$sym declares $table_param and its body never uses it"
  else
    if grep -q -- "$table_param" "$work/fixture-body.$sym.ll"; then
      fail "@$sym does not read the table but its fixture names $table_param"
    fi
  fi
done

[ -s "$work/table.rows" ] || fail "no table rewrite was recorded"

# --- the fixture's inventory ----------------------------------------------

inventory_of() {
  awk '
    /^[ \t]*;/ { next }
    /^[ \t]*$/ { next }
    /^[A-Za-z_][A-Za-z0-9_.]*:$/ { next }
    {
      line = $0
      sub(/^[ \t]+/, "", line)
      if (line ~ /^(define|declare) /) next
      if (substr(line, 1, 1) == "%") {
        eq = index(line, " = ")
        if (eq == 0) next
        line = substr(line, eq + 3)
      }
      if (line == "}") next
      if (line ~ /^(tail )?call /) print "opcode call"
      else {
        split(line, w, /[ \t]+/)
        if (w[1] ~ /^[a-z]+$/) print "opcode " w[1]
      }
      rest = line
      while (match(rest, /@[A-Za-z0-9_.$-]+/)) {
        print "call " substr(rest, RSTART, RLENGTH)
        rest = substr(rest, RSTART + RLENGTH)
      }
    }
  ' "$1" | LC_ALL=C sort -u
}

# --- the fixture ----------------------------------------------------------

# The module configuration the removed lines carried, read from the emission so
# the provenance comment cannot drift from it.
module_config() {
  awk '
    /^source_filename =/ { printf "%s\n", $0; next }
    /^target triple/ { printf "%s\n", $0; next }
    /^target datalayout/ { printf "%s\n", $0; next }
  ' "$1"
}
module_config "$work/module.ll" > "$work/config.txt"

{
  cat <<'PROVENANCE'
; The escape unit as emitted, in the fragment the parser reads: the
; escape-position list @leanllvm_json_escape_list, the list-driven expander's
; entry point @leanllvm_json_escape_expand, the decoder @us_dec_x it calls, and
; the out-of-line batch @xl_batch the list calls — in the emission's order.
; Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-escape.sh
;
; from kernel/json/escape.c, emitted with the measured compiler line
;
;   clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
;         -falign-loops=64 -falign-functions=64 -fno-discard-value-names
;
; and at the measured `-D` set (`build49.sh:19-21` plus `-DUS_EMIT4=1`), then
; reduced to those four `define` blocks.  `-fno-discard-value-names` is a naming
; flag: it names values and labels the entry block, which the parser requires,
; and the capture checks that it changes no instruction by emitting the source
; with and without it and comparing the two texts with every register name
; replaced by one placeholder.  It checks the `-D` set the same way, so a
; configuration the unit does not consult is recorded as such rather than
; assumed.
;
; Every parameter of every function is the source's own name, so the capture
; renames none.  Two headers below carry one parameter more than the source's
; list: the table base the rewrite appends.
;
; The table read is rewritten, because the fragment has no module-level
; globals.  @us_dec_x's
;
;   getelementptr inbounds nuw [256 x i8], ptr @UJ_UNESC, i64 0, i64 %idxprom.i
;
; becomes
;
;   getelementptr inbounds i8, ptr %tab, i64 %idxprom.i
;
; and %tab is appended to the parameter list of the bodies that read or pass it
; — @us_dec_x, and @leanllvm_json_escape_expand, which calls it.  The emitted
; form addresses @UJ_UNESC + 0 * 256 + idx * 1 and the rewritten form
; %tab + idx * 1, so the byte offset from the base is idx on both sides and only
; the base differs, which is what the record's table hypothesis supplies.  `nuw`
; is class 4's removal and is gone before the rewrite.  Each site, including the
; call that passes the base, is recorded in json-escape.table.tsv.
;
; The hex reader's four vector constants carry `poison` lanes past the four
; digits, and nothing reads past lane 3 — the class test takes the movemask
; `& 0x0F`, and the value is lane 0 of the `pmadd.wd` result — so each poisoned
; lane is written as the defined lane 0 and every replacement is a row in
; json-escape.rewrites.tsv.
;
; Removed from the emission, each item with its class and the class's reason, in
; json-escape.strip.tsv.  The lines removed from the module carried:
PROVENANCE
  sed -e 's/^/;   /' "$work/config.txt"
  cat <<'PROVENANCE'
;   (the attribute groups, the five callee declarations, the table's definition
;   and the module metadata nodes are recorded in json-escape.strip.tsv, where
;   they are removed; the table is recorded in json-escape.table.tsv as well)
;
; The fixture is checked as well-formed IR, not only as a text the parser reads,
; by the invocation a reader can repeat:
;
;   opt -passes=verify -disable-output json-escape.candidate.ll
;
; The fixture's own opcodes and call targets are in json-escape.inventory.
PROVENANCE
  while read -r start end sym; do
    cat "$work/fixture-body.$sym.ll"
  done < "$work/ranges"
} > "$work/fixture.ll"

inventory_of "$work/fixture.ll" > "$work/inventory.body"

# --- the intrinsic call set, and the models it needs ---------------------

# The emission's call set, enumerated by the same instrument that writes the
# inventory: every `call @llvm.*` line of the file.  This is the list the
# intrinsic vocabulary's count is derived from, so it is read, never recalled.
intrinsic_calls() {
  awk '$1 == "call" && $2 ~ /^@llvm\./ { sub(/^@/, "", $2); print $2 }' "$1" |
    LC_ALL=C sort -u
}
intrinsic_calls "$work/inventory.body" > "$work/intrinsics"

# The modelled set, extracted from the tree: the intrinsic spellings some `Calls`
# environment binds, in the emitted-IR bridges that define one.  `Parser.lean`
# is deliberately outside it — `checkIntrinsicShape` validates a spelling, and
# admission is not a model; the model is the binding the bridge supplies.
modelled_set() {
  local f
  for f in "$repo"/LeanLLVM/Refinement/*.lean; do
    grep -qE '^def [A-Za-z0-9_]*Calls : Calls' "$f" || continue
    grep -oE '^[[:space:]]*\| "llvm\.[^"]+"' "$f" |
      sed -E 's/.*"(llvm[^"]*)"/\1/'
  done | LC_ALL=C sort -u
}
modelled_set > "$work/modelled"

[ -s "$work/modelled" ] ||
  fail "no intrinsic binding was found in LeanLLVM/Refinement; the modelled set's extractor is not evidence"
grep -qx 'llvm.cttz.i64' "$work/modelled" ||
  fail "the modelled set's extractor does not see llvm.cttz.i64, a spelling the tree binds; it is not evidence"

LC_ALL=C comm -23 "$work/intrinsics" "$work/modelled" > "$work/new"
LC_ALL=C comm -12 "$work/intrinsics" "$work/modelled" > "$work/have"

# The inventory the fixture stands behind: the derived header, then the sorted
# body.  The counts are read off the lists beside them, so the file cannot claim
# a split the lists do not spell.
{
  cat <<'LEGEND'
# json-escape.inventory -- generated by
# probes/install/ir/capture-escape.sh; do not edit.
#
# The fixture's own opcodes and call targets, sorted and unique: one line per
# construct, so a form entering the emission shows as a line and not as a count.
#
# The intrinsic call set is what the escape unit's model vocabulary is sized
# from, so the split is measured here and printed beside the list it counts.
# "bound in the tree" means some `Calls` environment in `LeanLLVM/Refinement` binds
# the spelling; `Parser.lean`'s `checkIntrinsicShape` validates a spelling and is
# not a model, so it is outside the comparison.  A callee that is not an
# `llvm.*` intrinsic is one of the fixture's own definitions, and the capture
# refuses an internal call to anything the fixture does not define.
LEGEND
  printf '#   called: %s (%s)\n' \
    "$(wc -l < "$work/intrinsics" | tr -d ' ')" "$(tr '\n' ' ' < "$work/intrinsics")"
  printf '#   bound in the tree: %s (%s)\n' \
    "$(wc -l < "$work/have" | tr -d ' ')" "$(tr '\n' ' ' < "$work/have")"
  printf '#   no model: %s (%s)\n' \
    "$(wc -l < "$work/new" | tr -d ' ')" "$(tr '\n' ' ' < "$work/new")"
  cat "$work/inventory.body"
} > "$work/inventory.txt"

if grep -v '^;' "$work/fixture.ll" | grep -q "@$table_symbol"; then
  fail "the fixture still names @$table_symbol; the table read was not rewritten"
fi

# Every ``%tab`` in the fixture is one of the three recorded forms: the header
# of a taker, the rewritten GEP, or the argument a call passes.  A fourth form
# would be a rewrite no inventory row describes.
bad_tab=$(grep -v '^;' "$work/fixture.ll" \
  | grep -v '^define .*ptr %tab)' \
  | grep -v 'getelementptr inbounds i8, ptr %tab, i64 %' \
  | grep -v ', ptr %tab)$' \
  | grep -c -- '%tab' || true)
[ "$bad_tab" -eq 0 ] ||
  fail "the fixture names %tab in $bad_tab place(s) that are not a recorded rewrite form"

# The fixture is well-formed LLVM IR, not only a text the parser reads.  The
# invocation is the one the fixture's provenance comment names, so the claim and
# the command that checks it cannot drift apart.
command -v opt >/dev/null 2>&1 || fail "opt is not on PATH; the fixture's verify step needs it"
opt -passes=verify -disable-output "$work/fixture.ll" ||
  fail "the fixture does not verify as LLVM IR"
printf 'ok: the fixture verifies as LLVM IR (opt -passes=verify)\n'

# The repository's parser is a *report*, not a gate here.  `opt` says the IR is
# well-formed and says nothing about whether this repository can read it, so the
# verdict is taken from the parser and printed on every run: a fixture the
# parser refuses is the fragment's gap and is cleared by the slice that widens
# the fragment, and the capture must name it rather than leave it to be
# discovered.  Nothing is written conditionally on the verdict, because the
# artefacts are the derivation; the gate's parse criterion is the verdict.
repository_parse() { # <file> -- the parser's own output, its exit status
  if [ -x "$repo/.lake/build/bin/leanllvm" ]; then
    "$repo/.lake/build/bin/leanllvm" --passes none --no-check -o /dev/null "$1" 2>&1
  elif command -v lake >/dev/null 2>&1; then
    ( cd "$repo" && lake exe leanllvm --passes none --no-check -o /dev/null "$1" 2>&1 )
  else
    printf 'SETUP: no parser: build one with '"'"'lake build leanllvm'"'"' or put lake on PATH\n'
    return 3
  fi
}

parse_status=0
parse_out=$(repository_parse "$work/fixture.ll") || parse_status=$?
if [ "$parse_status" -eq 0 ]; then
  printf 'ok: the fixture parses under the repository parser\n'
else
  nrefused=$(grep -v '^;' "$work/fixture.ll" | grep -c '= select <16 x i1>' || true)
  printf 'REPORT: the fixture does not parse under the repository parser (exit %s)\n' "$parse_status"
  printf '%s\n' "$parse_out" |
    sed -e "s|$work/fixture.ll|probes/install/ir/json-escape.candidate.ll|g" -e 's/^/REPORT:   /'
  printf 'REPORT: the refused form is the lane-wise select: %s line(s) of this fixture\n' "$nrefused"
  printf 'REPORT: carry it — `<16 x i1>` condition, `<16 x i8>` operands, refused by name at\n'
  printf 'REPORT: LeanLLVM/Parser.lean:1160-1166.  The widening slice clears this red; until it\n'
  printf 'REPORT: lands the fixture is well-formed IR this repository cannot read, and the\n'
  printf 'REPORT: capture slice is not complete.\n'
  printf 'REPORT:   nix develop -c .lake/build/bin/leanllvm --passes none --no-check -o /dev/null probes/install/ir/json-escape.candidate.ll\n'
fi

# --- the inventories ------------------------------------------------------

{
  cat <<'LEGEND'
# json-escape.strip.tsv -- generated by
# probes/install/ir/capture-escape.sh; do not edit.
#
# What the normalisation took out of the clang emission of kernel/json/escape.c,
# by class.  Each row is one removed item: a token or contiguous run of tokens
# inside a `define` block, or a whole line.
# `line` is the line of the emission the item came from (the module as emitted,
# comment and blank lines dropped, so the four blocks' lines are numbered in one
# sequence and a row can be found in the emission).
#
# What the normalisation *rewrote* rather than removed — the `poison` lanes of
# the hex reader's four vector constants — is in json-escape.rewrites.tsv; the
# table read's rewrite, and the call that passes its base, are in
# json-escape.table.tsv.
#
# The ten classes:
#
#   1  argument, parameter and call-result attributes (`noundef`, `readonly`,
#      `writeonly`, `immarg`, `captures(...)`, `range(...)` on a call's result or
#      on a parameter)
#   2  function-header surface (`local_unnamed_addr`, `unnamed_addr`, `#N`, the
#      function's `align`, and a `declare` line)
#   3  attribute-group definitions
#   4  instruction flags that constrain (nuw, nsw, nusw, disjoint, nneg:
#      stripping widens; recorded, not re-established)
#   5  memory and analysis metadata (`!tbaa`, `!prof`, `!llvm.loop`, `!N = ...`)
#   6  poison as a value -- its instances are rewrites, so the rows are in
#      json-escape.rewrites.tsv
#   7  initializes((0, 32)) -- xl_batch's `%o` (the theorem's memory clause is
#      stronger for the bytes it covers)
#   8  module configuration and module-level symbols (the configuration is
#      recorded in the fixture's provenance comment and in PROVENANCE.md; the
#      table becomes the %tab parameter, json-escape.table.tsv)
#   9  instruction-level alignment (the parser's load has no alignment field)
#  10  a call's calling convention (`call fastcc`; the parser drops the same
#      token on a `define` header and refuses it on a call)
#
# A token matching no class stops the capture with exit 3, so this file cannot
# fall behind the emission.
LEGEND
  printf 'class\tkind\titem\timage\tline\treason\n'
  {
    cat "$work/rows.strip"
    cat "$work/strip.lines"
  } | LC_ALL=C sort -t "$(printf '\t')" -k1,1n -k5,5n -k3,3 -s
} > "$work/strip.tsv"

{
  cat <<'LEGEND'
# json-escape.rewrites.tsv -- generated by
# probes/install/ir/capture-escape.sh; do not edit.
#
# Every place the normalisation *rewrote* text of the clang emission of
# kernel/json/escape.c instead of removing it, with the reason the rewrite is
# sound.  One kind:
#
#   substituted  a token replaced by a defined one: `poison`, class 6 of the
#                normalisation's classes.  The hex reader's four vector
#                constants -- the `and` and the `select`'s two operands, and the
#                two pmadd calls' constants -- carry `poison` past the four
#                digits, and nothing reads past lane 3: the class test takes the
#                movemask `& 0x0F`, and the value is lane 0 of the
#                `llvm.x86.sse2.pmadd.wd` result.  The poisoned lanes therefore
#                feed lanes nothing observes, and the defined lane 0 stands in.
#                The `from` column is the emitted token, the `to` column the one
#                the fixture holds.
#
#   rename       a register renamed.  Every parameter is the source's own name,
#                so this unit's capture performs no rename and the kind has no
#                row here.  The machinery is kept and the names are read from
#                the emission; a row appearing that the source did not call for
#                is a diff.
#   splat        a splat vector constant written as its lane list.  This unit's
#                vector constants are lane lists the parser already reads, so
#                the kind has no row here either.
#
# A rewrite with no row here stops the capture: the alignment refuses any token
# the body adds that is not one of the substitutions declared here, and this
# file must account for every substitution the alignment made.  `line` is the
# line of the emission, as in the strip inventory.
LEGEND
  printf 'class\tkind\tfrom\tto\tline\treason\n'
  awk -F'\t' 'BEGIN { OFS = "\t" }
    { print $1, $2, $3, $4, $5, "poison replaced by the defined lane 0: the lane is past the four hex digits of a 16-byte constant, and nothing reads past lane 3 — the class test takes the movemask & 0x0F and the value is lane 0 of the llvm.x86.sse2.pmadd.wd result — so a defined lane stands in" }' \
    "$work/rows.subst" | LC_ALL=C sort -t "$(printf '\t')" -k2,2 -k5,5n -s
} > "$work/rewrites.tsv"

{
  cat <<'LEGEND'
# json-escape.table.tsv -- generated by
# probes/install/ir/capture-escape.sh; do not edit.
#
# The table read and the base that passes it, per site: the text the emission
# wrote and the text the fixture holds.  The fragment has no module-level
# globals, so the unit's table cannot be one; the base becomes a parameter.
#
#   gep   emitted    @UJ_UNESC + 0 * 256 + idx * 1   an aggregate base, two
#         rewritten  %tab     + idx * 1              the caller's base, one
#                                                    index, an i8 element type
#   call  emitted    @us_dec_x(... pos0)             the call to the body that
#         rewritten  @us_dec_x(... pos0, ptr %tab)   reads the table, one
#                                                    argument more
#
# The offset from the base is idx on both sides of the `gep` rows, so the
# differences are a base, an element type and an index arity, and nothing about
# the address.  `nuw` is class 4's removal and is gone before the rewrite; it is
# recorded in json-escape.strip.tsv.
#
# The parameter list differs by the appended `%tab` and by nothing else; a body
# that declares the base uses it, and one that does not never names it.  The rows
# are computed: the capture diffs its normalised emission against the text it
# emits, and a differing line that is neither one of these GEPs nor one of these
# calls stops it with exit 3.
LEGEND
  printf 'kind\temitted\trewritten\tline\treason\n'
  LC_ALL=C sort -t "$(printf '\t')" -k4,4n -s "$work/table.rows"
} > "$work/table.tsv"

# --- the derivation's own accounting -------------------------------------

grep -q '^opcode ' "$work/inventory.txt" || fail "the fixture inventory names no opcode"
grep -q '^call @' "$work/inventory.txt" || fail "the fixture inventory names no call target"

if awk -F'\t' '/^#/ || $1 == "class" { next } NF < 6 || $6 == ""' "$work/strip.tsv" |
     grep -q .; then
  fail "a removed item in the fixture has no recorded reason"
fi

if awk -F'\t' '/^#/ || $1 == "class" { next } NF < 6 || $6 == ""' "$work/rewrites.tsv" |
     grep -q .; then
  fail "a rewrite in the fixture has no recorded reason"
fi
nrewrite=$(awk -F'\t' '/^#/ || $1 == "class" { next } NF >= 6' "$work/rewrites.tsv" | wc -l | tr -d ' ')
[ "$nrewrite" -eq "$nsubst_total" ] ||
  fail "the rewrite inventory accounts for $nrewrite substitution(s); the alignment made $nsubst_total"
[ "$nrename" -eq 0 ] || fail "the rewrite inventory is empty and $nrename rename(s) were applied"

# Each count is read from the rows beside it, so a class that stops matching is
# a count that moves rather than a number that stays true.
class_count() { # <class>
  awk -F'\t' -v c="$1" '/^#/ || $1 == "class" { next } $1 == c' "$work/strip.tsv" |
    wc -l | tr -d ' '
}
# A class-5 item is a run of `!` tokens, so a metadata reference is counted by
# its first token and not by equality: `!tbaa !6` is one item and one `!tbaa`.
item_prefix_count() { # <class> <first token>
  awk -F'\t' -v c="$1" -v p="$2" '/^#/ || $1 == "class" { next }
    $1 == c && index($3, p) == 1' "$work/strip.tsv" | wc -l | tr -d ' '
}

nnuw=$(item_prefix_count 4 nuw)
nnsw=$(item_prefix_count 4 nsw)
nalign=$(item_prefix_count 9 'align')
ntbaa=$(item_prefix_count 5 '!tbaa')
nloop=$(item_prefix_count 5 '!llvm.loop')
ninit=$(item_prefix_count 7 'initializes')
ndec=$(item_prefix_count 2 'declare')
nattrs=$(item_prefix_count 3 'attributes')

# The table rewrite, counted both ways: the emission's own table reads and calls
# to a taker against the rows the attributor wrote.
ngep_emitted=$(cat "$work"/block.*.ll | grep -c "\[256 x i8\], ptr @$table_symbol, i64 0, i64" || true)
[ "$ngep_emitted" -ge 1 ] || fail "the emission reads @$table_symbol nowhere; the rewrite has no site"
[ "$(grep -c '^gep	' "$work/table.tsv" || true)" -eq "$ngep_emitted" ] ||
  fail "the table inventory accounts for $(grep -c '^gep	' "$work/table.tsv" || true) table read(s); the emission has $ngep_emitted"
ncall_emitted=0
for t in $(cat "$work/takers"); do
  for sym in "${symbols[@]}"; do
    [ "$sym" = "$t" ] && continue
    n=$(grep -c "@$t(" "$work/block.$sym.ll" || true)
    ncall_emitted=$((ncall_emitted + n))
  done
done
[ "$ncall_emitted" -ge 1 ] ||
  fail "no body calls a table taker; the fixpoint's transitive step has nothing to carry"
[ "$(grep -c '^call	' "$work/table.tsv" || true)" -eq "$ncall_emitted" ] ||
  fail "the table inventory accounts for $(grep -c '^call	' "$work/table.tsv" || true) passing call(s); the emission has $ncall_emitted"

# Every non-intrinsic callee the fixture calls is one of its own definitions:
# an internal call to a body the fixture does not hold would be an unmodelled
# call that is not an intrinsic, and the inventory would name it without saying
# where its meaning is.
while read -r kind target; do
  [ "$kind" = call ] || continue
  name=${target#@}
  case "$name" in
    llvm.*) continue ;;
    "$table_symbol")
      fail "the fixture calls @$name; the table read was not rewritten"
      ;;
  esac
  printf '%s\n' "${symbols[@]}" | grep -qx "$name" ||
    fail "the fixture calls @$name, which is neither an intrinsic nor one of its definitions"
done < "$work/inventory.txt"


# --- write the five artefacts, together ----------------------------------

cp "$work/fixture.ll" "$fixture"
cp "$work/strip.tsv" "$strip"
cp "$work/rewrites.tsv" "$rewrites"
cp "$work/table.tsv" "$table"
cp "$work/inventory.txt" "$inventory"

printf 'capture-escape: wrote probes/install/ir/json-escape.candidate.ll (%s line(s), %s function(s))\n' \
  "$(wc -l < "$work/fixture.ll" | tr -d ' ')" "$nfunc"
printf 'capture-escape: wrote probes/install/ir/json-escape.strip.tsv (%s row(s): %s class 1, %s class 2,\n' \
  "$(($(class_count 1) + $(class_count 2) + $(class_count 3) + $(class_count 4) + $(class_count 5) + $(class_count 7) + $(class_count 8) + $(class_count 9) + $(class_count 10)))" \
  "$(class_count 1)" "$(class_count 2)"
printf '    %s class 3, %s class 4, %s class 5, %s class 7, %s class 8, %s class 9, %s class 10;\n' \
  "$(class_count 3)" "$(class_count 4)" "$(class_count 5)" "$(class_count 7)" "$(class_count 8)" "$(class_count 9)" "$(class_count 10)"
printf '    class 6 is
    in json-escape.rewrites.tsv, where its instances are rewrites)\n'
printf 'capture-escape: wrote probes/install/ir/json-escape.rewrites.tsv (%s row(s); poison lanes\n' \
  "$nrewrite"
printf '    stand in as the defined lane 0, no rename and no splat expansion is applied)\n'
printf 'capture-escape: wrote probes/install/ir/json-escape.table.tsv (%s gep row(s), %s call row(s);\n' \
  "$(grep -c '^gep	' "$work/table.tsv" || true)" "$(grep -c '^call	' "$work/table.tsv" || true)"
printf '    %s of %s function(s) take the table base: %s)\n' \
  "$(wc -l < "$work/takers" | tr -d ' ')" "$nfunc" "$(tr '\n' ' ' < "$work/takers")"
printf 'capture-escape: wrote probes/install/ir/json-escape.inventory (%s line(s))\n' \
  "$(wc -l < "$work/inventory.txt" | tr -d ' ')"
# The call set counted in the fixture body itself: one entry per call site, so
# the count and the target are read off the same text the inventory is derived
# from and neither is a recollection of the other.
printf 'capture-escape: call sites in the fixture body, counted there: %s\n' \
  "$(grep -v '^;' "$work/fixture.ll" |
     grep -oE '(tail )?call [^@]*@[A-Za-z0-9_.$-]+' | sed -E 's/.*@/@/' |
     LC_ALL=C sort | uniq -c | awk '{ printf "%s%s=%s", (n++ > 0 ? ", " : ""), $2, $1 }')"
printf 'capture-escape: intrinsic spellings called: %s (%s); modelled in the tree: %s;\n' \
  "$(wc -l < "$work/intrinsics" | tr -d ' ')" "$(tr '\n' ' ' < "$work/intrinsics")" \
  "$(wc -l < "$work/modelled" | tr -d ' ')"
printf '    already modelled: %s (%s); genuinely new: %s (%s)\n' \
  "$(wc -l < "$work/have" | tr -d ' ')" "$(tr '\n' ' ' < "$work/have")" \
  "$(wc -l < "$work/new" | tr -d ' ')" "$(tr '\n' ' ' < "$work/new")"
printf 'capture-escape: counted in the strip rows: %s nuw, %s nsw, %s "align", %s "!tbaa",\n' \
  "$nnuw" "$nnsw" "$nalign" "$ntbaa"
printf '    %s "!llvm.loop", %s "initializes", %s declare, %s attributes line(s)\n' \
  "$nloop" "$ninit" "$ndec" "$nattrs"
