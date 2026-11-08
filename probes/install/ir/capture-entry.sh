#!/usr/bin/env bash
# Regenerate the entry unit's emitted-IR fixture and its four inventories in
# probes/install/ir/.
#
# Run through the flake, from the repository root:
#
#   nix develop -c bash probes/install/ir/capture-entry.sh
#
# Input
#   kernel/json/entry.c               the entry unit: the two position emitters,
#                                     the table they read and the three public
#                                     entry points
#
# Output (all five in the same run, from the same compilation)
#   json-entry.candidate.ll           the fixture: the `define` blocks of
#                                     @s1f_k_pos8 and of @s1f_k_b8, in that
#                                     order, with the syntax listed below
#                                     removed and the table read rewritten
#   json-entry.strip.tsv              what the normalisation removed, by class,
#                                     derived by diffing the emission against
#                                     the text this script emits
#   json-entry.rewrites.tsv           what it rewrote rather than removed, with
#                                     the reason the rewrite is sound
#   json-entry.table.tsv              the table read: per site, the emitted
#                                     global GEP and the parameter GEP it became
#   json-entry.inventory              the fixture's own opcodes and call targets
#
# `kernel/json/identity/inventory.sh --unit entry` is the gate: it regenerates
# all five and compares them byte for byte, parses the fixture, and fires its
# controls.  This script only derives; the verdict is that gate's.
#
# --- Why the measured compiler line, and not the classifier's ------------
#
# The fixture is the emission the *measured* build compiled, not a portable
# re-phrasing of it: `tests/json-entry/check.sh` compiles the same C at the same
# flags and calls that object, so the body the theorem is about is the body the
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
# The unit's own translation unit is the subject, and the two `noinline`
# kernels it defines are the functions extracted: `S1F_DEFINE_KERNEL` marks
# them `noinline`, so the emission holds one function per kernel rather than an
# inlined copy in each wrapper, and the wrappers and `leanllvm_json_entry_table`
# are not part of the fixture.  Nothing in the extracted blocks names them.
#
# --- The parameter names --------------------------------------------------
#
# The emission names the parameters after the source's, and the source's names
# are the ABI's (`%ent`, `%blk0`, `%nblk`, `%out`, `%k`), so this unit's capture
# performs no rename.  The machinery is kept and the count is read from the
# emission, not assumed: the capture takes the last token of each top-level
# parameter, refuses anything but five of them, and substitutes each one
# throughout the block under a token boundary.  A row appearing in
# json-entry.rewrites.tsv beyond the parameter renames is a plan change, so a
# rename that the ABI did not make shows up as a diff instead of passing
# silently.
#
# --- The table read: the one new rewrite -------------------------------
#
# The fragment has no module-level globals, so the emission's table and the
# eight GEPs that name it cannot be represented.  Each
#
#   getelementptr inbounds nuw [256 x [8 x i32]], ptr @xl_pos8, i64 0, i64 %idx
#
# is rewritten to
#
#   getelementptr inbounds <8 x i32>, ptr %tab, i64 %idx
#
# and `%tab` is appended to the function's parameter list.  Three operand
# differences, stated rather than implied:
#
#   base          `@xl_pos8` -> `%tab`: the base becomes the caller's, which is
#                 what the theorem's table hypothesis supplies.
#   element type  `[256 x [8 x i32]]` -> `<8 x i32>`: `Ty` has no array, and a
#                 vector element type keeps the offset one operand.  A packed
#                 `<8 x i32>` is 32 bytes, which is the stride the emitted
#                 aggregate computes.
#   index arity   two indices (`0`, `%idx`) -> one (`%idx`): the first is the
#                 aggregate row that the base absorbs.
#
# The arithmetic is one equation: the emitted form addresses
# `@xl_pos8 + 0 * (256 * 32) + idx * 32` and the rewritten form addresses
# `%tab + idx * 32`, so the byte offset from the base is `32 * idx` on both
# sides for every index, and only the base differs.  That is what makes the
# element type a spelling rather than a different address.
#
# The emitted GEP carries `nuw` and the rewritten one does not: `nuw` is class
# 4's removal, so it is gone before the rewrite and is recorded in
# json-entry.strip.tsv, not here.
#
# The difference set is **computed, not listed**: the capture takes the
# normalised emission and the text it emits, and every differing line must be
#
#   * a `getelementptr` whose base is the table symbol, or
#   * the function's parameter list, which differs by the appended `%tab`;
#
# a differing line that is neither is a setup failure (exit 3).  The per-site
# record is json-entry.table.tsv, whose rows carry the emitted text and the
# rewritten text, and each row's emitted text is checked to be the emission's
# line normalised.  `attribute` is exposed as `--attribute <emitted> <candidate>
# [<raw>]` so the gate can run this same detector over a pair it knows is
# unattributable and watch it refuse.
#
# --- What the normalisation removes, and why it is a derivation -----------
#
# The emission at those flags carries syntax the parser refuses by name.  The
# removal is computed, not transcribed: the capture diffs its own clang blocks
# against the text it emits, groups the removed tokens into contiguous runs, and
# attributes each run to one of nine classes, writing a row per item with the
# class's reason.  A token that matches no class exits `3`, so syntax cannot be
# stripped silently and the inventory cannot fall behind the emission.  A token
# the parser already accepts and drops (`tail`, `inbounds`, `samesign`,
# `internal`, `fastcc`, the written callee type) is never removed, so it never
# appears — the inventory is a record of what was taken out, not of what the
# parser tolerates.
#
# The nine classes.  A token that matches none of them exits `3`, so a class
# added for a new emission carries its reason with it instead of arriving as an
# edit to a token list:
#
#   1. argument, parameter and call-result attributes — `noundef`, `readonly`,
#      `writeonly`, `immarg`, `captures(...)`, a call's `range(...)` and an
#      operand's `range(...)`: a promise about an argument or a result.  What
#      the value is is re-established by the theorem's hypotheses, and a call's
#      or an operand's `range` is a promise the model's own definition
#      restates.
#   2. function-header surface — `unnamed_addr`, `local_unnamed_addr`, `#N`,
#      the function's `align`: linkage and code placement, for which the model
#      has no semantics; `Calls` decides which definition answers.
#   3. attribute-group definitions — `attributes #N = { ... }`: the target
#      feature and memory promise its references carry, removed with them and
#      recorded in PROVENANCE.md.
#   4. instruction flags that constrain — `nuw`, `nsw`, `nusw`, `disjoint`,
#      `nneg`: each excludes inputs, so stripping *widens*; the widening is
#      recorded rather than re-established.  `nneg` is this unit's addition and
#      is the reason the class exists rather than a width rule: `zext nneg`
#      asserts a non-negative source, and the stripped `zext` accepts any.
#   5. memory and analysis metadata — `!tbaa`, `!alias.scope`, `!noalias`,
#      `!llvm.loop` and the module's `!N = ...` nodes: the model has no
#      aliasing relation and no loop model to read them with.
#   6. `poison` as a value — `insertelement <8 x i32> poison, i32 %conv, i64 0`
#      and `shufflevector <8 x i32> %v, <8 x i32> poison, <8 x i32> ...`: no
#      observable reads the poisoned lane (the insert writes lane 0 and every
#      mask entry selects lane 0 of the first operand), so a defined lane is
#      put in its place.
#   7. `initializes((0, 48))` — a promise about which bytes of the slot are
#      written; the theorem's memory clause is *stronger* for the bytes it
#      covers, so the item is subsumed rather than dropped.
#   8. module configuration and module-level symbols — `target datalayout`,
#      `target triple`, `source_filename`, and the unit's statics
#      (`@xl_pos8`, `@xl_pos8_ready`): the parser reads no module text outside
#      the `define`/`declare` lines, and the table's own bytes are the
#      theorem's hypothesis (`pos8Table`) rather than a global of the model.
#      The configuration values are recorded in the fixture's provenance
#      comment and in PROVENANCE.md; the table does not disappear, it becomes
#      `%tab` (json-entry.table.tsv).
#   9. instruction-level alignment — `load ..., align 1` and `store ...,
#      align 32`: the parser's `load` and `store` have no alignment field, and
#      the model addresses bytes, so the removal is a representation loss and
#      not a semantic one.
#
# Whole lines are removed as lines and carry a class too: `attributes #N = { ... }`
# is class 3, the module header and the two statics are class 8, and a module
# metadata node is class 5.  Comment lines and inline comments are dropped
# before the diff rather than classified: `tokenize` (`LeanLLVM/Parser.lean`)
# truncates a line at `;` and `tokenLines` drops empty lines, so a comment
# carries no token the parser reads.  The fixture therefore holds instruction
# text and block labels only, and the `preds` lists the emission writes after a
# block label are readable from the `br` that precedes the target.
#
# Two rewrites are applied to the emission before that diff, because they are
# substitutions of a value rather than of one token, and both are recorded in
# json-entry.rewrites.tsv with the line they changed:
#
#   poison -> zeroinitializer    class 6, `insertelement`'s vector operand.
#   <n x i32> zeroinitializer    the `shufflevector` mask: a splat constant
#     -> <n x i32> <i32 0, ...>  written as the lane list the parser reads, the
#                                same value at the same lanes.
#
# Exit status: 0 when the five artefacts are written; 3 when an input is
# missing or the derivation cannot be attributed — the same code the rest of the
# route uses for an unusable input.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)

src=kernel/json/entry.c
symbols=(s1f_k_pos8 s1f_k_b8)
abi_names=(ent blk0 nblk out k)
fixture=$here/json-entry.candidate.ll
strip=$here/json-entry.strip.tsv
rewrites=$here/json-entry.rewrites.tsv
table=$here/json-entry.table.tsv
inventory=$here/json-entry.inventory

fail() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

# The attribution program, which is also the `--attribute` mode's detector:
# every differing line between a normalised emission and the text the capture
# emits must be a table `getelementptr` or the parameter list.  Rows go to
# stdout; an unattributable line goes to stderr and exits 3.
attribute_program() {
  cat <<'AWK'
BEGIN { rows = 0; bad = 0; nraw = 0 }
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
    # The parameter list: the rewritten header is the emitted header with the
    # table base appended when the body reads the table, and identical when it
    # does not — a body with no table read that took the parameter would be a
    # `define` of a different function on no evidence at all.
    key = "getelementptr inbounds [256 x [8 x i32]], ptr @xl_pos8, i64 0, i64 "
    ntab = 0
    for (ln = 2; ln <= nem; ln++)
        if (index(em[ln], key) > 0) ntab++
    want = em[1]
    if (ntab > 0) {
        if (!sub(/\)[ \t]*\{[ \t]*$/, ", ptr %tab) {", want)) {
            printf "SETUP: the function header '%s' is not a parameter list\n", em[1] > "/dev/stderr"
            exit 3
        }
    }
    if (ca[1] != want) {
        bad++
        if (ntab > 0)
            printf "SETUP: unattributed: the header changed beyond the appended %%tab\n" > "/dev/stderr"
        else
            printf "SETUP: unattributed: the header changed, and the body reads no table to take %%tab for\n" > "/dev/stderr"
        printf "SETUP:   emitted:  %s\n", em[1] > "/dev/stderr"
        printf "SETUP:   fixture:  %s\n", ca[1] > "/dev/stderr"
    }
    for (ln = 2; ln <= nem; ln++) {
        if (em[ln] == ca[ln]) continue
        i = index(em[ln], key)
        if (i == 0) {
            bad++
            printf "SETUP: unattributed: line %d differs and is not the table read\n", ln > "/dev/stderr"
            printf "SETUP:   emitted:  %s\n", em[ln] > "/dev/stderr"
            printf "SETUP:   fixture:  %s\n", ca[ln] > "/dev/stderr"
            continue
        }
        prefix = substr(em[ln], 1, i - 1)
        idx = substr(em[ln], i + length(key))
        if (idx !~ /^%[A-Za-z0-9._$-]+$/) {
            bad++
            printf "SETUP: unattributed: line %d's table GEP has no bare register index\n", ln > "/dev/stderr"
            continue
        }
        want = prefix "getelementptr inbounds <8 x i32>, ptr %tab, i64 " idx
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
          "the unit's table read: base @xl_pos8 becomes the caller's %tab, element type [256 x [8 x i32]] with two indices becomes the packed <8 x i32> with one, and both address base + 32 * idx"
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
    awk -f "$ws/attribute.awk" "$1" "$2" "$3" || rc=$?
  else
    awk -f "$ws/attribute.awk" "$1" "$2" || rc=$?
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
work=$(mktemp -d "$repo/.lake/tmp-entry-capture.XXXXXX" 2>/dev/null) ||
  work=$(mktemp -d) ||
  fail "cannot create a work directory"
trap 'rm -rf "$work"' EXIT

# --- the emission ---------------------------------------------------------

flags=(-S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11
       -falign-loops=64 -falign-functions=64)

# The source is named relative to the repository root, so `source_filename`
# in the emission does not carry a checkout path.  `entry.c` includes `entry.h`
# from its own directory, so the include path is the unit's.
compile() { ( cd "$repo" && clang -I kernel/json "$@" ); }

compile "${flags[@]}" "$src" -o "$work/plain.ll"
compile "${flags[@]}" -fno-discard-value-names "$src" -o "$work/named.ll"

# The naming flag's claim, checked: the same source, the same instructions.
# The flag also *labels* the blocks it emits (the unnamed emission numbers them,
# and writes the numbering as the label), while its `; preds` list is padded to
# the label's length — so a block-label line is dropped from both texts.  A
# label is not an instruction, and the `; preds` list after one carries no token
# the parser reads.
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

# The module with comments and blank lines dropped, and with each line cut at
# its comment: the parser's own tokenizer drops both (`tokenize` truncates at
# `;`, `tokenLines` filters empty lines), so a comment carries nothing and is
# not part of the diff.  Cutting inline comments here as well as whole-line
# ones is what makes each block a verbatim contiguous run of this text, so a
# row's `line` is a line of the emission and nothing needs renumbering.
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

# The `define` block of @<symbol>, verbatim, from a clang emission, as the pair
# of line numbers it occupies in the comment-free module.
block_range() { # <symbol> -> "start end"
  awk -v head='define ' -v sym="@$1(" '
    !inblock && index($0, head) == 1 && index($0, sym) { inblock = 1; start = NR }
    inblock && $0 == "}" { print start, NR; exit }
  ' "$work/module.ll"
}

# Every `define` block of the module, so the whole-line classifier skips the
# three functions the fixture does not hold (`leanllvm_json_entry_pos8`, `…_b8`
# and `…_table`, whose body carries the initialiser's own table walk).
all_block_ranges() {
  awk '
    inblock && $0 == "}" { print start, NR; inblock = 0; next }
    !inblock && index($0, "define ") == 1 { inblock = 1; start = NR }
  ' "$work/module.ll"
}
all_block_ranges > "$work/allranges"
[ -s "$work/allranges" ] || fail "the emission holds no \`define\` block"

: > "$work/ranges"
for sym in "${symbols[@]}"; do
  range=$(block_range "$sym")
  [ -n "$range" ] || fail "the emission has no \`define\` block for @$sym"
  read -r start end <<< "$range"
  sed -n "${start},${end}p" "$work/module.ll" > "$work/block.$sym.ll"
  [ -s "$work/block.$sym.ll" ] || fail "the \`define\` block of @$sym is empty"
  printf '%s %s\n' "$start" "$end" >> "$work/ranges"
done

# The fixture's function order is the emission's, so a reordering cannot pass.
awk '{ if (NR > 1 && $1 <= prev) exit 1; prev = $2 }' "$work/ranges" ||
  fail "the emission's \`define\` blocks are not in the order the fixture holds them"

# --- the parameter names, and the ABI's spelling of them ------------------

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

: > "$work/rows.rename"
nrename=0
for sym in "${symbols[@]}"; do
  param_names "$sym" "$work/block.$sym.ll" > "$work/params.$sym" ||
    fail "cannot read the parameter list of @$sym in the emission"
  mapfile -t emitted_names < "$work/params.$sym"
  [ "${#emitted_names[@]}" -eq "${#abi_names[@]}" ] ||
    fail "@$sym has ${#emitted_names[@]} parameter(s); the ABI has ${#abi_names[@]}"

  rename_args=()
  for i in "${!abi_names[@]}"; do
    old=${emitted_names[$i]#%}
    new=${abi_names[$i]}
    [ "$old" = "$new" ] && continue
    rename_args+=(-e "s/%${old}([^A-Za-z0-9_.])/%${new}\1/g"
                  -e "s/%${old}\$/%${new}/")
    printf -- '-\trename\t%%%s\t%%%s\t1\t%s\n' "$old" "$new" \
      'parameter rename to the ABI'"'"'s spelling: a register name is not part of the computation, and the capture shows it so by emitting the source with and without -fno-discard-value-names and comparing the two texts with every register name replaced by one placeholder' \
      >> "$work/rows.rename"
    nrename=$((nrename + 1))
  done
  if [ "${#rename_args[@]}" -gt 0 ]; then
    sed -E "${rename_args[@]}" "$work/block.$sym.ll" > "$work/renamed.$sym.ll"
    for i in "${!abi_names[@]}"; do
      old=${emitted_names[$i]#%}
      [ "$old" = "${abi_names[$i]}" ] && continue
      if grep -q "%${old}\([^A-Za-z0-9_.]\|\$\)" "$work/renamed.$sym.ll"; then
        fail "the parameter rename left %${old} in @$sym"
      fi
    done
  else
    cp "$work/block.$sym.ll" "$work/renamed.$sym.ll"
  fi
done

# --- the value substitutions ---------------------------------------------

# A splat vector constant as the lane list the parser reads: `<n x i32>
# zeroinitializer` is the `n`-lane zero vector, and the lane count is read from
# the mask's own type rather than assumed.  One row per application, keyed by
# the line it changed.
: > "$work/rows.splat"
expand_splats() { # <file> <splatfile>
  awk -v splatfile="$2" '
    BEGIN { OFS = "\t" }
    {
      line = $0
      if (line ~ /shufflevector/) {
        last = 0
        for (i = length(line) - 2; i >= 1; i--)
          if (substr(line, i, 3) == ", <") { last = i; break }
        if (last > 0) {
          suffix = substr(line, last + 2)
          if (suffix ~ /^<[0-9]+ x i32> zeroinitializer$/) {
            open = index(suffix, ">")
            split(substr(suffix, 2, open - 2), w, " x ")
            n = w[1] + 0
            lanes = ""
            for (k = 1; k <= n; k++)
              lanes = lanes (k > 1 ? ", " : "") "i32 0"
            want = substr(suffix, 1, open) " <" lanes ">"
            line = substr(line, 1, last + 1) want
            printf "%d\t%s\t%s\n", NR, suffix, want >> splatfile
          }
        }
      }
      print line
    }
  ' "$1"
}

for sym in "${symbols[@]}"; do
  expand_splats "$work/renamed.$sym.ll" "$work/rows.splat" > "$work/emit.$sym.ll"
done

# --- the normalisation ----------------------------------------------------

# Header rules: the function-header surface, the parameter attributes and
# `initializes`, each a class of its own (2, 1 and 7).
normalise_header() {
  sed -E \
    -e 's/ noundef//g' \
    -e 's/ readonly//g' \
    -e 's/ writeonly//g' \
    -e 's/ captures\(none\)//g' \
    -e 's/ initializes\(\([^)]*\)\)//g' \
    -e 's/ unnamed_addr//g' \
    -e 's/ #[0-9]+//g' \
    -e 's/ align [0-9]+//g'
}

# Instruction rules: metadata (5), alignment (9), the constraining flags (4),
# call-argument and call-result attributes (1) — a call's `range(...)` and an
# operand's `range(...)` alike — and `poison` (6), whose removal leaves a
# defined lane in its place: the lane no observable reads.
normalise_body() {
  sed -E \
    -e 's/, !tbaa ![0-9]+//g' \
    -e 's/, !llvm\.loop ![0-9]+//g' \
    -e 's/, align [0-9]+//g' \
    -e 's/ nuw//g' \
    -e 's/ nsw//g' \
    -e 's/ nneg//g' \
    -e 's/ disjoint//g' \
    -e 's/ range\(i64 [^)]*\)//g' \
    -e 's/ range\(i32 [^)]*\)//g' \
    -e 's/insertelement <8 x i32> poison/insertelement <8 x i32> zeroinitializer/g' \
    -e 's/, <8 x i32> poison,/, <8 x i32> zeroinitializer,/g'
}

for sym in "${symbols[@]}"; do
  head -n 1 "$work/emit.$sym.ll" | normalise_header > "$work/body.$sym.ll"
  tail -n +2 "$work/emit.$sym.ll" | normalise_body >> "$work/body.$sym.ll"
  nemit=$(wc -l < "$work/emit.$sym.ll")
  nbody=$(wc -l < "$work/body.$sym.ll")
  [ "$nemit" -eq "$nbody" ] ||
    fail "the normalisation of @$sym changed the line count ($nemit -> $nbody); it removes tokens, not lines"
done

# --- the strip inventory: each block diffed against what it emits ---------

cat > "$work/classify.awk" <<'AWK'
BEGIN {
    seps = " \t,()<>{}"
    c1word["noundef"] = 1; c1word["readonly"] = 1; c1word["writeonly"] = 1
    c1word["immarg"] = 1
    c1paren["captures"] = 1; c1paren["range"] = 1
    c2word["local_unnamed_addr"] = 1; c2word["unnamed_addr"] = 1
    c4word["nuw"] = 1; c4word["nsw"] = 1; c4word["nusw"] = 1
    c4word["disjoint"] = 1; c4word["nneg"] = 1
    c7paren["initializes"] = 1
    subst["poison" SUBSEP "zeroinitializer"] = 6
    subst["poison" SUBSEP "0"] = 6
    reason[1] = "argument, parameter and call-result attributes: a promise about an argument or a result, re-established by the theorem's hypotheses; a call's or an operand's range is restated by the model's own definition"
    reason[2] = "function-header surface: linkage and code placement, which the model has no semantics for; the Calls environment decides which definition answers"
    reason[3] = "attribute-group definition: the target-feature and memory promise its references carry, recorded in PROVENANCE.md"
    reason[4] = "instruction flag that constrains: it excludes inputs, so stripping widens, and the widening is recorded rather than re-established"
    reason[5] = "memory and analysis metadata: the model has no aliasing relation and no loop model to read it with"
    reason[6] = "poison as a value: no observable reads the lane, so a defined lane stands in"
    reason[7] = "initializes((0, 48)): a promise about which slot bytes are written; the theorem's memory clause is stronger for the bytes it covers"
    reason[8] = "module configuration and module-level symbols: not read by the parser; the configuration is recorded in the fixture's provenance comment and in PROVENANCE.md, and the table becomes the %tab parameter (json-entry.table.tsv)"
    reason[9] = "instruction-level alignment: the parser's load and store have no alignment field, and the model addresses bytes"
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
    return 0
}

# Attribute the run ca..cb to classes, in class order, by consecutive prefixes.
function flush(   k, c, e, hit) {
    if (ca == 0) return
    k = ca
    while (k <= cb) {
        hit = 0
        for (c = 1; c <= 9; c++) {
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

# Each block's offset inside the comment-free module, so every row's `line` is
# a line of the emission.
nsubst_total=0
: > "$work/rows.strip"
ln=0
while read -r start end; do
  ln=$((ln + 1))
  sym=${symbols[$((ln - 1))]}
  ofs=$((start - 1))
  awk -v nsubstfile="$work/nsubst.$sym" -v ofs="$ofs" -f "$work/classify.awk" \
    "$work/emit.$sym.ll" "$work/body.$sym.ll" > "$work/rows.$sym" ||
    fail "the removal in @$sym could not be attributed to classes (see above)"
  awk -F'\t' '$2 == "substituted"' "$work/rows.$sym" >> "$work/rows.subst"
  awk -F'\t' '$2 != "substituted"' "$work/rows.$sym" >> "$work/rows.strip"
  n=$(cat "$work/nsubst.$sym" 2>/dev/null || printf '0')
  nsubst_total=$((nsubst_total + n))
done < "$work/ranges"

# --- the whole-line removals: what the module carries and the fixture does not

# The block ranges, so a whole-line row never names a line inside a function.
cp "$work/allranges" "$work/blockranges"

classify_lines() {
  awk -v ranges="$work/blockranges" '
    BEGIN {
      reason[3] = "attribute-group definition: the target-feature and memory promise its references carry, recorded in PROVENANCE.md"
      reason[5] = "memory and analysis metadata: the model has no aliasing relation and no loop model to read it with"
      reason[8] = "module configuration and module-level symbols: not read by the parser; the configuration is recorded in the fixture'"'"'s provenance comment and in PROVENANCE.md, and the table becomes the %tab parameter (json-entry.table.tsv)"
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
      else if (substr($1, 1, 1) == "@") c = 8
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

# --- the table rewrite: computed from the difference, per site -------------

: > "$work/table.rows"

# The fixture body is the normalised body with the table read rewritten.  The
# rows come from `attribute`, which diffs the two texts it is given, so the set
# is the difference and not a list kept here.
for sym in "${symbols[@]}"; do
  awk '
    BEGIN { OFS = "" }
    {
      line = $0
      key = "getelementptr inbounds [256 x [8 x i32]], ptr @xl_pos8, i64 0, i64 "
      i = index(line, key)
      if (i > 0) {
        pre = substr(line, 1, i - 1)
        idx = substr(line, i + length(key))
        if (idx ~ /^%[A-Za-z0-9._$-]+$/) {
          line = pre "getelementptr inbounds <8 x i32>, ptr %tab, i64 " idx
          ntab++
        }
      }
      body[NR] = line
      n = NR
    }
    END {
      # The parameter list gains the table base, and only the body that reads the
      # table takes it: the other kernel reads no table, so its parameter list is
      # the emission form unchanged.
      if (ntab > 0) sub(/\)[ \t]*\{[ \t]*$/, ", ptr %tab) {", body[1])
      for (k = 1; k <= n; k++) print body[k]
    }
  ' "$work/body.$sym.ll" > "$work/fixture-body.$sym.ll"

  attribute "$work/body.$sym.ll" "$work/fixture-body.$sym.ll" "$work/emit.$sym.ll" \
    > "$work/table.$sym" ||
    fail "the table rewrite of @$sym could not be attributed (see above)"
  cat "$work/table.$sym" >> "$work/table.rows"

  # The parameter and the reads stand or fall together: a function that reads
  # the table takes `%tab`, and one that does not has no `%tab` at all.
  if grep -q 'ptr @xl_pos8' "$work/emit.$sym.ll"; then
    if ! grep -q 'ptr %tab' "$work/fixture-body.$sym.ll"; then
      fail "@$sym reads the table but its fixture reads no %tab"
    fi
  else
    if grep -q 'ptr %tab' "$work/fixture-body.$sym.ll"; then
      fail "@$sym reads no table but its fixture takes a %tab parameter"
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
    /^target triple/ { printf "%s\n", $0; next }
    /^target datalayout/ { printf "%s\n", $0; next }
  ' "$1"
}
module_config "$work/module.ll" > "$work/config.txt"

{
  cat <<'PROVENANCE'
; The entry unit as emitted, in the fragment the parser reads: the two position
; emitters @s1f_k_pos8 and @s1f_k_b8, in the emission's order.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-entry.sh
;
; from kernel/json/entry.c, emitted with the measured compiler line
;
;   clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
;         -falign-loops=64 -falign-functions=64 -fno-discard-value-names
;
; and reduced to those two `define` blocks.  `-fno-discard-value-names` is a
; naming flag: it names values and labels the entry block, which the parser
; requires, and the capture checks that it changes no instruction by emitting
; the source with and without it and comparing the two texts with every
; register name replaced by one placeholder.
;
; The emission's five parameters are the ABI's own names (%ent, %blk0, %nblk,
; %out, %k), so the capture renames none; it refuses an emission whose parameter
; count is not five.  The POS8 `define` below therefore has six: the table base
; the rewrite appends.
;
; The table read is rewritten, because the fragment has no module-level
; globals.  Each
;
;   getelementptr inbounds nuw [256 x [8 x i32]], ptr @xl_pos8, i64 0, i64 %idx
;
; becomes
;
;   getelementptr inbounds <8 x i32>, ptr %tab, i64 %idx
;
; and %tab is appended to the parameter list.  Three operand differences and one
; equation: the base becomes the caller's; the element type becomes the packed
; <8 x i32>, which is 32 bytes, the stride the emitted aggregate computes; the
; two indices become one, the aggregate row the base absorbs.  The emitted form
; addresses @xl_pos8 + 0 * (256 * 32) + idx * 32 and the rewritten form
; %tab + idx * 32, so the offset from the base is 32 * idx on both sides and
; only the base differs.  `nuw` is class 4's removal, so it is gone before the
; rewrite.  Each site is recorded in json-entry.table.tsv.
;
; Removed from the emission, each item with its class and the class's reason, in
; json-entry.strip.tsv; rewritten rather than removed — the `poison` lanes and
; the `shufflevector` masks written as lane lists — in json-entry.rewrites.tsv.
; The lines removed from the module carried:
PROVENANCE
  sed -e 's/^/;   /' "$work/config.txt"
  cat <<'PROVENANCE'
;   (the attribute groups, source_filename, the unit's two statics and the module
;   metadata nodes are recorded in json-entry.strip.tsv, where they are removed)
;
; The fixture's own opcodes and call targets are in json-entry.inventory.
PROVENANCE
  for sym in "${symbols[@]}"; do
    cat "$work/fixture-body.$sym.ll"
  done
} > "$work/fixture.ll"

inventory_of "$work/fixture.ll" > "$work/inventory.txt"

if grep -v '^;' "$work/fixture.ll" | grep -q '@xl_pos8'; then
  fail "the fixture still names @xl_pos8; the table read was not rewritten"
fi

# --- the inventories ------------------------------------------------------

{
  cat <<'LEGEND'
# json-entry.strip.tsv -- generated by
# probes/install/ir/capture-entry.sh; do not edit.
#
# What the normalisation took out of the clang emission of
# kernel/json/entry.c, by class.  Each row is one removed item: a token or
# contiguous run of tokens inside a `define` block, or a whole line.
# `line` is the line of the emission the item came from (the module as emitted,
# comment and blank lines dropped, so the two blocks' lines are numbered in one
# sequence and a row can be found in the emission).
#
# What the normalisation *rewrote* rather than removed — the `poison` lanes and
# the `shufflevector` masks — is in json-entry.rewrites.tsv, with its own
# reason; the table read's rewrite is in json-entry.table.tsv.
#
# The nine classes, each with the reason the removal is sound:
#
#   1  argument, parameter and call-result attributes
#   2  function-header surface
#   3  attribute-group definitions
#   4  instruction flags that constrain (nuw, nsw, nneg, disjoint: stripping
#      widens; recorded, not re-established)
#   5  memory and analysis metadata
#   6  poison as a value (no observable reads the lane).  Its instances are
#      rewrites, so the rows are in json-entry.rewrites.tsv
#   7  initializes((0, 48)) (the theorem's memory clause is stronger)
#   8  module configuration and module-level symbols (the configuration is
#      recorded in the fixture's provenance comment and in PROVENANCE.md; the
#      table becomes the %tab parameter)
#   9  instruction-level alignment (the parser's load and store have no
#      alignment field)
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
# json-entry.rewrites.tsv -- generated by
# probes/install/ir/capture-entry.sh; do not edit.
#
# Every place the normalisation *rewrote* text of the clang emission of
# kernel/json/entry.c instead of removing it, with the reason the rewrite is
# sound.  Three kinds:
#
#   rename      a register renamed.  The five parameters are written %ent,
#               %blk0, %nblk, %out and %k, which are the ABI's names, so this
#               unit's capture performs no rename and the kind has no row here.
#               The machinery is kept and the names are read from the emission;
#               a row appearing that the ABI did not call for is a diff.
#   substitute  a token replaced by a defined one.  `poison`, class 6 of the
#               normalisation's classes: `insertelement`'s vector operand and
#               the second `shufflevector` operand, whose lane no observable
#               reads (the insert writes lane 0 and every mask entry selects
#               lane 0 of the first operand).
#   splat       a splat vector constant written as its lane list.  The
#               `shufflevector` mask is emitted as `<8 x i32> zeroinitializer`
#               and the parser reads a mask as a lane list, so the same value is
#               written lane by lane; the `from` column is the emitted spelling
#               and the `to` column the one the fixture holds.
#
# A rewrite with no row here stops the capture: the alignment refuses any token
# the body adds that is not one of the substitutions declared here, every
# applied splat has its own row, and this file must account for every
# substitution the alignment made.  `line` is the line of the emission, as in
# the strip inventory.
LEGEND
  printf 'class\tkind\tfrom\tto\tline\treason\n'
  {
    cat "$work/rows.rename"
    awk -F'\t' -v r='poison replaced by a defined lane: no observable reads the lane, so the text stands a value the model represents in its place' \
      'BEGIN { OFS = "\t" } { print $1, $2, $3, $4, $5, r }' "$work/rows.subst"
    awk -F'\t' -v r='splat vector constant written as its lane list: `<n x i32> zeroinitializer` is the n-lane zero vector, and the parser reads a shufflevector mask as a lane list, so the same value is written lane by lane' \
      'BEGIN { OFS = "\t" } NF >= 3 { print 6, "splat", $2, $3, $1, r }' "$work/rows.splat"
  } | LC_ALL=C sort -t "$(printf '\t')" -k2,2 -k1,1n -k5,5n -s
} > "$work/rewrites.tsv"

{
  cat <<'LEGEND'
# json-entry.table.tsv -- generated by
# probes/install/ir/capture-entry.sh; do not edit.
#
# The table read, per site: the GEP the emission wrote and the GEP the fixture
# holds.  The fragment has no module-level globals, so the unit's table cannot
# be one; the base becomes a parameter.
#
#   emitted    @xl_pos8 + 0 * (256 * 32) + idx * 32   an aggregate base, two
#              indices, and the row's own stride of 32 bytes
#   rewritten  %tab     + idx * 32                    the caller's base, one
#              index, a packed <8 x i32> element type of 32 bytes
#
# The offset from the base is 32 * idx on both sides for every index, so the
# differences are a base, an element type and an index arity, and nothing about
# the address.  `nuw` is class 4's removal and is gone before the rewrite; it is
# recorded in json-entry.strip.tsv.
#
# The rows are computed: the capture diffs its normalised emission against the
# text it emits, and a differing line that is neither one of these GEPs nor the
# parameter list stops it with exit 3.  The parameter list differs by the
# appended `%tab` and by nothing else.
LEGEND
  printf 'kind\temitted\trewritten\tline\treason\n'
  LC_ALL=C sort -t "$(printf '\t')" -k4,4n -s "$work/table.rows"
} > "$work/table.tsv"

# --- the derivation's own accounting -------------------------------------

if awk -F'\t' '/^#/ || $1 == "class" { next } NF < 6 || $6 == ""' "$work/rewrites.tsv" |
     grep -q .; then
  fail "a rewrite in the fixture has no recorded reason"
fi
[ "$(grep -c '	substituted	' "$work/rewrites.tsv" || true)" -eq "$nsubst_total" ] ||
  fail "the rewrite inventory accounts for $(grep -c '	substituted	' "$work/rewrites.tsv" || true) substitution(s); the alignment made $nsubst_total"
[ "$(grep -c '	rename	' "$work/rewrites.tsv" || true)" -eq "$nrename" ] ||
  fail "the rewrite inventory accounts for $(grep -c '	rename	' "$work/rewrites.tsv" || true) rename(s); $nrename were applied"
nsplat=$(grep -c '	splat	' "$work/rewrites.tsv" || true)
nshine=$(grep -v '^;' "$work/fixture.ll" | grep -c 'shufflevector' || true)
[ "$nsplat" -eq "$nshine" ] ||
  fail "the rewrite inventory accounts for $nsplat splat(s); the fixture holds $nshine shufflevector(s)"
ngep=$(cat "$work"/emit.*.ll | grep -c 'getelementptr inbounds \[256 x \[8 x i32\]\], ptr @xl_pos8, i64 0, i64' || true)
[ "$(grep -c '	gep	' "$work/table.tsv" || true)" -eq "$ngep" ] ||
  fail "the table inventory accounts for $(grep -c '	gep	' "$work/table.tsv" || true) GEP(s); the emission's two blocks have $ngep"

# --- write the five artefacts, together ----------------------------------

grep -q '^opcode ' "$work/inventory.txt" || fail "the fixture inventory names no opcode"
grep -q '^call @' "$work/inventory.txt" || fail "the fixture inventory names no call target"

cp "$work/fixture.ll" "$fixture"
cp "$work/strip.tsv" "$strip"
cp "$work/rewrites.tsv" "$rewrites"
cp "$work/table.tsv" "$table"
cp "$work/inventory.txt" "$inventory"

printf 'capture-entry: wrote probes/install/ir/json-entry.candidate.ll (%s line(s), %s function(s))\n' \
  "$(wc -l < "$work/fixture.ll")" "$(grep -c '^define ' "$work/fixture.ll")"
printf 'capture-entry: wrote probes/install/ir/json-entry.strip.tsv (%s row(s))\n' \
  "$(awk -F'\t' 'NF >= 6 && $1 ~ /^[0-9]+$/' "$work/strip.tsv" | wc -l)"
printf 'capture-entry: wrote probes/install/ir/json-entry.rewrites.tsv (%s row(s))\n' \
  "$(awk -F'\t' '$2 != "" && $1 != "class"' "$work/rewrites.tsv" | wc -l)"
printf 'capture-entry: wrote probes/install/ir/json-entry.table.tsv (%s row(s))\n' \
  "$(awk -F'\t' '$1 == "gep"' "$work/table.tsv" | wc -l)"
printf 'capture-entry: wrote probes/install/ir/json-entry.inventory (%s line(s))\n' \
  "$(wc -l < "$work/inventory.txt")"
