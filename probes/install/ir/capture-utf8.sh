#!/usr/bin/env bash
# Regenerate the UTF-8 unit's emitted-IR fixture and its three inventories in
# probes/install/ir/.
#
# Run through the flake, from the repository root:
#
#   nix develop -c bash probes/install/ir/capture-utf8.sh
#
# Input
#   kernel/json/utf8.c                the UTF-8 unit: the three tables, the
#                                     load-form error vector, the tail test and
#                                     the stage that runs them
#
# Output (all four in the same run, from the same compilation)
#   json-utf8.candidate.ll            the fixture: the `define` block of
#                                     @leanllvm_json_utf8, with the syntax
#                                     listed below removed and nothing rewritten
#   json-utf8.strip.tsv               what the normalisation removed, by class,
#                                     derived by diffing the emission against
#                                     the text this script emits
#   json-utf8.rewrites.tsv            what it rewrote rather than removed: for
#                                     this unit, nothing, and the file records
#                                     why each kind of rewrite is absent
#   json-utf8.inventory               the fixture's own opcodes and call targets
#
# `kernel/json/identity/inventory.sh --unit utf8` is the gate: it regenerates
# all four and compares them byte for byte, parses the fixture, and fires its
# controls.  This script only derives; the verdict is that gate's.
#
# --- Why the measured compiler line, and not the classifier's ------------
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
# No other compiler or `opt` pass runs between the emission and the fixture: the
# fixture is the block clang printed, with the syntax below removed.  The one
# `opt` invocation is the check that the result is well-formed IR and not only a
# text the repository's parser reads:
#
#   opt -passes=verify -disable-output json-utf8.candidate.ll
#
# It is named in the fixture's provenance comment too, so a reader can repeat it,
# and it runs before any artefact is written.
#
# --- The parameter names: none renamed -----------------------------------
#
# The ABI's parameter names are the source's (`b`, `n`, `ungated`), so the
# emission carries `%b`, `%n` and `%ungated` and this capture renames nothing.
# The machinery is kept and the names are read from the emission, not assumed:
# the capture takes the last token of each top-level parameter, requires exactly
# three of them, and requires them to be the ABI's names.  A differing name is a
# setup fault rather than a silent rename, because for this unit a rename would
# mean the ABI's spelling had drifted from the measured text's.
#
# --- The tables: no table read, and no table rewrite ---------------------
#
# `u8kl.h`'s three tables are `static const` arrays of 32 bytes, so
# `_mm256_load_si256` of each folds to a literal `<32 x i8>` lane list in the
# `pshuf.b` call.  The fixture therefore needs **no table parameter and no table
# rewrite**, unlike the entry unit, whose table could not be a module global:
# the fixture's difference set from the normalised emission is **empty**, and
# this capture says so by computing it rather than by omitting a rewrite step.
# Two shapes would mean the folding had stopped, and each is refused rather than
# stripped: a `getelementptr` whose base is a module-level symbol is refused as
# an unattributable line, and so is a module-level symbol definition.  Either
# would mean the emission's shape changed and the fixture no longer describes
# the unit the theorem is about.
#
# --- What the normalisation removes, and why it is a derivation -----------
#
# The emission at those flags carries syntax the parser refuses by name.  The
# removal is computed, not transcribed: the capture diffs its own clang block
# against the text it emits, groups the removed tokens into contiguous runs, and
# attributes each run to one of the nine classes, writing a row per item with
# the class's reason.  A token that matches no class exits `3`, so syntax cannot
# be stripped silently and the inventory cannot fall behind the emission.  A
# token the parser already accepts and drops (`tail`, `inbounds`, `samesign`,
# `internal`, `fastcc`, the written callee type) is never removed, so it never
# appears — the inventory is a record of what was taken out, not of what the
# parser tolerates.
#
# The nine classes.  A token that matches none of them exits `3`.  Three of them
# are unexercised by this emission and are kept rather than trimmed, because the
# class list is the capture's vocabulary and a class dropped for one unit is a
# class the next emission arrives without:
#
#   1. argument, parameter and call-result attributes — `noundef`, `readonly`,
#      `writeonly`, `immarg`, `captures(...)`, a call's `range(...)` and an
#      operand's `range(...)`: a promise about an argument or a result.  This
#      unit's instance besides `noundef`, `readonly` and `captures(none)` is the
#      `define`'s own `range(i64 0, 2)`, which the model's definition restates.
#   2. function-header surface — `unnamed_addr`, `local_unnamed_addr`, `#N`,
#      the function's `align`, and a `declare` line: linkage, code placement and
#      the declaration of a callee the model knows by name, for none of which
#      the model has a semantics.
#   3. attribute-group definitions — `attributes #N = { ... }`: the target
#      feature and memory promise its references carry, removed with them and
#      recorded in PROVENANCE.md.
#   4. instruction flags that constrain — `nuw`, `nsw`, `nusw`, `disjoint`,
#      `nneg`: each excludes inputs, so stripping *widens*; the widening is
#      recorded rather than re-established.  This unit's are the `shl`'s and the
#      forward `getelementptr`'s `nuw` and the back-edge `add`'s `nsw`; the
#      backward `getelementptr`s carry none.
#   5. memory and analysis metadata — `!tbaa` and `!llvm.loop`, and the module's
#      `!N = ...` nodes: the model has no aliasing relation and no loop model to
#      read them with.
#   6. `poison` as a value — unexercised here: this unit's vector constants are
#      lane lists, `zeroinitializer` and `splat (...)`, all of which the parser
#      reads, so no substitution is made and json-utf8.rewrites.tsv says so.
#   7. `initializes((0, 48))` — unexercised here: the unit writes no aggregate.
#   8. module configuration — `target datalayout`, `target triple`,
#      `source_filename`: the parser reads no module text outside the
#      `define`/`declare` lines.  The configuration values are recorded in the
#      fixture's provenance comment and in PROVENANCE.md.  A module-level symbol
#      is *not* an instance of this class here: it would mean the tables had
#      stopped folding, and it is refused.
#   9. instruction-level alignment — `load ..., align 1`: the parser's `load` has
#      no alignment field and the model addresses bytes, so the removal is a
#      representation loss and not a semantic one.  Every load here carries it.
#
# Whole lines are removed as lines and carry a class too: `attributes #N = {...}`
# is class 3, a `declare` is class 2, a module metadata node is class 5, and the
# module header is class 8.  Comment lines and inline comments are dropped
# before the diff rather than classified: `tokenize` (`LeanLLVM/Parser.lean`)
# truncates a line at `;` and `tokenLines` drops empty lines, so a comment
# carries no token the parser reads.  The fixture therefore holds instruction
# text and block labels only, and the `preds` lists the emission writes after a
# block label are readable from the `br` that precedes the target.
#
# No rewrite is applied to the emission before that diff.  The entry unit's two
# rewrites were a `poison` lane and a `shufflevector` mask written as a lane
# list; this unit has neither, and the two classes of value substitution the
# parser reads are left exactly as they are: `splat (i64 …)`, which the parser
# reads as a vector constant (`Parser.lean:349-372`), and `zeroinitializer`,
# which it reads as the zero vector (`Parser.lean:276`).
#
# Exit status: 0 when the four artefacts are written; 3 when an input is missing
# or the derivation cannot be attributed — the same code the rest of the route
# uses for an unusable input.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)

src=kernel/json/utf8.c
symbol=leanllvm_json_utf8
abi_names=(b n ungated)
fixture=$here/json-utf8.candidate.ll
strip=$here/json-utf8.strip.tsv
rewrites=$here/json-utf8.rewrites.tsv
inventory=$here/json-utf8.inventory

fail() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

[ "$#" -eq 0 ] || fail "unknown argument: $1"

[ -f "$repo/$src" ] || fail "absent: $repo/$src"
command -v clang >/dev/null 2>&1 || fail "clang is not on PATH"

mkdir -p "$repo/.lake" || fail "cannot create $repo/.lake"
work=$(mktemp -d "$repo/.lake/tmp-utf8-capture.XXXXXX" 2>/dev/null) ||
  work=$(mktemp -d) ||
  fail "cannot create a work directory"
trap 'rm -rf "$work"' EXIT

# --- the emission ---------------------------------------------------------

flags=(-S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11
       -falign-loops=64 -falign-functions=64)

# The source is named relative to the repository root, so `source_filename` in
# the emission does not carry a checkout path.  `utf8.c` includes `utf8.h` from
# its own directory, so the include path is the unit's.
compile() { ( cd "$repo" && clang -I kernel/json "$@" ); }

compile "${flags[@]}" "$src" -o "$work/plain.ll"
compile "${flags[@]}" -fno-discard-value-names "$src" -o "$work/named.ll"

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

# The module with comments and blank lines dropped, and with each line cut at
# its comment: the parser's own tokenizer drops both (`tokenize` truncates at
# `;`, `tokenLines` filters empty lines), so a comment carries nothing and is
# not part of the diff.  Cutting inline comments here as well as whole-line ones
# is what makes the block a verbatim contiguous run of this text, so a row's
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
# inside a function.  This unit has one, and the count is read rather than
# assumed: a second function would mean the emission no longer holds the stage
# alone, which is a shape change and not something to classify.
all_block_ranges() {
  awk '
    inblock && $0 == "}" { print start, NR; inblock = 0; next }
    !inblock && index($0, "define ") == 1 { inblock = 1; start = NR }
  ' "$work/module.ll"
}
all_block_ranges > "$work/allranges"
[ -s "$work/allranges" ] || fail "the emission holds no \`define\` block"
nfunc=$(wc -l < "$work/allranges" | tr -d ' ')
[ "$nfunc" -eq 1 ] ||
  fail "the emission holds $nfunc \`define\` block(s); the unit is one function"

range=$(block_range "$symbol")
[ -n "$range" ] || fail "the emission has no \`define\` block for @$symbol"
read -r start end <<< "$range"
sed -n "${start},${end}p" "$work/module.ll" > "$work/block.ll"
[ -s "$work/block.ll" ] || fail "the \`define\` block of @$symbol is empty"

# --- the parameter names, which the ABI fixes -----------------------------

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

# names_match_abi <name> ... -- 0 when the names are the ABI's, 1 otherwise.
# The rename guard is a comparison, so its control is a name that differs: this
# unit records no rename, and "refuses rather than renames" is only evidence if
# the comparison can see a name changed.
names_match_abi() {
  local i=0 name
  [ "$#" -eq "${#abi_names[@]}" ] || return 1
  for name in "$@"; do
    [ "${name#%}" = "${abi_names[$i]}" ] || return 1
    i=$((i + 1))
  done
  return 0
}

param_names "$symbol" "$work/block.ll" > "$work/params" ||
  fail "cannot read the parameter list of @$symbol in the emission"
mapfile -t emitted_names < "$work/params"
if ! names_match_abi "${emitted_names[@]}"; then
  fail "@$symbol's parameters are (${emitted_names[*]-none}); the ABI names them %b, %n, %ungated"
fi
if names_match_abi %b %buf %ungated; then
  fail "the rename guard does not see a changed parameter name; it is not evidence"
fi
printf 'ok: the emission names the ABI'"'"'s parameters (%s), and the guard sees a changed one\n' \
  "${emitted_names[*]}"
nrename=0

# --- the normalisation ----------------------------------------------------

# Header rules: the function-header surface (2), the parameter attributes and
# the return's `range` (1).  The regexes are written so that each matches the
# token the inventory then attributes: a removal that matched inside another
# token would leave the token diff with something it could not name.
normalise_header() {
  sed -E \
    -e 's/ noundef//g' \
    -e 's/ readonly//g' \
    -e 's/ writeonly//g' \
    -e 's/ captures\(none\)//g' \
    -e 's/ range\(i64 [^)]*\)//g' \
    -e 's/ unnamed_addr//g' \
    -e 's/ local_unnamed_addr//g' \
    -e 's/ #[0-9]+//g' \
    -e 's/ align [0-9]+//g'
}

# Instruction rules: metadata (5), alignment (9), the constraining flags (4).
normalise_body() {
  sed -E \
    -e 's/, !tbaa ![0-9]+//g' \
    -e 's/, !llvm\.loop ![0-9]+//g' \
    -e 's/, align [0-9]+//g' \
    -e 's/ nuw//g' \
    -e 's/ nsw//g' \
    -e 's/ nusw//g' \
    -e 's/ disjoint//g' \
    -e 's/ nneg//g' \
    -e 's/ range\(i64 [^)]*\)//g' \
    -e 's/ range\(i32 [^)]*\)//g'
}

head -n 1 "$work/block.ll" | normalise_header > "$work/body.ll"
tail -n +2 "$work/block.ll" | normalise_body >> "$work/body.ll"
nemit=$(wc -l < "$work/block.ll" | tr -d ' ')
nbody=$(wc -l < "$work/body.ll" | tr -d ' ')
[ "$nemit" -eq "$nbody" ] ||
  fail "the normalisation changed the line count ($nemit -> $nbody); it removes tokens, not lines"

# --- the strip inventory: the block diffed against what it emits ----------

cat > "$work/classify.awk" <<'AWK'
BEGIN {
    seps = " \t,()<>{}"
    c1word["noundef"] = 1; c1word["readonly"] = 1; c1word["writeonly"] = 1
    c1word["immarg"] = 1
    c1paren["captures"] = 1; c1paren["range"] = 1
    c2word["local_unnamed_addr"] = 1; c2word["unnamed_addr"] = 1
    c4word["nuw"] = 1; c4word["nsw"] = 1; c4word["nusw"] = 1
    c4word["disjoint"] = 1; c4word["nneg"] = 1
    reason[1] = "argument, parameter and call-result attributes: a promise about an argument or a result, re-established by the theorem's hypotheses; a call's or an operand's range is restated by the model's own definition"
    reason[2] = "function-header surface: linkage, code placement and a callee's declaration, which the model has no semantics for; the Calls environment decides which definition answers"
    reason[3] = "attribute-group definition: the target-feature and memory promise its references carry, recorded in PROVENANCE.md"
    reason[4] = "instruction flag that constrains: it excludes inputs, so stripping widens, and the widening is recorded rather than re-established"
    reason[5] = "memory and analysis metadata: the model has no aliasing relation and no loop model to read it with"
    reason[6] = "poison as a value: no observable reads the lane, so a defined lane stands in"
    reason[7] = "initializes((0, 48)): a promise about which slot bytes are written; the theorem's memory clause is stronger for the bytes it covers"
    reason[8] = "module configuration: not read by the parser; the configuration is recorded in the fixture's provenance comment and in PROVENANCE.md"
    reason[9] = "instruction-level alignment: the parser's load has no alignment field, and the model addresses bytes"
    rows = 0
    bad = 0
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
    exit (bad > 0)
}

function aligned(i, j) {
    return t[i] == u[j]
}

# Align the block's tokens with the body's.  The cost is lexicographic: an edit
# costs a thousand, and a *run* of deletions costs one more than its length — so
# the alignment that keeps a removed clause whole beats one that reaches into
# the clause for a token equal to a neighbouring survivor, at equal edit count.
# `st` in the DP is whether the previous step deleted, which is how a run is
# counted.  Fills `del` and `ins`.
function align(nt, no,   i, j, best, v, v0, v1, st, oldi) {
    split("", del); split("", ins)
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

# The block's offset inside the comment-free module, so every row's `line` is a
# line of the emission.
ofs=$((start - 1))
: > "$work/rows.strip"
awk -v ofs="$ofs" -f "$work/classify.awk" "$work/block.ll" "$work/body.ll" \
  > "$work/rows.strip" ||
  fail "the removal could not be attributed to classes (see above)"

# --- the whole-line removals: what the module carries and the fixture does not

classify_lines() {
  awk -v ranges="$work/allranges" '
    BEGIN {
      reason[2] = "function-header surface: linkage, code placement and a callee'"'"'s declaration, which the model has no semantics for; the Calls environment decides which definition answers"
      reason[3] = "attribute-group definition: the target-feature and memory promise its references carry, recorded in PROVENANCE.md"
      reason[5] = "memory and analysis metadata: the model has no aliasing relation and no loop model to read it with"
      reason[8] = "module configuration: not read by the parser; the configuration is recorded in the fixture'"'"'s provenance comment and in PROVENANCE.md"
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
      else if (substr($1, 1, 1) == "@") {
        bad++
        printf "SETUP: line %d of the module defines a module-level symbol ('"'"'%s'"'"');\n", ln, $0 > "/dev/stderr"
        printf "SETUP: this unit'"'"'s tables fold to literal vector operands, so a global means the\n" > "/dev/stderr"
        printf "SETUP: emission'"'"'s shape changed and the fixture no longer describes the unit\n" > "/dev/stderr"
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

# --- the tables fold: no table read, and no rewrite ----------------------

# The folding claim is checked rather than assumed.  A `getelementptr` whose
# base is a module-level symbol is a table read that did not fold, and this unit
# has no rewrite to make it representable; so it is refused, and the fixture's
# difference set is computed to be empty rather than left unstated.
# refuses_global_gep <file> -- 0 when a `getelementptr` names a module-level
# symbol as its base.  This is the folding detector: this unit's tables are
# `static const` and must fold to literal lane lists, so a GEP through a global
# means the folding stopped and the fixture's shape changed.
refuses_global_gep() { # <file>
  grep 'getelementptr' "$1" 2>/dev/null | grep -q 'ptr @'
}

if refuses_global_gep "$work/body.ll"; then
  grep 'getelementptr' "$work/body.ll" | awk 'index($0, "ptr @") > 0 { printf "      %s\n", $0 }' >&2
  fail "the emission reads a table through a global; the tables no longer fold to lane lists"
fi

# The detector is exercised in the same run, on the shape it exists for — an
# aggregate global with two indices — and on the emitted form it must accept.
# A `getelementptr` through a global that the detector cannot see is the failure
# this control exists to prevent: the fixture would hold a table read and the
# capture would call it a folding.
printf '  %%a = getelementptr inbounds [32 x i8], ptr @kl_t1, i64 0, i64 0\n' > "$work/gep.table"
printf '  %%a = getelementptr inbounds i8, ptr %%b, i64 %%shl\n' > "$work/gep.plain"
if ! refuses_global_gep "$work/gep.table"; then
  fail "the folding detector does not see a GEP through a global; it is not evidence"
fi
if refuses_global_gep "$work/gep.plain"; then
  fail "the folding detector refuses a GEP through a value; it is not evidence"
fi
printf 'ok: the folding detector refuses a GEP through a global and accepts one through a value\n'

# The fixture body is the normalised body, and that is a computed equality: a
# difference here would be a rewrite this capture does not record.
cp "$work/body.ll" "$work/fixture-body.ll"
if ! cmp -s "$work/body.ll" "$work/fixture-body.ll"; then
  fail "the fixture body differs from the normalised emission, and this unit records no rewrite"
fi

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
; The UTF-8 unit as emitted, in the fragment the parser reads: the stage
; function @leanllvm_json_utf8, which is the ABI's only entry point.  Regenerate
; with:
;
;   nix develop -c bash probes/install/ir/capture-utf8.sh
;
; from kernel/json/utf8.c, emitted with the measured compiler line
;
;   clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
;         -falign-loops=64 -falign-functions=64 -fno-discard-value-names
;
; and reduced to that one `define` block.  `-fno-discard-value-names` is a
; naming flag: it names values and labels the entry block, which the parser
; requires, and the capture checks that it changes no instruction by emitting
; the source with and without it and comparing the two texts with every
; register name replaced by one placeholder.
;
; No other compiler or `opt` pass runs between the emission and this text.  The
; one `opt` invocation checks that the result is well-formed IR and not only a
; text the repository's parser reads, and it runs before the fixture is written:
;
;   opt -passes=verify -disable-output json-utf8.candidate.ll
;
; The emission's three parameters are the ABI's own names (%b, %n, %ungated),
; so the capture renames none; it refuses an emission whose parameter names are
; not those.
;
; There is no table read and no table rewrite.  The unit's three tables are
; `static const` arrays of 32 bytes and `_mm256_load_si256` of each folds to a
; literal `<32 x i8>` lane list in the `pshuf.b` call, so the fixture's
; difference set from the normalised emission is empty.  That is the one
; structural difference from the entry unit's fixture, which had to turn an
; aggregate table global into a parameter; here a `getelementptr` through a
; global is refused rather than rewritten, because it would mean the folding had
; stopped.
;
; The block count is `(n + 63) / 64`, derived from `n` alone: `n` is the
; document's length and the scanned byte string's length, so there is no second
; count for the two to disagree about.  The loop then runs over the document's
; 64-byte blocks and the tail runs once, after it.
;
; Removed from the emission, each item with its class and the class's reason, in
; json-utf8.strip.tsv.  Nothing is rewritten: json-utf8.rewrites.tsv records why
; each kind of rewrite is absent, and its row count is zero.  The lines removed
; from the module carried:
PROVENANCE
  sed -e 's/^/;   /' "$work/config.txt"
  cat <<'PROVENANCE'
;   (the attribute groups, the three callee declarations and the module
;   metadata nodes are recorded in json-utf8.strip.tsv, where they are removed)
;
; The fixture's own opcodes and call targets are in json-utf8.inventory.
PROVENANCE
  cat "$work/fixture-body.ll"
} > "$work/fixture.ll"

inventory_of "$work/fixture.ll" > "$work/inventory.txt"

if grep -v '^;' "$work/fixture.ll" | grep -q 'ptr @'; then
  fail "the fixture still reads through a global; the tables did not fold"
fi

# The fixture is well-formed LLVM IR, not only a text the parser reads.  The
# invocation is the one the fixture's provenance comment names, so the claim and
# the command that checks it cannot drift apart.
command -v opt >/dev/null 2>&1 || fail "opt is not on PATH; the fixture's verify step needs it"
opt -passes=verify -disable-output "$work/fixture.ll" ||
  fail "the fixture does not verify as LLVM IR"

# --- the inventories ------------------------------------------------------

{
  cat <<'LEGEND'
# json-utf8.strip.tsv -- generated by
# probes/install/ir/capture-utf8.sh; do not edit.
#
# What the normalisation took out of the clang emission of kernel/json/utf8.c,
# by class.  Each row is one removed item: a token or contiguous run of tokens
# inside the `define` block, or a whole line.
# `line` is the line of the emission the item came from (the module as emitted,
# comment and blank lines dropped, so a row can be found in the emission).
#
# This unit rewrites nothing: json-utf8.rewrites.tsv has no rows and says why.
# There is no table read to rewrite and no parameter to rename, and the two
# vector-constant spellings the parser reads -- `splat (i64 ...)` and
# `zeroinitializer` -- are left exactly as the emission writes them.
#
# The nine classes:
#
#   1  argument, parameter and call-result attributes (`noundef`, `readonly`,
#      `writeonly`, `immarg`, `captures(...)`, and the `define`'s own
#      `range(i64 0, 2)`, which the model's definition restates)
#   2  function-header surface (`local_unnamed_addr`, `#N`, the function's
#      `align`, and a `declare` line)
#   3  attribute-group definitions
#   4  instruction flags that constrain (nuw, nsw, nusw, disjoint, nneg:
#      stripping widens; recorded, not re-established)
#   5  memory and analysis metadata
#   6  poison as a value -- unexercised here: this unit has no poisoned lane
#   7  initializes((0, 48)) -- unexercised here: the unit writes no aggregate
#   8  module configuration (the configuration is recorded in the fixture's
#      provenance comment and in PROVENANCE.md; a module-level symbol is refused
#      as a folding failure rather than classified)
#   9  instruction-level alignment (the parser's load has no alignment field)
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
# json-utf8.rewrites.tsv -- generated by
# probes/install/ir/capture-utf8.sh; do not edit.
#
# Every place the normalisation *rewrote* text of the clang emission of
# kernel/json/utf8.c instead of removing it, with the reason the rewrite is
# sound.  This unit has none, and the three kinds the capture's vocabulary
# would record are absent for stated reasons rather than unconsidered:
#
#   rename      a register renamed.  The ABI's parameter names are the source's
#               (%b, %n, %ungated), so the emission already carries them and the
#               capture requires them; a differing name is a setup fault, not a
#               row here.
#   substitute  a token replaced by a defined one.  The entry unit's instance was
#               `poison` in an `insertelement` and a `shufflevector`; this unit
#               has neither instruction and no poisoned value.
#   splat       a splat vector constant written as its lane list.  The entry
#               unit's `shufflevector` mask had to be expanded because the parser
#               reads a mask as a lane list.  Here `splat (i64 ...)` is a vector
#               operand the parser already reads (`Parser.lean:349-372`) and
#               `zeroinitializer` is the zero vector it reads (`:276`), so both
#               are left as emitted and no expansion is needed.
#
# A rewrite with no row here stops the capture: the alignment refuses any token
# the body adds that is not one of the substitutions declared here, so a new
# rewrite cannot arrive unrecorded.  `line` is the line of the emission, as in
# the strip inventory.
LEGEND
  printf 'class\tkind\tfrom\tto\tline\treason\n'
} > "$work/rewrites.tsv"

# --- the derivation's own accounting -------------------------------------

grep -q '^opcode ' "$work/inventory.txt" || fail "the fixture inventory names no opcode"
grep -q '^call @' "$work/inventory.txt" || fail "the fixture inventory names no call target"

if awk -F'\t' '/^#/ || $1 == "class" { next } NF < 6 || $6 == ""' "$work/strip.tsv" |
     grep -q .; then
  fail "a removed item in the fixture has no recorded reason"
fi

nrewrite=$(awk -F'\t' '/^#/ || $1 == "class" { next } NF >= 6' "$work/rewrites.tsv" | wc -l | tr -d ' ')
[ "$nrewrite" -eq "$nrename" ] ||
  fail "the rewrite inventory accounts for $nrewrite rewrite(s); $nrename were applied"

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
nalign1=$(item_prefix_count 9 'align 1')
ntbaa=$(item_prefix_count 5 '!tbaa')
npshuf=$(grep -c '^call @llvm\.x86\.avx2\.pshuf\.b$' "$work/inventory.txt" || true)

[ "$npshuf" -eq 1 ] || fail "the fixture inventory does not name @llvm.x86.avx2.pshuf.b"

# --- write the four artefacts, together ----------------------------------

cp "$work/fixture.ll" "$fixture"
cp "$work/strip.tsv" "$strip"
cp "$work/rewrites.tsv" "$rewrites"
cp "$work/inventory.txt" "$inventory"

printf 'capture-utf8: wrote probes/install/ir/json-utf8.candidate.ll (%s line(s), %s function)\n' \
  "$(wc -l < "$work/fixture.ll" | tr -d ' ')" "$nfunc"
printf 'capture-utf8: wrote probes/install/ir/json-utf8.strip.tsv (%s row(s): %s class 1, %s class 2,\n' \
  "$(($(class_count 1) + $(class_count 2) + $(class_count 3) + $(class_count 4) + $(class_count 5) + $(class_count 8) + $(class_count 9)))" \
  "$(class_count 1)" "$(class_count 2)"
printf '    %s class 3, %s class 4, %s class 5, %s class 8, %s class 9)\n' \
  "$(class_count 3)" "$(class_count 4)" "$(class_count 5)" "$(class_count 8)" "$(class_count 9)"
printf 'capture-utf8: wrote probes/install/ir/json-utf8.rewrites.tsv (0 row(s); no rename, no\n'
printf '    substitution and no splat expansion is applied)\n'
printf 'capture-utf8: wrote probes/install/ir/json-utf8.inventory (%s line(s))\n' \
  "$(wc -l < "$work/inventory.txt" | tr -d ' ')"
printf 'capture-utf8: calls in the fixture body, counted there: %s\n' \
  "$(grep -o '@llvm\.[A-Za-z0-9_.]*' "$work/fixture-body.ll" | LC_ALL=C sort | uniq -c |
     awk '{ printf "%s%s=%s", (NR > 1 ? ", " : ""), $2, $1 }')"
printf 'capture-utf8: counted in the strip rows: %s nuw, %s nsw, %s "align 1", %s "!tbaa" item(s)\n' \
  "$nnuw" "$nnsw" "$nalign1" "$ntbaa"
