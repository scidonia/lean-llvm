#!/usr/bin/env bash
# Regenerate the stage-1 classification mask unit's emitted-IR fixture and its
# three inventories in probes/install/ir/.
#
# Run through the flake, from the repository root:
#
#   nix develop -c bash probes/install/ir/capture-s1-masks.sh
#
# Input
#   kernel/json/s1_block.c            the mask unit, one public entry point
#
# Output (all four in the same run, from the same compilation)
#   json-s1-masks.candidate.ll        the fixture: the `define` block, with the
#                                     syntax listed below removed
#   json-s1-masks.strip.tsv           what the normalisation removed, by class,
#                                     derived by diffing the clang block against
#                                     the text this script emits
#   json-s1-masks.rewrites.tsv        what it rewrote rather than removed, with
#                                     the reason the rewrite is sound
#   json-s1-masks.inventory           the fixture's own opcodes and call targets
#
# `kernel/json/identity/inventory.sh` is the gate: it regenerates all four and
# compares them byte for byte, parses the fixture, and fires both of its
# controls.  This script only derives; the verdict is that gate's.
#
# --- Why the measured compiler line, and not the classifier's ------------
#
# The fixture is the emission the *measured* build compiled, not a portable
# re-phrasing of it: `kernel/json/bench/paired.sh` and the route's object arm
# compile the same C at the same flags, so the body the proof is about is the
# body the object runs.  The line is `build49.sh:17`'s:
#
#   clang -O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
#         -falign-functions=64
#
# `-fno-discard-value-names` is added to it.  It is a naming flag: it writes the
# source's value names and, because a named entry block is emitted with its
# label, it supplies the one block label the parser requires.  That it changes
# no instruction is checked here rather than asserted: the same source is
# emitted with and without the flag, every register name is replaced by one
# placeholder and label lines are dropped, and the two texts must be identical.
#
# --- The parameter names --------------------------------------------------
#
# The emission names the parameters after the source's (`%p`, `%carry`, `%out`).
# The ABI the theorem is stated over writes them `%p`, `%c`, `%o`, so the three
# parameter registers are renamed.  The names are read from the header, not
# assumed: the capture takes the last token of each top-level parameter, refuses
# anything but exactly three of them, and substitutes each one throughout the
# block under a token boundary.  A rename is a substitution, not a removal, and
# it is invisible to the strip inventory for the same reason: the renamed block
# is the *input* to the diff.
#
# --- What the normalisation removes, and why it is a derivation -----------
#
# The emission at those flags carries syntax the parser refuses by name.  The
# removal is computed, not transcribed: the capture diffs its own clang block
# against the text it emits, groups the removed tokens into contiguous runs, and
# attributes each run to one of nine classes, writing a row per item with the
# class's reason.  A token that matches no class exits `3`, so syntax cannot be
# stripped silently and the inventory cannot fall behind the emission.  A token
# the parser already accepts and drops (`tail`, `inbounds`, the written callee
# type, `samesign`) is never removed, so it never appears — the inventory is a
# record of what was taken out, not of what the parser tolerates.
#
# The nine classes.  A token that matches none of them exits `3`, so a class
# added for a new emission carries its reason with it instead of arriving as an
# edit to a token list:
#
#   1. argument, parameter and call-result attributes — `noundef`, `readonly`,
#      `writeonly`, `immarg`, `captures(...)`, a call's `range(...)`: a promise
#      about an argument or a result.  What the value is is re-established by
#      the theorem's hypotheses (64 readable bytes, the two slots disjoint), and
#      a call's `range` is implied by the model's own definition.
#   2. function-header surface — `local_unnamed_addr`, `#N`, the function's
#      `align`: linkage and code placement, for which the model has no
#      semantics; `Calls` decides which definition answers.
#   3. attribute-group definitions — `attributes #N = { ... }`: the target
#      feature and memory promise its references carry, removed with them and
#      recorded in PROVENANCE.md.
#   4. instruction flags that constrain — `nuw`, `nusw`, `disjoint`: each
#      excludes inputs, so stripping *widens*; the widening is recorded rather
#      than re-established.
#   5. memory and analysis metadata — `!tbaa`, `!alias.scope`, `!noalias` and
#      the module's `!N = ...` nodes: the model has no aliasing relation to read
#      them with.
#   6. `poison` as a value — no observable reads the lane (`pclmulqdq` at
#      immediate 0 uses lane 0 and the `extractelement ... 0` that follows reads
#      lane 0), so it is replaced by a defined lane rather than carried.
#   7. `initializes((0, 48))` — a promise about which bytes of the slot are
#      written; the theorem's memory clause is *stronger* for the bytes it
#      covers, so the item is subsumed rather than dropped.
#   8. module configuration — `target datalayout`, `target triple`,
#      `source_filename`: not read by the parser; the values are recorded in the
#      fixture's provenance comment and in PROVENANCE.md.
#   9. instruction-level alignment — `load ..., align 1` and `store ...,
#      align 8`: the parser's `load` and `store` have no alignment field, and
#      the model addresses bytes, so the removal is a representation loss and
#      not a semantic one.
#
# Whole lines are removed as lines and carry a class too: `declare` lines are
# class 2 (the fixture holds the `define` block only, and `Calls` decides which
# definition answers), `attributes #N = { ... }` is class 3, the module header is
# class 8, and a module metadata node is class 5.  Comment and blank lines are
# dropped before the diff rather than classified: `tokenize`
# (`LeanLLVM/Parser.lean`) truncates a line at `;` and `tokenLines` drops empty
# lines, so a comment carries no token the parser reads.
#
# Exit status: 0 when the four artefacts are written; 3 when an input is
# missing or the derivation cannot be attributed — the same code the rest of the
# route uses for an unusable input.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)

src=kernel/json/s1_block.c
symbol=leanllvm_json_s1_masks
fixture=$here/json-s1-masks.candidate.ll
strip=$here/json-s1-masks.strip.tsv
inventory=$here/json-s1-masks.inventory
rewrites=$here/json-s1-masks.rewrites.tsv

fail() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

[ -f "$repo/$src" ] || fail "absent: $repo/$src"
command -v clang >/dev/null 2>&1 || fail "clang is not on PATH"

work=$(mktemp -d "$repo/.lake/tmp-s1-capture.XXXXXX" 2>/dev/null) ||
  work=$(mktemp -d) ||
  fail "cannot create a work directory"
trap 'rm -rf "$work"' EXIT

# --- the emission ---------------------------------------------------------

flags=(-S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11
       -falign-loops=64 -falign-functions=64)

# The source is named relative to the repository root, so `source_filename`
# in the emission does not carry a checkout path.
compile() { ( cd "$repo" && clang "$@" ); }

compile "${flags[@]}" "$src" -o "$work/plain.ll"
compile "${flags[@]}" -fno-discard-value-names "$src" -o "$work/named.ll"

# The naming flag's claim, checked: the same source, the same instructions.
neutralise() {
  sed -E -e 's/%[A-Za-z0-9._$-]+/%N/g' -e '/^[A-Za-z_][A-Za-z0-9_.]*:$/d' "$1"
}
neutralise "$work/plain.ll" > "$work/plain.norm.ll"
neutralise "$work/named.ll" > "$work/named.norm.ll"
if ! cmp -s "$work/plain.norm.ll" "$work/named.norm.ll"; then
  diff -u "$work/plain.norm.ll" "$work/named.norm.ll" | awk 'NR <= 40' >&2
  fail "-fno-discard-value-names changed the emission beyond register names"
fi

# The `define` block of @<symbol>, verbatim, from a clang emission.
extract_block() {
  awk -v head='define ' -v sym="@$symbol(" '
    index($0, head) == 1 && index($0, sym) {
      found = 1
      p = 1
    }
    p { print }
    p && $0 == "}" { exit }
    END { if (!found) exit 1 }
  ' "$1"
}

extract_block "$work/named.ll" > "$work/block.raw.ll" ||
  fail "the emission has no \`define\` block for @$symbol"
[ -s "$work/block.raw.ll" ] || fail "the \`define\` block of @$symbol is empty"

# The module without comments and blank lines: the parser's own tokenizer drops
# both (`tokenize` truncates at `;`, `tokenLines` filters empty lines), so they
# carry nothing and are not part of the diff.
drop_comments() {
  awk '/^[ \t]*;/ { next } /^[ \t]*$/ { next } { print }' "$1"
}

# --- the parameter names, and the ABI's spelling of them ------------------

# The three parameter registers the statement writes, in the order the ABI
# declares its parameters.  `kernel/json/s1_block.h` declares
# `leanllvm_json_s1_masks(const uint8_t *p, s1_carry *carry, s1_masks *out)`, and
# the body is stated over `%p`, `%c` and `%o`, so the header's names map onto
# these three positionally: `p` stays `p`, `carry` becomes `c`, `out` becomes
# `o`.  That the declaration has exactly three parameters, and which name each
# position carries, is read below from the emission; a count mismatch refuses.
abi_names=(p c o)

# One parameter name per line, from the header's parameter list.
param_names() {
  awk -v sym="@$symbol(" '
    {
      i = index($0, sym)
      if (i == 0) next
      rest = substr($0, i + length(sym) - 1)
      depth = 0
      chunk = ""
      n = 0
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
  ' "$1"
}

param_names "$work/block.raw.ll" > "$work/params.txt" ||
  fail "cannot read the parameter list of @$symbol in the emission"
mapfile -t emitted_names < "$work/params.txt"
[ "${#emitted_names[@]}" -eq "${#abi_names[@]}" ] ||
  fail "@$symbol has ${#emitted_names[@]} parameter(s); the ABI has ${#abi_names[@]}"

rename_args=()
for i in "${!abi_names[@]}"; do
  old=${emitted_names[$i]#%}
  new=${abi_names[$i]}
  [ "$old" = "$new" ] && continue
  rename_args+=(-e "s/%${old}([^A-Za-z0-9_.])/%${new}\1/g"
                -e "s/%${old}\$/%${new}/")
done
if [ "${#rename_args[@]}" -gt 0 ]; then
  sed -E "${rename_args[@]}" "$work/block.raw.ll" > "$work/block.ll"
  for i in "${!abi_names[@]}"; do
    old=${emitted_names[$i]#%}
    [ "$old" = "${abi_names[$i]}" ] && continue
    if grep -q "%${old}\([^A-Za-z0-9_.]\|\$\)" "$work/block.ll"; then
      fail "the parameter rename left %${old} in the block"
    fi
  done
else
  cp "$work/block.raw.ll" "$work/block.ll"
fi

# The whole module, comments dropped, with the same rename applied.
drop_comments "$work/named.ll" > "$work/module.comments.ll"
if [ "${#rename_args[@]}" -gt 0 ]; then
  sed -E "${rename_args[@]}" "$work/module.comments.ll" > "$work/module.ll"
else
  cp "$work/module.comments.ll" "$work/module.ll"
fi

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
    -e 's/ local_unnamed_addr//g' \
    -e 's/ #[0-9]+//g' \
    -e 's/ align [0-9]+//g'
}

# Instruction rules: metadata (5), alignment (9), the constraining flags (4),
# call-argument and call-result attributes (1), and `poison` (6), whose removal
# leaves a defined lane in its place — the lane no observable reads.
normalise_body() {
  sed -E \
    -e 's/, !tbaa ![0-9]+//g' \
    -e 's/, align [0-9]+//g' \
    -e 's/ nuw//g' \
    -e 's/ disjoint//g' \
    -e 's/ range\(i64 [^)]*\)//g' \
    -e 's/insertelement <2 x i64> poison/insertelement <2 x i64> zeroinitializer/g' \
    -e 's/i64 poison/i64 0/g'
}

head -n 1 "$work/block.ll" | normalise_header > "$work/body.head.ll"
tail -n +2 "$work/block.ll" | normalise_body > "$work/body.rest.ll"
cat "$work/body.head.ll" "$work/body.rest.ll" > "$work/body.ll"

nblock=$(wc -l < "$work/block.ll")
nbody=$(wc -l < "$work/body.ll")
[ "$nblock" -eq "$nbody" ] ||
  fail "the normalisation changed the block's line count ($nblock -> $nbody); it removes tokens, not lines"

# --- the strip inventory: the block diffed against what it emits ----------

# The diff aligns the block's tokens with the body's, line by line: a token that
# matches is kept, a declared substitution is recorded as one, a token with no
# counterpart is a removal.  Removals are contiguous runs, and each run is
# attributed to classes by consecutive prefix matches; a token no class matches
# is a setup failure.  The record joins the run's tokens with the separators it
# had, so a removal reads the way the emission spells it.
cat > "$work/classify.awk" <<'AWK'
BEGIN {
    seps = " \t,()<>{}"
    c1word["noundef"] = 1; c1word["readonly"] = 1; c1word["writeonly"] = 1
    c1word["immarg"] = 1
    c1paren["captures"] = 1; c1paren["range"] = 1
    c2word["local_unnamed_addr"] = 1
    c4word["nuw"] = 1; c4word["nusw"] = 1; c4word["disjoint"] = 1
    c4word["inbounds"] = 1
    c7paren["initializes"] = 1
    subst["poison" SUBSEP "zeroinitializer"] = 6
    subst["poison" SUBSEP "0"] = 6
    reason[1] = "argument, parameter and call-result attributes: a promise about an argument or a result, re-established by the theorem's hypotheses; a call's range is implied by the model's own definition"
    reason[2] = "function-header surface: linkage and code placement, which the model has no semantics for; the Calls environment decides which definition answers"
    reason[3] = "attribute-group definition: the target-feature and memory promise its references carry, recorded in PROVENANCE.md"
    reason[4] = "instruction flag that constrains: it excludes inputs, so stripping widens, and the widening is recorded rather than re-established"
    reason[5] = "memory and analysis metadata: the model has no aliasing relation to read it with"
    reason[6] = "poison as a value: no observable reads the lane, so a defined lane stands in"
    reason[7] = "initializes((0, 48)): a promise about which slot bytes are written; the theorem's memory clause is stronger for the bytes it covers"
    reason[8] = "module configuration: not read by the parser; recorded in the fixture's provenance comment and in PROVENANCE.md"
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
        curline = ln
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
                       item(i, i), subimg[i], ln)
            }
        }
        flush()
        for (j = 1; j <= no; j++)
            if (j in ins) {
                bad++
                printf "SETUP: line %d emits '%s', which the block does not have\n", ln, u[j] > "/dev/stderr"
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

awk -v nsubstfile="$work/nsubst" -f "$work/classify.awk" "$work/block.ll" "$work/body.ll" \
  > "$work/rows" ||
  fail "the block's removals could not be attributed to classes (see above)"

# The alignment's own count of substitutions, so the rewrite inventory can be
# shown to account for every one of them.
nsubst=$(cat "$work/nsubst" 2>/dev/null || printf '0')
awk -F'\t' '$2 == "substituted"' "$work/rows" > "$work/rows.subst"
awk -F'\t' '$2 != "substituted"' "$work/rows" > "$work/rows.strip"

# --- the whole-line removals: what the module carries and the fixture does not

# The block's first line inside the comment-free module, so a whole-line row can
# name the line it came from.
start=$(awk -v head='define ' -v sym="@$symbol(" '
  index($0, head) == 1 && index($0, sym) { print NR; exit }' "$work/module.ll")

classify_lines() {
  awk -v start="$start" -v nb="$nblock" '
    BEGIN {
      reason[2] = "function-header surface: a declaration is a header with no body, and the Calls environment decides which definition answers"
      reason[3] = "attribute-group definition: the target-feature and memory promise its references carry, recorded in PROVENANCE.md"
      reason[5] = "memory and analysis metadata: the model has no aliasing relation to read it with"
      reason[8] = "module configuration: not read by the parser; recorded in the fixture'"'"'s provenance comment and in PROVENANCE.md"
      bad = 0
    }
    {
      ln = NR
      if (ln >= start && ln < start + nb) next
      if ($1 == "declare") c = 2
      else if ($1 == "attributes") c = 3
      else if ($1 == "!" || substr($1, 1, 1) == "!") c = 5
      else if ($1 == "target" || $1 == "source_filename") c = 8
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

# --- the strip inventory --------------------------------------------------

{
  cat <<'LEGEND'
# json-s1-masks.strip.tsv -- generated by
# probes/install/ir/capture-s1-masks.sh; do not edit.
#
# What the normalisation took out of the clang emission of
# kernel/json/s1_block.c, by class.  Each row is one removed item: a token or
# contiguous run of tokens inside the `define` block, or a whole line.
# `line` is the line of the emission the item came from (the module as emitted,
# comment and blank lines dropped).
#
# What the normalisation *rewrote* rather than removed — the parameter names and
# the `poison` lanes — is in json-s1-masks.rewrites.tsv, with its own reason.
#
# The nine classes, each with the reason the removal is sound:
#
#   1  argument, parameter and call-result attributes
#   2  function-header surface
#   3  attribute-group definitions
#   4  instruction flags that constrain (stripping widens; recorded, not
#      re-established)
#   5  memory and analysis metadata
#   6  poison as a value (no observable reads the lane).  Its instances are
#      rewrites, so the rows are in json-s1-masks.rewrites.tsv
#   7  initializes((0, 48)) (the theorem's memory clause is stronger)
#   8  module configuration (recorded in PROVENANCE.md)
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

# --- the rewrite inventory ------------------------------------------------

rename_reason='parameter rename to the ABI'"'"'s spelling: a register name is not part of the computation, and the capture shows it so by emitting the source with and without -fno-discard-value-names and comparing the two texts with every register name replaced by one placeholder'
subst_reason='poison replaced by a defined lane: no observable reads the lane, so the text stands a value the model represents in its place'

: > "$work/rows.rename"
nrename=0
for i in "${!abi_names[@]}"; do
  old=${emitted_names[$i]}
  new="%${abi_names[$i]}"
  [ "$old" = "$new" ] && continue
  printf -- '-\trename\t%s\t%s\t1\t%s\n' "$old" "$new" "$rename_reason" \
    >> "$work/rows.rename"
  nrename=$((nrename + 1))
done

{
  cat <<'LEGEND'
# json-s1-masks.rewrites.tsv -- generated by
# probes/install/ir/capture-s1-masks.sh; do not edit.
#
# Every place the normalisation *rewrote* text of the clang emission of
# kernel/json/s1_block.c instead of removing it, with the reason the rewrite is
# sound.  Two kinds:
#
#   rename      a register renamed.  The three parameters are written %p, %c and
#               %o; the names on the left are the emission's own, read from the
#               header.  Innocence is shown, not asserted: the capture emits the
#               source with and without -fno-discard-value-names and requires
#               the two texts to be identical once every register name is
#               replaced by one placeholder.
#   substitute  a token replaced by a defined one.  `poison`, class 6 of the
#               normalisation's classes; the lane it occupies is read by no
#               observable (`pclmulqdq` at immediate 0 uses lane 0 and the
#               `extractelement ... 0` that follows reads lane 0).
#
# A rewrite with no row here stops the capture: the alignment refuses any token
# the body adds that is not one of the substitutions declared here, and this
# file must account for every substitution it made.  `line` is the line of the
# emission, as in the strip inventory.
LEGEND
  printf 'class\tkind\tfrom\tto\tline\treason\n'
  {
    cat "$work/rows.rename"
    awk -F'\t' -v r="$subst_reason" \
      'BEGIN { OFS = "\t" } { print $1, $2, $3, $4, $5, r }' "$work/rows.subst"
  } | LC_ALL=C sort -t "$(printf '\t')" -k2,2 -k1,1n -k5,5n -s
} > "$work/rewrites.tsv"

# Every rewrite carries a reason, and the inventory accounts for every
# substitution the alignment made and every rename it applied.
if awk -F'\t' '/^#/ || $1 == "class" { next } NF < 6 || $6 == ""' "$work/rewrites.tsv" |
     grep -q .; then
  fail "a rewrite in the fixture has no recorded reason"
fi
[ "$(grep -c '	substituted	' "$work/rewrites.tsv" || true)" -eq "$nsubst" ] ||
  fail "the rewrite inventory accounts for $(grep -c '	substituted	' "$work/rewrites.tsv" || true) substitution(s); the alignment made $nsubst"
[ "$(grep -c '	rename	' "$work/rewrites.tsv" || true)" -eq "$nrename" ] ||
  fail "the rewrite inventory accounts for $(grep -c '	rename	' "$work/rewrites.tsv" || true) rename(s); $nrename were applied"

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
    /^attributes #[0-9]+ = \{/ { printf "%s\n", $0; next }
  ' "$1"
}
module_config "$work/named.ll" > "$work/config.txt"

{
  cat <<'PROVENANCE'
; The stage-1 classification mask unit as emitted, in the fragment the parser
; reads.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-s1-masks.sh
;
; from kernel/json/s1_block.c, emitted with the measured compiler line
;
;   clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
;         -falign-loops=64 -falign-functions=64 -fno-discard-value-names
;
; and reduced to the `define` block of @leanllvm_json_s1_masks.
; `-fno-discard-value-names` is a naming flag: it names values and labels the
; entry block, which the parser requires, and the capture checks that it changes
; no instruction by emitting the source with and without it and comparing the
; two texts with every register name replaced by one placeholder.
;
; The three parameters are written %p, %c and %o.  The capture reads their
; emitted names from the header and substitutes them; it refuses an emission
; whose parameter count is not three.
;
; Removed from the emission, each item with its class and the class's reason, in
; json-s1-masks.strip.tsv; rewritten rather than removed — the parameter names
; and two `poison` lanes — in json-s1-masks.rewrites.tsv.  The lines removed
; from the module carried:
PROVENANCE
  sed -e 's/^/;   /' "$work/config.txt"
  cat <<'PROVENANCE'
;
; The fixture's own opcodes and call targets are in json-s1-masks.inventory.
PROVENANCE
  cat "$work/body.ll"
} > "$work/fixture.ll"

inventory_of "$work/fixture.ll" > "$work/inventory.txt"

# --- write the four artefacts, together -----------------------------------

grep -q '^opcode ' "$work/inventory.txt" || fail "the fixture inventory names no opcode"
grep -q '^call @' "$work/inventory.txt" || fail "the fixture inventory names no call target"

cp "$work/fixture.ll" "$fixture"
cp "$work/strip.tsv" "$strip"
cp "$work/rewrites.tsv" "$rewrites"
cp "$work/inventory.txt" "$inventory"

printf 'capture-s1-masks: wrote probes/install/ir/json-s1-masks.candidate.ll\n'
printf 'capture-s1-masks: wrote probes/install/ir/json-s1-masks.strip.tsv (%s row(s))\n' \
  "$(awk -F'\t' 'NF >= 6 && $1 ~ /^[0-9]+$/' "$work/strip.tsv" | wc -l)"
printf 'capture-s1-masks: wrote probes/install/ir/json-s1-masks.rewrites.tsv (%s row(s))\n' \
  "$(( $(grep -c '	' "$work/rewrites.tsv" || true) - 1 ))"
printf 'capture-s1-masks: wrote probes/install/ir/json-s1-masks.inventory (%s line(s))\n' \
  "$(wc -l < "$work/inventory.txt")"
