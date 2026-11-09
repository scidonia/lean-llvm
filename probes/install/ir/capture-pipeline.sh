#!/usr/bin/env bash
# Regenerate the assembled pipeline's emitted-IR fixture and its three
# inventories in probes/install/ir/.
#
# Run through the flake, from the repository root:
#
#   nix develop -c bash probes/install/ir/capture-pipeline.sh
#
# Input
#   kernel/json/pipeline.c            the assembled caller, one public entry point
#
# Output (all four in the same run, from the same compilation)
#   json-pipeline.candidate.ll        the fixture: the `define` block, with the
#                                     syntax listed below removed
#   json-pipeline.strip.tsv           what the normalisation removed, by class,
#                                     derived by diffing the clang block against
#                                     the text this script emits
#   json-pipeline.rewrites.tsv        what it rewrote rather than removed, with
#                                     the reason the rewrite is sound; this unit
#                                     rewrites nothing, and the file says so
#   json-pipeline.inventory           the fixture's own opcodes and call targets
#
# `kernel/json/identity/inventory.sh` is the gate; this script only derives.
#
# --- Why the measured compiler line ---------------------------------------
#
# The fixture is the emission the assembled build compiles, not a portable
# re-phrasing of it: `kernel/json/bench/paired.sh` and the route's object arm
# compile the same C at the same flags, so the body the proof is about is the
# body the object runs.  The line is `build49.sh:17`'s, and the assembled
# pipeline has no unit `-D` set of its own: it reaches each unit through the
# external ABI that unit's header declares, so there is no configuration arm
# to name.
#
# `-fno-discard-value-names` is added to it.  It is a naming flag: it writes the
# source's value names and, because a named entry block is emitted with its
# label, it supplies the labels the parser requires.  That it changes no
# instruction is checked here rather than asserted: the same source is emitted
# with and without the flag, every register name is replaced by one placeholder
# and label lines are dropped, and the two texts must be identical.
#
# --- The parameter names --------------------------------------------------
#
# The emission names the parameters after the source's own (`%b`, `%n`, `%sc`,
# … `%arm`).  The ABI `pipeline.h` declares is the same list, so the capture
# renames none and refuses a name that differs.
#
# --- What the normalisation removes, and why it is a derivation -----------
#
# The emission at those flags carries syntax the parser refuses by name.  The
# removal is computed, not transcribed: the capture diffs its own clang block
# against the text it emits, groups the removed tokens into contiguous runs, and
# attributes each run to one of the classes, writing a row per item with the
# class's reason.  A token that matches no class exits `3`, so syntax cannot be
# stripped silently and the inventory cannot fall behind the emission.  A token
# the parser already accepts and drops (`tail`, `inbounds`, `samesign`) is never
# removed, so it never appears — the inventory is a record of what was taken
# out, not of what the parser tolerates.
#
# The classes this unit exercises:
#
#   1. argument, parameter and call-result attributes — `noundef`,
#      `nonnull`, `captures(none)`: a promise about an argument or a result,
#      re-established by the theorem's hypotheses.
#   2. function-header surface — `local_unnamed_addr`, `#N`, the function's
#      `align`, and the six callee `declare` lines: linkage, code placement and
#      the declaration of a callee the model knows by name, for none of which
#      the model has a semantics; `Calls` decides which definition answers.
#   3. attribute-group definitions — `attributes #N = { ... }`: the target
#      feature and memory promise its references carry, removed with them and
#      recorded in PROVENANCE.md.
#   4. instruction flags that constrain — `nuw`, `nsw`, `disjoint`: each
#      excludes inputs, so stripping *widens*; the widening is recorded rather
#      than re-established.  This unit's are `nuw`/`nsw` on the `shl`, `add`,
#      `lshr` and `getelementptr`s of the loop and on `%add` in the entry block,
#      and `disjoint` on the `or` that places the previous block's scalar lane.
#   5. memory and analysis metadata — `!tbaa` and `!llvm.loop`, and the module's
#      `!N = ...` nodes: the model has no aliasing relation and no loop model to
#      read them with.
#   9. instruction-level alignment — `load ..., align 8` and `store ..., align 8`:
#      the parser's `load` and `store` have no alignment field, and the model
#      addresses bytes, so the removal is a representation loss and not a
#      semantic one.
#
# Classes 6 (`poison`), 7 (`initializes`), and 10 (a call's calling convention)
# have no instance here, and the capture asserts the zero rather than assuming
# it: a substitution appearing with no row in json-pipeline.rewrites.tsv is a
# setup failure.
#
# Whole lines are removed as lines and carry a class too: a `declare` line is
# class 2, `attributes #N = { ... }` is class 3, the module header is class 8,
# and a module metadata node is class 5.  Comment and blank lines are dropped
# before the diff rather than classified: `tokenize` (`LeanLLVM/Parser.lean`)
# truncates a line at `;` and `tokenLines` drops empty lines, so a comment
# carries no token the parser reads.
#
# Exit status: 0 when the four artefacts are written; 3 when an input is
# missing or the derivation cannot be attributed — the same code the rest of the
# route uses for an unusable input.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)

src=kernel/json/pipeline.c
symbol=leanllvm_json_pipeline
# The source's own parameter names, in order; the ABI `pipeline.h` declares is
# this list, so the capture renames none.
pipeline_names=(b n sc mk entw ep epcap nk xp xpcap nxp xcarry dst dstcap ndst
                ev evcap nev err arm)
fixture=$here/json-pipeline.candidate.ll
strip=$here/json-pipeline.strip.tsv
rewrites=$here/json-pipeline.rewrites.tsv
inventory=$here/json-pipeline.inventory

fail() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

[ -f "$repo/$src" ] || fail "absent: $repo/$src"
command -v clang >/dev/null 2>&1 || fail "clang is not on PATH"

work=$(mktemp -d "$repo/.lake/tmp-pipeline-capture.XXXXXX" 2>/dev/null) ||
  work=$(mktemp -d) ||
  fail "cannot create a work directory"
trap 'rm -rf "$work"' EXIT

neutralise() {
  sed -E -e 's/%[A-Za-z0-9._$-]+/%N/g' \
         -e 's/^[A-Za-z0-9_.$-]+:/%L:/' \
         -e '/^%L:/d' "$1"
}
strip_comments() {
  awk '{
    i = index($0, ";")
    if (i > 0) $0 = substr($0, 1, i - 1)
    sub(/[ \t]+$/, "", $0)
    if ($0 == "") next
    print
  }' "$1"
}
block_range() { # <symbol> -> "start end"
  awk -v head='define ' -v sym="@$1(" '
    !inblock && index($0, head) == 1 && index($0, sym) { inblock = 1; start = NR }
    inblock && $0 == "}" { print start, NR; exit }
  ' "$work/module.ll"
}
all_block_ranges() {
  awk '
    inblock && $0 == "}" { print start, NR; inblock = 0; next }
    !inblock && index($0, "define ") == 1 { inblock = 1; start = NR }
  ' "$work/module.ll"
}
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
normalise_body() {
  sed -E \
    -e 's/ noundef//g' \
    -e 's/ nonnull//g' \
    -e 's/, !tbaa ![0-9]+//g' \
    -e 's/, !prof ![0-9]+//g' \
    -e 's/, !llvm\.loop ![0-9]+//g' \
    -e 's/, align [0-9]+//g' \
    -e 's/ #[0-9]+//g' \
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
module_config() {
  awk '
    /^source_filename =/ { printf "%s\n", $0; next }
    /^target triple/ { printf "%s\n", $0; next }
    /^target datalayout/ { printf "%s\n", $0; next }
  ' "$1"
}
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

# --- the emission ---------------------------------------------------------

flags=(-S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11
       -falign-loops=64 -falign-functions=64)

# The source is named relative to the repository root, so `source_filename`
# in the emission does not carry a checkout path.
compile() { ( cd "$repo" && clang -I kernel/json "$@" ); }

compile "${flags[@]}" "$src" -o "$work/plain.ll"
compile "${flags[@]}" -fno-discard-value-names "$src" -o "$work/named.ll"

# The naming flag's claim, checked: the same source, the same instructions.  The
# flag also labels the blocks it emits, and the label line carries a `preds`
# list, so label lines are dropped from both texts.
neutralise "$work/plain.ll" > "$work/plain.norm.ll"
neutralise "$work/named.ll" > "$work/named.norm.ll"
if ! cmp -s "$work/plain.norm.ll" "$work/named.norm.ll"; then
  diff -u "$work/plain.norm.ll" "$work/named.norm.ll" | awk 'NR <= 40' >&2
  fail "-fno-discard-value-names changed the emission beyond register names"
fi

strip_comments "$work/named.ll" > "$work/module.ll"

# --- the `define` block, and the function set ------------------------------

range=$(block_range "$symbol") || fail "the emission has no \`define\` block for @$symbol"
read -r start end <<< "$range"
sed -n "${start},${end}p" "$work/module.ll" > "$work/block.ll"
[ -s "$work/block.ll" ] || fail "the \`define\` block of @$symbol is empty"
printf '%s %s %s\n' "$start" "$end" "$symbol" > "$work/ranges"

all_block_ranges > "$work/allranges"
[ -s "$work/allranges" ] || fail "the emission holds no \`define\` block"
nfunc=$(wc -l < "$work/allranges" | tr -d ' ')
[ "$nfunc" -eq 1 ] || fail "the emission holds $nfunc \`define\` blocks; the pipeline is one function"

awk '
  inblock && $0 == "}" { inblock = 0; next }
  !inblock && index($0, "define ") == 1 {
    line = $0
    sub(/^.*@/, "", line)
    sub(/\(.*$/, "", line)
    print line
  }
' "$work/module.ll" > "$work/have.names"
[ "$(cat "$work/have.names")" = "$symbol" ] ||
  fail "the emission defines ($(tr '\n' ' ' < "$work/have.names")); the unit is $symbol"

# --- the parameter names, and the source's spelling of them --------------

param_names "$symbol" "$work/block.ll" > "$work/params" ||
  fail "cannot read the parameter list of @$symbol in the emission"
mapfile -t emitted_names < "$work/params"
if ! names_match "${pipeline_names[@]}" -- "${emitted_names[@]}"; then
  fail "@$symbol's parameters are (${emitted_names[*]-none}); the source names them (${pipeline_names[*]})"
fi
# The guard's own control: a name that differs by one character must be seen.
if names_match "${pipeline_names[@]}" -- "${emitted_names[@]/%nk/%nkk}"; then
  fail "the parameter guard does not see a changed name; it is not evidence"
fi
printf 'ok: the emission names the source'"'"'s %s parameters, and the guard sees a changed one\n' \
  "${#pipeline_names[@]}"

# --- the normalisation ----------------------------------------------------

head -n 1 "$work/block.ll" | normalise_header > "$work/body.ll"
tail -n +2 "$work/block.ll" | normalise_body >> "$work/body.ll"
nemit=$(wc -l < "$work/block.ll" | tr -d ' ')
nbody=$(wc -l < "$work/body.ll" | tr -d ' ')
[ "$nemit" -eq "$nbody" ] ||
  fail "the normalisation changed the block's line count ($nemit -> $nbody); it removes tokens, not lines"

# --- the strip inventory: the block diffed against what it emits ----------

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
    reason[3] = "attribute-group definition and its reference: the target-feature and memory promise the group carries; the definition is recorded in PROVENANCE.md, and the reference on a call is the same promise"
    reason[4] = "instruction flag that constrains: it excludes inputs, so stripping widens, and the widening is recorded rather than re-established"
    reason[5] = "memory and analysis metadata: the model has no aliasing relation and no loop model to read it with"
    reason[6] = "poison as a value: no observable reads the lane, so a defined lane stands in"
    reason[7] = "initializes((0, 32)): a promise about which slot bytes are written; the theorem's memory clause is stronger for the bytes it covers"
    reason[8] = "module configuration: not read by the parser; the values are recorded in the fixture's provenance comment and in PROVENANCE.md"
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
    if (c == 3) return (t[a] ~ /^#[0-9]+$/) ? a : 0
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
            if (c == 8) continue   # whole lines, not tokens
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

ofs=$((start - 1))
awk -v nsubstfile="$work/nsubst" -v ofs="$ofs" -f "$work/classify.awk" \
  "$work/block.ll" "$work/body.ll" > "$work/rows" ||
  fail "the removal could not be attributed to classes (see above)"
nsubst=$(cat "$work/nsubst" 2>/dev/null || printf '0')
[ "$nsubst" -eq 0 ] ||
  fail "the emission substitutes $nsubst token(s); none is declared in json-pipeline.rewrites.tsv"
cp "$work/rows" "$work/rows.strip"

# --- the whole-line removals: what the module carries and the fixture does not

classify_lines() {
  awk -v ranges="$work/allranges" '
    BEGIN {
      reason[2] = "function-header surface: linkage, code placement and a callee'"'"'s declaration, which the model has no semantics for; the Calls environment decides which definition answers"
      reason[3] = "attribute-group definition: the target-feature and memory promise its references carry, recorded in PROVENANCE.md"
      reason[5] = "memory and analysis metadata: the model has no aliasing relation and no loop model to read it with"
      reason[8] = "module configuration: not read by the parser; the values are recorded in the fixture'"'"'s provenance comment and in PROVENANCE.md"
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
      else if ($1 == "declare") next   # kept; its surface is token-classified below
      else if (substr($1, 1, 1) == "!") c = 5
      else if ($1 == "target" || $1 == "source_filename") c = 8
      else if (substr($1, 1, 1) == "@") {
        bad++
        printf "SETUP: line %d of the module defines a module-level symbol ('"'"'%s'"'"');\n", ln, $0 > "/dev/stderr"
        printf "SETUP: the pipeline has no module-level object, so a global appearing means the\n" > "/dev/stderr"
        printf "SETUP: emission has changed shape and the fixture no longer describes the unit\n" > "/dev/stderr"
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

# --- the callee declarations: kept, with their surface removed ------------

# The six declarations stay in the fixture: a call to an undeclared symbol is
# not well-formed IR, and the IR arm's instrument refuses it.  Their surface is
# removed by the same rules a `define`'s header takes, and every removed item is
# a row: a declaration the fixture holds without its `noundef` and `#N` is the
# emission less the strip table, which is the same claim the `define` makes.
: > "$work/declarations.ll"
: > "$work/strip.declares"
ndec=0
while IFS= read -r dln; do
  sed -n "${dln}p" "$work/module.ll" > "$work/decl.raw.ll"
  normalise_header < "$work/decl.raw.ll" > "$work/decl.body.ll"
  awk -v nsubstfile=/dev/null -v ofs="$((dln - 1))" -f "$work/classify.awk" \
    "$work/decl.raw.ll" "$work/decl.body.ll" >> "$work/strip.declares" ||
    fail "the surface of the declaration at line $dln could not be attributed to classes"
  cat "$work/decl.body.ll" >> "$work/declarations.ll"
  ndec=$((ndec + 1))
done < <(grep -n '^declare ' "$work/module.ll" | cut -d: -f1)
[ "$ndec" -eq 6 ] ||
  fail "the module declares $ndec callee(s); the pipeline calls six units"
printf 'ok: the six callee declarations are kept, with their surface removed\n'

# --- the strip table reconstructs the emission ---------------------------

if ! reconstruct_check "$work/block.ll" "$work/body.ll" "$work/rows.strip" "$ofs"; then
  fail "the strip table is not the emission less its rows"
fi
printf 'ok: the block is the emission less the strip table'\''s rows\n'

# The reconstruction is exercised in the same run on a body it must refuse: one
# token deleted is a difference no row records, so a reconstruction that accepts
# it is not evidence about the real pair.
awk '!done && /^  ret / { sub(/^  ret /, "  "); done = 1 } { print }' \
  "$work/body.ll" > "$work/body.perturbed.ll"
cmp -s "$work/body.ll" "$work/body.perturbed.ll" &&
  fail "the reconstruction control did not change the body; it is not evidence"
if reconstruct_check "$work/block.ll" "$work/body.perturbed.ll" "$work/rows.strip" "$ofs" \
     > "$work/perturbed.out" 2>&1; then
  fail "the reconstruction accepts a body difference the strip table does not record; it is not evidence"
fi
printf 'ok: the reconstruction refuses an unrecorded change\n'

# --- the fixture ----------------------------------------------------------

module_config "$work/module.ll" > "$work/config.txt"

{
  cat <<'PROVENANCE'
; The assembled JSON pipeline as emitted, in the fragment the parser reads: the
; caller @leanllvm_json_pipeline and nothing else.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-pipeline.sh
;
; from kernel/json/pipeline.c, emitted with the measured compiler line
;
;   clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
;         -falign-loops=64 -falign-functions=64 -fno-discard-value-names
;
; and reduced to the one `define` block.  The pipeline has no unit `-D` set: it
; reaches each unit through the external ABI its header declares.
; `-fno-discard-value-names` is a naming flag: it names values and labels the
; entry block, which the parser requires, and the capture checks that it changes
; no instruction by emitting the source with and without it and comparing the
; two texts with every register name replaced by one placeholder.
;
; Every parameter is the source's own name, so the capture renames none.  The
; six callees are reached through the ABI their headers declare:
;
;   @leanllvm_json_s1_masks     the mask unit, per block
;   @leanllvm_json_entry_pos8   the first entry emitter, per block
;   @leanllvm_json_entry_b8     the second entry emitter, per block
;   @leanllvm_json_escape_list  the escape-position list, per block, on the gate
;   @leanllvm_json_utf8         the document-level validity stage
;   @leanllvm_json_stage2       the entry stream's walk
;
; Their `declare` lines are kept, with their surface (`noundef`,
; `local_unnamed_addr`, `#N`) removed so the text is the syntax the parser
; reads; the declarations are what makes the fixture well-formed IR.  The
; `call` instructions stay, so the fixture's call targets are the census.  Nothing is rewritten: this unit has no table and no
; `poison` lane, and json-pipeline.rewrites.tsv is empty and says so.
;
; Removed from the emission, each item with its class and the class's reason, in
; json-pipeline.strip.tsv.  The lines removed from the module carried:
PROVENANCE
  sed -e 's/^/;   /' "$work/config.txt"
  cat <<'PROVENANCE'
;   (the attribute groups and the module metadata nodes are recorded in
;   json-pipeline.strip.tsv, where they are removed; the six declarations are
;   kept and their removed surface is in that file's rows too)
;
; The fixture's own opcodes and call targets are in json-pipeline.inventory.
PROVENANCE
  cat "$work/declarations.ll"
  cat "$work/body.ll"
} > "$work/fixture.ll"

inventory_of "$work/fixture.ll" > "$work/inventory.body"

# --- the two verdicts printed on every run -------------------------------

# `opt -passes=verify` says the fixture is well-formed IR; it says nothing about
# whether this repository can read it, so the parser is run as well.  Neither is
# a gate here: the artefacts are the derivation and the gate's criteria are the
# verdicts.
if command -v opt >/dev/null 2>&1; then
  if opt -passes=verify -disable-output "$work/fixture.ll" > "$work/opt.out" 2>&1; then
    printf 'ok: opt -passes=verify accepts the fixture\n'
  else
    printf 'REPORT: opt -passes=verify refused the fixture:\n'
    sed -n '1,20p' "$work/opt.out" | sed 's/^/REPORT:   /'
  fi
else
  printf 'REPORT: opt is not on PATH; the IR well-formedness arm did not run\n'
fi

parse_status=0
parse_out=$(repository_parse "$work/fixture.ll") || parse_status=$?
if [ "$parse_status" -eq 0 ]; then
  printf 'ok: the fixture parses under the repository parser\n'
else
  printf 'REPORT: the fixture does not parse under the repository parser (exit %s)\n' "$parse_status"
  printf '%s\n' "$parse_out" |
    sed -e "s|$work/fixture.ll|probes/install/ir/json-pipeline.candidate.ll|g" -e 's/^/REPORT:   /'
fi

# --- the inventories -----------------------------------------------------

{
  cat <<'LEGEND'
# json-pipeline.strip.tsv -- generated by
# probes/install/ir/capture-pipeline.sh; do not edit.
#
# What the normalisation took out of the clang emission of
# kernel/json/pipeline.c, by class.  Each row is one removed item: a token or
# contiguous run of tokens inside the `define` block, or a whole line.
# `line` is the line of the emission the item came from (the module as emitted,
# comment and blank lines dropped).
#
# This unit rewrites nothing: json-pipeline.rewrites.tsv is empty, and the
# capture refuses a substitution the file does not account for.
#
# The classes:
#
#   1  argument, parameter and call-result attributes (noundef, nonnull,
#      captures(...))
#   2  function-header surface (local_unnamed_addr, #N, the function's align, and
#      the surface of the six callee declarations, which the fixture keeps)
#   3  attribute-group definitions and the reference a call makes to one (#N)
#   4  instruction flags that constrain (nuw, nsw, disjoint: stripping widens;
#      recorded, not re-established)
#   5  memory and analysis metadata (!tbaa, !llvm.loop, !N = ...)
#   6  poison as a value -- no instance here
#   7  initializes(...) -- no instance here
#   8  module configuration (source_filename, target triple, target datalayout)
#   9  instruction-level alignment (the parser's load and store have no
#      alignment field)
#  10  a call's calling convention -- no instance here
#
# A token matching no class stops the capture with exit 3, so this file cannot
# fall behind the emission.
LEGEND
  printf 'class\tkind\titem\timage\tline\treason\n'
  {
    cat "$work/rows.strip"
    cat "$work/strip.declares"
    cat "$work/strip.lines"
  } | LC_ALL=C sort -t "$(printf '\t')" -k1,1n -k5,5n -k3,3 -s
} > "$work/strip.tsv"

{
  cat <<'LEGEND'
# json-pipeline.rewrites.tsv -- generated by
# probes/install/ir/capture-pipeline.sh; do not edit.
#
# Every place the normalisation *rewrote* text of the clang emission of
# kernel/json/pipeline.c instead of removing it, with the reason the rewrite is
# sound.  The kinds are the ones capture-escape.sh defines:
#
#   substituted  a token replaced by a defined one (`poison`, class 6).  The
#                pipeline has no vector constant and no `poison` lane, so the
#                kind has no row here and the capture asserts that the emission
#                makes no substitution.
#   rename       a register renamed.  Every parameter is the source's own name,
#                so this unit's capture performs no rename and the kind has no
#                row here.
#   splat        a splat vector constant written as its lane list.  The
#                pipeline emits no vector constant, so the kind has no row here.
#
# An empty file is the claim: the fixture is the emission less the strip
# table's rows and nothing else.  The capture fails if a substitution appears
# with no row here.
LEGEND
  printf 'class\tkind\tfrom\tto\tline\treason\n'
} > "$work/rewrites.tsv"

{
  cat <<'LEGEND'
# json-pipeline.inventory -- generated by
# probes/install/ir/capture-pipeline.sh; do not edit.
#
# The fixture's own opcodes and call targets, sorted and unique: one line per
# construct, so a form entering the emission shows as a line and not as a count.
# The `call` lines are the pipeline's census: the six units it reaches through
# their external ABIs, plus nothing else — a seventh callee, or an `llvm.*`
# intrinsic, appears here rather than in a proof that resolves it as `ub`.
LEGEND
  cat "$work/inventory.body"
} > "$work/inventory"

# --- the derivation's own accounting, and the artefacts ------------------

printf 'capture-pipeline: %s strip row(s), %s rewrite row(s), %s inventory line(s)\n' \
  "$(tail -n +2 "$work/strip.tsv" | wc -l | tr -d ' ')" \
  "$(awk 'BEGIN{c=0} !/^#/ && $0 !~ /^class\t/ {c++} END{print c}' "$work/rewrites.tsv")" \
  "$(wc -l < "$work/inventory.body" | tr -d ' ')"

cp "$work/fixture.ll" "$fixture"
cp "$work/strip.tsv" "$strip"
cp "$work/rewrites.tsv" "$rewrites"
cp "$work/inventory" "$inventory"
printf 'ok: wrote %s, %s, %s, %s\n' \
  "${fixture#$repo/}" "${strip#$repo/}" "${rewrites#$repo/}" "${inventory#$repo/}"
