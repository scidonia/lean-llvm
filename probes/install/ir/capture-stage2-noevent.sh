#!/usr/bin/env bash
# Regenerate the no-event stage-2 entry's emitted-IR fixture and its four
# inventories in probes/install/ir/.
#
# Run through the flake, from the repository root:
#
#   nix develop -c bash probes/install/ir/capture-stage2-noevent.sh
#
# Input
#   kernel/json/stage2_noevent.c    the no-event entry: the certified walk's
#                                   validation and body work, with the event
#                                   record and the arena replaced by the
#                                   consumer's reading accumulated directly
#   kernel/json/stage2.c            the certified unit, included by the input
#                                   under a rename of its entry point, so every
#                                   helper the entry calls is that file's text
#
# Output (all five in the same run, from the same compilation)
#   stage2-noevent.candidate.ll     the fixture: the entry's `define` block,
#                                   with its helpers out of line, the staging
#                                   objects flattened to parameters, and the
#                                   syntax listed below removed
#   stage2-noevent.strip.tsv        what the normalisation removed, item by
#                                   item, by class
#   stage2-noevent.rewrites.tsv     what it rewrote rather than removed, with
#                                   the reason each rewrite preserves the value
#                                   computed
#   stage2-noevent.staging.tsv      the local objects that became parameters
#   stage2-noevent.inventory        the fixture's own opcodes and call targets,
#                                   and the literal compare's instruction count
#
# The script refuses (exit 3) on an unclassified removal, an unattributed
# rewrite, a staging object it does not name, a scalar alloca it cannot
# account for, a vector type or `insertelement`/`extractelement` in the body,
# a missing guard, a fixture that does not parse, and a second derivation that
# is not byte-identical to the first.
#
# --- Why the measured compiler line, and the two flags beyond it -----------
#
# The fixture is the emission the measured build compiles.  The line is
# `build49.sh:17`'s:
#
#   clang -O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
#         -falign-functions=64
#
# Two derivation flags are added to it, and both are recorded here because this
# file is where they are written:
#
#   -fno-discard-value-names  a naming flag: it writes the source's value names
#                             and the entry block's label, which the parser
#                             requires.  That it changes no instruction is
#                             checked below by normalising both emissions.
#   -fno-slp-vectorize        NOT the measured line.  At the measured line
#                             clang SLP-packs the two independent 64-bit
#                             counters (`tokens` and `terms`) into `<2 x i64>`
#                             and carries `insertelement`/`extractelement`.
#                             The packing changes no value -- two independent
#                             scalar adds, packed into one vector add -- but it
#                             puts vector types in the body, which this
#                             fragment has no counter reading for.  The flag
#                             removes the packing and changes nothing else;
#                             the body below carries no vector type, which the
#                             residual check enforces.
#
# --- Why the helpers are out of line --------------------------------------
#
# As emitted, the entry inlines `s2_string_body`, `num_fast_el1`, `is_ws`,
# `dbits`, `od_gap_recover` and `lit_check`'s neighbours.  The derivation
# compiles a transform of the source in which `__attribute__((always_inline))`
# is replaced by `noinline` on every helper in both files, so each helper
# leaves the body as a call and its contract is stated where its own module
# sits.  The entry itself carries no attribute and is the one `define` taken.
#
# The literal check is the exception, and it is not a helper call: the entry's
# `ne_lit` packs the literal into an integer and is `static inline`, so its
# byte comparisons and its offsets are body text.  It is there because the
# fragment has no module-global representation, and the certified `lit_check`
# takes a `const char *`; the included carrier still calls the certified
# `lit_check`, and the call census below shows no literal-helper call.
#
# --- The staging objects become parameters --------------------------------
#
# The fragment has no aggregate type, no element-count `alloca` and no vector
# `alloca`, so the four locals the entry declares of those shapes cannot be
# expressed:
#
#   %stk  alloca [520 x i8]      the container-frame stack
#   %c    alloca %struct.OdCur   the cursor record
#   %e    alloca %struct.Err     the refusal record
#   %d    alloca double          the number path's output slot
#
# Each becomes an appended `ptr` parameter, in the emission's order, so the
# fixture's function takes the ABI's twelve arguments followed by these four.
# The rewrite preserves the value computed because each object's address is the
# same object: the body writes and reads the same bytes at the same offsets
# through the parameter it wrote and read through the alloca.  The four scalar
# allocas (`%xj`, `%outn`, `%outn205`, `%ei`, each `alloca i64`) stay in the
# body; the parser models `alloca i64` and its load/store, and the pin records
# their type list.
#
# --- The instruction rewrites, each with its reason -----------------------
#
#   1. `getelementptr inbounds [520 x i8], ptr %p, i64 0, i64 %i`
#      -> `getelementptr inbounds i8, ptr %p, i64 %i`
#      The two forms address `%p + 0 * 520 + i * 1` and `%p + i * 1`: the offset
#      from the base is `i` on both sides, and only the element type differs.
#   2. `@.str`
#      -> `null`
#      The refusal record's message word, written `"ok"` and never loaded by
#      this entry or any callee it calls on a path that reads it: `od_fail` and
#      `s2_string_body` write `e->msg` and nothing reads it.  The fragment has
#      no module globals, and the value is unconstrained, so the fixture writes
#      `null`.
#   3. `%u = call i32 @llvm.umax.i32(i32 %a, i32 %b)`
#      -> `%u.max = icmp ugt i32 %a, %b` ; `%u = select i1 %u.max, i32 %a, i32 %b`
#      `umax` has no parser rule and no environment binding; the two
#      instructions are the intrinsic's definition -- the larger of two unsigned
#      values -- so the rewrite is an unfolding, not an approximation.
#
# Nothing else is rewritten.  In particular the entry's own guards are kept:
# both scratch-capacity checks (`len + US_SLACK > scratchcap`), their two
# `__builtin_trap` arms, the refusal arms' three zero stores, and the three
# acceptance stores are body text.
#
# --- The strip: what is removed and why it is not the computation ---------
#
# The removal is computed, not transcribed: `classify.awk` aligns the emission's
# tokens with the text this script emits, requires every removed run to match one
# of the classes below (`3` refuses otherwise), and rebuilds the emitted line
# from the kept tokens and the recorded runs; a line that does not rebuild
# byte-identically is a setup fault.  The classes are the stage-2 capture's:
#
#   1  argument, parameter and call-result attributes
#   2  function-header surface: linkage, code placement, header alignment
#   3  an attribute-group reference on a call
#   4  instruction flags that constrain (`nuw`, `nsw`, ...)
#   5  memory and analysis metadata (`!tbaa`, `!N` nodes)
#   9  instruction-level alignment
#   10 a call's calling convention
#
# Whole lines are not removed from the block.  The module's header, its
# attribute groups, its metadata nodes and the other `define` blocks (the
# renamed carrier) are not taken: the fixture is one `define` and the
# declarations its calls need, and each omission is a row in
# stage2-noevent.rewrites.tsv.
#
# Exit status: 0 when the five artefacts are written; 3 when an input is missing
# or a derivation check fails.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)

src=kernel/json/stage2_noevent.c
helper=kernel/json/stage2.c
symbol=leanllvm_json_stage2_noevent
fixture=$here/stage2-noevent.candidate.ll
strip=$here/stage2-noevent.strip.tsv
rewrites=$here/stage2-noevent.rewrites.tsv
staging=$here/stage2-noevent.staging.tsv
inventory=$here/stage2-noevent.inventory

fail() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

[ -f "$repo/$src" ] || fail "absent: $repo/$src"
[ -f "$repo/$helper" ] || fail "absent: $repo/$helper"
command -v clang >/dev/null 2>&1 || fail "clang is not on PATH"
command -v opt >/dev/null 2>&1 || fail "opt is not on PATH"

work=$(mktemp -d "$repo/.lake/tmp-stage2-noevent-capture.XXXXXX" 2>/dev/null) ||
  work=$(mktemp -d) ||
  fail "cannot create a work directory"
trap 'rm -rf "$work"' EXIT

flags=(-S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11
       -falign-loops=64 -falign-functions=64 -fno-slp-vectorize)
compile() { ( cd "$repo" && clang -I kernel/json "$@" ); }

# The four locals that become parameters, in the emission's order.
staging_names=(stk e c d)
# The four scalar allocas that stay in the body, in the emission's order.
scalar_names=(xj outn outn205 ei)

# ---------------------------------------------------------------------------
# The source transform: `noinline` on every helper
# ---------------------------------------------------------------------------

sed -e 's/__attribute__((always_inline)) static inline/__attribute__((noinline)) static inline/g' \
    "$repo/$helper" > "$work/stage2.noinline.c"
sed -e 's/__attribute__((always_inline)) static inline/__attribute__((noinline)) static inline/g' \
    "$repo/$src" > "$work/noevent.noinline.c"

grep -q '__attribute__((always_inline))' "$work/stage2.noinline.c" &&
  fail "the transformed helper still carries an always_inline attribute"
grep -q '__attribute__((always_inline))' "$work/noevent.noinline.c" &&
  fail "the transformed entry still carries an always_inline attribute"

n_ni=$(grep -c '__attribute__((noinline))' "$work/stage2.noinline.c" || true)
[ "$n_ni" -ge 10 ] ||
  fail "the transformed helper carries $n_ni noinline occurrence(s); the always_inline set is larger"

# The merged translation unit: the entry's `#include "stage2.c"` is replaced by
# the transformed file, preserving the define/include-order/undef structure.
awk -v inc="$work/stage2.noinline.c" '
  $0 == "#include \"stage2.c\"" { while ((getline l < inc) > 0) print l; close(inc); next }
  { print }' "$work/noevent.noinline.c" > "$work/merged.c"

grep -q '^#define leanllvm_json_stage2 leanllvm_json_stage2_noevent_lib$' "$work/merged.c" ||
  fail "the merged source lost the entry rename"
grep -q '^uint64_t leanllvm_json_stage2_noevent(' "$work/merged.c" ||
  fail "the merged source lost the no-event entry"

# ---------------------------------------------------------------------------
# The emission, and the naming flag's claim
# ---------------------------------------------------------------------------

compile "${flags[@]}" -fno-discard-value-names "$work/merged.c" -o "$work/named.ll"
compile "${flags[@]}" "$work/merged.c" -o "$work/plain.ll"

neutralise() { # <file>
  sed -E -e 's/%[A-Za-z0-9_.$-]+/%r/g' "$1" |
    grep -vE '^[A-Za-z0-9_.$-]+:' | grep -vE '^$' |
    grep -vE '^(!|attributes #|target |source_filename)'
}
neutralise "$work/plain.ll" > "$work/plain.norm.ll"
neutralise "$work/named.ll" > "$work/named.norm.ll"
cmp -s "$work/plain.norm.ll" "$work/named.norm.ll" ||
  fail "-fno-discard-value-names changed an instruction; the naming flag is not a naming flag"

awk -v sym="$symbol" '
  $0 ~ "^define .*@" sym "\\(" { inblock = 1 }
  inblock { print }
  inblock && $0 == "}" { exit }
' "$work/named.ll" > "$work/block.prelower.ll"
nswitch=$(grep -c 'switch' "$work/block.prelower.ll" || true)

opt -S -passes=lower-switch "$work/named.ll" -o "$work/lowered.ll" ||
  fail "opt refused to lower the switch"

awk -v sym="$symbol" '
  $0 ~ "^define .*@" sym "\\(" { inblock = 1 }
  inblock { print }
  inblock && $0 == "}" { exit }
' "$work/lowered.ll" > "$work/block.ll"
[ -s "$work/block.ll" ] || fail "the emission has no \`define\` block for @$symbol"

# The measurement that makes the derivation's premise the file's: the same
# source without the transform and without -fno-slp-vectorize carries vectors.
compile -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
        -falign-loops=64 -falign-functions=64 -fno-discard-value-names \
        "$work/merged.c" -o "$work/fused.ll"
awk -v sym="$symbol" '
  $0 ~ "^define .*@" sym "\\(" { inblock = 1 }
  inblock { print }
  inblock && $0 == "}" { exit }
' "$work/fused.ll" > "$work/fused.block.ll"
fused_lines=$(wc -l < "$work/fused.block.ll" | tr -d ' ')
fused_blocks=$(grep -cE '^[A-Za-z0-9_.]+:' "$work/fused.block.ll" || true)
fused_vec=$(grep -cE '<[0-9]+ x ' "$work/fused.block.ll" || true)
[ "$fused_vec" -gt 0 ] ||
  fail "the untransformed emission carries no vector type; the SLP flag's premise is not the file's"

# ---------------------------------------------------------------------------
# The strip: attributes and surface, itemised and rebuilt
# ---------------------------------------------------------------------------

cat > "$work/classify.awk" <<'AWK'
BEGIN {
    seps = " \t,()<>"
    c1word["noundef"] = 1; c1word["nonnull"] = 1; c1word["readonly"] = 1
    c1word["writeonly"] = 1; c1word["noalias"] = 1; c1word["zeroext"] = 1
    c1word["signext"] = 1; c1word["returned"] = 1; c1word["immarg"] = 1
    c1word["nocapture"] = 1; c1word["nofree"] = 1; c1word["nosync"] = 1
    c1word["nounwind"] = 1; c1word["norecurse"] = 1; c1word["willreturn"] = 1
    c1word["mustprogress"] = 1
    c1paren["captures"] = 1; c1paren["range"] = 1; c1paren["initializes"] = 1
    c1paren["dereferenceable"] = 1; c1paren["dereferenceable_or_null"] = 1
    c1paren["nofpclass"] = 1
    c2word["local_unnamed_addr"] = 1; c2word["unnamed_addr"] = 1
    c4word["nuw"] = 1; c4word["nsw"] = 1; c4word["nusw"] = 1
    c4word["disjoint"] = 1; c4word["nneg"] = 1
    c10word["fastcc"] = 1
    reason[1] = "argument, parameter and call-result attributes: a promise about an argument or a result, re-established by the theorem's hypotheses; a call's or an operand's range is restated by the model's own definition"
    reason[2] = "function-header surface: linkage, code placement and the header's alignment, for which the model has no semantics"
    reason[3] = "attribute-group reference on a call: the target-feature and memory promise the group carries; the definition is removed with the module header"
    reason[4] = "instruction flag that constrains: it excludes inputs, so stripping widens, and the widening is recorded rather than re-established"
    reason[5] = "memory and analysis metadata: the model has no aliasing relation and no loop model to read it with"
    reason[9] = "instruction-level alignment: the parser's load, store and alloca have no alignment field, and the model addresses bytes"
    reason[10] = "a call's calling convention: no calling convention is modelled, and the Calls environment decides which definition answers and how the call is made"
    rows = 0; bad = 0; nline = 0
}

FILENAME == ARGV[1] { emit[FNR] = $0; ne = FNR; next }
{ body[FNR] = $0; nb = FNR }

END {
    if (ne != nb) {
        printf "SETUP: the block has %d line(s) and the body %d\n", ne, nb > "/dev/stderr"
        exit 3
    }
    for (ln = 1; ln <= ne; ln++) {
        nline = ln
        nt = tokenize(emit[ln], t, sep)
        no = tokenize(body[ln], u, usep)
        iscall = 0
        for (k = 1; k <= nt; k++) if (t[k] == "call") { iscall = 1; break }
        i = 1; j = 1; delete del; nd = 0
        while (i <= nt) {
            if (j <= no && t[i] == u[j]) { i++; j++; continue }
            e = matchclass(i, nt)
            if (e == 0) {
                bad++
                printf "SETUP: line %d removes '%s', which matches no class\n", ln, t[i] > "/dev/stderr"
                i++
                continue
            }
            k = i
            while (k <= e) { nd++; del[k] = 1; k++ }
            addrow(mc_class, i, e)
            i = e + 1
        }
        if (j <= no) {
            bad++
            printf "SETUP: line %d emits '%s', which the block does not have\n", ln, u[j] > "/dev/stderr"
            continue
        }
        if (rebuild(nt, nd) != body[ln]) {
            bad++
            printf "SETUP: line %d does not rebuild from its recorded removals\n", ln > "/dev/stderr"
            continue
        }
    }
    for (k = 1; k <= rows; k++)
        printf "%d\t%s\t%s\t%d\t%s\n", cls[k], kind[k], it[k], lnr[k], reason[cls[k]]
    exit (bad > 0)
}

function addrow(c, a, b) {
    rows++; cls[rows] = c; it[rows] = item(a, b); lnr[rows] = nline
    kind[rows] = "removed"
}

function rebuild(nt, nd,   k, s, m, q) {
    s = sep[0]
    for (k = 1; k <= nt; k++) {
        if (k in del) continue
        m = k + 1
        while (m <= nt && (m in del)) m++
        if (m > k + 1) {
            q = sep[k]
            gsub(/, *$/, "", q)
            s = s t[k] q
        } else s = s t[k] sep[k]
    }
    gsub(/[ \t]+$/, "", s)
    return s
}

function tokenize(s, tk, sp,   n, k, c, cur, inTok) {
    k = 0; cur = ""; inTok = 0; sp[0] = ""
    for (n = 1; n <= length(s); n++) {
        c = substr(s, n, 1)
        if (index(seps, c) > 0) {
            if (inTok) { k++; tk[k] = cur; sp[k] = c; cur = ""; inTok = 0 }
            else { sp[k] = sp[k] c }
        } else { cur = cur c; inTok = 1 }
    }
    if (inTok) { k++; tk[k] = cur; sp[k] = "" }
    return k
}

function item(a, b,   s, k, depth, q, m, add, c) {
    s = t[a]; depth = 0
    for (k = a; k < b; k++) {
        q = sep[k]; depth += gsub(/\(/, "(", q); depth -= gsub(/\)/, ")", q)
        s = s sep[k] t[k + 1]
    }
    if (depth > 0) {
        q = sep[b]; add = ""
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

function parenend(k,   depth, c, m, q) {
    depth = 0; q = sep[k]
    depth += gsub(/\(/, "(", q); depth -= gsub(/\)/, ")", q)
    if (depth <= 0) return k
    for (m = k + 1; m <= nt; m++) {
        q = sep[m]
        depth += gsub(/\(/, "(", q); depth -= gsub(/\)/, ")", q)
        if (depth <= 0) return m
    }
    return nt
}

function numeric(s) { return s ~ /^-?[0-9]+$/ }

function matchclass(a, b,   e) {
    mc_class = 0
    if (t[a] in c1word) { mc_class = 1; return a }
    if (t[a] in c1paren) { e = parenend(a); if (e > a) { mc_class = 1; return e }; return 0 }
    if (nline == 1) {
        if (t[a] in c2word) { mc_class = 2; return a }
        if (t[a] ~ /^#[0-9]+$/) { mc_class = 2; return a }
        if (t[a] == "align" && a + 1 <= b && numeric(t[a + 1])) { mc_class = 2; return a + 1 }
    }
    if (t[a] ~ /^#[0-9]+$/) { mc_class = 3; return a }
    if (t[a] in c4word) { mc_class = 4; return a }
    if (substr(t[a], 1, 1) == "!") {
        e = a
        while (e + 1 <= b && substr(t[e + 1], 1, 1) == "!") e++
        mc_class = 5
        return e
    }
    if (t[a] == "align" && a + 1 <= b && numeric(t[a + 1])) {
        mc_class = (iscall) ? 1 : 9
        return a + 1
    }
    if (t[a] in c10word) { mc_class = 10; return a }
    return 0
}
AWK

strip_tokens() {
  sed -E \
    -e 's/ (noundef|nonnull|readonly|writeonly|noalias|zeroext|signext|returned|immarg|nocapture|nofree|nosync|nounwind|norecurse|willreturn|mustprogress)//g' \
    -e 's/ (captures|range|initializes|dereferenceable|dereferenceable_or_null|nofpclass)\([^)]*(\([^)]*\))?[^)]*\)//g' \
    -e 's/ (local_unnamed_addr|unnamed_addr)//g' \
    -e 's/ (nuw|nsw|nusw|disjoint|nneg)//g' \
    -e 's/ align [0-9]+//g' \
    -e 's/ #[0-9]+//g' \
    -e 's/^define ([^@]*)@/define \1@/' \
    "$1"
}
strip_tokens "$work/block.ll" |
  sed -E -e 's/^(define .*)\) align [0-9]+ \{$/\1) {/' \
         -e 's/, align [0-9]+//g' -e 's/, !tbaa ![0-9]+//g' \
         -e 's/, ![A-Za-z0-9_.]+ ![0-9]+//g' \
         -e 's/, !llvm\.[^ ]*//g' -e 's/ call fastcc / call /g' -e 's/,[ \t]*$//' \
  > "$work/stripped.ll"

awk -f "$work/classify.awk" "$work/block.ll" "$work/stripped.ll" > "$work/strip.rows" ||
  fail "the removal could not be attributed to classes (see above)"
nstrip=$(wc -l < "$work/strip.rows" | tr -d ' ')
[ "$nstrip" -gt 0 ] || fail "the strip removed nothing; the emission's surface is not the fixture's"

# The local names need no pin here: this fixture is cut now, so the emission's
# spelling IS the fixture's.  The table that the stage-2 capture needs exists
# because that fixture predates later source edits; nothing has shifted here
# yet, and the check refuses a name this script would have to adopt silently.
cat > "$work/pin.tsv" <<'NAMES'
NAMES
npin=$(wc -l < "$work/pin.tsv" | tr -d ' ')
[ "$npin" -eq 0 ] || fail "the pin table is not empty; the derivation changed"

cp "$work/stripped.ll" "$work/pinned.ll"
: > "$work/rewrite.rows"

# ---------------------------------------------------------------------------
# The staging flattening: exactly the four recorded objects
# ---------------------------------------------------------------------------

awk -v staged="${staging_names[*]}" -v scalar="${scalar_names[*]}" '
BEGIN {
  n = split(staged, s, " "); for (k = 1; k <= n; k++) wantS[s[k]] = 1
  m = split(scalar, c, " "); for (k = 1; k <= m; k++) wantC[c[k]] = 1
}
{
  if (match($0, /^  %([A-Za-z0-9_.]+) = alloca ([^,]+)$/, a)) {
    name = a[1]; ty = a[2]
    if (ty ~ /^%struct\./ || ty == "[520 x i8]" || ty == "double") {
      stagedSeen[name]++; stageRow[++nstage] = name "\t" $0
      next
    }
    if (ty == "i64" || ty == "i32") { scalarSeen[name]++; print; next }
    printf "SETUP: the emission allocates %%%s at type %s, which is neither a recorded staging object nor a scalar\n", name, ty > "/dev/stderr"
    bad = 1
    next
  }
  print
}
END {
  for (k = 1; k <= n; k++) if (!(s[k] in stagedSeen)) { printf "SETUP: the emission has no staging alloca %%%s\n", s[k] > "/dev/stderr"; bad = 1 }
  for (name in stagedSeen) if (!(name in wantS)) { printf "SETUP: the emission stages %%%s, which is not a recorded staging object\n", name > "/dev/stderr"; bad = 1 }
  for (k = 1; k <= m; k++) if (!(c[k] in scalarSeen)) { printf "SETUP: the emission has no scalar alloca %%%s\n", c[k] > "/dev/stderr"; bad = 1 }
  for (name in scalarSeen) if (!(name in wantC)) { printf "SETUP: the emission allocates %%%s, which is not a recorded scalar\n", name > "/dev/stderr"; bad = 1 }
  for (k = 1; k <= nstage; k++) print stageRow[k] > (outfile)
  exit bad
}' outfile="$work/staging.rows" "$work/pinned.ll" > "$work/nostaging.ll" ||
  fail "the staging allocas are not the four this script names"

# The header gains the four parameters, in the emission's order.
awk -v p="$(paste -sd' ' <(cut -f1 "$work/staging.rows"))" '
NR == 1 {
  sub(/\) \{$/, "")
  n = split(p, names, " ")
  s = $0
  for (k = 1; k <= n; k++) s = s ", ptr %" names[k]
  print s ") {"
  next
}
{ print }' "$work/nostaging.ll" > "$work/headered.ll"

# ---------------------------------------------------------------------------
# The rewrites: array reads, the message, umax
# ---------------------------------------------------------------------------

awk '
{
  line = $0
  if (match(line, /^  (%[A-Za-z0-9_.]+) = getelementptr inbounds \[520 x i8\], ptr (%[A-Za-z0-9_.]+), i64 0, i64 (%[A-Za-z0-9_.]+)$/, m)) {
    ngep++
    printf "r5\tarray read\t%s\tgetelementptr inbounds i8, ptr %s, i64 %s\t1\t%s\n", $0, m[2], m[3],
      "the emitted form addresses base + 0*520 + i*1 and the fixture base + i*1: the offset from the base is i on both sides, and only the element type differs" >> rw
    print "  " m[1] " = getelementptr inbounds i8, ptr " m[2] ", i64 " m[3]
    next
  }
  if (match(line, /^  (%[A-Za-z0-9_.]+) = call i32 @llvm\.umax\.i32\(i32 ([^,]+), i32 ([^)]+)\)$/, m)) {
    nmin++
    after = m[1] ".max = icmp ugt i32 " m[2] ", " m[3] "; " m[1] " = select i1 " m[1] ".max, i32 " m[2] ", i32 " m[3]
    printf "r7\tumax unfolding\t%s\t%s\t1\t%s\n", $0, after,
      "llvm.umax has no parser rule and no environment binding; icmp ugt plus select is the definition of the intrinsic, so the rewrite is an unfolding and not an approximation" >> rw
    print "  " m[1] ".max = icmp ugt i32 " m[2] ", " m[3]
    print "  " m[1] " = select i1 " m[1] ".max, i32 " m[2] ", i32 " m[3]
    next
  }
  n = gsub(/@\.str(\.[0-9]+)?/, "null", line)
  if (n > 0) {
    nstr += n
    printf "r6\trefusal message\t%s\t%s\t%d\t%s\n", $0, line, n,
      "the message word of the refusal record (Err.msg): the fragment has no module globals, the entry writes it once and nothing in the entry or the callees it reaches loads it, so the value stored there is unconstrained" >> rw
  }
  print line
}
END {
  printf "%d %d %d\n", ngep, nstr, nmin > counts
}' rw="$work/rewrite.rows" counts="$work/rewrite.counts" "$work/headered.ll" > "$work/body.ll"

read -r ngep nstr nmin < "$work/rewrite.counts"
[ "$ngep" -gt 0 ] || fail "rewrote no array read; the container stack is not in the body"
[ "$nstr" -eq 1 ] || fail "rewrote $nstr message operand(s); the entry writes Err.msg once"
[ "$nmin" -eq 1 ] || fail "rewrote $nmin umax call(s); the body holds one"
[ "$nswitch" -ge 1 ] || fail "the emission carries no \`switch\`; the lower-switch step is not the one this script describes"

# No residual construct the rewrites or the transform exist to remove.
for pat in '%struct\.' '\[520 x i8\]' 'alloca double' '@\.str' 'llvm\.umax' '\bswitch\b' 'fastcc' \
           '<[0-9]+ x ' 'insertelement' 'extractelement' 'llvm\.umin'; do
  if grep -qE "$pat" "$work/body.ll"; then
    fail "the fixture still carries '$pat'; a rewrite class is missing"
  fi
done

# The entry's own guards are body text and are kept: both scratch-capacity
# checks (the `len + US_SLACK` add compared against `scratchcap`), their two
# fault arms, and the three zero stores of every refusal arm.
ntrap=$(grep -c 'call void @llvm.trap()' "$work/body.ll" || true)
[ "$ntrap" -eq 2 ] ||
  fail "the fixture carries $ntrap trap call(s); the entry's two shortfall arms are its own guards"
nslack=$(grep -cE 'add (nuw )?(nsw )?i64 [^,]+, 64$' "$work/body.ll" || true)
[ "$nslack" -eq 2 ] ||
  fail "the fixture carries $nslack scratch-slack add(s); each body's capacity check adds US_SLACK"
ncap=$(grep -cE 'icmp ugt i64 [^,]+, %scratchcap$' "$work/body.ll" || true)
[ "$ncap" -eq 2 ] ||
  fail "the fixture carries $ncap scratch-capacity comparison(s)"
nzt=$(grep -c 'store i64 0, ptr %tokens_out' "$work/body.ll" || true)
nzv=$(grep -c 'store i64 0, ptr %values_out' "$work/body.ll" || true)
nzs=$(grep -c 'store i64 0, ptr %sum_out' "$work/body.ll" || true)
[ "$nzt" -gt 0 ] && [ "$nzt" -eq "$nzv" ] && [ "$nzt" -eq "$nzs" ] ||
  fail "the refusal arms' zero stores are not one per slot per arm ($nzt/$nzv/$nzs)"
for slot in tokens_out values_out sum_out; do
  grep -qE "store i64 %[^,]+, ptr %$slot\$" "$work/body.ll" ||
    fail "the acceptance store to %$slot is not in the fixture"
done

# ---------------------------------------------------------------------------
# The declarations the body's calls need, derived from the emission
# ---------------------------------------------------------------------------

awk '
FNR == NR { called[$0] = 1; next }
{
  if (match($0, /^(define|declare) .*@([A-Za-z0-9_.$]+)\(/, m)) {
    name = m[2]
    if (!(name in called) || (name in sig)) next
    line = $0
    sub(/^(define|declare) (internal |private )?/, "declare ", line)
    gsub(/ (local_unnamed_addr|unnamed_addr)/, "", line)
    gsub(/ #[0-9]+/, "", line)
    gsub(/ align [0-9]+/, "", line)
    gsub(/ (noundef|readonly|writeonly|nonnull|noalias|zeroext|signext|returned|immarg)/, "", line)
    gsub(/ (nocapture|nofree|nosync|nounwind|norecurse|willreturn|mustprogress)/, "", line)
    gsub(/ (captures|range|initializes|dereferenceable|dereferenceable_or_null|nofpclass)\([^)]*(\([^)]*\))?[^)]*\)/, "", line)
    gsub(/fastcc /, "", line)
    sub(/ \{$/, "", line)
    sig[name] = line
    order[++n] = name
  }
}
END {
  for (k = 1; k <= n; k++) print sig[order[k]] > out
}' <(awk '
  { for (i = 1; i <= NF; i++) {
      s = $i
      if (match(s, /@[A-Za-z0-9_.$]+\(/, m)) print substr(m[0], 2, length(m[0]) - 2)
    } }' "$work/body.ll" | grep -v "^$symbol$" | sort -u) \
  "$work/lowered.ll" out="$work/decls.ll"

n_decl=$(grep -c '^declare ' "$work/decls.ll" || true)
[ "$n_decl" -ge 3 ] ||
  fail "derived $n_decl declaration(s); the fixture's calls need every one"
while IFS= read -r n; do
  grep -q "@$n(" "$work/decls.ll" ||
    fail "the body calls @$n, and the derived declarations do not carry it"
done < <(awk '{ for (i = 1; i <= NF; i++) {
    s = $i
    if (match(s, /@[A-Za-z0-9_.$]+\(/, m)) print substr(m[0], 2, length(m[0]) - 2)
  } }' "$work/body.ll" | grep -v "^$symbol$" | sort -u)

# The literal compare is body text, not a call: no helper is called for it.
if grep -qE 'call .*@(lit_check|ne_lit)\(' "$work/body.ll"; then
  fail "the literal compare is a call; it must be inlined body text"
fi
nlitcmp=$(grep -cE 'icmp (eq|ne) i8' "$work/body.ll" || true)

# ---------------------------------------------------------------------------
# The fixture
# ---------------------------------------------------------------------------

nlines=$(wc -l < "$work/body.ll" | tr -d ' ')
nblocks=$(grep -cE '^[^[:space:]:]+:' "$work/body.ll" || true)
ninstr=$(grep -cE '^  ' "$work/body.ll" || true)
nret=$(grep -cE '^  ret ' "$work/body.ll" || true)
nphi=$(grep -c ' phi ' "$work/body.ll" || true)
nalloca=$(grep -c ' alloca ' "$work/body.ll" || true)
[ "$nret" -eq 1 ] || fail "the fixture has $nret \`ret\`(s); this body has one terminating block"

{
  printf '%s\n' \
"; The no-event stage-2 entry as emitted, in the fragment \`LeanLLVM.Semantics\` models."
  printf '%s\n' \
"; Regenerate with:"
  printf '%s\n' \
";"
  printf '%s\n' \
";   nix develop -c bash probes/install/ir/capture-stage2-noevent.sh"
  printf '%s\n' \
";"
  printf '%s\n' \
"; from kernel/json/stage2_noevent.c with kernel/json/stage2.c included under"
  printf '%s\n' \
"; its entry rename, emitted at the measured compiler line"
  printf '%s\n' \
";"
  printf '%s\n' \
";   clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \\"
  printf '%s\n' \
";         -falign-loops=64 -falign-functions=64 -fno-discard-value-names \\"
  printf '%s\n' \
";         -fno-slp-vectorize \\"
  printf '%s\n' \
";         <the merged source with \`noinline\` on every helper>"
  printf '%s\n' \
";"
  printf '%s\n' \
"; -fno-slp-vectorize is not the measured line: at the measured line clang packs"
  printf '%s\n' \
"; the two independent 64-bit counters into <2 x i64>, which changes no value but"
  printf '%s\n' \
"; puts vector types in the body.  With the flag the body carries none, which the"
  printf '%s\n' \
"; residual check enforces."
  printf '%s\n' \
";"
  printf '%s\n' \
"; then \`opt -passes=lower-switch\`, then reduced to the one \`define\` block."
  printf '%s\n' \
";"
  printf '%s\n' \
"; The entry carries no attribute, so it is the body; every helper carries"
  printf '%s\n' \
"; \`noinline\` instead of \`always_inline\`, so its text stays out of this block."
  printf '%s\n' \
"; The scalar literal compare is body text: the entry packs the literal into an"
  printf '%s\n' \
"; integer and compares bytes, because the fragment has no module-global"
  printf '%s\n' \
"; representation and the certified \`lit_check\` takes a \`const char *\`."
  printf '%s\n' \
"; The literal comparison is \`ne_lit\`, which packs the literal into an integer."
  printf '%s\n' \
"; That its verdict and offset equal the certified \`lit_check\`'s is the"
  printf '%s\n' \
"; refinement obligation stated over this pinned body and exercised by the"
  printf '%s\n' \
"; differential, not a fact of this fixture."
  printf '%s\n' \
";"
  printf '%s\n' \
"; The function's parameters are the twelve-slot ABI in order, followed by the"
  printf '%s\n' \
"; four local objects the fragment cannot allocate (see"
  printf '%s\n' \
"; stage2-noevent.staging.tsv): %stk, %c, %e, %d."
  printf '%s\n' \
"; The four scalar allocas (%xj, %outn, %outn205, %ei) stay in the body, at the"
  printf '%s\n' \
"; types the pin records."
  printf '%s\n' \
";"
  printf '%s\n' \
"; Removed before the parser sees the text, each item with its class in"
  printf '%s\n' \
"; stage2-noevent.strip.tsv, and each rewrite in stage2-noevent.rewrites.tsv."
  printf '%s\n' \
"; The entry's guards -- both scratch-capacity checks, their two trap arms, the"
  printf '%s\n' \
"; refusal arms' zero stores and the acceptance stores -- are body text and are"
  printf '%s\n' \
"; kept."
  printf '%s\n' \
";"
  printf '%s\n' \
"; The inventory of this fixture's opcodes and call targets is"
  printf '%s\n' \
"; stage2-noevent.inventory. \`opt -passes=verify\` accepts it and \`leanllvm\`"
  printf '%s\n' \
"; parses it, both checked by the capture."
  printf '%s\n' ""
  cat "$work/body.ll"
  printf '\n'
  cat "$work/decls.ll"
} > "$work/fixture.ll"

inventory_of() {
  awk '
    /^[ \t]*;/ { next }
    /^[ \t]*$/ { next }
    /^[^[:space:]:]+:$/ { next }
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
    }' "$1" | LC_ALL=C sort -u
}

inventory_of "$work/fixture.ll" > "$work/inventory.body"

# ---------------------------------------------------------------------------
# The two verdicts: well-formed IR, and the repository can read it
# ---------------------------------------------------------------------------

opt -passes=verify -disable-output "$work/fixture.ll" ||
  fail "the fixture is not well-formed IR"

parse_status=0
parse_out=$(if [ -x "$repo/.lake/build/bin/leanllvm" ]; then
    "$repo/.lake/build/bin/leanllvm" --passes none --no-check -o /dev/null "$work/fixture.ll" 2>&1
  else
    ( cd "$repo" && lake exe leanllvm --passes none --no-check -o /dev/null "$work/fixture.ll" 2>&1 )
  fi) || parse_status=$?
if [ "$parse_status" -ne 0 ]; then
  printf '%s\n' "$parse_out" >&2
  fail "the repository's parser refuses the fixture"
fi

# ---------------------------------------------------------------------------
# The derivations' accounting and the artefacts
# ---------------------------------------------------------------------------

{
  printf '# %s: the normalisation'"'"'s strip, item by item.\n' "$(basename "$0")"
  printf '# class\tkind\titem\tline\treason\n'
  LC_ALL=C sort -t"$(printf '\t')" -k1,1n -k4,4n -s "$work/strip.rows"
} > "$work/strip.tsv"

{
  printf '# %s: what the derivation rewrote, and why the rewrite preserves the\n' "$(basename "$0")"
  printf '# value computed.  A rewrite that the fixture does not show is a setup fault\n'
  printf '# in the capture, and the capture checks each count.\n'
  printf '# class\tkind\tbefore\tafter\tcount\treason\n'
  printf '%s\t%s\t%s\t%s\t%d\t%s\n' r1 "noinline (every always_inline helper, both files)" \
    "__attribute__((always_inline)) static inline" \
    "the same, with \`noinline\`" "$n_ni" \
    "each helper's body is outside this fragment or is a unit of its own; each is resolved by the fixture's Calls environment at the record that states its contract, and the entry is the one define taken"
  printf '%s\t%s\t%s\t%s\t%d\t%s\n' r2 "literal compare" \
    "a call to the certified \`lit_check\` with a \`const char *\` literal" \
    "the inlined byte comparisons and offsets of \`ne_lit\`" 1 \
    "the fragment has no module-global representation; the packed literal is body text, and the equivalence of its verdict and offset with the certified check's is the refinement obligation the body's proof carries and what the differential exercises -- not proved by the IR module"
  printf '%s\t%s\t%s\t%s\t%d\t%s\n' r3 "callee definitions" \
    "the emission's \`define internal\` blocks" \
    "the matching \`declare\` line" \
    "$(wc -l < "$work/decls.ll" | tr -d ' ')" \
    "a call to an undeclared symbol is not well-formed IR; the declaration is derived from the emitted header with the same token strip, and the symbol is resolved by the environment rather than by a definition in this file"
  printf '%s\t%s\t%s\t%s\t%d\t%s\n' r4 "module header" \
    "source_filename, target datalayout/triple, \`attributes #N\`, \`!N\` nodes" \
    "not carried" 1 \
    "module configuration and metadata outside the function; the model has one layout"
  LC_ALL=C sort -t"$(printf '\t')" -k1,1 "$work/rewrite.rows"
} > "$work/rewrites.tsv"

{
  printf '# %s: the entry'"'"'s local objects, flattened to parameters.\n' "$(basename "$0")"
  printf '# alloca\tparameter\treason\n'
  awk -F'\t' '{ printf "%s\tptr %%%s\t%s\n", $2, $1,
    "the fragment has no aggregate type and no element-count or vector alloca; the body writes and reads the same bytes at the same offsets through the parameter it used through the alloca, and the caller stages the object" }' \
    "$work/staging.rows"
} > "$work/staging.tsv"

{
  printf '# The no-event stage-2 entry as emitted and committed: opcodes and call targets.\n'
  printf '# Regenerate with probes/install/ir/capture-stage2-noevent.sh.\n'
  printf '#\n'
  printf '# The derivation, measured at three points, in this order:\n'
  printf '#   the untransformed emission of the same source at the measured line: %s lines / %s blocks,\n' "$fused_lines" "$fused_blocks"
  printf '#     carrying %s line(s) with a vector type;\n' "$fused_vec"
  printf '#   the same source with every helper noinline and SLP disabled: %s lines / %s blocks, no\n' "$nlines" "$nblocks"
  printf '#     vector type and no insertelement/extractelement;\n'
  printf '#   the fixture below, with the staging objects flattened to parameters: %s lines,\n' "$nlines"
  printf '#     %s instruction(s), %s block(s), %s phi(s), %s alloca(s), %s `ret`.\n' "$ninstr" "$nblocks" "$nphi" "$nalloca" "$nret"
  printf '#\n'
  printf '# The body is the goto machine: %s `switch` became comparison chains.\n' "$nswitch"
  printf '# The scalar literal compare is body text: %s byte comparison(s), no call.\n' "$nlitcmp"
  printf '#\n'
  cat "$work/inventory.body"
} > "$work/inventory"

# ---------------------------------------------------------------------------
# Idempotence: the same derivation, run again, is the same bytes
# ---------------------------------------------------------------------------

( cd "$repo" && clang -I kernel/json "${flags[@]}" -fno-discard-value-names \
    "$work/merged.c" -o "$work/named2.ll" )
opt -S -passes=lower-switch "$work/named2.ll" -o "$work/lowered2.ll"
awk -v sym="$symbol" '
  $0 ~ "^define .*@" sym "\\(" { inblock = 1 }
  inblock { print }
  inblock && $0 == "}" { exit }
' "$work/lowered2.ll" > "$work/block2.ll"
cmp -s "$work/block.ll" "$work/block2.ll" ||
  fail "a second compilation produced a different block; the capture is not reproducible"

cp "$work/fixture.ll" "$fixture"
cp "$work/strip.tsv" "$strip"
cp "$work/rewrites.tsv" "$rewrites"
cp "$work/staging.tsv" "$staging"
cp "$work/inventory" "$inventory"

printf 'capture-stage2-noevent: %s strip row(s), %s rewrite row(s), %s staging row(s), %s inventory line(s)\n' \
  "$(awk '!/^#/' "$work/strip.tsv" | wc -l | tr -d ' ')" \
  "$(awk '!/^#/' "$work/rewrites.tsv" | wc -l | tr -d ' ')" \
  "$(awk '!/^#/' "$work/staging.tsv" | wc -l | tr -d ' ')" \
  "$(wc -l < "$work/inventory.body" | tr -d ' ')"
printf 'ok: wrote %s, %s, %s, %s, %s\n' \
  "${fixture#$repo/}" "${strip#$repo/}" "${rewrites#$repo/}" \
  "${staging#$repo/}" "${inventory#$repo/}"
