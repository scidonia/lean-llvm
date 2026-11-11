#!/usr/bin/env bash
# Regenerate the stage-2 walk's emitted-IR fixture and its four inventories in
# probes/install/ir/.
#
# Run through the flake, from the repository root:
#
#   nix develop -c bash probes/install/ir/capture-stage2.sh
#
# Input
#   kernel/json/stage2.c            the stage-2 unit: `s2_walk`'s per-entry
#                                   dispatch, and the ABI wrapper
#                                   `leanllvm_json_stage2` that stages the
#                                   caller's buffers into it
#
# Output (all five in the same run, from the same compilation)
#   stage2.candidate.ll             the fixture: the wrapper's `define` block,
#                                   with the walk inlined, its binary64 helpers
#                                   out of line, the staging objects flattened
#                                   to parameters, and the syntax listed below
#                                   removed
#   stage2.strip.tsv                what the normalisation removed, item by
#                                   item, by class, derived by aligning the
#                                   emission with the text this script emits
#   stage2.rewrites.tsv             what it rewrote rather than removed, with
#                                   the reason each rewrite preserves the value
#                                   computed
#   stage2.staging.tsv              the eight local objects that became
#                                   parameters: the alloca the emission holds,
#                                   the parameter that replaces it, and the
#                                   offset argument for each array read
#   stage2.inventory                the fixture's own opcodes and call targets
#
# `kernel/json/identity/inventory.sh` is the gate for the four stage-1 units;
# this unit has no arm there, so this script's own checks are the derivation's
# gate: it refuses (exit 3) on an unclassified removal, an unattributed rewrite,
# a guard line that disappeared, a fixture that does not parse, and a second
# derivation that is not byte-identical to the first.
#
# --- Why the measured compiler line, and the one flag beyond it -----------
#
# The fixture is the emission the measured build compiles, not a portable
# re-phrasing of it: `kernel/json/bench/paired.sh` and the route's object arm
# compile the same C at the same flags.  The line is `build49.sh:17`'s:
#
#   clang -O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
#         -falign-functions=64
#
# `-fno-discard-value-names` is added to it.  It is a naming flag: it writes the
# source's value names and, because a named entry block is emitted with its
# label, it supplies the labels the parser requires.  That it changes no
# instruction is checked here rather than asserted: the same source is emitted
# with and without the flag, every register name is replaced by one placeholder
# and label lines are dropped, and the two texts must be identical.
#
# --- Why the helpers are out of line, and what that costs -----------------
#
# As emitted, `@leanllvm_json_stage2` is 1754 lines in 233 blocks and carries
# **binary64**: `od_scalar_value` (`stage2.c:929`) and `num_fast_el1`
# (`:379`) are `__attribute__((always_inline))`, so the number path's
# `alloca double`, `uitofp`, `fmul`, `fdiv`, `fneg`, `select double` and
# `phi double` are inlined into the only function this unit has.  `Ty` and
# `Semantics` have no floating point, so no strip reaches a parseable fixture of
# that text: the FP is semantic, not surface.
#
# The derivation therefore compiles a *transform of the source* in which the
# `always_inline` attribute is replaced by `noinline` on every helper except
# `s2_walk` itself.  `s2_walk` still inlines -- the mode is a constant at the
# wrapper's call site, so the branches the mode does not take fold away -- and
# every helper leaves the body as a call:
#
#   not inlined                     why it is a callee and not body text
#   el_pack, el_exact, num_d8_el1,  the number path: binary64 arithmetic the
#   num_fast_el1, od_scalar_value    fragment has no operations for; its
#                                   contract is the tier composition proved in
#                                   `LeanLLVM/Refinement/JsonStage2Body.lean`
#                                   (`numFastEmitted_strtodSpec`)
#   num_scan                         binary64 conversion and the SSE word
#                                   kernels; the same reason
#   touch_bytes, touch_u64           cursor value helpers, not the walk
#   s2_value_pos, s2_after_value,    the value-position rules; each is a
#   s2_string_body, s2_string_touch  function of the walk's state, and a call
#                                   keeps its interface visible
#
# Measured, and checked below rather than asserted: the fused emission is 1754
# lines/233 blocks and the fixture is 944 lines/165 blocks before the parameter
# flattening, with **zero** binary64 or vector operations in the body.  So the
# fixture is the walk's text **with its intra-unit helper boundaries preserved
# and the mode constant**, not the measured object's text: the object inlines
# these helpers, and the distance between the two is the call composition, which
# is the composition this development is built for.  The fixture says so in its
# own header.
#
# --- The staging objects become parameters: the one flattening -------------
#
# The fragment has no aggregate type, no element-count `alloca` and no vector
# `alloca`, so eight locals the walk declares cannot be expressed:
#
#   %d.i     alloca double         the number path's output slot
#   %c.i     alloca %struct.OdCur  the cursor record
#   %ctype.i alloca [520 x i8]     the container-type stack
#   %cst.i   alloca [520 x i8]     the container-state stack
#   %t352.i  alloca %struct.OdTok  the scalar token
#   %s       alloca %struct.S2     the walk's own staging record
#   %z       alloca %struct.ZOut   the caller's arena and event stream
#   %e       alloca %struct.Err    the refusal record
#
# Each becomes an appended `ptr` parameter, so the fixture's function takes the
# ABI's thirteen arguments followed by these eight, in the order the emission
# declares them.  The rewrite preserves the value computed because each object's
# address is the same object: the body writes and reads the same bytes at the
# same offsets through the parameter it wrote and read through the alloca, and
# the caller's staging of those eight objects is an extension of the caller's
# obligation, not a change to the walk's arithmetic.  The precedent is the entry
# unit's `%tab`: `capture-entry.sh` turns that unit's static table into a
# parameter, and `JsonPipelineIR.Γ_entry_pos8at` re-indexes the record at the
# appended argument.  The re-indexing adapter for this unit is stated with the
# record, in `LeanLLVM/Refinement/JsonStage2IR.lean`, and the distance from the
# thirteen-argument ABI to the twenty-one-argument fixture is a mapping between
# two named interfaces rather than an implied one.
#
# --- The instruction rewrites, each with its reason -----------------------
#
#   1. `getelementptr inbounds [520 x i8], ptr %p, i64 0, i64 %i`
#      -> `getelementptr inbounds i8, ptr %p, i64 %i`
#      The two forms address `%p + 0 * 520 + i * 1` and `%p + i * 1`: the offset
#      from the base is `i` on both sides, and only the element type written
#      differs.  Eleven sites, all constant-first-index.
#   2. `@.str.17`, `@.str.18`, `@.str.19`
#      -> `null`
#      The three refusal messages the walk passes to `od_fail`.  The fragment has
#      no module globals; the pointer is a call argument, and no clause of the
#      record reads `e->msg`.  The value stored there is unconstrained, so the
#      fixture writes a `null` operand.  Three sites, all operands of one `phi`.
#   3. `%d = call i64 @llvm.umin.i64(i64 %a, i64 %b)`
#      -> `%d.min = icmp ult i64 %a, %b` ; `%d = select i1 %d.min, i64 %a, i64 %b`
#      The parser models `llvm.umin` at `i32` only and refuses the `i64` width by
#      name.  The two instructions are the intrinsic's definition -- the smaller
#      of two unsigned values -- so the rewrite is an unfolding, not an
#      approximation.  One site.
#   4. `switch` -> `opt -passes=lower-switch`, run before the block is taken.
#      The parser has no `switch`; the pass lowers it to the comparison chain and
#      the branches LLVM would lower it to.  The block structure of the fixture
#      is therefore the lowered structure, and the inventory says which form the
#      reader is looking at.  One switch in the walk.
#   5. `call fastcc` -> `call` (a class of the strip below, not a rewrite of the
#      instructions): the parser refuses a calling convention on a call, and the
#      `Calls` environment decides how a symbol is reached.  The callee
#      declarations are derived from the emission with the same token removed.
#
# Nothing else is rewritten.  In particular the walk's own guards are kept: the
# two reserve checks (`out_reserve` on the event stream, `z_arena_reserve` on the
# arena), their `__builtin_trap` fault arms (four `@llvm.trap` calls in the
# fixture), the thirteen-byte record's four stores, and the number dispatch's
# counters are body text, and a fixture that dropped one would pin a different
# program.  The number conversion's two caps (`idig < 19`, `exp10 < 100000`)
# live in `od_scalar_value`, which this derivation makes a callee; they are
# stated at that callee's contract rather than in this body, and the module says
# so.
#
# --- The strip: what is removed and why it is not the computation ---------
#
# The removal is computed, not transcribed: `classify.awk` aligns the emission's
# tokens with the text this script emits, requires every removed run to match one
# of the classes below (`3` refuses otherwise), and rebuilds the emitted line
# from the kept tokens and the recorded runs; a line that does not rebuild
# byte-identically is a setup fault.  The classes:
#
#   1  argument, parameter and call-result attributes: `noundef`, `nonnull`,
#      `readonly`, `writeonly`, `noalias`, `zeroext`, `signext`, `returned`,
#      `dereferenceable(…)`, `initializes(…)`, `captures(…)`, `range(…)`,
#      `nofpclass(…)`, `immarg` -- a promise about an argument or a result,
#      re-established by the theorem's hypotheses
#   2  function-header surface: `local_unnamed_addr`, `unnamed_addr`, `#N`, and
#      the header's `align N` -- linkage and code placement, for which the model
#      has no semantics
#   3  an attribute-group reference on a call (`#19`): the group's target-feature
#      and memory promise, removed with the module header that defined it
#   4  instruction flags that constrain: `nuw`, `nsw`, `nusw`, `disjoint`,
#      `nneg` -- each excludes inputs, so stripping *widens*, and the widening is
#      recorded rather than re-established
#   5  memory and analysis metadata: `!tbaa` and the module's `!N` nodes -- the
#      model has no aliasing relation to read them with
#   9  instruction-level alignment (`load`, `store`, `alloca`): the parser's
#      instructions have no alignment field, and the model addresses bytes
#   10 a call's calling convention (`fastcc`): no calling convention is modelled;
#      the environment decides which definition answers
#
# Whole lines are not removed from the block.  The module's header, its attribute
# groups, its metadata nodes and the other `define` blocks are simply not taken:
# the fixture is one `define` and the declarations its calls need, and each of
# those omissions is a row in stage2.rewrites.tsv (a definition replaced by its
# declaration is a rewrite of the module, not a token strip of the body).
#
# Exit status: 0 when the five artefacts are written; 3 when an input is missing
# or a derivation check fails -- the same code the rest of the route uses for an
# unusable input.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)

src=kernel/json/stage2.c
symbol=leanllvm_json_stage2
fixture=$here/stage2.candidate.ll
strip=$here/stage2.strip.tsv
rewrites=$here/stage2.rewrites.tsv
staging=$here/stage2.staging.tsv
inventory=$here/stage2.inventory

fail() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

[ -f "$repo/$src" ] || fail "absent: $repo/$src"
command -v clang >/dev/null 2>&1 || fail "clang is not on PATH"
command -v opt >/dev/null 2>&1 || fail "opt is not on PATH"

work=$(mktemp -d "$repo/.lake/tmp-stage2-capture.XXXXXX" 2>/dev/null) ||
  work=$(mktemp -d) ||
  fail "cannot create a work directory"
trap 'rm -rf "$work"' EXIT

flags=(-S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11
       -falign-loops=64 -falign-functions=64)
compile() { ( cd "$repo" && clang -I kernel/json "$@" ); }

# The eight locals that become parameters, in the emission's order.  A ninth is a
# shape change and is refused rather than flattened without a reason.
staging_names=(d.i c.i ctype.i cst.i t352.i s z e)

# ---------------------------------------------------------------------------
# The source transform: `noinline` on every helper except `s2_walk`
# ---------------------------------------------------------------------------

sed -e 's/__attribute__((always_inline)) static inline/__attribute__((noinline)) static inline/g' \
    -e 's/#define EL_ENTRY __attribute__((always_inline)) static inline/#define EL_ENTRY __attribute__((noinline)) static inline/' \
    "$repo/$src" > "$work/step1.c"

awk '{ if (hold) { print "__attribute__((always_inline)) static inline uint64_t"; hold = 0 }
       if ($0 == "__attribute__((noinline)) static inline uint64_t") { hold = 1; next }
       print }
     END { if (hold) exit 1 }' "$work/step1.c" > "$work/stage2.noinline.c" ||
  fail "the s2_walk attribute was not restored; the transform is not the one this script describes"

n_al=$(grep -c 'always_inline' "$work/stage2.noinline.c" || true)
n_ni=$(grep -c '__attribute__((noinline))' "$work/stage2.noinline.c" || true)
[ "$n_al" -eq 2 ] ||
  fail "the transformed source carries $n_al 'always_inline' occurrences; the transform leaves the comment and s2_walk's attribute, so 2"
[ "$n_ni" -eq 12 ] ||
  fail "the transformed source carries $n_ni 'noinline' occurrences; the always_inline set is 12"
grep -A1 '^__attribute__((always_inline)) static inline uint64_t$' "$work/stage2.noinline.c" |
  grep -q '^s2_walk(' ||
  fail "the one forced-inline function is not s2_walk"

awk '/__attribute__\(\(noinline\)\)/ {
       line = $0
       sub(/.*__attribute__\(\(noinline\)\)/, "", line)
       while (line !~ /\(/) { if ((getline nxt) <= 0) exit 1; line = line " " nxt }
       if (match(line, /[A-Za-z_][A-Za-z0-9_]*\(/))
         print substr(line, RSTART, RLENGTH - 1)
     }' "$work/stage2.noinline.c" | sort > "$work/noinline.names" || true
n_noinline=$(wc -l < "$work/noinline.names" | tr -d ' ')
[ "$n_noinline" -eq 12 ] ||
  fail "read $n_noinline noinline symbol name(s), not 12"

# ---------------------------------------------------------------------------
# The emission, and the naming flag's claim
# ---------------------------------------------------------------------------

compile "${flags[@]}" -fno-discard-value-names "$work/stage2.noinline.c" -o "$work/named.ll"
compile "${flags[@]}" "$work/stage2.noinline.c" -o "$work/plain.ll"

neutralise() { # <file>
  # Register names and block labels are the naming flag's whole effect; module
  # metadata and attribute groups are not instructions (and are not carried into
  # the fixture), so they are dropped rather than compared.
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
[ "$nswitch" -ge 1 ] ||
  fail "the emission carries no \`switch\`; the lower-switch step is not the one this script describes"

opt -S -passes=lower-switch "$work/named.ll" -o "$work/lowered.ll" ||
  fail "opt refused to lower the switch"

# The wrapper's `define` block, verbatim.
awk -v sym="$symbol" '
  $0 ~ "^define .*@" sym "\\(" { inblock = 1 }
  inblock { print }
  inblock && $0 == "}" { exit }
' "$work/lowered.ll" > "$work/block.ll"
[ -s "$work/block.ll" ] || fail "the emission has no \`define\` block for @$symbol"

# The evidence for "the FP is semantic, not surface": the fused emission, at the
# same flags, measured and recorded beside the fixture.
compile "${flags[@]}" -fno-discard-value-names "$repo/$src" -o "$work/fused.ll"
awk -v sym="$symbol" '
  $0 ~ "^define .*@" sym "\\(" { inblock = 1 }
  inblock { print }
  inblock && $0 == "}" { exit }
' "$work/fused.ll" > "$work/fused.block.ll"
fused_lines=$(wc -l < "$work/fused.block.ll" | tr -d ' ')
fused_blocks=$(grep -cE '^[A-Za-z0-9_.]+:' "$work/fused.block.ll" || true)
fused_fp=$(grep -cE '(^|[^a-z])double([^a-z]|$)|\b(fadd|fsub|fmul|fdiv|fneg|uitofp|sitofp|fpext|fptrunc|fcmp)\b' "$work/fused.block.ll" || true)
[ "$fused_fp" -gt 0 ] ||
  fail "the fused emission carries no binary64 text; the derivation's premise is not the file's"

# ---------------------------------------------------------------------------
# The strip: attributes and surface, itemised and rebuilt
# ---------------------------------------------------------------------------

cat > "$work/classify.awk" <<'AWK'
BEGIN {
    # Brackets stay inside tokens: `[520 x i8]` is a token pair, so a class that
    # removes the token after it does not take the bracket with it.
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
        # Greedy alignment: a token survives when it equals the body's next
        # token; otherwise it must be a class's removal.  The rebuild below is
        # what makes the greedy choice safe: a misalignment cannot rebuild the
        # emitted line.
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

# The emitted line rebuilt from the kept tokens only, with the separators of the
# kept tokens; after a removed run the preceding kept token takes the separator
# that followed the run, which is what a comma-then-attribute removal needs.
function rebuild(nt, nd,   k, s, m, q) {
    s = sep[0]
    for (k = 1; k <= nt; k++) {
        if (k in del) continue
        m = k + 1
        while (m <= nt && (m in del)) m++
        if (m > k + 1) {
            # A comma that introduced the removed run goes with it; anything
            # else in the separator (a closing paren, a space) stays.
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

# The last token of the class item starting at `a`, or 0; the class is left in
# `mc_class`.  A comma that separates an item from the tokens it followed is part
# of the item: removing `align 8` from `ptr %p, align 8` removes the comma too,
# and the rebuild below is what proves the attribution exact.
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
        # An argument's alignment, or a load's, store's or alloca's: the same
        # token in two places, and the class says which promise is dropped.
        mc_class = (iscall) ? 1 : 9
        return a + 1
    }
    if (t[a] in c10word) { mc_class = 10; return a }
    return 0
}
AWK

# The strip itself is the same class list applied by sed: the classifier derives
# the record from the difference, and the script refuses if the difference holds
# an item the classes do not name.
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

nstripped=$(wc -l < "$work/stripped.ll" | tr -d ' ')
awk -f "$work/classify.awk" "$work/block.ll" "$work/stripped.ll" > "$work/strip.rows" ||
  fail "the removal could not be attributed to classes (see above)"
nstrip=$(wc -l < "$work/strip.rows" | tr -d ' ')
[ "$nstrip" -gt 0 ] || fail "the strip removed nothing; the emission's surface is not the fixture's"

# ---------------------------------------------------------------------------
# The rewrites: allocation flattening, array reads, messages, umin
# ---------------------------------------------------------------------------

# 1. The eight staging allocas become parameters.
awk -v names="${staging_names[*]}" '
BEGIN { n = split(names, want, " "); for (k = 1; k <= n; k++) expected[want[k]] = 1 }
{
  if (match($0, /^  %([A-Za-z0-9_.]+) = alloca (%struct\.[A-Za-z0-9_]+|\[520 x i8\]|double)$/, m)) {
    seen[m[1]]++
    stagerows[++nstage] = m[1] "\t" $0
    next
  }
  print
}
END {
  bad = 0
  for (k = 1; k <= n; k++) {
    if (!(want[k] in seen)) { printf "SETUP: the emission has no staging alloca %%%s\n", want[k] > "/dev/stderr"; bad = 1 }
  }
  for (name in seen) {
    if (!(name in expected)) { printf "SETUP: the emission stages %%%s, which is not a recorded staging object\n", name > "/dev/stderr"; bad = 1 }
    if (seen[name] != 1) { printf "SETUP: %%%s is allocated %d times\n", name, seen[name] > "/dev/stderr"; bad = 1 }
  }
  for (k = 1; k <= nstage; k++) print stagerows[k] > (outfile)
  exit bad
}' outfile="$work/staging.rows" "$work/stripped.ll" > "$work/nostaging.ll" ||
  fail "the staging allocas are not the eight this script names"

# The header gains the eight parameters, in the emission's order.
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

# 2. `[520 x i8]` reads become `i8` reads; 3. the messages become `null`;
# 4. `umin.i64` unfolds to its definition.
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
  if (match(line, /^  (%[A-Za-z0-9_.]+) = call i64 @llvm\.umin\.i64\(i64 (%[A-Za-z0-9_.]+), i64 (%[A-Za-z0-9_.]+)\)$/, m)) {
    nmin++
    after = m[1] ".min = icmp ult i64 " m[2] ", " m[3] "; " m[1] " = select i1 " m[1] ".min, i64 " m[2] ", i64 " m[3]
    printf "r7\tumin unfolding\t%s\t%s\t1\t%s\n", $0, after,
      "llvm.umin is modelled at i32 only and the parser refuses the i64 width by name; icmp ult plus select is the definition of the intrinsic, so the rewrite is an unfolding and not an approximation" >> rw
    print "  " m[1] ".min = icmp ult i64 " m[2] ", " m[3]
    print "  " m[1] " = select i1 " m[1] ".min, i64 " m[2] ", i64 " m[3]
    next
  }
  n = gsub(/@\.str\.(17|18|19)/, "null", line)
  if (n > 0) {
    nstr += n
    printf "r6\trefusal message\t%s\t%s\t%d\t%s\n", $0, line, n,
      "the fragment has no module globals; the pointer is a call argument and no clause of the record reads e->msg, so the value stored there is unconstrained" >> rw
  }
  print line
}
END {
  printf "%d %d %d\n", ngep, nstr, nmin > counts
}' rw="$work/rewrite.rows" counts="$work/rewrite.counts" "$work/headered.ll" > "$work/body.ll"

read -r ngep nstr nmin < "$work/rewrite.counts"
[ "$ngep" -eq 11 ] || fail "rewrote $ngep array read(s); the emission holds 11"
[ "$nstr" -eq 3 ] || fail "rewrote $nstr message operand(s); the walk passes 3"
[ "$nmin" -eq 1 ] || fail "rewrote $nmin umin call(s); the walk holds 1"

# No residual construct the rewrites exist to remove.
for pat in '%struct\.' '\[520 x i8\]' 'alloca double' '@\.str\.' 'umin\.i64' '\bswitch\b' 'fastcc'; do
  if grep -qE "$pat" "$work/body.ll"; then
    fail "the fixture still carries '$pat'; a rewrite class is missing"
  fi
done

# The walk's own guards are body text and are kept: the two reserves' fault arms
# and the record's thirteen bytes.
ntrap=$(grep -c 'call void @llvm.trap()' "$work/body.ll" || true)
[ "$ntrap" -eq 4 ] ||
  fail "the fixture carries $ntrap trap call(s); the walk's four fault arms are its own guards"
# Both reserves are inlined in the walk: the arena's check adds `US_SLACK` (64)
# to the escaped body's length and compares against `%acap`, and the event
# stream's adds the record's thirteen bytes and compares against `%cap`.
grep -qE 'add i64 [^,]+, 64$' "$work/body.ll" ||
  fail "the arena reserve's slack add is not in the fixture; the walk's own guard was removed"
grep -qE 'add i64 [^,]+, 13$' "$work/body.ll" ||
  fail "the thirteen-byte record's add is not in the fixture"
for slot in alen acap len cap; do
  grep -q "ptr %$slot" "$work/body.ll" ||
    fail "the walk no longer reads %$slot; a reserve check is not in the fixture"
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
    gsub(/ (noundef|readonly|writeonly|nonnull|noalias|zeroext|signext|returned|immcat|immarg)/, "", line)
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
[ "$n_decl" -ge 8 ] ||
  fail "derived $n_decl declaration(s); the fixture's calls need every one"
while IFS= read -r n; do
  grep -q "@$n(" "$work/decls.ll" ||
    fail "the body calls @$n, and the derived declarations do not carry it"
done < <(awk '{ for (i = 1; i <= NF; i++) {
    s = $i
    if (match(s, /@[A-Za-z0-9_.$]+\(/, m)) print substr(m[0], 2, length(m[0]) - 2)
  } }' "$work/body.ll" | grep -v "^$symbol$" | sort -u)

# ---------------------------------------------------------------------------
# The fixture
# ---------------------------------------------------------------------------

nlines=$(wc -l < "$work/body.ll" | tr -d ' ')
nblocks=$(grep -cE '^[A-Za-z0-9_.]+:' "$work/body.ll" || true)
ninstr=$(grep -cE '^  ' "$work/body.ll" || true)
nret=$(grep -cE '^  ret ' "$work/body.ll" || true)
nphi=$(grep -c ' phi ' "$work/body.ll" || true)
nalloca=$(grep -c ' alloca ' "$work/body.ll" || true)
[ "$nret" -eq 1 ] || fail "the fixture has $nret \`ret\`s; a function has one per terminating block and this body has one"

{
  printf '%s\n' \
"; The stage-2 walk as emitted, in the fragment \`LeanLLVM.Semantics\` models."
  printf '%s\n' \
"; Regenerate with:"
  printf '%s\n' \
";"
  printf '%s\n' \
";   nix develop -c bash probes/install/ir/capture-stage2.sh"
  printf '%s\n' \
";"
  printf '%s\n' \
"; from kernel/json/stage2.c, emitted at the measured compiler line"
  printf '%s\n' \
";"
  printf '%s\n' \
";   clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \\"
  printf '%s\n' \
";         -falign-loops=64 -falign-functions=64 -fno-discard-value-names \\"
  printf '%s\n' \
";         <stage2.c with \`noinline\` on every helper except s2_walk>"
  printf '%s\n' \
";"
  printf '%s\n' \
"; then \`opt -passes=lower-switch\`, then reduced to the one \`define\` block."
  printf '%s\n' \
";"
  printf '%s\n' \
"; The source transform is part of the derivation, not of the file: \`s2_walk\`"
  printf '%s\n' \
"; keeps \`__attribute__((always_inline))\` and inlines into the wrapper, where the"
  printf '%s\n' \
"; mode is the constant \`S2_VAL | S2_STR | S2_EV\` and the branches that mode does"
  printf '%s\n' \
"; not take fold away; the twelve helpers listed in stage2.rewrites.tsv carry"
  printf '%s\n' \
"; \`noinline\` instead, so their bodies stay out of this text.  That boundary is"
  printf '%s\n' \
"; the point: the number path's arithmetic is binary64, which this fragment has no"
  printf '%s\n' \
"; operations for, and its contract is the tier composition proved in"
  printf '%s\n' \
"; LeanLLVM/Refinement/JsonStage2Body.lean (\`numFastEmitted_strtodSpec\`)."
  printf '%s\n' \
";"
  printf '%s\n' \
"; So this is the walk's text with its intra-unit helper boundaries preserved and"
  printf '%s\n' \
"; the mode constant: NOT the measured object's text, which inlines the helpers."
  printf '%s\n' \
"; Measured: the fused emission of the same source is ${fused_lines} lines and"
  printf '%s\n' \
"; ${fused_blocks} blocks and carries binary64; the body below is ${nlines} lines and"
  printf '%s\n' \
"; ${nblocks} blocks and carries none."
  printf '%s\n' \
";"
  printf '%s\n' \
"; The function's parameters are \`stage2.h\`'s thirteen in their ABI order,"
  printf '%s\n' \
"; followed by the eight local objects the fragment cannot allocate (see"
  printf '%s\n' \
"; stage2.staging.tsv): %d.i, %c.i, %ctype.i, %cst.i, %t352.i, %s, %z, %e."
  printf '%s\n' \
"; The re-indexing between the twenty-one-argument body and the thirteen-argument"
  printf '%s\n' \
"; ABI is stated in LeanLLVM/Refinement/JsonStage2IR.lean, and the pin there is"
  printf '%s\n' \
"; what makes this text the body those theorems run."
  printf '%s\n' \
";"
  printf '%s\n' \
"; Removed before the parser sees the text, each item with its class in"
  printf '%s\n' \
"; stage2.strip.tsv, and each rewrite in stage2.rewrites.tsv; the walk's own"
  printf '%s\n' \
"; guards (both reserves, their four trap arms, the thirteen-byte record) are"
  printf '%s\n' \
"; body text and are kept."
  printf '%s\n' \
";"
  printf '%s\n' \
"; The inventory of this fixture's opcodes and call targets is"
  printf '%s\n' \
"; stage2.inventory. \`opt -passes=verify\` accepts it and \`leanllvm\` parses it,"
  printf '%s\n' \
"; both checked by the capture."
  printf '%s\n' ""
  cat "$work/body.ll"
  printf '\n'
  cat "$work/decls.ll"
} > "$work/fixture.ll"

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
  printf '%s\t%s\t%s\t%s\t%d\t%s\n' r1 "s2_walk forced inline" \
    "__attribute__((always_inline)) static inline uint64_t s2_walk(...)" \
    "the same, and it is the only forced-inline function" 1 \
    "the mode is a constant at the wrapper's call site, so inlining the walk folds the branches that mode does not take; every other helper is noinline, which is why the walk's text is the body and the helpers are calls"
  printf '%s\t%s\t%s\t%s\t%d\t%s\n' r2 "noinline (12 helpers)" \
    "$(paste -sd' ' "$work/noinline.names")" \
    "each a call in the fixture" 12 \
    "their bodies are outside this fragment (binary64, vector word kernels) or are units of their own; each is resolved by the fixture's Calls environment at the record or tier theorem that states its contract"
  printf '%s\t%s\t%s\t%s\t%d\t%s\n' r3 "callee definitions" \
    "the emission's \`define internal\` blocks" \
    "the matching \`declare\` line" \
    "$(wc -l < "$work/decls.ll" | tr -d ' ')" \
    "a call to an undeclared symbol is not well-formed IR; the declaration is derived from the emitted header with the same token strip, and the symbol is resolved by the environment rather than by a definition in this file"
  printf '%s\t%s\t%s\t%s\t%d\t%s\n' r4 "module header" \
    "source_filename, target datalayout/triple, \`attributes #N\`, \`!N\` nodes" \
    "not carried" 1 \
    "module configuration and metadata outside the function; the datalayout is recorded here and in PROVENANCE.md, and the model has one layout"
  LC_ALL=C sort -t"$(printf '\t')" -k1,1 "$work/rewrite.rows"
} > "$work/rewrites.tsv"

{
  printf '# %s: the walk'"'"'s local objects, flattened to parameters.\n' "$(basename "$0")"
  printf '# alloca\tparameter\treason\n'
  awk -F'\t' '{ printf "%s\tptr %%%s\t%s\n", $2, $1,
    "the fragment has no aggregate type and no element-count or vector alloca; the body writes and reads the same bytes at the same offsets through the parameter it used through the alloca, and the caller stages the object" }' \
    "$work/staging.rows"
} > "$work/staging.tsv"

{
  printf '# The stage-2 walk as emitted and committed: opcodes and call targets.\n'
  printf '# Regenerate with probes/install/ir/capture-stage2.sh.\n'
  printf '#\n'
  printf '# The derivation, measured at three points, in this order:\n'
  printf '#   the fused emission of the same source at the same flags: %s lines / %s blocks,\n' "$fused_lines" "$fused_blocks"
  printf '#     carrying binary64 (the always_inline number path);\n'
  printf '#   the same source with the twelve helpers noinline: %s lines / %s blocks, no\n' "$nstripped" "$nblocks"
  printf '#     binary64 and no vector operation -- this is the point that makes "the FP is\n'
  printf '#     semantic, not surface" a measurement;\n'
  printf '#   the fixture below, with the staging objects flattened to parameters: %s lines,\n' "$nlines"
  printf '#     %s instruction(s), %s block(s), %s phi(s), %s alloca(s), %s `ret`.\n' "$ninstr" "$nblocks" "$nphi" "$nalloca" "$nret"
  printf '#\n'
  printf '# The body is the switch-lowered form: %s `switch` became comparison chains.\n' "$nswitch"
  printf '#\n'
  cat "$work/inventory.body"
} > "$work/inventory"

# ---------------------------------------------------------------------------
# Idempotence: the same derivation, run again, is the same bytes
# ---------------------------------------------------------------------------

( cd "$repo" && clang -I kernel/json "${flags[@]}" -fno-discard-value-names \
    "$work/stage2.noinline.c" -o "$work/named2.ll" )
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

printf 'capture-stage2: %s strip row(s), %s rewrite row(s), %s staging row(s), %s inventory line(s)\n' \
  "$(awk '!/^#/' "$work/strip.tsv" | wc -l | tr -d ' ')" \
  "$(awk '!/^#/' "$work/rewrites.tsv" | wc -l | tr -d ' ')" \
  "$(awk '!/^#/' "$work/staging.tsv" | wc -l | tr -d ' ')" \
  "$(wc -l < "$work/inventory.body" | tr -d ' ')"
printf 'ok: wrote %s, %s, %s, %s, %s\n' \
  "${fixture#$repo/}" "${strip#$repo/}" "${rewrites#$repo/}" \
  "${staging#$repo/}" "${inventory#$repo/}"
