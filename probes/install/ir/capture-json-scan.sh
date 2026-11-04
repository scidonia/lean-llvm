#!/usr/bin/env bash
# Regenerate the window scanner's emitted-IR fixture in probes/install/ir/.
#
# Run through the flake, from the repository root:
#
#   nix develop -c bash probes/install/ir/capture-json-scan.sh
#
# Input
#   probes/install/json/scan-window.candidate.c
#                                 the window scanner, AVX2 lane masks and the
#                                 byte rule over the window
#
# Output
#   probes/install/ir/json-scan.candidate.ll
#                                 parseable fixture: the verbatim `define`
#                                 block of @leanllvm_json_scan_window, after
#                                 the pipeline below and with the textual
#                                 syntax listed under "Text removed" removed
#
# --- The pipeline, and why each step is there ----------------------------
#
#   clang -S -emit-llvm -O2 -mavx2 -fno-slp-vectorize \
#     probes/install/json/scan-window.candidate.c
#   opt -passes='reg2mem,instnamer'
#
# `-O2 -mavx2` is the classifier's emission mode and the only level at which
# the three lane-mask chains come out in the fragment's form: clang lowers
# `_mm256_movemask_epi8` of a comparison to `bitcast <32 x i1> to i32` in its
# optimised pipelines, while at -O0 the same source reaches IR as
# `call @llvm.x86.avx2.pmovmskb` over `<4 x i64>` loads and bitcasts, none of
# which the fragment models.
#
# `-fno-slp-vectorize` is load-bearing, not cosmetic: with the SLP vectoriser
# enabled the scalar structural-mask pass is turned into `insertelement` and
# `shufflevector` over `<8 x i8>` constants.  The source's two
# `#pragma clang loop vectorize(disable) unroll(disable)` lines cover the loop
# vectoriser; SLP works on straight-line code inside a block and is not
# covered by loop metadata, so the flag is the only control for it.
#
# `reg2mem` is what makes the emission part of the fragment at all.
# `LeanLLVM.Syntax` has no `phi` (`Term` is `ret`/`br`/`condbr`/`unreachable`),
# and clang's -O2 promotes every loop-carried value -- the lane counter, the
# loop-invariant masks, the values the byte rule's arms merge -- into phi
# nodes.  `reg2mem` demotes each value whose definition block differs from a
# use block into an `alloca`, a store on every incoming path and a load at
# every use, which is the shape `D6` states for the loop: the loop's values
# live in memory.  Its demotion set is the pass's, not this script's, so the
# fixture's alloca count is measured below and recorded rather than asserted to
# a predicted number.
#
# `instnamer` names every value and block, which labels the entry block
# (`LeanLLVM.Parser` requires a label on every block, and textual IR leaves the
# entry block unlabelled).  It changes no instruction.
#
# --- Text removed before the parser sees the fixture ----------------------
#
# The parser refuses the syntax it does not model, so the emission is reduced
# to the function it analyses plus the instruction text.  Removed, and why it
# is irrelevant to the value computed:
#
#   `noundef`        parameter attribute; a promise about the argument, not
#                    part of the computation
#   `readonly`, `writeonly`, `captures(none)`
#                    promises about reads and captures; the theorem's
#                    footprint clause re-establishes them rather than assuming
#                    them
#   `local_unnamed_addr`, `#0`, `attributes #0 = { ... }`
#                    linkage and attribute-group references; the group
#                    (`memory(argmem: readwrite)`, target features and the
#                    rest) is removed with them, and its targets/features are
#                    recorded here: `x86_64-unknown-linux-gnu`, `+avx2`
#   `, align N`      the parser's `load`/`store` have no alignment field.  Under
#                    LLVM's own reading an unadorned access assumes ABI
#                    alignment, which is stricter than the unaligned accesses
#                    the source asks for; this text is parsed by LeanLLVM's
#                    parser rather than compiled as LLVM IR, and the theorem
#                    claims nothing about alignment.  `JsonScanABI`'s
#                    `scanAlignmentFree` is the contract side of this.
#   `, !tbaa !N` and every `!llvm.*` / `!N = ...` line
#                    per-instruction metadata and module-level lines
#   `target datalayout`, `target triple`, `source_filename`
#                    module-level configuration; recorded here (little-endian
#                    `e`, 64-bit pointers) rather than read by the parser
#   `nuw`, `nsw`, `nneg`, `exact`, `disjoint`
#                    (the substitution runs twice: a `nuw nsw` pair leaves the
#                    second flag against the space the first replacement
#                    consumed, so one pass would keep it)
#                    poison/UB-promise flags on `add`, `shl`, `trunc`, `zext`,
#                    `or` and `getelementptr`.  `LeanLLVM.Syntax` has no field
#                    for any of them, and `Parser.lean` refuses a `getelementptr`
#                    carrying `nuw`/`nusw` by name, so the flag is dropped
#                    rather than approximated.  Dropping a promise permits more
#                    programs than LLVM does, never fewer: the fixture is the
#                    text compiled at the end of the route, so no semantic
#                    bridge is crossed.
#   `range(i32 64, 1)` on the `define`
#                    a return attribute clang infers for the status word's
#                    value range.  A `range` attribute is a `ConstantRange`
#                    and its interval may wrap, so `[64, 1)` is `{0}` plus
#                    `[64, 2^32 - 1]`, not the empty set: the word is zero or
#                    at least 64, which every return satisfies -- zero is `0`,
#                    and a non-zero status carries a non-zero kind in bits
#                    6-7.  `Parser.lean` refuses a return attribute before the
#                    return type by name, and the attribute is a promise about
#                    the returned value rather than part of the computation:
#                    the refinement theorem states the returned word as an
#                    equation, which is narrower than the range, and dropping
#                    the attribute can only enlarge the permitted returns.
#   `%"reg2mem alloca point" = bitcast i32 0 to i32`
#                    a dead marker `reg2mem` inserts once per function.  It has
#                    no uses, and `bitcast i32 0 to i32` is not a shape the
#                    parser models (only `<n x i1>` to `iN` is).
#
# Nothing else inside the retained instruction list is rewritten.  The removal
# is a per-item claim that the value computed is unchanged -- not a proof that
# the stripped and original texts are semantically equivalent, and it does not
# undo an assumption a caller compiled against the original attributes may have
# drawn.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)

src="$repo/probes/install/json/scan-window.candidate.c"
sym=leanllvm_json_scan_window

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# The `define` block of @<symbol>, verbatim, from a clang emission.
extract_fn() {
  awk -v sym="$2" '
    !d && $0 ~ ("^define .*@" sym "\\(") { d = 1; print; depth += gsub(/\{/, "{"); next }
    d { print; depth += gsub(/\{/, "{"); depth -= gsub(/\}/, "}"); if (depth <= 0) exit }
  ' "$1"
}

# Text the parser does not model; see the header comment.
strip_ir() {
  sed -E \
    -e 's/^define range\([^)]*\) /define /' \
    -e 's/, *align [0-9]+//g' \
    -e 's/, *![a-zA-Z0-9_.]+ ![-a-zA-Z0-9_.]+//g' \
    -e 's/, *![a-zA-Z0-9_.]+ [0-9]+//g' \
    -e 's/ noundef//g' \
    -e 's/ (readonly|writeonly)//g' \
    -e 's/ captures\(none\)//g' \
    -e 's/ local_unnamed_addr//g' \
    -e 's/ #[0-9]+//g' \
    -e 's/ (nuw|nsw|nneg|exact|disjoint) / /g' \
    -e 's/ (nuw|nsw|nneg|exact|disjoint) / /g' \
    -e '/^  %"reg2mem alloca point" = bitcast i32 0 to i32$/d'
}

# The stripped syntax, one token per entry, in the form the fixture's
# provenance comment must name it.  `check_provenance` refuses a fixture whose
# heading omits one, and refuses a heading that carries a `$name` placeholder:
# a comment that says "counted on this text" and then states its own variable
# names is worse than no comment.
#
# What this check cannot see: a `sed` rule added above without a token here.
# The detector of record for that is the by-omission diff -- apply every rule
# but one to a fresh raw emission and diff against the fixture, so a rule whose
# effect is unclaimed shows up as a diff.  The token check runs on every
# capture and guards the enumeration; the diff guards the rule set, and is run
# when the rules change rather than on every capture.
strip_tokens=(
  'noundef' 'readonly' 'writeonly' 'captures(none)' 'local_unnamed_addr'
  '#0' 'attributes #0' ', align N' ', !tbaa !N' '!llvm.*' '!N = ...'
  'target datalayout' 'target triple' 'source_filename'
  'nuw' 'nsw' 'nneg' 'exact' 'disjoint' 'range(i32 64, 1)'
  'reg2mem alloca point'
)

has_placeholder() { grep -qE '\$[A-Za-z_]' "$1"; }

missing_token() { # 0 when the heading omits <token>
  ! sed -n '1,/^define /p' "$1" | grep -qF -- "$2"
}

check_token_list() { # 1 when the list is empty, or the heading omits a token
  local file=$1 header tok
  if [ "${#strip_tokens[@]}" -eq 0 ]; then
    echo "capture-json-scan: strip_tokens is empty; the token check would pass vacuously" >&2
    return 1
  fi
  header=$(sed -n '1,/^define /p' "$file")
  for tok in "${strip_tokens[@]}"; do
    if ! printf '%s\n' "$header" | grep -qF -- "$tok"; then
      echo "capture-json-scan: the fixture's heading does not name the stripped token '$tok'" >&2
      return 1
    fi
  done
}

check_provenance() {
  local file=$1 bad=0
  if has_placeholder "$file"; then
    echo "capture-json-scan: the fixture carries a \$name placeholder:" >&2
    grep -nE '\$[A-Za-z_]' "$file" >&2
    bad=1
  fi
  check_token_list "$file" || bad=1
  [ "$bad" = 0 ] || exit 1
}

# The detectors' own controls, on copies, in the same run that accepts the
# fixture: a check that cannot fail is not a check, and a later run has to be
# able to tell a genuine absence from a pattern that stopped matching.
check_controls() {
  local file=$1 bad=0
  sed '/^define /i ; placeholder $blocks' "$file" > "$work/ctl-placeholder.ll"
  if has_placeholder "$work/ctl-placeholder.ll"; then
    echo "capture-json-scan: control: the placeholder detector refused a heading carrying a \$name"
  else
    echo "capture-json-scan: control FAILED: the placeholder detector accepted a heading carrying a \$name" >&2
    bad=1
  fi
  sed 's/source_filename/SOURCE-REMOVED/' "$file" > "$work/ctl-token.ll"
  if ! check_token_list "$work/ctl-token.ll" 2>/dev/null; then
    echo "capture-json-scan: control: the token detector refused a heading missing 'source_filename'"
  else
    echo "capture-json-scan: control FAILED: the token detector accepted a heading missing 'source_filename'" >&2
    bad=1
  fi
  if ( strip_tokens=(); check_token_list "$file" ) 2>/dev/null; then
    echo "capture-json-scan: control FAILED: the token check passed with an empty token list" >&2
    bad=1
  else
    echo "capture-json-scan: control: an empty token list is refused"
  fi
  [ "$bad" = 0 ] || exit 1
}

# Every block is labelled and terminated, nothing is left without a `ret`, and
# the entry block is the first line.
check_shape() {
  local file=$1
  if [ "$(head -1 "$file" | grep -cE '^define ')" -ne 1 ]; then
    echo "capture-json-scan: $file does not start with a define" >&2; exit 1
  fi
  if [ "$(grep -cE '^[A-Za-z0-9_.]+:' "$file")" -lt 2 ]; then
    echo "capture-json-scan: $file has no labelled blocks" >&2; exit 1
  fi
  if [ "$(grep -cE '^  ret ' "$file")" -lt 1 ]; then
    echo "capture-json-scan: $file has no ret" >&2; exit 1
  fi
}

# The stop condition.  `LeanLLVM.Syntax` has no `phi`, `freeze`,
# `shufflevector`, `insertelement` or `extractelement`; `store` and `alloca`
# refuse vector types in `Parser.lean`; a lane-wise `icmp` admits only `eq` and
# `ult`; and `call` is outside the fragment, which is what keeps the AVX2
# intrinsics out (`@llvm.x86.avx2.pmovmskb` and the vector reductions).  A
# construct the byte counts below cannot see -- `alloca <32 x i8>` leaves every
# counted token unchanged -- is refused here by name.
refuse_unmodelled() {
  local file=$1 bad
  bad=$(grep -nE '\b(phi|freeze|shufflevector|insertelement|extractelement|call|fence|switch|invoke)\b|llvm\.|store +<|alloca +<|icmp +(ne|slt|sgt|sle|sge|ugt|uge) +<|select +<' "$file" || true)
  if [ -n "$bad" ]; then
    echo "capture-json-scan: $file contains a construct outside the modelled fragment:" >&2
    printf '%s\n' "$bad" >&2
    exit 1
  fi
}

# Count occurrences of a fixed string in a file.
count() { { grep -oF -- "$2" "$1" || true; } | wc -l | tr -d ' '; }

# Count lines matching an extended regex.
count_ln() { { grep -cE -- "$2" "$1" || true; } | tr -d ' '; }

emit() { # emit <out> <provenance-comment> <body-file>
  { printf '%s\n' "$2"; cat "$3"; } > "$1"
}

# --- the emission --------------------------------------------------------

clang -S -emit-llvm -O2 -mavx2 -fno-slp-vectorize "$src" -o "$work/scan.O2.ll"

extract_fn "$work/scan.O2.ll" $sym > "$work/raw.body.ll"

# The raw emission is allowed to carry `phi` and the values `reg2mem` will
# demote; it is not allowed to carry something demotion cannot fix, because
# that would be a source-level mistake rather than a pipeline one.
refuse_unfixable() {
  local file=$1 bad
  bad=$(grep -nE '\b(call|invoke|fence|switch)\b|llvm\.|store +<|alloca +<|shufflevector|insertelement|extractelement|freeze' "$file" || true)
  if [ -n "$bad" ]; then
    echo "capture-json-scan: $file contains a construct the pipeline cannot promote:" >&2
    printf '%s\n' "$bad" >&2
    exit 1
  fi
}
extract_fn "$work/scan.O2.ll" $sym | strip_ir > "$work/raw.stripped.ll"
refuse_unfixable "$work/raw.stripped.ll"

opt -passes='reg2mem,instnamer' -S "$work/scan.O2.ll" -o "$work/scan.promoted.ll"
extract_fn "$work/scan.promoted.ll" $sym | strip_ir > "$work/fixture.body.ll"

check_shape "$work/fixture.body.ll"
refuse_unmodelled "$work/fixture.body.ll"

# --- the measured inventory ----------------------------------------------

# Counted on the fixture text, so the provenance comment records what this
# script wrote rather than what was predicted.
body="$work/fixture.body.ll"
blocks=$(count_ln "$body" '^[A-Za-z0-9_.]+:')
alloca=$(count "$body" 'alloca i')
load_i32=$(count_ln "$body" '= load i32,')
store_i32=$(count_ln "$body" '  store i32 ')
load_i8=$(count_ln "$body" '= load i8,')
store_i8=$(count_ln "$body" '  store i8 ')
load_i1=$(count_ln "$body" '= load i1,')
store_i1=$(count_ln "$body" '  store i1 ')
gep=$(count "$body" 'getelementptr inbounds i8')
vload=$(count_ln "$body" '= load <32 x i8>,')
v_eq=$(count "$body" 'icmp eq <32 x i8>')
v_ult=$(count "$body" 'icmp ult <32 x i8>')
v_bc=$(count_ln "$body" 'bitcast <32 x i1>.* to i32')
lshr=$(count_ln "$body" '= lshr i64')
shl=$(count_ln "$body" '= shl i32')
mul_i32=$(count_ln "$body" '= mul i32')
and_i32=$(count_ln "$body" '= and i32')
or_i32=$(count_ln "$body" '= or i32')
add_i32=$(count_ln "$body" '= add i32')
sub_i32=$(count_ln "$body" '= sub i32')
condbr=$(count_ln "$body" '^  br i1 ')
br=$(count_ln "$body" '^  br label ')
ret=$(count_ln "$body" '^  ret i32 ')

# The inventory the fixture's provenance comment states.  A change here is a
# change to the fragment, so it fails rather than silently rewriting the claim.
expect() { # expect <what> <got> <want>
  if [ "$2" != "$3" ]; then
    echo "capture-json-scan: inventory: $1 is $2, expected $3" >&2
    exit 1
  fi
}
expect 'blocks'            "$blocks"    37
expect 'allocas'           "$alloca"    100
expect 'load i32'          "$load_i32"  144
expect 'store i32'         "$store_i32" 141
expect 'load i8'           "$load_i8"   24
expect 'store i8'          "$store_i8"  2
expect 'load i1'           "$load_i1"   7
expect 'store i1'          "$store_i1"  5
expect 'getelementptr'     "$gep"       5
expect 'load <32 x i8>'    "$vload"     1
expect 'icmp eq <32 x i8>' "$v_eq"      2
expect 'icmp ult <32 x i8>' "$v_ult"    1
expect 'bitcast mask'      "$v_bc"      3
expect 'lshr (i64)'        "$lshr"      1
expect 'shl i32'           "$shl"       6
expect 'and i32'           "$and_i32"   8
expect 'or i32'            "$or_i32"    23
expect 'add i32'           "$add_i32"   6
expect 'mul i32'           "$mul_i32"   2
expect 'sub i32'           "$sub_i32"   0
expect 'condbr'            "$condbr"    14
expect 'br'                "$br"        22
expect 'ret'               "$ret"       1

# --- the fixture ---------------------------------------------------------

emit "$work/json-scan.candidate.ll" "; The window scanner as emitted, in the fragment \`LeanLLVM.Semantics\`
; models.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-json-scan.sh
;
; from probes/install/json/scan-window.candidate.c, emitted with
;
;   clang -S -emit-llvm -O2 -mavx2 -fno-slp-vectorize probes/install/json/scan-window.candidate.c
;
; and demoted with
;
;   opt -passes='reg2mem,instnamer'
;
; then the verbatim \`define\` block of @leanllvm_json_scan_window, with the
; textual syntax listed in capture-json-scan.sh removed.  \`instnamer\` labels
; the entry block (the parser requires a label on every block) and names
; values; it changes no instruction.
;
; The optimiser form is clang 21.1.8 at -O2 -mavx2 for
; x86_64-unknown-linux-gnu with +avx2.  \`reg2mem\` is not a convenience: the
; fragment has no \`phi\`, and every loop-carried value clang promotes -- the
; lane counter, the loop-invariant masks, the values the byte rule's arms
; merge -- is demoted into an \`alloca\` with a store on each incoming
; path and a load at each use, which is the memory-carried loop the module
; proves.  \`-fno-slp-vectorize\` keeps the SLP vectoriser from rewriting the
; scalar structural-mask pass into \`insertelement\`/\`shufflevector\`.
;
; Removed before the parser sees the text, each because it does not change the
; value computed: \`noundef\`; \`readonly\`; \`writeonly\`; \`captures(none)\`;
; \`local_unnamed_addr\`; \`#0\` and the \`attributes #0 = { ... }\` group
; (including \`memory(argmem: readwrite)\` and the target-feature list);
; \`, align N\`; \`, !tbaa !N\`; every \`!llvm.*\` and \`!N = ...\` line;
; \`target datalayout\`; \`target triple\`; \`source_filename\`; the
; poison-promise flags \`nuw\`, \`nsw\`, \`nneg\`, \`exact\` and \`disjoint\`;
; \`range(i32 64, 1)\` on the \`define\`; and the dead
; \`%\"reg2mem alloca point\" = bitcast i32 0 to i32\` that \`reg2mem\` inserts as
; its alloca point.  The module configuration those lines carried is:
; x86_64-unknown-linux-gnu, little endian, 64-bit pointers, +avx2.
;
; \`range(i32 64, 1)\` is clang's inferred value range for the returned status
; word.  An LLVM \`range\` attribute is a \`ConstantRange\`, whose interval may
; wrap, so as written \`[64, 1)\` is the union of \`{0}\` and \`[64, 2^32 - 1]\`,
; not the empty set (which is spelled \`[0, 0)\`): the returned word is zero, or
; at least 64.  Every return of this body satisfies that -- a zero status is
; \`0\`, and a non-zero one carries a non-zero kind in bits 6-7, so it is at
; least 64 -- and dropping the attribute at capture therefore removes a
; caller-facing promise rather than a computation: it can only enlarge the set
; of permitted returns.  \`Parser.lean\` refuses a return attribute before the
; return type by name, and the fixture is the text that is compiled at the end
; of the route, so nothing semantic is crossed.
;
; The accesses carry no \`align\` because the parser's \`load\`/\`store\` have no
; alignment field; the contract's \`scanAlignmentFree\` records that none is
; required or assumed, and the theorem claims nothing about alignment.
;
; Measured inventory of the block below (counted on this text):
;   blocks $blocks, allocas $alloca
;   scalar memory: load i32 $load_i32, store i32 $store_i32, load i8 $load_i8,
;                  store i8 $store_i8, load i1 $load_i1, store i1 $store_i1,
;                  getelementptr $gep
;   vector: load <32 x i8> $vload, icmp eq <32 x i8> $v_eq,
;           icmp ult <32 x i8> $v_ult, bitcast mask $v_bc
;   scalar arithmetic: lshr i64 $lshr, shl $shl, and $and_i32, or $or_i32,
;                      add $add_i32, mul $mul_i32, sub $sub_i32
;   terminators: condbr $condbr, br $br, ret $ret
;
; The body reads the first \`valid\` bytes once for the structural mask and once
; for the byte rule, writes the mask at \`%out\` and the carry in the sixteen
; bytes at \`%state\`, calls nothing, and contains no \`phi\`, no vector store,
; no vector \`alloca\`, no shuffle and no intrinsic." "$work/fixture.body.ll"

# --- the fixture is checked before it is installed ------------------------
#
# Everything below runs against the copy in the work tree, and the committed
# fixture is replaced only after all of it passes, so a refused capture leaves
# nothing stale behind and a control failure cannot be mistaken for a
# successful regeneration.

check_provenance "$work/json-scan.candidate.ll"
check_controls "$work/json-scan.candidate.ll"

opt -passes=verify -disable-output "$work/json-scan.candidate.ll"

cp "$work/json-scan.candidate.ll" "$here/json-scan.candidate.ll"

echo "capture-json-scan: wrote probes/install/ir/json-scan.candidate.ll"
echo "capture-json-scan: blocks $blocks, allocas $alloca"
echo "capture-json-scan: memory: load i32 $load_i32, store i32 $store_i32, load i8 $load_i8, store i8 $store_i8, load i1 $load_i1, store i1 $store_i1, gep $gep"
echo "capture-json-scan: vector: <32 x i8> load $vload, eq $v_eq, ult $v_ult, bitcast $v_bc"
