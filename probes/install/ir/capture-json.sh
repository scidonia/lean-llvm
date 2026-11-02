#!/usr/bin/env bash
# Regenerate the JSON classifier's emitted-IR fixture in probes/install/ir/.
#
# Run through the flake, from the repository root:
#
#   nix develop -c bash probes/install/ir/capture-json.sh
#
# Input
#   probes/install/json/classify.candidate.c
#                                 the 32-byte classifier, AVX2 intrinsics
#                                 lowered to portable vector IR by clang
#
# Output
#   probes/install/ir/json-classify.candidate.ll
#                                 parseable fixture: the verbatim `define`
#                                 block of @leanllvm_json_classify32, with the
#                                 textual syntax listed below removed
#
# --- Why -O2 -mavx2, and not the -O0 route the comma mask uses ------------
#
# The comma mask is emitted at -O0 and promoted with `mem2reg`, because its
# source is a scalar fold whose -O0 body is already the fragment the semantics
# models.  The classifier's portable form is *produced by the optimiser*:
# instcombine folds the two comparisons for `'\t'` and `'\n'` into a range
# test,
#
#   %20 = add <32 x i8> %2, splat (i8 -9)
#   %21 = icmp ult <32 x i8> %20, splat (i8 2)
#
# so the fragment J2 models is the -O2 -mavx2 body, and that is what is
# captured.  At -O0 the same source emits `icmp eq` for both bytes and no
# `add`/`icmp ult`; capturing that body would certify a fragment the candidate
# does not ship.  The emitted body is measured, not assumed: the inventory in
# the fixture's provenance comment is computed from the fixture
# this script writes, and the script fails if any construct the stop
# condition below names appears.
#
#   clang -S -emit-llvm -O2 -mavx2 probes/install/json/classify.candidate.c
#
# The emission is passed through
#
#   opt -passes=instnamer
#
# only.  `instnamer` names every value and block, which labels the entry block
# (`LeanLLVM.Parser` requires a label on every block, and textual IR leaves the
# entry block unlabelled).  It changes no instruction: the opcode sequence and
# operand types below are clang's -O2 -mavx2 output.
#
# --- Text removed before the parser sees the fixture ----------------------
#
# The parser refuses the instruction and header syntax it does not model
# (`Parser.lean:455,469` refuse a return attribute and a function attribute),
# so the emission is reduced to the function it analyses plus the instruction
# text.  Removed, and why it is irrelevant to the value computed:
#
#   `noundef`        parameter attribute; a promise about the argument, not
#                    part of the computation (the per-item-claim discipline of
#                    capture.sh)
#   `readonly`, `captures(none)`
#                    promises about reads and captures; re-established by the
#                    theorem's `mem' = mem` clause rather than assumed
#   `local_unnamed_addr`, `#0`, `attributes #0 = { ... }`
#                    linkage and attribute-group references; the group
#                    (`memory(argmem: read)`, target features and the rest) is
#                    removed with them, and its targets/features are recorded
#                    here: `x86_64-unknown-linux-gnu`, `+avx2`, AVX2 lowers the
#                    intrinsics to the portable vector operations below
#   `, align 1`      the parser's `load` has no alignment field, so the fixture
#                    does not carry one.  Under LLVM's own reading an unadorned
#                    load assumes ABI alignment (`llvm-as` then `llvm-dis`
#                    renders this one `align 32`), which is stricter than the
#                    `align 1` clang emitted for the unaligned source load;
#                    this text is parsed by LeanLLVM's parser rather than
#                    compiled as LLVM IR, and the theorem claims nothing about
#                    a stricter alignment.
#   `, !tbaa !6` and every `!llvm.*` / `!N = ...` line
#                    per-instruction metadata and module-level lines
#   `target datalayout`, `target triple`, `source_filename`
#                    module-level configuration; recorded here (little-endian
#                    `e`, 64-bit pointers) rather than read by the parser
#
# Nothing inside the retained instruction list is rewritten.  The removal is a
# per-item claim that the value computed is unchanged -- not a proof that the
# stripped and original texts are semantically equivalent, and it does not undo
# an assumption a caller compiled against the original attributes may have
# drawn.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)

src="$repo/probes/install/json/classify.candidate.c"

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
    -e 's/, *align [0-9]+//g' \
    -e 's/, *![a-zA-Z0-9_.]+ ![-a-zA-Z0-9_.]+//g' \
    -e 's/, *![a-zA-Z0-9_.]+ [0-9]+//g' \
    -e 's/ noundef//g' \
    -e 's/ readonly//g' \
    -e 's/ captures\(none\)//g' \
    -e 's/ local_unnamed_addr//g' \
    -e 's/ #[0-9]+//g'
}

# One block, one `ret`.
check_shape() {
  local file=$1
  if [ "$(grep -cE '^[^ ;{}]+:$' "$file")" -ne 1 ]; then
    echo "capture-json: $file is not single-block" >&2; exit 1
  fi
  if [ "$(grep -cE '^  ret ' "$file")" -ne 1 ]; then
    echo "capture-json: $file does not end in a single ret" >&2; exit 1
  fi
}

# A construct the captured body must not contain; the stop condition.  `call`,
# `getelementptr`, `shufflevector`, `insertelement`, `select`, `phi`, `freeze`
# and `llvm.vector.reduce.*` are outside the fragment J2 adds, and `alloca`,
# `fence`, `store`, `and`, `shl`, `lshr`, `trunc` and `extractelement` are
# instruction kinds the classifier does not emit; their appearance would be a
# scope change rather than a stripping decision.  The opcode counts below
# cannot catch them on their own (`alloca i8` and `fence seq_cst` leave every
# counted token unchanged), so the kind is refused here by name.
refuse_unmodelled() {
  local file=$1 bad
  bad=$(grep -nE '\b(call|getelementptr|shufflevector|insertelement|select|phi|freeze|alloca|fence|store|and|shl|lshr|trunc|extractelement)\b|llvm\.vector\.reduce\.' "$file" || true)
  if [ -n "$bad" ]; then
    echo "capture-json: $file contains a construct outside the modelled fragment:" >&2
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

clang -S -emit-llvm -O2 -mavx2 "$src" -o "$work/json.O2.ll"

extract_fn "$work/json.O2.ll" leanllvm_json_classify32 > "$work/raw.body.ll"
refuse_unmodelled "$work/raw.body.ll"

opt -passes=instnamer -S "$work/json.O2.ll" -o "$work/json.named.ll"
extract_fn "$work/json.named.ll" leanllvm_json_classify32 | strip_ir \
  > "$work/fixture.body.ll"

check_shape "$work/fixture.body.ll"
refuse_unmodelled "$work/fixture.body.ll"

# --- the measured inventory ----------------------------------------------

# Counted on the fixture text, so the provenance comment records what this
# script wrote rather than what was predicted.
body="$work/fixture.body.ll"
v_i8=$(count "$body" '<32 x i8>')
v_i1=$(count "$body" '<32 x i1>')
v_i32=$(count "$body" 'i32')
v_ptr=$(count "$body" 'ptr')
splat=$(count "$body" 'splat (i8 ')
load=$(count_ln "$body" '^  %[A-Za-z0-9_.]+ = load <32 x i8>')
icmp_eq=$(count "$body" 'icmp eq <32 x i8>')
icmp_ult=$(count "$body" 'icmp ult <32 x i8>')
v_or=$(count "$body" 'or <32 x i1>')
v_add=$(count "$body" 'add <32 x i8>')
bitcast=$(count "$body" 'bitcast <32 x i1>')
bitcast_to=$(count_ln "$body" 'bitcast <32 x i1> .* to i32')
ret=$(count "$body" 'ret i32')

# The inventory the fixture's provenance comment states, and the shape the
# semantics extension is justified by.  A change here is a change to the
# fragment, so it fails rather than silently rewriting the claim.
expect() { # expect <what> <got> <want>
  if [ "$2" != "$3" ]; then
    echo "capture-json: $1 is $2, expected $3; the emission changed the modelled fragment" >&2
    exit 1
  fi
}
expect 'load'          "$load"      1
expect 'icmp eq'       "$icmp_eq"   10
expect 'icmp ult'      "$icmp_ult"  1
expect 'or <32 x i1>'  "$v_or"      10
expect 'add'           "$v_add"     1
expect 'bitcast'       "$bitcast"   1
expect 'bitcast to i32' "$bitcast_to" 1
expect 'ret'           "$ret"       1
expect '<32 x i8>'     "$v_i8"      13
expect '<32 x i1>'     "$v_i1"      11
expect 'i32'           "$v_i32"     3
expect 'ptr'           "$v_ptr"     2
expect 'splat (i8'     "$splat"     12

# --- the fixture ---------------------------------------------------------

emit "$here/json-classify.candidate.ll" "; The JSON block classifier as emitted, in the fragment \`LeanLLVM.Semantics\`
; models.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-json.sh
;
; from probes/install/json/classify.candidate.c, emitted with
;
;   clang -S -emit-llvm -O2 -mavx2 probes/install/json/classify.candidate.c
;
; and passed through
;
;   opt -passes=instnamer
;
; then the verbatim \`define\` block of @leanllvm_json_classify32, with the
; textual syntax listed in capture-json.sh removed.  \`instnamer\` labels the
; entry block (the parser requires a label on every block) and names values;
; it changes no instruction.  The optimiser form is clang 21.1.8 at -O2 -mavx2
; for x86_64-unknown-linux-gnu with +avx2: instcombine folded the two
; comparisons for the tab and newline bytes into a range test, which is why
; the body contains \`add <32 x i8>\` and \`icmp ult <32 x i8>\` and why the
; splat constant is negative.  At -O0 the same source emits an \`icmp eq\` for
; each of the twelve bytes and neither of those two instructions.
;
; Removed before the parser sees the text, each because it does not change the
; value computed: \`noundef\`; \`readonly\`; \`captures(none)\`;
; \`local_unnamed_addr\`; \`#0\` and the \`attributes #0 = { ... }\` group
; (including \`memory(argmem: read)\` and the target-feature list);
; \`, align 1\`; \`, !tbaa !6\`; every \`!llvm.*\` and \`!N = ...\` line;
; \`target datalayout\`; \`target triple\`; \`source_filename\`.  The module
; configuration those lines carried is: x86_64-unknown-linux-gnu, little
; endian, 64-bit pointers, +avx2.
;
; The load's \`align 1\` is dropped because the parser's \`load\` has no
; alignment field.  Under LLVM's own reading an unadorned load assumes ABI
; alignment (\`llvm-as\` then \`llvm-dis\` renders this one \`align 32\`), which
; is stricter than the \`align 1\` clang emitted for the unaligned source
; load; this text is parsed by LeanLLVM's parser rather than compiled as LLVM
; IR, and the theorem claims nothing about a stricter alignment.
;
; Measured inventory of the block below (counted on this text):
;   opcodes:  load $load, icmp $((icmp_eq + icmp_ult)) ($icmp_eq eq, $icmp_ult ult),
;             or $v_or, add $v_add, bitcast $bitcast, ret $ret
;   vector types: <32 x i8> $v_i8, <32 x i1> $v_i1
;   scalar types: i8 $splat (in splat constants), i32 $v_i32 (header return
;                 type, bitcast target, ret), ptr $v_ptr (parameter, load
;                 address)
;   vector constants: splat (i8 N) $splat
;
; The body reads 32 bytes and writes none; it calls nothing, allocates
; nothing and contains no \`getelementptr\`, shuffle, select or \`phi\`." "$work/fixture.body.ll"

# --- the fixture is still valid LLVM IR -----------------------------------

opt -passes=verify -disable-output "$here/json-classify.candidate.ll"

echo "capture-json: wrote probes/install/ir/json-classify.candidate.ll"
echo "capture-json: opcodes: load $load, icmp $((icmp_eq + icmp_ult)) ($icmp_eq eq, $icmp_ult ult), or $v_or, add $v_add, bitcast $bitcast, ret $ret"
echo "capture-json: types: <32 x i8> $v_i8, <32 x i1> $v_i1, i8 $splat (splat), i32 $v_i32, ptr $v_ptr"
