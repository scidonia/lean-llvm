#!/usr/bin/env bash
# Regenerate the stage-2 helpers' emitted bodies, as the emission holds them
# before the walk's own fixture reduces them to calls.
#
# Run through the flake, from the repository root:
#
#   nix develop -c bash probes/install/ir/capture-stage2-helpers.sh
#
# Input
#   kernel/json/stage2.c   the stage-2 unit: the six helpers `s2_walk` calls out
#                          of line, and the walk and wrapper around them
#
# Output (one fixture per helper the fragment models, and the inventory of all
# six)
#   stage2.helper.s2_init.ll
#   stage2.helper.s2_value_pos.ll
#   stage2.helper.s2_after_value.ll
#   stage2.helper.s2_string_body.ll
#   stage2.helper.od_scalar_value.ll
#   stage2.helpers.tsv      every helper's emitted shape, and whether the
#                           fragment has a representation for its body
#
# The derivation is `capture-stage2.sh`'s, up to the point where that script
# reduces the walk to one `define` block.  The same source transform makes the
# twelve helpers `noinline`; the same compiler line emits the module; the same
# `opt -passes=lower-switch` runs; and the same token strip removes the
# attributes and surface the parser does not model.  What differs is the
# extraction: it takes each helper's own `define` block instead of the
# wrapper's, so the body is the function's text rather than a call to it.
#
# --- The flags, and why they are the walk's ---------------------------------
#
# The compiler line is the measured build's, `build49.sh:17`'s, with
# `-fno-discard-value-names` added so the parser sees the source's labels:
#
#   clang -S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11
#         -falign-loops=64 -falign-functions=64 -fno-discard-value-names
#
# The bodies are the ones the walk's *fixture* leaves out of line, so the
# cross-check below is against that fixture: each captured body must be the
# symbol `stage2.candidate.ll` declares, at the same argument list, with only
# the staging parameters this script appends.
#
# --- What is captured, and what is not representable ------------------------
#
# Four bodies are programs of `LeanLLVM.Semantics` after the same strip the walk
# received: `s2_init`, `s2_value_pos`, `s2_after_value` and `od_scalar_value`.
# `od_scalar_value` needs the walk's own rewrites as well — its `alloca double`
# becomes a parameter, its refusal messages become `null`, and its one
# `llvm.umin.i64` unfolds — because its number path takes the conversion's slot
# as a pointer exactly as the walk's `%d.i` does.
#
# The two bodies the core extension is about are measured rather than asserted:
#
#   s2_string_body   `ptrtoint` (the body's `%sub.ptr.sub`) and the
#                    global-symbol operand `@.str.14`.  Both are modelled —
#                    `Instr.ptrtoint` at the model's 64-bit pointer width,
#                    `Operand.global` read from the run's staging — so the body
#                    is a program of the fragment, and `JsonStage2HelperIR`
#                    pins the AST it parses to.
#   num_fast_el1     aggregate and binary64 text: `alloca [768 x i8]`,
#                    `alloca %struct.Stk`, `alloca double`, and the `uitofp`/
#                    `fmul`/`fdiv`/`fneg`/`select double` chain, all modelled.
#                    The body is still outside the fragment, on three grounds
#                    this capture leaves in place, measured by reading the body
#                    with `LeanLLVM.Parser`:
#
#                      %struct.Stk   the extraction takes one `define` block, so
#                                    the module's `%struct.Stk = type { … }` line
#                                    is not in the text, and the parser takes a
#                                    struct's extent from its `Layout` argument
#                                    rather than recomputing it from fields
#                                    (`expectAllocaTy`);
#                      llvm.umin.i64 one call, at i64 with an immediate operand;
#                                    the model's unsigned minimum is
#                                    `@llvm.umin.i32` at i32 with two operands;
#                      ashr exact    `exact` on the shift, a flag the token strip
#                                    does not remove and the parser refuses by
#                                    name.
#
#                    The double reader accepts the body's literals —
#                    `-0.000000e+00` and `0.000000e+00` included.
#
# num_fast_el1's text is not written to the tree: a fixture nothing can read is
# not a pin.  The inventory records the shape and the verdict, and the checks
# below refuse if the emission stops having the measured constructs.
#
# Exit status: 0 when the fixtures and the inventory are written; 3 when an
# input is missing or a derivation check fails.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)

src=kernel/json/stage2.c
walk=$here/stage2.candidate.ll
inventory=$here/stage2.helpers.tsv

fail() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

[ -f "$repo/$src" ] || fail "absent: $repo/$src"
[ -f "$walk" ] || fail "absent: $walk (run capture-stage2.sh first)"
command -v clang >/dev/null 2>&1 || fail "clang is not on PATH"
command -v opt >/dev/null 2>&1 || fail "opt is not on PATH"

work=$(mktemp -d "$repo/.lake/tmp-stage2-helpers.XXXXXX" 2>/dev/null) ||
  work=$(mktemp -d) ||
  fail "cannot create a work directory"
trap 'rm -rf "$work"' EXIT

flags=(-S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11
       -falign-loops=64 -falign-functions=64)
compile() { ( cd "$repo" && clang -I kernel/json "$@" ); }

# The six helpers the walk calls out of line, in the order §7.6 lists them.
symbols=(s2_init s2_value_pos s2_after_value s2_string_body od_scalar_value
         num_fast_el1)

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

n_ni=$(grep -c '__attribute__((noinline))' "$work/stage2.noinline.c" || true)
[ "$n_ni" -eq 12 ] ||
  fail "the transformed source carries $n_ni 'noinline' occurrences; the always_inline set is 11 helpers plus the EL_ENTRY macro definition"

# ---------------------------------------------------------------------------
# The emission
# ---------------------------------------------------------------------------

compile "${flags[@]}" -fno-discard-value-names "$work/stage2.noinline.c" -o "$work/named.ll"
opt -S -passes=lower-switch "$work/named.ll" -o "$work/lowered.ll" ||
  fail "opt refused to lower the switch"

# ---------------------------------------------------------------------------
# The strip: the walk fixture's classes, applied to a body
# ---------------------------------------------------------------------------

strip_body() { # <file> <out>
  sed -E \
    -e 's/ (noundef|nonnull|readonly|writeonly|noalias|zeroext|signext|returned|immarg|nocapture|nofree|nosync|nounwind|norecurse|willreturn|mustprogress)//g' \
    -e 's/ (captures|range|initializes|dereferenceable|dereferenceable_or_null|nofpclass)\([^)]*(\([^)]*\))?[^)]*\)//g' \
    -e 's/ (local_unnamed_addr|unnamed_addr)//g' \
    -e 's/ (nuw|nsw|nusw|disjoint|nneg)//g' \
    -e 's/ align [0-9]+//g' \
    -e 's/ #[0-9]+//g' \
    "$1" |
    sed -E -e 's/^(define .*)\) align [0-9]+ \{$/\1) {/' \
           -e 's/, align [0-9]+//g' -e 's/, !tbaa ![0-9]+//g' \
           -e 's/, ![A-Za-z0-9_.]+ ![0-9]+//g' \
           -e 's/, !llvm\.[^ ]*//g' -e 's/ call fastcc / call /g' \
           -e 's/,[ \t]*$//' \
           -e 's/^define (internal |private )?fastcc /define /' \
           -e 's/^define (internal |private )?/define /' \
    > "$2"
}

# The helper's own `define` block, from the module the walk's fixture is taken
# from.
extract_define() { # <symbol> <out>
  awk -v sym="$1" '
    $0 ~ "^define .*@" sym "\\(" { inblock = 1 }
    inblock { print }
    inblock && $0 == "}" { exit }
  ' "$work/lowered.ll" > "$2"
  [ -s "$2" ] || fail "the emission has no \`define\` block for @$1"
}

# ---------------------------------------------------------------------------
# The captured bodies, and the one rewrite the walk applies
# ---------------------------------------------------------------------------

# `od_scalar_value`'s staging: its `alloca double` becomes an appended pointer
# parameter, exactly as the walk's `%d.i` does, and its messages become `null`.
od_rewrites() { # <in> <out>
  local out1="$work/od.1.ll" out2="$work/od.2.ll"
  awk '
    NR == 1 {
      sub(/\) \{$/, ", ptr %d) {")
    }
    /^  %d = alloca double$/ { next }
    { print }' "$1" > "$out1"
  awk '
    {
      line = $0
      if (match(line, /^  (%[A-Za-z0-9_.]+) = tail call i64 @llvm\.umin\.i64\(i64 (%[A-Za-z0-9_.]+), i64 (%[A-Za-z0-9_.]+)\)$/, m)) {
        print "  " m[1] ".min = icmp ult i64 " m[2] ", " m[3]
        print "  " m[1] " = select i1 " m[1] ".min, i64 " m[2] ", i64 " m[3]
        next
      }
      gsub(/@\.str\.[0-9]+/, "null", line)
      print line
    }' "$out1" > "$out2"
  grep -q ', ptr %d) {' "$out2" ||
    fail "od_scalar_value's staging parameter was not appended"
  grep -qE '^  %d = alloca ' "$out2" &&
    fail "od_scalar_value still allocates its conversion slot"
  mv "$out2" "$2"
}

capture() { # <symbol> <rewrite: none|od|as-is>
  local sym=$1 mode=$2
  extract_define "$sym" "$work/$sym.raw.ll"
  strip_body "$work/$sym.raw.ll" "$work/$sym.stripped.ll"
  case "$mode" in
    none) cp "$work/$sym.stripped.ll" "$work/$sym.body.ll" ;;
    od) od_rewrites "$work/$sym.stripped.ll" "$work/$sym.body.ll" ;;
    as-is) cp "$work/$sym.stripped.ll" "$work/$sym.body.ll" ;;
    *) fail "unknown capture mode $mode" ;;
  esac
}

capture s2_init none
capture s2_value_pos none
capture s2_after_value none
capture s2_string_body as-is
capture od_scalar_value od
capture num_fast_el1 as-is

# These four bodies carry none of the constructs the two measured bodies do,
# and the check refuses if a regeneration introduces one.
for sym in s2_init s2_value_pos s2_after_value od_scalar_value; do
  for pat in 'ptrtoint' 'double' '%struct\.' '\[[0-9]+ x ' '@\.str\.' 'umin' ' fastcc '; do
    if grep -qE "$pat" "$work/$sym.body.ll"; then
      fail "$sym's body still carries '$pat'; the fragment has no representation for it"
    fi
  done
  nret=$(grep -cE '^  ret ' "$work/$sym.body.ll" || true)
  [ "$nret" -ge 1 ] || fail "$sym's body has no \`ret\`"
done

# The two measured bodies: the construct is measured, not assumed, and the
# script refuses if the emission stops carrying it.
nptrtoint=$(grep -c 'ptrtoint ' "$work/s2_string_body.body.ll" || true)
[ "$nptrtoint" -ge 1 ] ||
  fail "s2_string_body's body no longer carries \`ptrtoint\`; the recorded construct is not the emission's"
nfp=$(grep -cE '\b(uitofp|sitofp|fadd|fsub|fmul|fdiv|fneg|fcmp|fpext|fptrunc)\b|(^|[^a-z])double([^a-z]|$)' "$work/num_fast_el1.body.ll" || true)
nagg=$(grep -cE 'alloca (\[[0-9]+ x |%struct\.)' "$work/num_fast_el1.body.ll" || true)
[ "$nfp" -ge 1 ] ||
  fail "num_fast_el1's body no longer carries binary64; the recorded construct is not the emission's"
[ "$nagg" -ge 1 ] ||
  fail "num_fast_el1's body no longer carries an aggregate alloca; the recorded construct is not the emission's"

# ---------------------------------------------------------------------------
# The cross-check: each captured body is the symbol the walk's fixture declares
# ---------------------------------------------------------------------------

decl_of() { # <symbol>
  awk -v sym="$1" '
    $0 ~ "^declare .*@" sym "\\(" { print; exit }
  ' "$walk"
}

arity_of() { # <header line>
  sed -E -e 's/.*\(//' -e 's/\).*//' <<<"$1" | awk -F', ' '{ print NF }'
}

for sym in s2_init s2_value_pos s2_after_value s2_string_body od_scalar_value num_fast_el1; do
  d=$(decl_of "$sym")
  [ -n "$d" ] || fail "the walk fixture does not declare @$sym"
  head=$(head -1 "$work/$sym.body.ll")
  # The declare's parameter list, and the body's, agree up to the staging
  # parameters this script appends: one for od_scalar_value, none otherwise.
  want=$(arity_of "$d")
  got=$(arity_of "$head")
  case "$sym" in
    od_scalar_value) [ "$got" -eq $((want + 1)) ] || fail "$sym: declared $want, body $got" ;;
    *) [ "$got" -eq "$want" ] || fail "$sym: declared $want, body $got" ;;
  esac
  dnames=$(sed -E -e 's/.*\(//' -e 's/\).*//' <<<"$d" | tr ',' '\n' | sed -E 's/^ *[^%]*//' | paste -sd' ')
  bnames=$(sed -E -e 's/.*\(//' -e 's/\).*//' <<<"$head" | tr ',' '\n' | sed -E 's/^ *[^%]*//' | paste -sd' ')
  case "$sym" in
    od_scalar_value) bnames=${bnames% %d} ;;
  esac
  [ "$dnames" = "$bnames" ] ||
    fail "$sym: the walk declares ($dnames), the body is ($bnames)"
done

# ---------------------------------------------------------------------------
# The fixtures and the inventory
# ---------------------------------------------------------------------------

banner() { # <symbol> <what>
  cat <<EOF
; The stage-2 helper \`$1\`, as emitted, in the fragment \`LeanLLVM.Semantics\`
; models.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-stage2-helpers.sh
;
; from kernel/json/stage2.c, emitted at the measured compiler line with
; \`noinline\` on every helper except s2_walk, the same token strip
; capture-stage2.sh applies, and — for od_scalar_value only — the walk's own
; three rewrites: its conversion slot becomes a pointer parameter, its
; messages become \`null\`, and its one llvm.umin.i64 unfolds.  $2
;
EOF
}

for sym in s2_init s2_value_pos s2_after_value s2_string_body od_scalar_value; do
  out=$here/stage2.helper.$sym.ll
  case "$sym" in
    s2_string_body)
      note='The body is a program of this fragment: its `ptrtoint` pair and its `@.str.14` symbol operand are both modelled, and `JsonStage2HelperIR` pins the AST it parses to.' ;;
    od_scalar_value)
      note='The body is captured as the fragment expresses it; its accepted path calls `num_fast_el1`, whose own body is outside the fragment at the surfaces `stage2.helpers.tsv` names.' ;;
    *)
      note='The body is captured and the fragment expresses it.' ;;
  esac
  { banner "$sym" "$note"; cat "$work/$sym.body.ll"; } > "$out"
  [ -s "$out" ] || fail "$out is empty"
done

{
  printf '# The stage-2 helpers as emitted, and whether this fragment models their bodies.\n'
  printf '# Regenerate with probes/install/ir/capture-stage2-helpers.sh.\n'
  printf '#\n'
  printf '# symbol\tlines\tblocks\tinstr_lines\tparams\tverdict\tbasis\n'
  printf '# instr_lines counts the body\x27s instruction lines in the fixture; the parsed\n'
  printf '# instruction count is what the Lean pin states (od_scalar_value: 145).\n'
  for sym in "${symbols[@]}"; do
    f="$work/$sym.body.ll"
    lines=$(wc -l < "$f" | tr -d ' ')
    blocks=$(grep -cE '^[A-Za-z0-9_.]+:' "$f" || true)
    instrs=$(grep -cE '^  ' "$f" || true)
    params=$(arity_of "$(head -1 "$f")")
    case "$sym" in
      s2_string_body)
        verdict=expressible
        basis="parsed by LeanLLVM.Parser; pinned in LeanLLVM/Refinement/JsonStage2HelperIR.lean and tests/core-extension.lean" ;;
      num_fast_el1)
        verdict=refused
        basis="aggregate and binary64 text ($nagg aggregate alloca(s), $nfp floating-point site(s)), all modelled; refused at three surfaces this capture leaves in place: the extracted block has no %struct.Stk declaration and the parser takes a struct's extent from a Layout argument, the one llvm.umin.i64 call is at i64 with an immediate where the model's umin is i32 with two operands, and ashr exact's flag is refused by name; the decimal literals parse" ;;
      *)
        verdict=expressible
        basis="parsed by LeanLLVM.Parser; pinned in LeanLLVM/Refinement/JsonStage2HelperIR.lean" ;;
    esac
    printf '%s\t%d\t%d\t%d\t%d\t%s\t%s\n' "$sym" "$lines" "$blocks" "$instrs" "$params" "$verdict" "$basis"
  done
} > "$inventory"

printf 'wrote %s and %s\n' "$here/stage2.helper.*.ll" "$inventory"
