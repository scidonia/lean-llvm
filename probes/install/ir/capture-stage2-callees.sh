#!/usr/bin/env bash
# Regenerate the three out-of-line callees' emitted bodies.
#
# Run through the flake, from the repository root:
#
#   nix develop -c bash probes/install/ir/capture-stage2-callees.sh
#
# Input
#   kernel/json/stage2.c   the stage-2 unit, which defines `num_el_el1`,
#                          `num_d8_el1`, `stk_mul_add` and `stk_mul_u64`
#   kernel/json/measured/numf_el1.h
#                          the measured header's `num_d8_el1`
#
# Output (one fixture per callee)
#   stage2.callee.num_d8_el1.ll
#   stage2.callee.num_el_el1.ll
#   stage2.callee.stk_mul_u64.ll
#   stage2.callees.tsv      each callee's emitted shape and parse verdict
#
# The derivation is `capture-stage2-helpers.sh`'s: the same source transform
# gives the twelve helpers `noinline`, the same compiler line emits the module,
# the same `opt -passes=lower-switch` runs, the same token strip applies, and
# each fixture is one `define` block extracted from the same module.  What
# differs is which symbols are extracted: the three the walk's conversion calls
# out of line, which the helper capture does not write because the helper
# capture is about the walk's own callees.
#
# `num_d8_el1` and `num_el_el1` are `always_inline` in the text and the existing
# transform already marks them `noinline`, so their bodies are already in the
# module the helper capture extracts from.  `stk_mul_u64` is spelled `static
# void`, and this script marks it `noinline` too, one occurrence, checked below.
# `stk_mul_add` is left as the text has it, so the extracted `stk_mul_u64` body
# is the multiply with its carry chain inlined — the shape the walk's call
# returns from, not a call to a second symbol.
#
# Exit status: 0 when the fixtures are written; 3 when an input is missing or a
# derivation check fails.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)

src=kernel/json/stage2.c
inventory=$here/stage2.callees.tsv

fail() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

# ---------------------------------------------------------------------------
# --emit-pins [<symbol>]: the body literal and block pins a callee module holds
#
# The pinned body is parsed from the fixture, not copied from it, so a
# regeneration that drifts fails the build rather than pinning text nobody read:
# this mode prints the Lean the module holds.  `<symbol>` is one of the three
# fixtures, `num_d8_el1` by default; the prefix it generates names with is the
# module's own (`numD8`, `numEl`, `stkMul`), and the declared layout is the one
# the fixture's struct types need (`%struct.EPow` for `num_el_el1`, whose extent
# `JsonStage2NumFastCalleeEl` states and whose `#guard` holds to the body's own
# `getelementptr [91 x %struct.EPow]` stride).
#
#   nix develop -c bash probes/install/ir/capture-stage2-callees.sh --emit-pins
#   nix develop -c bash probes/install/ir/capture-stage2-callees.sh --emit-pins num_el_el1
# ---------------------------------------------------------------------------
if [ "${1:-}" = "--emit-pins" ]; then
  symbol=${2:-num_d8_el1}
  case "$symbol" in
    num_d8_el1) prefix=numD8 ;;
    num_el_el1) prefix=numEl ;;
    stk_mul_u64) prefix=stkMul ;;
    *) fail "--emit-pins: no pin prefix for '$symbol'" ;;
  esac
  fixture=$here/stage2.callee.$symbol.ll
  [ -f "$fixture" ] || fail "absent: $fixture (run the capture first)"
  command -v lake >/dev/null 2>&1 || fail "lake is not on PATH"
  gen=$repo/.lake/tmp-callee-pins.lean
  cat > "$gen" <<'LEANGEN'
import LeanLLVM.Parser

open LeanLLVM

namespace Gen

def hexOf (w : Nat) (v : BitVec w) : String :=
  let digits := (w + 3) / 4
  let s := String.ofList (Nat.toDigits 16 v.toNat)
  "0x" ++ String.ofList (List.replicate (digits - s.length) '0') ++ s ++ "#" ++ toString w

partial def tyStr : Ty → String
  | .int w => s!"(Ty.int {w})"
  | .ptr => "Ty.ptr"
  | .void => "Ty.void"
  | .double => "Ty.double"
  | .vec n e => s!"(Ty.vec {n} {tyStr e})"
  | .array n e => s!"(Ty.array {n} {tyStr e})"
  | .struct n b => s!"(Ty.struct \"{n}\" {b})"

def constStr : Const → String
  | .int w v => s!"(Const.int {w} {hexOf w v})"
  | .null => "Const.null" | .undef => "Const.undef" | .poison => "Const.poison"
  | .splat n w v => s!"(Const.splat {n} {w} {hexOf w v})"
  | .vector w lanes => s!"(Const.vector {w} [{String.intercalate ", " (lanes.map (hexOf w))}])"
  | .float b => s!"(Const.float {hexOf 64 b})"

def opStr : Operand → String
  | .reg n => s!"(Operand.reg \"{n}\")"
  | .global n => s!"(Operand.global \"{n}\")"
  | .imm c => s!"(Operand.imm {constStr c})"

def predStr : IPred → String
  | .eq => "IPred.eq" | .ne => "IPred.ne" | .ult => "IPred.ult" | .ule => "IPred.ule"
  | .ugt => "IPred.ugt" | .uge => "IPred.uge" | .slt => "IPred.slt" | .sle => "IPred.sle"
  | .sgt => "IPred.sgt" | .sge => "IPred.sge"

def binStr : BinOp → String
  | .add => "BinOp.add" | .sub => "BinOp.sub" | .mul => "BinOp.mul" | .udiv => "BinOp.udiv"
  | .sdiv => "BinOp.sdiv" | .urem => "BinOp.urem" | .srem => "BinOp.srem" | .and => "BinOp.and"
  | .or => "BinOp.or" | .xor => "BinOp.xor" | .shl => "BinOp.shl" | .lshr => "BinOp.lshr"
  | .ashr => "BinOp.ashr"

def argsStr (args : List (Ty × Operand)) : String :=
  "[" ++ String.intercalate ",\n                             "
    (args.map fun (t, o) => s!"({tyStr t}, {opStr o})") ++ "]"

def instrStr : Instr → String
  | .binop d op w a b => s!"Instr.binop \"{d}\" ({binStr op}) {w} {opStr a} {opStr b}"
  | .icmp d p w a b => s!"Instr.icmp \"{d}\" ({predStr p}) {w} {opStr a} {opStr b}"
  | .icmpPtr d p a b => s!"Instr.icmpPtr \"{d}\" ({predStr p}) {opStr a} {opStr b}"
  | .select d t c a b => s!"Instr.select \"{d}\" {tyStr t} {opStr c} {opStr a} {opStr b}"
  | .trunc d wi wo v => s!"Instr.trunc \"{d}\" {wi} {wo} {opStr v}"
  | .zext d wi wo v => s!"Instr.zext \"{d}\" {wi} {wo} {opStr v}"
  | .sext d wi wo v => s!"Instr.sext \"{d}\" {wi} {wo} {opStr v}"
  | .ptrtoint d v => s!"Instr.ptrtoint \"{d}\" {opStr v}"
  | .inttoptr d v => s!"Instr.inttoptr \"{d}\" {opStr v}"
  | .uitofp d w v => s!"Instr.uitofp \"{d}\" {w} {opStr v}"
  | .fmul d a b => s!"Instr.fmul \"{d}\" {opStr a} {opStr b}"
  | .fdiv d a b => s!"Instr.fdiv \"{d}\" {opStr a} {opStr b}"
  | .fneg d v => s!"Instr.fneg \"{d}\" {opStr v}"
  | .fcmp d p a b => s!"Instr.fcmp \"{d}\" (FPred.oeq) {opStr a} {opStr b}"
  | .bitcastToInt d v => s!"Instr.bitcastToInt \"{d}\" {opStr v}"
  | .bitcastToDouble d v => s!"Instr.bitcastToDouble \"{d}\" {opStr v}"
  | .alloca d t al => s!"Instr.alloca \"{d}\" {tyStr t} {al}"
  | .load d t p => s!"Instr.load \"{d}\" {tyStr t} {opStr p}"
  | .store t v p => s!"Instr.store {tyStr t} {opStr v} {opStr p}"
  | .gep d t b o => s!"Instr.gep \"{d}\" {tyStr t} {opStr b} {opStr o}"
  | .icmpVec d p n w a b => s!"Instr.icmpVec \"{d}\" ({predStr p}) {n} {w} {opStr a} {opStr b}"
  | .binopVec d op n w a b => s!"Instr.binopVec \"{d}\" ({binStr op}) {n} {w} {opStr a} {opStr b}"
  | .bitcastMask d n v => s!"Instr.bitcastMask \"{d}\" {n} {opStr v}"
  | .extractelement d n w v i => s!"Instr.extractelement \"{d}\" {n} {w} {opStr v} {opStr i}"
  | .insertelement d n w v e i => s!"Instr.insertelement \"{d}\" {n} {w} {opStr v} {opStr e} {opStr i}"
  | .shuffleVec d n w a b m => s!"Instr.shuffleVec \"{d}\" {n} {w} {opStr a} {opStr b} {m}"
  | .vecBitcast d n w m jw v => s!"Instr.vecBitcast \"{d}\" {n} {w} {m} {jw} {opStr v}"
  | .call d t c args => s!"Instr.call \"{d}\" {tyStr t} \"{c}\" {argsStr args}"
  | .callVoid c args => s!"Instr.callVoid \"{c}\" {argsStr args}"
  | .phi d t inc =>
      s!"Instr.phi \"{d}\" {tyStr t} [" ++ String.intercalate ",\n                                       "
        (inc.map fun (b, o) => s!"(\"{b}\", {opStr o})") ++ "]"

def termStr : Term → String
  | .ret t (some v) => s!"Term.ret {tyStr t} (some {opStr v})"
  | .ret t none => s!"Term.ret {tyStr t} none"
  | .br d => s!"Term.br \"{d}\""
  | .condbr c t f => s!"Term.condbr {opStr c} \"{t}\" \"{f}\""
  | .unreachable => "Term.unreachable"

def pinList (b : Block) : String :=
  "[\n" ++ String.intercalate ",\n" (b.instrs.map fun i => "          " ++ instrStr i) ++ "]"

def blockStr (b : Block) : String :=
  "\n    { name := \"" ++ b.name ++ "\",\n      instrs := [\n" ++
    String.intercalate ",\n" (b.instrs.map fun i => "        " ++ instrStr i) ++
    "\n      ],\n      term := " ++ termStr b.term ++ " }"

def fnStr (f : Function) : String :=
  "{ name := \"" ++ f.name ++ "\",\n  retTy := " ++ tyStr f.retTy ++ ",\n  params := [" ++
    String.intercalate ",\n             " (f.params.map fun (n, t) => s!"(\"{n}\", {tyStr t})") ++
    "],\n  blocks := [" ++ String.intercalate "," (f.blocks.map blockStr) ++ "] }"

def sanitize (s : String) : String :=
  String.ofList (s.toList.map fun c => if c.isAlphanum then c else '_')

def camel (s : String) : String :=
  let parts := (s.splitOn ".").filter (· ≠ "")
  String.join (parts.map fun p =>
    match p.toList with
    | [] => ""
    | c :: rest => String.singleton c.toUpper ++ String.ofList rest)

def defOf (pre : String) (b : Block) : String :=
  "def " ++ pre ++ camel b.name ++ "Instrs : List Instr :=\n  [\n" ++
    String.intercalate ",\n" (b.instrs.map fun i => "    " ++ instrStr i) ++ "]\n"

def pin (pre : String) (b : Block) (lhs : String) : String :=
  "theorem " ++ pre ++ "_findBlock_" ++ sanitize b.name ++ " :\n    " ++ pre ++
    "Body.findBlock \"" ++ b.name ++
    "\" = some ⟨\"" ++ b.name ++ "\", " ++ lhs ++ ", " ++ termStr b.term ++ "⟩ := by decide\n"

end Gen

open Gen

/-- The declared layout a fixture's struct types need: the extent is the
datalayout's, and the parser takes it from the caller rather than recomputing it
from fields.  `%struct.EPow` is `uint64_t hi, lo; int32_t e` — twenty bytes
padded to its eight-byte alignment, so twenty-four — and the body's own
`getelementptr [91 x %struct.EPow]` is the stride that number declares. -/
def layoutOf : String → Layout
  | "num_el_el1" => [("EPow", 24)]
  | _ => []

def main (args : List String) : IO Unit := do
  let (symbol, pre) ← match args with
    | [s, p] => pure (s, p)
    | _ => do
        IO.eprintln "usage: tmp-callee-pins.lean <symbol> <prefix>"
        IO.Process.exit 2
  let path := s!"probes/install/ir/stage2.callee.{symbol}.ll"
  let src ← IO.FS.readFile path
  match parseModuleWith (layoutOf symbol) src with
  | .error e => IO.eprintln s!"ERROR: {e}"; IO.Process.exit 3
  | .ok m =>
    match m.functions.head? with
    | none => IO.eprintln "ERROR: no function"; IO.Process.exit 3
    | some f =>
      if f.name ≠ symbol then
        IO.eprintln s!"ERROR: the fixture's function is {f.name}"; IO.Process.exit 3
      IO.println "-- § the body literal"
      IO.println ("def " ++ pre ++ "Body : Function :=\n" ++ fnStr f)
      IO.println "-- § the instruction lists"
      for b in f.blocks do IO.print (defOf pre b ++ "\n")
      IO.println "-- § the pins"
      for b in f.blocks do IO.print (pin pre b (pre ++ camel b.name ++ "Instrs"))
      IO.eprintln s!"emitted the literal and pins for {f.blocks.length} blocks, {(f.blocks.flatMap (·.instrs)).length} instructions"
LEANGEN
  ( cd "$repo" && lake env lean --run "$gen" "$symbol" "$prefix" 2>/dev/null |
      grep -v '^lean-llvm: Lean' )
  rc=${PIPESTATUS[0]}
  rm -f "$gen"
  exit $rc
fi

[ -f "$repo/$src" ] || fail "absent: $repo/$src"
command -v clang >/dev/null 2>&1 || fail "clang is not on PATH"
command -v opt >/dev/null 2>&1 || fail "opt is not on PATH"

work=$(mktemp -d "$repo/.lake/tmp-stage2-callees.XXXXXX" 2>/dev/null) ||
  work=$(mktemp -d) ||
  fail "cannot create a work directory"
trap 'rm -rf "$work"' EXIT

flags=(-S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11
       -falign-loops=64 -falign-functions=64)
compile() { ( cd "$repo" && clang -I kernel/json "$@" ); }

# ---------------------------------------------------------------------------
# The source transform: the helper capture's, plus `stk_mul_u64`
# ---------------------------------------------------------------------------

sed -e 's/__attribute__((always_inline)) static inline/__attribute__((noinline)) static inline/g' \
    -e 's/#define EL_ENTRY __attribute__((always_inline)) static inline/#define EL_ENTRY __attribute__((noinline)) static inline/' \
    -e 's/^static void od_gap_recover(OdCur \*c, const OdTok \*t) {$/__attribute__((noinline)) static void od_gap_recover(OdCur *c, const OdTok *t) {/' \
    -e 's/^static void stk_mul_u64(StkBn \*a, uint64_t m) {/__attribute__((noinline)) static void stk_mul_u64(StkBn *a, uint64_t m) {/' \
    "$repo/$src" > "$work/step1.c"
grep -q '^__attribute__((noinline)) static void stk_mul_u64(StkBn \*a, uint64_t m) {' "$work/step1.c" ||
  fail "the source has no \`static void stk_mul_u64(StkBn *a, uint64_t m)\` line to mark noinline"

awk '{ if (hold) { print "__attribute__((always_inline)) static inline uint64_t"; hold = 0 }
       if ($0 == "__attribute__((noinline)) static inline uint64_t") { hold = 1; next }
       print }
     END { if (hold) exit 1 }' "$work/step1.c" > "$work/stage2.noinline.c" ||
  fail "the s2_walk attribute was not restored; the transform is not the one this script describes"

# ---------------------------------------------------------------------------
# The emission
# ---------------------------------------------------------------------------

compile "${flags[@]}" -fno-discard-value-names "$work/stage2.noinline.c" -o "$work/named.ll"
opt -S -passes=lower-switch "$work/named.ll" -o "$work/lowered.ll" ||
  fail "opt refused to lower the switch"
command -v llvm-as >/dev/null 2>&1 || fail "llvm-as is not on PATH"
llvm-as "$work/lowered.ll" -o "$work/lowered.bc" ||
  fail "llvm-as refused the lowering the bodies are extracted from"
opt -passes=verify "$work/lowered.bc" -o /dev/null ||
  fail "opt -passes=verify rejected the lowering the bodies are extracted from"

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

extract_define() { # <symbol> <out>
  awk -v sym="$1" '
    $0 ~ "^define .*@" sym "\\(" { inblock = 1 }
    inblock { print }
    inblock && $0 == "}" { exit }
  ' "$work/lowered.ll" > "$2"
  [ -s "$2" ] || fail "the emission has no \`define\` block for @$1"
}

# The declarations and struct types the extracted body needs to assemble on its
# own: the intrinsics and callees it names, and the module's own
# `%struct.<name> = type …` lines for the aggregates it indexes.  The extraction
# takes one `define` block, so neither is in the fixture; they are read from the
# module the block came out of, never written into it.
types_for() { # <body> <out>
  local body=$1 out=$2
  : > "$out"
  local name
  while IFS= read -r name; do
    grep -E "^%struct\.$name = type " "$work/lowered.ll" >> "$out" ||
      fail "the module has no definition for %struct.$name"
  done < <(grep -oE '%struct\.[A-Za-z0-9_]+' "$body" | sed -E 's/%struct\.//' | sort -u)
}
declarations_for() { # <body> <out>
  local body=$1 out=$2
  : > "$out"
  awk '
    /^declare / {
      line = $0
      sub(/^declare [^@]*@/, "", line)
      sub(/\(.*/, "", line)
      print line "\t" $0
    }' "$work/lowered.ll" > "$work/decls.tsv"
  local sym decl
  while IFS= read -r sym; do
    decl=$(awk -F'\t' -v s="$sym" '$1 == s { print $2; exit }' "$work/decls.tsv")
    [ -n "$decl" ] || continue
    printf '%s\n' "$decl" >> "$out"
  done < <(grep -oE 'call [^@]*@[A-Za-z0-9_.]+' "$body" |
             sed -E 's/.*@//' | sort -u)
}

# ---------------------------------------------------------------------------
# The captured bodies
# ---------------------------------------------------------------------------

# `num_d8_el1`'s `poison` lanes, and the ledger that accounts for them.
#
# The emission writes three literal vectors whose trailing lanes are `poison`:
# the `insertelement`'s two-lane source, the `pmadd.ub.sw` constant's upper
# eight bytes and the `pmadd.wd` constant's upper two words.  The fragment's
# `Const.vector` carries lane *values* and `Value.vec` carries none, so a
# poisoned lane is not a value the model can hold, and this capture substitutes
# the defined lane 0 exactly as `capture-escape.sh` does for the hex reader's two
# constants (class 6, "substituted").  Each substitution is sound where it is
# made: the `insertelement`'s poisoned lane 0 is the one the instruction
# overwrites; the `pmadd.ub.sw` constant's lanes 8-15 produce result lanes 4-7,
# which nothing reads; and the `pmadd.wd` constant's lanes 4-7 produce result
# lanes 2-3, which nothing reads.  The body's observable — the returned word and
# the four bytes at `%val` — is lanes 0 and 1 of the `pmadd.wd` result, which
# read lanes 0-3 of its input and so lanes 0-7 of the `pmadd.ub.sw` result.
poison_rewrites() { # <in> <out> <ledger>
  local in=$1 out=$2 ledger=$3
  : > "$ledger"
  local line ty
  while IFS=$'\t' read -r line content; do
    while read -r ty; do
      printf '6\tsubstituted\t%s poison\t%s 0\t%s\t%s\n' "$ty" "$ty" "$line" \
        "poison replaced by the defined lane 0: the lane is one the body overwrites or one whose only readers are result lanes the body never reads" \
        >> "$ledger"
    done < <(grep -oE '\bi(8|16|32|64) poison\b' <<<"$content" | sed -E 's/ poison//' | sort -u)
  done < <(grep -n 'poison' "$in" | sed -E 's/^([0-9]+):/\1\t/')
  sed -E 's/\b(i8|i16|i32|i64) poison\b/\1 0/g' "$in" > "$out"
  grep -qE '\bi(8|16|32|64) poison\b' "$out" &&
    fail "a poison lane survived the substitution"
  [ -s "$ledger" ] || fail "no poison lane was substituted, so the ledger would be empty"
}

capture() { # <symbol> <rewrite: none|nf> <assemble: yes|no> [why-not]
  local sym=$1 mode=$2 asms=$3 why=${4:-}
  extract_define "$sym" "$work/$sym.raw.ll"
  strip_body "$work/$sym.raw.ll" "$work/$sym.stripped.ll"
  case "$mode" in
    none) cp "$work/$sym.stripped.ll" "$work/$sym.body.ll" ;;
    nf)
      # `num_d8_el1` takes the two strip rewrites `num_fast_el1` already takes —
      # the `llvm.umin.i64` fold and the dropped `exact` flag — and the `poison`
      # substitution above.
      sed -E -e 's/^  (%[A-Za-z0-9_.]+) = tail call /  \1 = call /' "$work/$sym.stripped.ll" > "$work/$sym.nf1.ll"
      sed -E -e 's/^  (%[A-Za-z0-9_.]+) = call i64 @llvm\.umin\.i64\(i64 ([^,]+), i64 ([^)]+)\)$/  \1.min = icmp ult i64 \2, \3\n  \1 = select i1 \1.min, i64 \2, i64 \3/' \
        -e 's/ashr exact /ashr /' "$work/$sym.nf1.ll" > "$work/$sym.nf2.ll"
      poison_rewrites "$work/$sym.nf2.ll" "$work/$sym.body.ll" "$work/$sym.rewrites.tsv"
      ;;
    el)
      # `num_el_el1` takes one rewrite: the second argument of its
      # `llvm.ctlz.i64` call is written `i1 true`, and the fixture holds
      # `i1 false`.  The parser admits only the `false` form, because `true`
      # promises poison at the zero word and this model has no poison; the two
      # flags denote the same value wherever the operand is nonzero, and the
      # only path to this call is the `if.end4` block, which the entry's
      # `%w == 0` test cannot reach with a zero word.  So the rewrite drops a
      # promise no execution of the body observes, and the ledger records it as
      # a weakened token rather than a substitution.  The instruction is
      # rewritten once, below, and the ledger row is built from the line it is
      # on: a second occurrence, or none, fails the capture.
      local hits
      hits=$(grep -cE '@llvm\.ctlz\.i64\(i64 [^,]+, i1 true\)' "$work/$sym.stripped.ll" || true)
      [ "$hits" = 1 ] ||
        fail "$sym: expected exactly one \`llvm.ctlz.i64 … i1 true\` call to weaken, found $hits"
      : > "$work/$sym.rewrites.tsv"
      awk -v ledger="$work/$sym.rewrites.tsv" '
        {
          line = $0
          if (match(line, /@llvm\.ctlz\.i64\([^)]*\)/)) {
            from = substr(line, RSTART, RLENGTH)
            to = from
            sub(/i1 true\)$/, "i1 false)", to)
            printf "n/a\tweakened\t%s\t%s\t%d\t%s\n", from, to, NR,
              "the flag makes the zero word poison and lets the optimizer assume a nonzero operand; the false form returns the width there, and the entry\047s `%w == 0` return keeps the zero word off the only path to this call, so no execution observes the difference" >> ledger
          }
          print line
        }' "$work/$sym.stripped.ll" |
        sed -E 's/(@llvm\.ctlz\.i64\(i64 [^,]+, )i1 true\)/\1i1 false)/' > "$work/$sym.body.ll"
      ;;
    *) fail "unknown capture mode $mode" ;;
  esac
  declarations_for "$work/$sym.body.ll" "$work/$sym.decls.ll"
  types_for "$work/$sym.body.ll" "$work/$sym.types.ll"
  # The body is a `define` block with its callees' declarations and the module's
  # aggregate types missing, as the helper fixtures are.  A body that names no
  # module-level global assembles and verifies once they are supplied, and that
  # is a check on the capture rather than a change to the text; one that reads a
  # global cannot, because the symbol's declaration is outside the extraction.
  case "$asms" in
    yes)
      cat "$work/$sym.types.ll" "$work/$sym.body.ll" "$work/$sym.decls.ll" > "$work/$sym.asm.ll"
      llvm-as "$work/$sym.asm.ll" -o "$work/$sym.bc" ||
        fail "$sym does not assemble with its own declarations"
      opt -passes=verify "$work/$sym.bc" -o /dev/null ||
        fail "$sym does not verify"
      printf 'yes\n' > "$work/$sym.asmverdict"
      ;;
    no)
      [ -n "$why" ] || fail "$sym is unchecked without a reason"
      printf 'no: %s\n' "$why" > "$work/$sym.asmverdict"
      ;;
    *) fail "unknown assemble mode $asms" ;;
  esac
}

capture num_d8_el1 nf yes
capture num_el_el1 el no "reads the module-level @EPOW table, whose declaration the extracted block does not carry"
capture stk_mul_u64 none yes

banner() { # <symbol> <note>
  cat <<EOF
; The stage-2 callee \`$1\`, as emitted, in the fragment \`LeanLLVM.Semantics\`
; models.  Regenerate with:
;
;   nix develop -c bash probes/install/ir/capture-stage2-callees.sh
;
; from kernel/json/stage2.c, emitted at the measured compiler line with
; \`noinline\` on every helper and on \`stk_mul_u64\`, then the same token strip
; capture-stage2.sh applies.  $2
;
EOF
}

note_d8='`num_d8_el1` takes two of the same strip rewrites `num_fast_el1` does — its `llvm.umin.i64` folds to the icmp/select pair and `ashr exact` loses its flag — and one substitution: its three literal vectors carry `poison` in lanes the body overwrites or never reads, and each becomes the defined lane 0, as `capture-escape.sh` does for the hex reader'"'"'s constants.  `stage2.callees.rewrites.tsv` accounts for every substitution.  Its eight-byte read is the body'"'"'s own `load i64`, and its two `madd` calls are the x86 intrinsics `escapeCalls` already answers.'
note_el='`num_el_el1` calls `el_exact` and `el_pack` out of line and reads the `EPOW` table through a global symbol operand, so it is not a closed unit: its fixture needs those two bodies and the table staged before it denotes.  Its one rewrite is the `llvm.ctlz.i64` flag: the emission writes `i1 true` and the fixture holds `i1 false`, because the parser admits only the `false` form and the entry'"'"'s `%w == 0` return keeps the zero word off the path to the call, so the two flags agree wherever the body executes; `stage2.callees.rewrites.tsv` records the row.'
note_stk='`stk_mul_u64` calls `stk_mul_add`, which the emission inlines, so the body is the multiply with its `unsigned __int128` carry chain in the loop and the tail word the trailing `while` appends.  It calls nothing and reads no global.'

{ banner num_d8_el1 "$note_d8"; cat "$work/num_d8_el1.body.ll"; } > "$here/stage2.callee.num_d8_el1.ll"
{ banner num_el_el1 "$note_el"; cat "$work/num_el_el1.body.ll"; } > "$here/stage2.callee.num_el_el1.ll"
{ banner stk_mul_u64 "$note_stk"; cat "$work/stk_mul_u64.body.ll"; } > "$here/stage2.callee.stk_mul_u64.ll"

{
  printf '# stage2.callees.rewrites.tsv -- generated by\n'
  printf '# probes/install/ir/capture-stage2-callees.sh; do not edit.\n'
  printf '#\n'
  printf '# Every place the capture *rewrote* a token of the emission instead of\n'
  printf '# removing it, with the reason the rewrite is sound.  Two kinds:\n'
  printf '#\n'
  printf '#   substituted  a token replaced by a defined one: `poison`, the class\n'
  printf '#                `capture-escape.sh` records for the hex reader'"'"'s two\n'
  printf '#                vector constants.  `num_d8_el1`'"'"'s three literal vectors\n'
  printf '#                carry it in lanes the body overwrites (the\n'
  printf '#                `insertelement`'"'"'s lane 0) or whose results the body never\n'
  printf '#                reads (the `pmadd` constants'"'"' upper lanes), so the defined\n'
  printf '#                lane 0 stands in.\n'
  printf '#   weakened     a token replaced by one that promises less: the second\n'
  printf '#                argument of `num_el_el1`'"'"'s one `llvm.ctlz.i64` call is\n'
  printf '#                written `i1 true` and held as `i1 false`.  LLVM'"'"'s flag\n'
  printf '#                `true` makes the zero word poison and licenses the\n'
  printf '#                optimizer to assume a nonzero operand; the parser admits\n'
  printf '#                only `false`, which returns the width at zero, so the\n'
  printf '#                fixture states the weaker promise.  The entry'"'"'s\n'
  printf '#                `%%w == 0` return keeps the zero word off the only path to\n'
  printf '#                the call, so the two flags denote the same value wherever\n'
  printf '#                the body executes.\n'
  printf '#\n'
  printf '# The `from` column is the emitted token, the `to` column the one the\n'
  printf '# fixture holds, and `line` is the line of the extracted body.  The\n'
  printf '# `class` column is the normalisation class where the row is one of\n'
  printf '# `capture-escape.sh`'"'"'s (the `poison` substitution is class 6), and\n'
  printf '# `n/a` where the row is this capture'"'"'s own rewrite (`weakened`).\n'
  printf '#\n'
  printf '# A callee with no row is a body the capture did not rewrite.  `stk_mul_u64`\n'
  printf '# is such a body: the strip removes surface, and it needs no token\n'
  printf '# substituted or weakened.\n'
  printf 'class\tkind\tfrom\tto\tline\treason\n'
  cat "$work/num_d8_el1.rewrites.tsv"
  cat "$work/num_el_el1.rewrites.tsv"
} > "$here/stage2.callees.rewrites.tsv"

{
  printf '# The three out-of-line callees as emitted.\n'
  printf '# Regenerate with probes/install/ir/capture-stage2-callees.sh.\n'
  printf '#\n'
  printf '# `blocks` counts label lines and `instr_lines` counts lines that begin with\n'
  printf '# two spaces, which includes an instruction\x27s continuation lines; neither is\n'
  printf '# the parsed shape.  The parsed shapes below are the output of\n'
  printf '# `lake env lean --run probes/install/ir/parse-callees.lean`, read back here,\n'
  printf '# so the counts and the layout literal are the parse\x27s own:\n'
  # The probe is the one place the parsed shape is stated; the three lines
  # below are its rows, formatted.  A refusal there stops the capture rather
  # than being written into the inventory as a shape.
  command -v lake >/dev/null 2>&1 || fail "lake is not on PATH (needed for the parsed shapes)"
  # The probe imports `LeanLLVM.Parser`, so the library's own sources must be
  # built first: a stale olean would report a shape for a parser that is not the
  # one the fixtures are read by.
  ( cd "$repo" && lake build LeanLLVM.Parser ) >/dev/null 2>&1 ||
    fail "lake could not build LeanLLVM.Parser, which the parsed-shape probe imports"
  shapes=$( cd "$repo" && lake env lean --run probes/install/ir/parse-callees.lean 2>/dev/null |
              grep -v '^lean-llvm: Lean' ) ||
    fail "the parsed-shape probe failed (by hand: lake env lean --run probes/install/ir/parse-callees.lean)"
  shape_field() { awk -F'\t' -v s="$1" -v k="$2" '$1 == s { print $k }' <<<"$shapes"; }
  for sym in num_d8_el1 num_el_el1 stk_mul_u64; do
    [ -n "$(shape_field "$sym" 2)" ] || fail "the parsed-shape probe has no row for $sym"
    [ "$(shape_field "$sym" 2)" != "ERROR" ] ||
      fail "the parsed-shape probe refused $sym: $(shape_field "$sym" 3)"
    case "$sym" in
      num_d8_el1)
        printf '#   %-11s %s blocks, %s instructions, %s params  (pinned in\n' \
          "$sym" "$(shape_field "$sym" 2)" "$(shape_field "$sym" 3)" "$(shape_field "$sym" 4)"
        printf '#               JsonStage2NumFastCalleeD8, whose #guard states the counts)\n' ;;
      stk_mul_u64)
        printf '#   %-11s %s blocks, %s instructions, %s params\n' \
          "$sym" "$(shape_field "$sym" 2)" "$(shape_field "$sym" 3)" "$(shape_field "$sym" 4)" ;;
      num_el_el1)
        printf '#   %-11s %s blocks, %s instructions, %s params  (pinned in\n' \
          "$sym" "$(shape_field "$sym" 2)" "$(shape_field "$sym" 3)" "$(shape_field "$sym" 4)"
        printf '#               JsonStage2NumFastCalleeEl, whose #guard states the counts;\n'
        printf '#               parsed with the declared layout %s)\n' "$(shape_field "$sym" 5)" ;;
    esac
  done
  printf '#\n'
  printf '# symbol\tlines\tblocks\tinstr_lines\tparams\tsymbols_called\tglobals\tassembles\n'
  for sym in num_d8_el1 num_el_el1 stk_mul_u64; do
    f="$work/$sym.body.ll"
    lines=$(wc -l < "$f" | tr -d ' ')
    blocks=$(grep -cE '^[A-Za-z0-9_.-]+:' "$f" || true)
    instrs=$(grep -cE '^  ' "$f" || true)
    params=$(sed -E -e 's/.*\(//' -e 's/\).*//' <<<"$(head -1 "$f")" | awk -F', ' '{ print NF }')
    called=$(grep -oE 'call [^@]*@[A-Za-z0-9_.]+' "$f" | sed -E 's/.*@//' | sort -u | paste -sd, - || true)
    globals=$(grep -oE '@[A-Za-z0-9_.]+' "$f" | sort -u | paste -sd, - || true)
    asm=$(cat "$work/$sym.asmverdict")
    printf '%s\t%d\t%d\t%d\t%d\t%s\t%s\t%s\n' "$sym" "$lines" "$blocks" "$instrs" "$params" "$called" "$globals" "$asm"
  done
} > "$inventory"

printf 'wrote %s and %s\n' "$here/stage2.callee.*.ll" "$inventory"
