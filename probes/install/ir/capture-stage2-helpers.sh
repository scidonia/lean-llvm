#!/usr/bin/env bash
# Regenerate the stage-2 helpers' emitted bodies, as the emission holds them
# before the walk's own fixture reduces them to calls.
#
# Run through the flake, from the repository root:
#
#   nix develop -c bash probes/install/ir/capture-stage2-helpers.sh
#
# The bodies' Lean pins are generated from the same parse rather than copied
# from the text; `--emit-pins [symbol]` prints them, which is how
# LeanLLVM/Refinement/JsonStage2HelperIRNumFast's generated section and
# JsonStage2HelperIROdScalar's body literal are produced (`num_fast_el1` by
# default, `od_scalar_value` the other configured body):
#
#   nix develop -c bash probes/install/ir/capture-stage2-helpers.sh --emit-pins
#   nix develop -c bash probes/install/ir/capture-stage2-helpers.sh --emit-pins od_scalar_value
#
# Input
#   kernel/json/stage2.c   the stage-2 unit: the seven helpers the walk and the
#                          additive entry call out of line, and the walk and
#                          wrapper around them
#
# Output (one fixture per helper the fragment models, and the inventory of all
# seven)
#   stage2.helper.s2_init.ll
#   stage2.helper.s2_value_pos.ll
#   stage2.helper.s2_after_value.ll
#   stage2.helper.s2_string_body.ll
#   stage2.helper.od_scalar_value.ll
#   stage2.helper.od_gap_recover.ll
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
# `od_gap_recover` is the seventh, and its two rewrites are the same kinds: the
# walk's `llvm.umin.i64` fold (its literal compare takes an unsigned minimum at
# `i64`) and the refusal record's message word, which carries the `err_set` site's
# tag rather than a symbol address — the model's `GapWrite` records which site ran
# and nothing reads the word (rewrite r6), so the store is `i64 <tag>` where the
# text stores `ptr @.str.N`.  The body is emitted only when the source transform
# gives it `noinline` too: the source spells it `static void`, so at the measured
# line clang inlines it into `s2_walk`, and the additive entry is the fixture that
# kept it a call.  The argument list the emission produces is that entry's
# declaration exactly — `(ptr %c, i64 %t.0.val)` — because SROA drops the token
# pointer's dead fields, so the cross-check below reads `stage2-noevent.candidate.ll`
# for this symbol and `stage2.candidate.ll` for the other six.
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
#                    Three surfaces keep the raw text out of the fragment, and
#                    this capture closes them in the two ways the format allows:
#
#                      %struct.Stk   the extraction takes one `define` block, so
#                                    the module's `%struct.Stk = type { … }` line
#                                    is not in the text.  The parser takes a
#                                    struct's extent from its `Layout` argument
#                                    (`expectAllocaTy`), so the extent is the
#                                    pin's to supply: 1568 bytes, which is the
#                                    number the body's own
#                                    `llvm.lifetime.start.p0(i64 1568, …)` names
#                                    and the checks below hold the two to.
#                      llvm.umin.i64 folded to `icmp ult` and `select` at i64 —
#                                    the same function the fragment's umin.i32
#                                    is, at the width the text uses.
#                      ashr exact    the `exact` flag is dropped, so the pinned
#                                    body is the flag-erased form.  The flag's
#                                    obligation — the bits shifted out are zero
#                                    — is then a staging fact the text does not
#                                    carry, and it is recorded as such here and
#                                    in the ledger rather than assumed.
#
#                    The double reader accepts the body's literals —
#                    `-0.000000e+00` and `0.000000e+00` included.
#
# Every helper's text is written to the tree now that every one of them parses:
# the inventory records the shape and the verdict, and the checks below refuse
# if the emission stops having the measured constructs.
#
# Exit status: 0 when the fixtures and the inventory are written; 3 when an
# input is missing or a derivation check fails.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)

src=kernel/json/stage2.c
walk=$here/stage2.candidate.ll
noevent=$here/stage2-noevent.candidate.ll
inventory=$here/stage2.helpers.tsv

fail() { printf 'SETUP: %s\n' "$*" >&2; exit 3; }

# ---------------------------------------------------------------------------
# --emit-pins: the block pins `JsonStage2HelperIRNumFast` holds
#
# The first body with more than a handful of blocks is pinned block by block,
# and its pins are *generated from the parse* rather than copied from the
# fixture: this mode parses `stage2.helper.num_fast_el1.ll` under the declared
# layout and prints the Lean text the module holds — the whole-body literal, the
# instruction lists the runs read, the two hundred and fifty-five `findBlock`
# equations, and the instruction-list projections.  The module's `#guard`s are
# what hold that text to the fixture; this mode is how the text is produced.
#
#   nix develop -c bash probes/install/ir/capture-stage2-helpers.sh --emit-pins
#
# Exit status: 0 when the text is printed; 3 when the fixture is missing or the
# parser refuses it.
# ---------------------------------------------------------------------------
if [ "${1:-}" = "--emit-pins" ]; then
  sym=${2:-num_fast_el1}
  case "$sym" in
    num_fast_el1 | od_scalar_value | od_gap_recover) ;;
    *) fail "--emit-pins: no pin configuration for ${sym} (num_fast_el1, od_scalar_value, od_gap_recover)" ;;
  esac
  fixture=$here/stage2.helper.$sym.ll
  [ -f "$fixture" ] || fail "absent: $fixture"
  command -v lake >/dev/null 2>&1 || fail "lake is not on PATH"
  gen=$repo/.lake/tmp-numfast-pins.lean
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

def instrsEq (pre : String) (b : Block) : String :=
  "theorem " ++ pre ++ camel b.name ++ "Instrs_eq :\n    (" ++ pre ++ "Body.findBlock \"" ++
    b.name ++ "\").map (·.instrs) = some " ++ pre ++ camel b.name ++
    "Instrs := by decide\n"

end Gen

open Gen

/-- The blocks a run reads: the refusal arm's four, the integer digit run's four
and its exit, and each of the fraction and exponent runs' four blocks with the
blocks its exit lands in.  `if.end230` is both runs' end-of-lexeme exit and the
merge `JsonStage2NumFastCounters` reads. -/
def runBlocks : List String :=
  ["entry", "land.lhs.true", "if.end", "if.then5", "if.end6", "if.else", "if.else66",
   "cleanup300", "land.lhs.true41", "while.body52", "if.then55", "if.end62", "if.end68",
   "land.lhs.true119", "while.body130", "if.then133", "if.end140", "if.end144",
   "land.lhs.true195", "while.body206", "if.then209", "if.end216", "cleanup223.thread",
   "if.end226", "if.end230"]

/-- The fixture, its declared layout, the prefix of the generated names, and the
blocks a run reads (an empty list emits the body literal alone). -/
def config : String → Option (String × List (String × Nat) × String × List String)
  | "num_fast_el1" =>
      some ("probes/install/ir/stage2.helper.num_fast_el1.ll", [("Stk", 1568)], "numFast",
        runBlocks)
  | "od_scalar_value" =>
      some ("probes/install/ir/stage2.helper.od_scalar_value.ll", [], "odScalarValue", [])
  | "od_gap_recover" =>
      some ("probes/install/ir/stage2.helper.od_gap_recover.ll", [], "odGapRecover", [])
  | _ => none

def main : IO Unit := do
  let sym := (← IO.getEnv "STAGE2_PIN_SYMBOL").getD "num_fast_el1"
  let some (path, layout, pre, runs) := config sym
    | IO.eprintln s!"ERROR: no pin configuration for {sym}"; IO.Process.exit 3
  let src ← IO.FS.readFile path
  match parseModuleWith layout src with
  | .error e => IO.eprintln s!"ERROR: {e}"; IO.Process.exit 3
  | .ok m =>
    match m.functions.head? with
    | none => IO.eprintln "ERROR: no function"; IO.Process.exit 3
    | some f =>
      if f.name ≠ sym then
        IO.eprintln s!"ERROR: the fixture's function is {f.name}, not {sym}"; IO.Process.exit 3
      IO.println "-- § the body literal"
      IO.println ("def " ++ pre ++ "Body : Function :=\n" ++ fnStr f)
      if runs.isEmpty then
        IO.eprintln s!"emitted the literal for {f.blocks.length} blocks, {(f.blocks.flatMap (·.instrs)).length} instructions (no block runs)"
      else
        IO.println "-- § the instruction lists"
        let mut defs := ""
        for b in f.blocks do
          if runs.contains b.name then defs := defs ++ defOf pre b ++ "\n"
        IO.print defs
        IO.println "-- § the pins"
        let mut pins := ""
        for b in f.blocks do
          if runs.contains b.name then
            pins := pins ++ pin pre b (pre ++ camel b.name ++ "Instrs") ++ "\n"
          else
            pins := pins ++ pin pre b (pinList b) ++ "\n"
        IO.print pins
        IO.println "-- § the instruction-list projections"
        let mut eqs := ""
        for b in f.blocks do
          if runs.contains b.name then eqs := eqs ++ instrsEq pre b ++ "\n"
        IO.print eqs
        IO.eprintln s!"emitted pins for {f.blocks.length} blocks, {(f.blocks.flatMap (·.instrs)).length} instructions"
LEANGEN
  ( cd "$repo" && STAGE2_PIN_SYMBOL=$sym lake env lean --run "$gen" 2>/dev/null |
      grep -v '^lean-llvm: Lean' )
  rc=${PIPESTATUS[0]}
  rm -f "$gen"
  exit $rc
fi

[ -f "$repo/$src" ] || fail "absent: $repo/$src"
[ -f "$walk" ] || fail "absent: $walk (run capture-stage2.sh first)"
[ -f "$noevent" ] || fail "absent: $noevent (run capture-stage2-noevent.sh first)"
command -v clang >/dev/null 2>&1 || fail "clang is not on PATH"
command -v opt >/dev/null 2>&1 || fail "opt is not on PATH"

work=$(mktemp -d "$repo/.lake/tmp-stage2-helpers.XXXXXX" 2>/dev/null) ||
  work=$(mktemp -d) ||
  fail "cannot create a work directory"
trap 'rm -rf "$work"' EXIT

flags=(-S -emit-llvm -O3 -march=x86-64-v3 -mpclmul -std=gnu11
       -falign-loops=64 -falign-functions=64)
compile() { ( cd "$repo" && clang -I kernel/json "$@" ); }

# The seven helpers the walk and the additive entry call out of line, in the
# order §7.6 lists them.
symbols=(s2_init s2_value_pos s2_after_value s2_string_body od_scalar_value
         od_gap_recover num_fast_el1)

# ---------------------------------------------------------------------------
# The source transform: `noinline` on every helper except `s2_walk`
# ---------------------------------------------------------------------------

sed -e 's/__attribute__((always_inline)) static inline/__attribute__((noinline)) static inline/g' \
    -e 's/#define EL_ENTRY __attribute__((always_inline)) static inline/#define EL_ENTRY __attribute__((noinline)) static inline/' \
    -e 's/^static void od_gap_recover(OdCur \*c, const OdTok \*t) {$/__attribute__((noinline)) static void od_gap_recover(OdCur *c, const OdTok *t) {/' \
    "$repo/$src" > "$work/step1.c"
grep -q '^__attribute__((noinline)) static void od_gap_recover(OdCur \*c, const OdTok \*t) {$' "$work/step1.c" ||
  fail "the source has no \`static void od_gap_recover(OdCur *c, const OdTok *t)\` line to mark noinline"

awk '{ if (hold) { print "__attribute__((always_inline)) static inline uint64_t"; hold = 0 }
       if ($0 == "__attribute__((noinline)) static inline uint64_t") { hold = 1; next }
       print }
     END { if (hold) exit 1 }' "$work/step1.c" > "$work/stage2.noinline.c" ||
  fail "the s2_walk attribute was not restored; the transform is not the one this script describes"

n_ni=$(grep -c '__attribute__((noinline))' "$work/stage2.noinline.c" || true)
[ "$n_ni" -eq 13 ] ||
  fail "the transformed source carries $n_ni 'noinline' occurrences; the always_inline set is 11 helpers plus the EL_ENTRY macro definition, and od_gap_recover is the twelfth definition"

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
# The fixtures are `define` blocks plus the declarations they need, so each one
# assembles and verifies on its own.
verify_fixture() { # <file>
  llvm-as "$1" -o "$2" || fail "$1 does not assemble"
  opt -passes=verify "$2" -o /dev/null || fail "$1 does not verify"
}

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

# `num_fast_el1`'s two strip rewrites, and nothing else.
#
# Its `llvm.umin.i64` takes a register and an immediate where the fragment's
# unsigned minimum is `llvm.umin.i32` at two registers, so it is folded to the
# `icmp`/`select` pair that is the same function at the same width.  Its `ashr`
# carries `exact`, a flag the token strip does not remove and the parser refuses
# by name; the flag is dropped, so the pinned body is the flag-erased form and
# the obligation it states — the bits shifted out are zero — is a staging fact
# the text does not carry, recorded in `stage2.helpers.tsv` and in the ledger
# rather than silently satisfied.
#
# The body's third obstruction is not a rewrite: the extraction takes one
# `define` block, so the module's `%struct.Stk = type { … }` line is absent and
# the parser takes a struct's extent from its `Layout` argument.  `Stk` is
# `{ StkBn m; StkBn pow; int64_t S; int sticky; }` with `StkBn` 96 `u64` limbs
# and a count word — 776 bytes each, 1552 for the pair, so 1568 for the struct —
# which is the number the body's own `llvm.lifetime.start` names.  The pin
# supplies it as `[("Stk", 1568)]`; nothing in the text is added.
nf_rewrites() { # <in> <out>
  local out1="$work/nf.1.ll"
  sed -E -e 's/^  (%[A-Za-z0-9_.]+) = tail call /  \1 = call /' "$1" > "$out1"
  sed -E     -e 's/^  (%[A-Za-z0-9_.]+) = call i64 @llvm\.umin\.i64\(i64 ([^,]+), i64 ([^)]+)\)$/  \1.min = icmp ult i64 \2, \3\n  \1 = select i1 \1.min, i64 \2, i64 \3/' \
    -e 's/ashr exact /ashr /' "$out1" > "$2"
  grep -qE 'llvm\.umin\.i64|ashr exact' "$2" &&
    fail "num_fast_el1 still carries a construct the fragment has no term for"
  grep -qE '^  %[A-Za-z0-9_.]+\.min = icmp ult i64 ' "$2" ||
    fail "num_fast_el1's llvm.umin.i64 was not folded to its icmp/select pair"
}

# `s2_string_body`'s one rewrite: its refusal message becomes `null`, as
# `od_scalar_value`'s three already do.
#
# The message pointer is a diagnostic and not a parse result, and the call
# boundary cannot carry it: `Calls` is
# `String -> List Value -> Mem -> Nat -> Option CallOutcome`, with no global
# table, and the extraction takes one `define` block, so the module's global
# declarations are not in the text to read the symbol's address from.  The word
# the refusal arm stores is therefore modelled as the zero word, and the text
# says the same thing.
#
# The cost is evidence, not correctness: `stage2.helper.s2_string_body.ll` stops
# being a fixture that carries an `Operand.global` through a run.  That operand's
# body-level evidence is `tests/core-extension.lean`'s acceptance pins (the
# store, load, `icmpPtr` and `gep` forms at a global symbol), and the ledger says
# where it moved.
msgs_rewrites() { # <in> <out>
  sed -E -e 's/@\.str\.[0-9]+/null/g' "$1" > "$2"
  grep -qE '@\.str\.' "$2" &&
    fail "s2_string_body still names its refusal message symbol"
  grep -qE '^  store ptr null, ptr %msg2\.i\.i$' "$2" ||
    fail "s2_string_body's refusal message store was not rewritten to null"
}

# `od_gap_recover`'s two rewrites: the four refusal record sites' message word
# becomes the site's tag, and its one `llvm.umin.i64` unfolds.
#
# The model records *which* `err_set` ran (`GapWrite.err off tag`), and nothing in
# the entry or its callees loads the record's message word (the no-event
# derivation's rewrite r6), so the word the text fills with a symbol address is
# the site's tag here: `i64 1` for the number refusal, `2` for the literal, `3`
# for the scalar and `4` for the extra token, at the same three-field record
# `stage2ErrSetMsg` writes.  The tags are the model's, and `gap_tag` below checks
# each block's symbol against the module's own string constant before the store
# is retagged, so a renumbered emission is refused rather than silently mapped to
# the wrong site.
gap_tag() { # <block> <tag> <literal>
  local blk=$1 tag=$2 lit=$3 sym def
  sym=$(awk -v blk="$blk" '
    BEGIN { pre = blk ":" }
    substr($0, 1, length(pre)) == pre { inb = 1; next }
    inb && /^[A-Za-z0-9_.]+:/ { inb = 0 }
    inb && /^  store ptr @\.str\.[0-9]+, ptr %msg/ {
      s = $0; sub(/^  store ptr /, "", s); sub(/,.*/, "", s); print s; exit
    }' "$work/od_gap_recover.stripped.ll")
  [ -n "$sym" ] || fail "od_gap_recover: $blk has no message store to tag"
  def=$(grep -E "^$sym = " "$work/lowered.ll" | head -1)
  [ -n "$def" ] || fail "od_gap_recover: $sym has no constant in the module"
  printf '%s' "$def" | grep -qF "c\"$lit\\00\"" ||
    fail "od_gap_recover: $sym is not \"$lit\"; tag $tag would name another site"
}

# The three literal-address phis: the emission selects one of `@.str.17`,
# `@.str.18` and `@.str.19` per arm, and a global constant is not a symbol the
# extracted `define` can carry (`parseModule` reads declarations and definitions
# only, and llvm-as wants the constant defined).  The three pointers are appended
# staging parameters instead, and this check ties each edge to the literal the
# module's own constant holds, as `gap_tag` does for the tags.
gap_phi_lit() { # <edge block> <literal>
  local edge=$1 lit=$2 sym def
  sym=$(awk -v edge="$edge" '
    /^  %[A-Za-z0-9_.]+ = phi ptr \[/ {
      n = split($0, parts, ",")
      for (i = 2; i <= n; i++) {
        if (index(parts[i], "%" edge " ]") > 0) {
          s = parts[i - 1]; sub(/.*\[ */, "", s); sub(/,.*/, "", s); print s; exit
        }
      }
    }' "$work/od_gap_recover.stripped.ll")
  [ -n "$sym" ] || fail "od_gap_recover: no literal phi at edge $edge to stage"
  def=$(grep -E "^$sym = " "$work/lowered.ll" | head -1)
  [ -n "$def" ] || fail "od_gap_recover: $sym has no constant in the module"
  printf '%s' "$def" | grep -qF "c\"$lit\\00\"" ||
    fail "od_gap_recover: $sym at edge $edge is not \"$lit\""
}

gap_rewrites() { # <in> <out>
  local out1="$work/gap.1.ll" out2="$work/gap.2.ll" out3="$work/gap.3.ll"
  gap_tag if.then25 1 number
  gap_tag if.else43 3 scalar
  gap_tag if.then57 2 literal
  gap_tag while.end78 4 'extra token'
  gap_phi_lit if.then37 false
  gap_phi_lit if.then42 null
  gap_phi_lit LeafBlock11 true
  sed -E \
    -e '/^if\.then25:/,/^[A-Za-z0-9_.]+:/ s/^(  store )ptr @\.str\.[0-9]+(, ptr %msg.*)$/\1i64 1\2/' \
    -e '/^if\.else43:/,/^[A-Za-z0-9_.]+:/ s/^(  store )ptr @\.str\.[0-9]+(, ptr %msg.*)$/\1i64 3\2/' \
    -e '/^if\.then57:/,/^[A-Za-z0-9_.]+:/ s/^(  store )ptr @\.str\.[0-9]+(, ptr %msg.*)$/\1i64 2\2/' \
    -e '/^while\.end78:/,/^[A-Za-z0-9_.]+:/ s/^(  store )ptr @\.str\.[0-9]+(, ptr %msg.*)$/\1i64 4\2/' \
    "$1" > "$out1"
  # The literal phis' three symbols become the appended parameters, and the
  # header carries them: the emission's own two arguments, then the staging.
  sed -E \
    -e 's/^define void @od_gap_recover\(ptr %c, i64 %t\.0\.val\) \{$/define void @od_gap_recover(ptr %c, i64 %t.0.val, ptr %littrue, ptr %litfalse, ptr %litnull) {/' \
    -e 's/@\.str\.[0-9]+, %if\.then37 \]/%litfalse, %if.then37 ]/' \
    -e 's/@\.str\.[0-9]+, %if\.then42 \]/%litnull, %if.then42 ]/' \
    -e 's/@\.str\.[0-9]+, %LeafBlock11 \]/%littrue, %LeafBlock11 ]/' \
    "$out1" > "$out2"
  sed -E 's/^  (%[A-Za-z0-9_.]+) = tail call i64 @llvm\.umin\.i64\(i64 ([^,]+), i64 ([^)]+)\)$/  \1.min = icmp ult i64 \2, \3\n  \1 = select i1 \1.min, i64 \2, i64 \3/' \
    "$out2" > "$out3"
  # The callee and the two lifetime intrinsics are declared, so the extracted
  # body assembles on its own: a `define` block's text is what llvm-as needs a
  # symbol for, and the emission's own declarations are outside the block.
  {
    cat "$out3"
    printf '\n; The callee and the intrinsics the body calls, so the fixture assembles.\n'
    printf 'declare i32 @num_fast_el1(ptr, i64, ptr, ptr)\n'
    printf 'declare void @llvm.lifetime.start.p0(i64, ptr)\n'
    printf 'declare void @llvm.lifetime.end.p0(i64, ptr)\n'
  } > "$2"
  grep -qE '@\.str\.|llvm\.umin\.i64' "$2" &&
    fail "od_gap_recover still carries a global symbol or an umin the fragment has no term for"
  ntags=$(grep -cE '^  store i64 [1-4], ptr %msg' "$2" || true)
  [ "$ntags" -eq 4 ] ||
    fail "od_gap_recover's four refusal sites are not all tagged ($ntags of 4)"
  grep -qE '^  %[A-Za-z0-9_.]+\.min = icmp ult i64 ' "$2" ||
    fail "od_gap_recover's llvm.umin.i64 was not folded to its icmp/select pair"
  grep -qE '^define void @od_gap_recover\(ptr %c, i64 %t\.0\.val, ptr %littrue, ptr %litfalse, ptr %litnull\) \{$' "$2" ||
    fail "od_gap_recover's staging parameters were not appended"
}

capture() { # <symbol> <rewrite: none|od|nf|msgs|as-is>
  local sym=$1 mode=$2
  extract_define "$sym" "$work/$sym.raw.ll"
  strip_body "$work/$sym.raw.ll" "$work/$sym.stripped.ll"
  case "$mode" in
    none) cp "$work/$sym.stripped.ll" "$work/$sym.body.ll" ;;
    od) od_rewrites "$work/$sym.stripped.ll" "$work/$sym.body.ll" ;;
    nf) nf_rewrites "$work/$sym.stripped.ll" "$work/$sym.body.ll" ;;
    msgs) msgs_rewrites "$work/$sym.stripped.ll" "$work/$sym.body.ll" ;;
    gap) gap_rewrites "$work/$sym.stripped.ll" "$work/$sym.body.ll" ;;
    as-is) cp "$work/$sym.stripped.ll" "$work/$sym.body.ll" ;;
    *) fail "unknown capture mode $mode" ;;
  esac
}

capture s2_init none
capture s2_value_pos none
capture s2_after_value none
capture s2_string_body msgs
capture od_scalar_value od
capture od_gap_recover gap
capture num_fast_el1 nf

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
grep -q 'alloca %struct\.Stk' "$work/num_fast_el1.body.ll" ||
  fail "num_fast_el1's body no longer allocates %struct.Stk; the pin's declared Layout is then a claim about a struct the emission stopped naming"
nstk=$(grep -cE '^  call void @llvm\.lifetime\.start\.p0\(i64 1568, ptr %v\.i\.i\)$' "$work/num_fast_el1.body.ll" || true)
[ "$nstk" -ge 1 ] ||
  fail "num_fast_el1's lifetime marker for %struct.Stk no longer names 1568 bytes; the pin's Layout disagrees with the body"

# `od_gap_recover`'s measured constructs: the two body-allocated slots, the
# number path's call, and the literal compare's three-symbol `phi` (whose
# operands are what the pin stages).
grep -qE '^  %d = alloca double$' "$work/od_gap_recover.body.ll" ||
  fail "od_gap_recover's conversion slot is no longer an \`alloca double\`"
grep -qE '^  %ei = alloca i64$' "$work/od_gap_recover.body.ll" ||
  fail "od_gap_recover's offset slot is no longer an \`alloca i64\`"
grep -qE '^  %call[0-9]+ = call i32 @num_fast_el1\(' "$work/od_gap_recover.body.ll" ||
  fail "od_gap_recover's number path no longer calls \`num_fast_el1\`"
nglob=$(grep -cE '^  %[A-Za-z0-9_.]+ = phi ptr \[ %lit' "$work/od_gap_recover.body.ll" || true)
[ "$nglob" -eq 1 ] ||
  fail "od_gap_recover's literal compare no longer selects its literal through one staged phi ($nglob found)"
grep -qE '^define void @od_gap_recover\(ptr %c, i64 %t\.0\.val, ptr %littrue, ptr %litfalse, ptr %litnull\) \{$' "$work/od_gap_recover.body.ll" ||
  fail "od_gap_recover's emitted argument surface is not the two arguments plus the three staged literal pointers"

# ---------------------------------------------------------------------------
# The cross-check: each captured body is the symbol its calling fixture declares
# ---------------------------------------------------------------------------

decl_of() { # <file> <symbol>
  awk -v sym="$2" '
    $0 ~ "^declare .*@" sym "\\(" { print; exit }
  ' "$1"
}

arity_of() { # <header line>
  sed -E -e 's/.*\(//' -e 's/\).*//' <<<"$1" | awk -F', ' '{ print NF }'
}

# `od_gap_recover` is the one captured body the walk's fixture does not declare:
# `capture-stage2.sh`'s emission inlines it, so the symbol's declaration is the
# additive entry's, and the argument list there is the emission's own.
for sym in s2_init s2_value_pos s2_after_value s2_string_body od_scalar_value od_gap_recover num_fast_el1; do
  case "$sym" in
    od_gap_recover) declsrc=$noevent; what="stage2-noevent.candidate.ll" ;;
    *) declsrc=$walk; what="stage2.candidate.ll" ;;
  esac
  d=$(decl_of "$declsrc" "$sym")
  [ -n "$d" ] || fail "$what does not declare @$sym"
  head=$(head -1 "$work/$sym.body.ll")
  # The declare's parameter list, and the body's, agree up to the staging
  # parameters this script appends: one for od_scalar_value, none otherwise.
  want=$(arity_of "$d")
  got=$(arity_of "$head")
  case "$sym" in
    od_scalar_value) [ "$got" -eq $((want + 1)) ] || fail "$sym: declared $want, body $got" ;;
    od_gap_recover) [ "$got" -eq $((want + 3)) ] || fail "$sym: declared $want, body $got" ;;
    *) [ "$got" -eq "$want" ] || fail "$sym: declared $want, body $got" ;;
  esac
  dnames=$(sed -E -e 's/.*\(//' -e 's/\).*//' <<<"$d" | tr ',' '\n' | sed -E 's/^ *[^%]*//' | paste -sd' ')
  bnames=$(sed -E -e 's/.*\(//' -e 's/\).*//' <<<"$head" | tr ',' '\n' | sed -E 's/^ *[^%]*//' | paste -sd' ')
  case "$sym" in
    od_scalar_value) bnames=${bnames% %d} ;;
    od_gap_recover) bnames=${bnames% %litnull}; bnames=${bnames% %litfalse}; bnames=${bnames% %littrue} ;;
  esac
  [ "$dnames" = "$bnames" ] ||
    fail "$sym: $what declares ($dnames), the body is ($bnames)"
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
; capture-stage2.sh applies.  od_scalar_value takes the walk's own three
; rewrites — its conversion slot becomes a pointer parameter, its messages
; become \`null\`, and its one llvm.umin.i64 unfolds — and num_fast_el1 takes
; two of the same kind: its llvm.umin.i64 folds to the icmp/select pair, and
; \`ashr exact\` loses its flag.  s2_string_body takes one: its refusal message
; becomes \`null\`, because the call boundary has no global table to read the
; symbol's address from, and od_gap_recover takes three: its llvm.umin.i64
; unfolds, each refusal site's message word becomes that site's tag, and the
; literal compare's three globals become appended pointer parameters.
; $2
;
EOF
}

for sym in s2_init s2_value_pos s2_after_value s2_string_body od_scalar_value od_gap_recover num_fast_el1; do
  out=$here/stage2.helper.$sym.ll
  case "$sym" in
    od_gap_recover)
      note='The body is captured as the fragment expresses it after its rewrites: its one llvm.umin.i64 unfolds (its literal compare takes an unsigned minimum at i64), each refusal record site stores its tag (`i64 1` number, `2` literal, `3` scalar, `4` extra token) where the text stores the message symbol because nothing loads the word and the model records which site ran, and the literal compare'"'"'s three `@.str.*` operands become three appended pointer parameters, since a global constant is neither a declaration `parseModule` reads nor a symbol a lone `define` assembles against.  The callee and the two lifetime intrinsics are declared after the body for the same reason.' ;;
    s2_string_body)
      note='The body is a program of this fragment: its `ptrtoint` pair is modelled, and `JsonStage2StringBody` pins the AST it parses to and proves the helper contract of that body.  Its refusal message is `null` here — the call boundary carries no global table — so this fixture is not where `Operand.global`'"'"'s body-level evidence lives; that evidence is tests/core-extension.lean'"'"'s acceptance pins.' ;;
    od_scalar_value)
      note='The body is captured as the fragment expresses it and pinned whole in `JsonStage2HelperIROdScalar`; its accepted path calls `num_fast_el1`, whose own body is `stage2.helper.num_fast_el1.ll`.' ;;
    num_fast_el1)
      note='The body is a program of this fragment after its two strip rewrites (the `llvm.umin.i64` fold and the dropped `exact` flag) and with the extent of `%struct.Stk` supplied as the `Layout` `[("Stk", 1568)]` the pin states, which is the number the body own `llvm.lifetime.start` names.  `JsonStage2HelperIRNumFast` pins the AST it parses to, block by block.' ;;
    *)
      note='The body is captured and the fragment expresses it.' ;;
  esac
  { banner "$sym" "$note"; cat "$work/$sym.body.ll"; } > "$out"
  [ -s "$out" ] || fail "$out is empty"
  # `od_gap_recover`'s fixture declares the callee it calls, so it assembles on
  # its own; the other six name their callees without a declaration, as they have
  # since they were captured, and their evidence is the parse pin.
  case "$sym" in
    od_gap_recover) verify_fixture "$out" "$work/$sym.bc" ;;
  esac
done

{
  printf '# The stage-2 helpers as emitted, and whether this fragment models their bodies.\n'
  printf '# Regenerate with probes/install/ir/capture-stage2-helpers.sh.\n'
  printf '#\n'
  printf '# symbol\tlines\tblocks\tinstr_lines\tparams\tverdict\tbasis\n'
  printf '# instr_lines counts the body\x27s instruction lines in the fixture; the parsed\n'
  printf '# instruction count is what the Lean pin states (od_scalar_value: 145,\n'
  printf '# od_gap_recover: 110).\n'
  for sym in "${symbols[@]}"; do
    f="$work/$sym.body.ll"
    lines=$(wc -l < "$f" | tr -d ' ')
    blocks=$(grep -cE '^[A-Za-z0-9_.]+:' "$f" || true)
    instrs=$(grep -cE '^  ' "$f" || true)
    params=$(arity_of "$(head -1 "$f")")
    case "$sym" in
      s2_string_body)
        verdict=expressible
        basis="parsed by LeanLLVM.Parser; pinned in LeanLLVM/Refinement/JsonStage2HelperIR.lean and tests/core-extension.lean.  One strip rewrite: the refusal message becomes null, because Calls has no global table and the extracted block carries no global declaration; Operand.global's body-level evidence is tests/core-extension.lean's pins, not this fixture" ;;
      num_fast_el1)
        verdict=expressible
        basis="aggregate and binary64 text ($nagg aggregate alloca(s), $nfp floating-point site(s)); parses after two strip rewrites — the one llvm.umin.i64 folds to its icmp/select pair (the fragment's umin is i32 at two registers), and ashr exact loses the flag, so the pinned body is the flag-erased form and 'the bits shifted out are zero' is a staging fact the text does not carry — and with %struct.Stk's 1568-byte extent supplied as the Layout the pin states; the decimal literals parse.  Pinned at every block in LeanLLVM/Refinement/JsonStage2HelperIRNumFast.lean (255 findBlock equations emitted by --emit-pins); the digit scan's BoundLoop is JsonStage2NumFastScan's, and the empty lexeme's refusal is proved of the body in JsonStage2NumFastBody.lean; the conversion arm is open" ;;
      od_gap_recover)
        verdict=expressible
        basis="parsed by LeanLLVM.Parser; pinned whole in LeanLLVM/Refinement/JsonStage2HelperIROdGap.lean — the body literal and its #guard equality, with a mutated-tag control.  Three rewrites: the one llvm.umin.i64 unfolds, each refusal site stores its tag where the text stores the message symbol (nothing loads the word; the model records the site), and the literal compare's three symbols become appended pointer parameters (a global constant is not a declaration parseModule reads, nor a symbol a lone define assembles against).  Only the certified fixture inlines this body, so the cross-check reads the declaration from stage2-noevent.candidate.ll, and the two arguments there are the fixture's first two.  Its block pins and the instruction and terminator steps a run proof is written in are in LeanLLVM/Refinement/JsonStage2HelperIROdGapSteps.lean; no contract theorem relates the body to the rule, so the helper's ledger row is unchanged" ;;
      od_scalar_value)
        verdict=expressible
        basis="parsed by LeanLLVM.Parser; pinned whole in LeanLLVM/Refinement/JsonStage2HelperIROdScalar.lean — the body literal and its #guard equality, with a mutated-pivot control — so the block and instruction counts above are a corollary of what the text is.  The three rewrites are the walk's own: the conversion slot becomes a pointer parameter, the message stores become null, and the one llvm.umin.i64 unfolds to its icmp/select pair.  The body's contract proof is obstructed by its num_fast_el1 call and by the outTag/emitBlobs record chain it must match" ;;
      *)
        verdict=expressible
        basis="parsed by LeanLLVM.Parser; pinned in LeanLLVM/Refinement/JsonStage2HelperIR.lean" ;;
    esac
    printf '%s\t%d\t%d\t%d\t%d\t%s\t%s\n' "$sym" "$lines" "$blocks" "$instrs" "$params" "$verdict" "$basis"
  done
} > "$inventory"

printf 'wrote %s and %s\n' "$here/stage2.helper.*.ll" "$inventory"
