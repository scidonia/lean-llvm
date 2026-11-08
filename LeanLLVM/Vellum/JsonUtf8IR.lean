/-
The UTF-8 stage's call environment.

The stage's emission calls three intrinsics and no others:
`llvm.x86.avx2.pshuf.b` for the table lookups, `llvm.usub.sat.v32i8` for the
two saturating subtracts, and `llvm.x86.avx.ptestz.256` for the zero tests.
This module binds those three to `BitLanes`' and `Semantics`' lane vocabulary —
`pshufbLanes`, `subsSat`, `ptestz` — and to nothing else: an unresolved symbol
stays `ub`, which is what makes an emission this environment does not describe
fail rather than be read as something it is not.

The parser validates the three symbols' arity, operand types and result type
(`checkIntrinsicShape`), so the shapes matched below are the only ones that
reach this environment from a parsed module.

The tables the stage shuffles are folded to literal `<32 x i8>` operands by the
compiler, so the shuffle arm takes its table from the call's first operand and
this environment carries no table parameter.  That is the structural difference
between this unit's call sites and the mask unit's, whose table arrives as a
`<32 x i8>` register read from the caller's buffer.
-/
import LeanLLVM.Memory
import LeanLLVM.Parser
import LeanLLVM.Vellum.BitLanes

namespace LeanLLVM.Vellum.JsonUtf8IR

open LeanLLVM

/-- The stage's reference call environment: the three intrinsics the emission
calls, each at the shape the parser admits, and nothing else. -/
def utf8Calls : Calls :=
  fun callee args mem next =>
    match callee, args with
    | "llvm.x86.avx2.pshuf.b", [.vec 32 8 table, .vec 32 8 control] =>
        some { ret := .vec 32 8 (pshufbLanes table control), mem := mem, next := next }
    | "llvm.usub.sat.v32i8", [.vec 32 8 a, .vec 32 8 b] =>
        some { ret := .vec 32 8 (List.zipWith BitLanes.subsSat a b),
               mem := mem, next := next }
    | "llvm.x86.avx.ptestz.256", [.vec 4 64 a, .vec 4 64 b] =>
        some { ret := .int 32 (BitLanes.ptestz (BitVec.ofNat 256 (packLanes a))
              (BitVec.ofNat 256 (packLanes b))), mem := mem, next := next }
    | _, _ => none

/-- The table lookup: `pshuf.b`'s meaning is `pshufbLanes` on the two operand
lane lists, the table then the control. -/
theorem utf8Calls_pshufb (table control : List (BitVec 8)) (mem : Mem) (next : Nat) :
    utf8Calls "llvm.x86.avx2.pshuf.b" [.vec 32 8 table, .vec 32 8 control] mem next =
      some { ret := .vec 32 8 (pshufbLanes table control), mem := mem, next := next } :=
  rfl

/-- The saturating subtract: `subsSat` applied lane by lane, and no flag. -/
theorem utf8Calls_usubSat (a b : List (BitVec 8)) (mem : Mem) (next : Nat) :
    utf8Calls "llvm.usub.sat.v32i8" [.vec 32 8 a, .vec 32 8 b] mem next =
      some { ret := .vec 32 8 (List.zipWith BitLanes.subsSat a b),
             mem := mem, next := next } :=
  rfl

/-- The zero test: the two `<4 x i64>` operands packed little-endian into one
256-bit word each, and `ptestz` read at that word. -/
theorem utf8Calls_ptestz (a b : List (BitVec 64)) (mem : Mem) (next : Nat) :
    utf8Calls "llvm.x86.avx.ptestz.256" [.vec 4 64 a, .vec 4 64 b] mem next =
      some { ret := .int 32 (BitLanes.ptestz (BitVec.ofNat 256 (packLanes a))
            (BitVec.ofNat 256 (packLanes b))), mem := mem, next := next } :=
  rfl

/-! ### The fixture

`probes/install/ir/json-utf8.candidate.ll` is the emission of `kernel/json/utf8.c`
at the measured compiler line, reduced to the unit's one `define` block.  The
module parses it and pins the parsed AST against the literal below, the way
`JsonEntryIR` and `JsonS1MasksIR` pin theirs: the pin is a `#guard` because the
parser runs on `String` primitives, which the kernel does not reduce, so an AST
proposition cannot be closed by reflexivity.

The block count is derived from `n` alone — `(n + 63) / 64` — and `n` is both the
document's length and the staged window's, so there is no second count for the
two to disagree about.
-/

/-- The unit as emitted and committed. -/
def utf8Src : String :=
  include_str "../../probes/install/ir/json-utf8.candidate.ll"

/-- Parse a fixture and take its single function. -/
def firstFunction (src : String) : Option Function :=
  match parseModule src with
  | .ok m => m.functions.head?
  | .error _ => none

/-! #### The pinned AST

The body, instruction by instruction, in the fixture's order.  The helpers only
spell an operand the way the parser reads one; they decide nothing. -/

/-- A register operand. -/
def reg (n : String) : Operand := .reg n

/-- An integer literal of width `w`. -/
def lit (w : Nat) (v : Int) : Operand := .imm (.int w (BitVec.ofInt w v))

/-- A `splat` vector constant: `splat (i<w> <v>)` at `n` lanes. -/
def splatOf (n w : Nat) (v : Int) : Operand := .imm (.splat n w (BitVec.ofInt w v))

/-- A lane-list vector constant `<i<w> v₀, …, i<w> v₍ₖ₋₁₎>`. -/
def lanesOf (w : Nat) (vs : List Int) : Operand := .imm (.vector w (vs.map (BitVec.ofInt w)))

/-- `<32 x i8>`, the lane type of the three tables and of every byte vector the
body forms. -/
abbrev v32i8 : Ty := .vec 32 (.int 8)

/-- `<4 x i64>`, the accumulator's own type: the words the two `ptestz` calls
test and the value the loop carries. -/
abbrev v4i64 : Ty := .vec 4 (.int 64)

/-- The mask `%and.i.i.i58.us` and its siblings apply:
`splat (i64 -9187201950435737472)`, i.e. `0x80` in the high bit of every byte. -/
def highBitMask : Operand := splatOf 4 64 (-9187201950435737472)

/-- `kl_t1` as the two `pshuf.b` calls spell it: the sixteen table entries
doubled, one copy per 128-bit lane.  The tie to the specification's `klT1` is
`t1Lanes_eq` in `JsonUtf8Steps`, where both the table and the specification are
in scope; this module has no `klT1` to compare against. -/
def t1Lanes : List Int :=
  [-0x19, -0x5D, -0x7D, -0x7D, -0x75, -0x35, -0x35, -0x35,
   -0x35, -0x35, -0x35, -0x35, -0x35, -0x25, -0x35, -0x35,
   -0x19, -0x5D, -0x7D, -0x7D, -0x75, -0x35, -0x35, -0x35,
   -0x35, -0x35, -0x35, -0x35, -0x35, -0x25, -0x35, -0x35]

/-- `kl_t2` as the calls spell it. -/
def t2Lanes : List Int :=
  [0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
   -0x80, -0x80, -0x80, -0x80, 0x21, 0x01, 0x15, 0x49,
   0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
   -0x80, -0x80, -0x80, -0x80, 0x21, 0x01, 0x15, 0x49]

/-- `kl_t3` as the calls spell it. -/
def t3Lanes : List Int :=
  [0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
   -0x1A, -0x52, -0x46, -0x46, 0x01, 0x01, 0x01, 0x01,
   0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
   -0x1A, -0x52, -0x46, -0x46, 0x01, 0x01, 0x01, 0x01]

/-- One `pshuf.b` table lookup: the table's lane list against the nibble lanes. -/
def pshufb (dst : String) (tab : List Int) (v : Operand) : Instr :=
  .call dst v32i8 "llvm.x86.avx2.pshuf.b" [(v32i8, lanesOf 8 tab), (v32i8, v)]

/-- One `llvm.usub.sat.v32i8` against a splat constant: the `p2 -s 0x60` and
`p3 -s 0x70` halves of `must`. -/
def usubSat (dst : String) (v : Operand) (c : Int) : Instr :=
  .call dst v32i8 "llvm.usub.sat.v32i8" [(v32i8, v), (v32i8, splatOf 32 8 c)]

/-- One `llvm.x86.avx.ptestz.256` at the given pair of `<4 x i64>` operands. -/
def ptestz (dst : String) (a b : Operand) : Instr :=
  .call dst (.int 32) "llvm.x86.avx.ptestz.256" [(v4i64, a), (v4i64, b)]

/-! ##### `entry` — the block count, and the zero-block guard -/

def utf8Entry : Block :=
  { name := "entry",
    instrs := [
      .binop "%add" .add 64 (reg "%n") (lit 64 63),
      .binop "%div44" .lshr 64 (reg "%add") (lit 64 6),
      .icmp "%cmp74.not" .ult 64 (reg "%add") (lit 64 64)],
    term := .condbr (reg "%cmp74.not") "for.cond.cleanup" "for.body.lr.ph" }

/-! ##### `for.body.lr.ph` — the gate selection -/

def utf8LrPh : Block :=
  { name := "for.body.lr.ph",
    instrs := [
      .icmp "%tobool.not" .eq 32 (reg "%ungated") (lit 32 0)],
    term := .condbr (reg "%tobool.not") "for.body.us" "for.body" }

/-! ##### `for.body.us` — the gated loop's header: the ASCII gate -/

def utf8ForBodyUs : Block :=
  { name := "for.body.us",
    instrs := [
      .phi "%prev_ascii.077.us" (.int 32)
        [("if.end14.us", reg "%2"), ("for.body.lr.ph", lit 32 1)],
      .phi "%u8k.076.us" v4i64
        [("if.end14.us", reg "%u8k.2.us"), ("for.body.lr.ph", splatOf 4 64 0)],
      .phi "%bi.075.us" (.int 64)
        [("if.end14.us", reg "%inc.us"), ("for.body.lr.ph", lit 64 0)],
      .binop "%shl.us" .shl 64 (reg "%bi.075.us") (lit 64 6),
      .gep "%add.ptr.us" (.int 8) (reg "%b") (reg "%shl.us"),
      .load "%0" v4i64 (reg "%add.ptr.us"),
      .gep "%add.ptr3.us" (.int 8) (reg "%add.ptr.us") (lit 64 32),
      .load "%1" v4i64 (reg "%add.ptr3.us"),
      .binopVec "%or.i46.us" .or 4 64 (reg "%1") (reg "%0"),
      ptestz "%2" (reg "%or.i46.us") highBitMask,
      .icmp "%tobool9.us" .ne 32 (reg "%2") (lit 32 0),
      .icmp "%tobool10.us" .ne 32 (reg "%prev_ascii.077.us") (lit 32 0),
      .binop "%or.cond.us" .and 1 (reg "%tobool9.us") (reg "%tobool10.us")],
    term := .condbr (reg "%or.cond.us") "if.end14.us" "if.then11.us" }

/-! ##### `if.then11.us` — the gated path's DFA body, two 32-byte halves -/

def utf8ThenUs : Block :=
  { name := "if.then11.us",
    instrs := [
      .gep "%add.ptr.i.i48.us" (.int 8) (reg "%add.ptr.us") (lit 64 (-1)),
      .load "%3" v4i64 (reg "%add.ptr.i.i48.us"),
      .gep "%add.ptr3.i.i49.us" (.int 8) (reg "%add.ptr.us") (lit 64 (-2)),
      .load "%4" v32i8 (reg "%add.ptr3.i.i49.us"),
      .gep "%add.ptr5.i.i50.us" (.int 8) (reg "%add.ptr.us") (lit 64 (-3)),
      .load "%5" v32i8 (reg "%add.ptr5.i.i50.us"),
      .vecBitcast "%6" 4 64 32 8 (reg "%3"),
      .binopVec "%7" .and 32 8 (reg "%6") (splatOf 32 8 15),
      pshufb "%8" t1Lanes (reg "%7"),
      .vecBitcast "%9" 4 64 16 16 (reg "%3"),
      .binopVec "%10" .lshr 16 16 (reg "%9") (splatOf 16 16 4),
      .vecBitcast "%11" 16 16 32 8 (reg "%10"),
      .binopVec "%12" .and 32 8 (reg "%11") (splatOf 32 8 15),
      pshufb "%13" t2Lanes (reg "%12"),
      .binopVec "%and.i3741.i.i51.us" .and 32 8 (reg "%13") (reg "%8"),
      .vecBitcast "%14" 4 64 16 16 (reg "%0"),
      .binopVec "%15" .lshr 16 16 (reg "%14") (splatOf 16 16 4),
      .vecBitcast "%16" 16 16 32 8 (reg "%15"),
      .binopVec "%17" .and 32 8 (reg "%16") (splatOf 32 8 15),
      pshufb "%18" t3Lanes (reg "%17"),
      .binopVec "%and.i3542.i.i52.us" .and 32 8 (reg "%and.i3741.i.i51.us") (reg "%18"),
      .vecBitcast "%and.i35.i.i53.us" 32 8 4 64 (reg "%and.i3542.i.i52.us"),
      usubSat "%elt.sat.i40.i.i54.us" (reg "%4") 96,
      usubSat "%elt.sat.i.i.i55.us" (reg "%5") 112,
      .binopVec "%or.i43.i.i56.us" .or 32 8 (reg "%elt.sat.i.i.i55.us")
        (reg "%elt.sat.i40.i.i54.us"),
      .vecBitcast "%or.i.i.i57.us" 32 8 4 64 (reg "%or.i43.i.i56.us"),
      .binopVec "%and.i.i.i58.us" .and 4 64 (reg "%or.i.i.i57.us") highBitMask,
      .binopVec "%xor.i.i.i59.us" .xor 4 64 (reg "%and.i.i.i58.us")
        (reg "%and.i35.i.i53.us"),
      .gep "%add.ptr.i4.i60.us" (.int 8) (reg "%add.ptr.us") (lit 64 31),
      .load "%19" v4i64 (reg "%add.ptr.i4.i60.us"),
      .gep "%add.ptr3.i5.i61.us" (.int 8) (reg "%add.ptr.us") (lit 64 30),
      .load "%20" v32i8 (reg "%add.ptr3.i5.i61.us"),
      .gep "%add.ptr5.i6.i62.us" (.int 8) (reg "%add.ptr.us") (lit 64 29),
      .load "%21" v32i8 (reg "%add.ptr5.i6.i62.us"),
      .vecBitcast "%22" 4 64 32 8 (reg "%19"),
      .binopVec "%23" .and 32 8 (reg "%22") (splatOf 32 8 15),
      pshufb "%24" t1Lanes (reg "%23"),
      .vecBitcast "%25" 4 64 16 16 (reg "%19"),
      .binopVec "%26" .lshr 16 16 (reg "%25") (splatOf 16 16 4),
      .vecBitcast "%27" 16 16 32 8 (reg "%26"),
      .binopVec "%28" .and 32 8 (reg "%27") (splatOf 32 8 15),
      pshufb "%29" t2Lanes (reg "%28"),
      .binopVec "%and.i3741.i7.i63.us" .and 32 8 (reg "%29") (reg "%24"),
      .vecBitcast "%30" 4 64 16 16 (reg "%1"),
      .binopVec "%31" .lshr 16 16 (reg "%30") (splatOf 16 16 4),
      .vecBitcast "%32" 16 16 32 8 (reg "%31"),
      .binopVec "%33" .and 32 8 (reg "%32") (splatOf 32 8 15),
      pshufb "%34" t3Lanes (reg "%33"),
      .binopVec "%and.i3542.i8.i64.us" .and 32 8 (reg "%and.i3741.i7.i63.us")
        (reg "%34"),
      .vecBitcast "%and.i35.i9.i65.us" 32 8 4 64 (reg "%and.i3542.i8.i64.us"),
      usubSat "%elt.sat.i40.i10.i66.us" (reg "%20") 96,
      usubSat "%elt.sat.i.i11.i67.us" (reg "%21") 112,
      .binopVec "%or.i43.i12.i68.us" .or 32 8 (reg "%elt.sat.i.i11.i67.us")
        (reg "%elt.sat.i40.i10.i66.us"),
      .vecBitcast "%or.i.i13.i69.us" 32 8 4 64 (reg "%or.i43.i12.i68.us"),
      .binopVec "%and.i.i14.i70.us" .and 4 64 (reg "%or.i.i13.i69.us") highBitMask,
      .binopVec "%xor.i.i15.i71.us" .xor 4 64 (reg "%and.i.i14.i70.us")
        (reg "%and.i35.i9.i65.us"),
      .binopVec "%35" .or 4 64 (reg "%xor.i.i.i59.us") (reg "%xor.i.i15.i71.us"),
      .binopVec "%or.i.us" .or 4 64 (reg "%35") (reg "%u8k.076.us")],
    term := .br "if.end14.us" }

/-! ##### `if.end14.us` — the gated loop's latch -/

def utf8EndUs : Block :=
  { name := "if.end14.us",
    instrs := [
      .phi "%u8k.2.us" v4i64
        [("for.body.us", reg "%u8k.076.us"), ("if.then11.us", reg "%or.i.us")],
      .binop "%inc.us" .add 64 (reg "%bi.075.us") (lit 64 1),
      .icmp "%exitcond79.not" .eq 64 (reg "%inc.us") (reg "%div44")],
    term := .condbr (reg "%exitcond79.not") "for.cond.cleanup" "for.body.us" }

/-! ##### `for.cond.cleanup` — the reduce and the tail's guard -/

def utf8Cleanup : Block :=
  { name := "for.cond.cleanup",
    instrs := [
      .phi "%u8k.0.lcssa" v4i64
        [("entry", splatOf 4 64 0), ("if.end14.us", reg "%u8k.2.us"),
         ("for.body", reg "%or.i47")],
      ptestz "%36" (reg "%u8k.0.lcssa") (reg "%u8k.0.lcssa"),
      .icmp "%tobool16.not" .eq 32 (reg "%36") (lit 32 0),
      .icmp "%tobool17.not" .ne 64 (reg "%n") (lit 64 0),
      .binop "%and" .and 64 (reg "%n") (lit 64 63),
      .icmp "%tobool19.not" .eq 64 (reg "%and") (lit 64 0),
      .binop "%or.cond45" .and 1 (reg "%tobool17.not") (reg "%tobool19.not")],
    term := .condbr (reg "%or.cond45") "if.then20" "if.end24" }

/-! ##### `for.body` — the ungated path's DFA body -/

def utf8ForBody : Block :=
  { name := "for.body",
    instrs := [
      .phi "%u8k.076" v4i64
        [("for.body", reg "%or.i47"), ("for.body.lr.ph", splatOf 4 64 0)],
      .phi "%bi.075" (.int 64)
        [("for.body", reg "%inc"), ("for.body.lr.ph", lit 64 0)],
      .binop "%shl" .shl 64 (reg "%bi.075") (lit 64 6),
      .gep "%add.ptr" (.int 8) (reg "%b") (reg "%shl"),
      .load "%37" (.vec 16 (.int 16)) (reg "%add.ptr"),
      .gep "%add.ptr3" (.int 8) (reg "%add.ptr") (lit 64 32),
      .load "%38" (.vec 16 (.int 16)) (reg "%add.ptr3"),
      .gep "%add.ptr.i.i" (.int 8) (reg "%add.ptr") (lit 64 (-1)),
      .load "%39" v4i64 (reg "%add.ptr.i.i"),
      .gep "%add.ptr3.i.i" (.int 8) (reg "%add.ptr") (lit 64 (-2)),
      .load "%40" v32i8 (reg "%add.ptr3.i.i"),
      .gep "%add.ptr5.i.i" (.int 8) (reg "%add.ptr") (lit 64 (-3)),
      .load "%41" v32i8 (reg "%add.ptr5.i.i"),
      .vecBitcast "%42" 4 64 32 8 (reg "%39"),
      .binopVec "%43" .and 32 8 (reg "%42") (splatOf 32 8 15),
      pshufb "%44" t1Lanes (reg "%43"),
      .vecBitcast "%45" 4 64 16 16 (reg "%39"),
      .binopVec "%46" .lshr 16 16 (reg "%45") (splatOf 16 16 4),
      .vecBitcast "%47" 16 16 32 8 (reg "%46"),
      .binopVec "%48" .and 32 8 (reg "%47") (splatOf 32 8 15),
      pshufb "%49" t2Lanes (reg "%48"),
      .binopVec "%and.i3741.i.i" .and 32 8 (reg "%49") (reg "%44"),
      .binopVec "%50" .lshr 16 16 (reg "%37") (splatOf 16 16 4),
      .vecBitcast "%51" 16 16 32 8 (reg "%50"),
      .binopVec "%52" .and 32 8 (reg "%51") (splatOf 32 8 15),
      pshufb "%53" t3Lanes (reg "%52"),
      .binopVec "%and.i3542.i.i" .and 32 8 (reg "%and.i3741.i.i") (reg "%53"),
      .vecBitcast "%and.i35.i.i" 32 8 4 64 (reg "%and.i3542.i.i"),
      usubSat "%elt.sat.i40.i.i" (reg "%40") 96,
      usubSat "%elt.sat.i.i.i" (reg "%41") 112,
      .binopVec "%or.i43.i.i" .or 32 8 (reg "%elt.sat.i.i.i")
        (reg "%elt.sat.i40.i.i"),
      .vecBitcast "%or.i.i.i" 32 8 4 64 (reg "%or.i43.i.i"),
      .binopVec "%and.i.i.i" .and 4 64 (reg "%or.i.i.i") highBitMask,
      .binopVec "%xor.i.i.i" .xor 4 64 (reg "%and.i.i.i") (reg "%and.i35.i.i"),
      .gep "%add.ptr.i4.i" (.int 8) (reg "%add.ptr") (lit 64 31),
      .load "%54" v4i64 (reg "%add.ptr.i4.i"),
      .gep "%add.ptr3.i5.i" (.int 8) (reg "%add.ptr") (lit 64 30),
      .load "%55" v32i8 (reg "%add.ptr3.i5.i"),
      .gep "%add.ptr5.i6.i" (.int 8) (reg "%add.ptr") (lit 64 29),
      .load "%56" v32i8 (reg "%add.ptr5.i6.i"),
      .vecBitcast "%57" 4 64 32 8 (reg "%54"),
      .binopVec "%58" .and 32 8 (reg "%57") (splatOf 32 8 15),
      pshufb "%59" t1Lanes (reg "%58"),
      .vecBitcast "%60" 4 64 16 16 (reg "%54"),
      .binopVec "%61" .lshr 16 16 (reg "%60") (splatOf 16 16 4),
      .vecBitcast "%62" 16 16 32 8 (reg "%61"),
      .binopVec "%63" .and 32 8 (reg "%62") (splatOf 32 8 15),
      pshufb "%64" t2Lanes (reg "%63"),
      .binopVec "%and.i3741.i7.i" .and 32 8 (reg "%64") (reg "%59"),
      .binopVec "%65" .lshr 16 16 (reg "%38") (splatOf 16 16 4),
      .vecBitcast "%66" 16 16 32 8 (reg "%65"),
      .binopVec "%67" .and 32 8 (reg "%66") (splatOf 32 8 15),
      pshufb "%68" t3Lanes (reg "%67"),
      .binopVec "%and.i3542.i8.i" .and 32 8 (reg "%and.i3741.i7.i") (reg "%68"),
      .vecBitcast "%and.i35.i9.i" 32 8 4 64 (reg "%and.i3542.i8.i"),
      usubSat "%elt.sat.i40.i10.i" (reg "%55") 96,
      usubSat "%elt.sat.i.i11.i" (reg "%56") 112,
      .binopVec "%or.i43.i12.i" .or 32 8 (reg "%elt.sat.i.i11.i")
        (reg "%elt.sat.i40.i10.i"),
      .vecBitcast "%or.i.i13.i" 32 8 4 64 (reg "%or.i43.i12.i"),
      .binopVec "%and.i.i14.i" .and 4 64 (reg "%or.i.i13.i") highBitMask,
      .binopVec "%xor.i.i15.i" .xor 4 64 (reg "%and.i.i14.i") (reg "%and.i35.i9.i"),
      .binopVec "%or.i.i" .or 4 64 (reg "%xor.i.i.i") (reg "%u8k.076"),
      .binopVec "%or.i47" .or 4 64 (reg "%or.i.i") (reg "%xor.i.i15.i"),
      .binop "%inc" .add 64 (reg "%bi.075") (lit 64 1),
      .icmp "%exitcond.not" .eq 64 (reg "%inc") (reg "%div44")],
    term := .condbr (reg "%exitcond.not") "for.cond.cleanup" "for.body" }

/-! ##### `if.then20` — the tail byte's own test -/

def utf8Then20 : Block :=
  { name := "if.then20",
    instrs := [
      .gep "%69" (.int 8) (reg "%b") (reg "%n"),
      .gep "%arrayidx" (.int 8) (reg "%69") (lit 64 (-1)),
      .load "%70" (.int 8) (reg "%arrayidx"),
      .binop "%71" .and 8 (reg "%70") (lit 8 (-2)),
      .icmp "%cmp.i" .eq 8 (reg "%71") (lit 8 (-64)),
      .icmp "%cmp3.i" .ugt 8 (reg "%70") (lit 8 (-12)),
      .binop "%72" .or 1 (reg "%cmp3.i") (reg "%cmp.i"),
      .binop "%or2373" .or 1 (reg "%tobool16.not") (reg "%72")],
    term := .br "if.end24" }

/-! ##### `if.end24` — the returned word -/

def utf8End24 : Block :=
  { name := "if.end24",
    instrs := [
      .phi "%err.0.in" (.int 1)
        [("if.then20", reg "%or2373"), ("for.cond.cleanup", reg "%tobool16.not")],
      .zext "%err.0" 1 64 (reg "%err.0.in")],
    term := .ret (.int 64) (some (reg "%err.0")) }

/-- The unit: the ABI's three parameters and the nine blocks in the emission's
order. -/
def utf8Function : Function :=
  { name := "leanllvm_json_utf8",
    retTy := .int 64,
    params := [("%b", .ptr), ("%n", .int 64), ("%ungated", .int 32)],
    blocks :=
      [utf8Entry, utf8LrPh, utf8ForBodyUs, utf8ThenUs, utf8EndUs, utf8Cleanup,
       utf8ForBody, utf8Then20, utf8End24] }

/-! ### The pin -/

-- The committed text parses to the body above, and to one function.
#guard decide (firstFunction utf8Src = some utf8Function)

-- The ABI: the three parameters the capture refuses to rename, in their order.
#guard
  match firstFunction utf8Src with
  | some f =>
      f.name = "leanllvm_json_utf8" ∧ f.retTy = Ty.int 64 ∧
      f.params = [("%b", Ty.ptr), ("%n", Ty.int 64), ("%ungated", Ty.int 32)]
  | none => false

-- Every count below is the enumeration beside it.  The nine blocks, and the
-- instruction lines of each.
#guard utf8Function.blocks.length = 9

#guard utf8Entry.instrs.length = 3
#guard utf8LrPh.instrs.length = 1
#guard utf8ForBodyUs.instrs.length = 13
#guard utf8ThenUs.instrs.length = 58
#guard utf8EndUs.instrs.length = 3
#guard utf8Cleanup.instrs.length = 7
#guard utf8ForBody.instrs.length = 65
#guard utf8Then20.instrs.length = 8
#guard utf8End24.instrs.length = 2

-- The staged window's three halves, and so the total the nine blocks carry:
-- 3 + 1 + 13 + 58 + 3 + 7 + 65 + 8 + 2 = 160 instruction lines plus nine
-- terminators.
#guard utf8Function.blocks.map (fun b => b.instrs.length) =
  [3, 1, 13, 58, 3, 7, 65, 8, 2]

/-! ### The staged window, and the fuel

`utf8Window` is the window the body reads, written the way the readability
hypothesis writes it: three prefix bytes, the document, and zero padding to the
64-byte boundary `nb` counts.  `fuelOf` is the run's budget as a function of that
block count.  Each loop body is one block, so the ungated loop takes **one**
control step per block (`for.body` is its own successor) and the gated loop at
most three (`for.body.us`, then `if.then11.us` and `if.end14.us`); the five steps
outside the loops are `entry`, `for.body.lr.ph`, `for.cond.cleanup`, `if.then20`
and `if.end24`.  The worst case is therefore `3 * nb + 5`, and `3 * nb + 8` is
that bound with three steps of slack — slack rather than a count of anything,
which is why what has to be shown later is that the budget suffices, not that it
is tight. -/

/-- The window the body reads: three zero prefix bytes, the document, zero
padding to `64 * nb` bytes after the document. -/
def utf8Window (doc : List UInt8) (n nb : Nat) : List UInt8 :=
  List.replicate 3 0 ++ doc ++ List.replicate (64 * nb - n) 0

/-- A length is inside its own block count: `n ≤ 64 * ((n + 63) / 64)`.  This is
what makes the padding count `64 * nb - n` a subtraction of something smaller,
which is why `utf8Window_length` does not need a hypothesis about it. -/
theorem le_mul_div_sixtyfour (n : Nat) : n ≤ 64 * ((n + 63) / 64) := by
  have h := Nat.div_add_mod (n + 63) 64
  have hmod : (n + 63) % 64 < 64 := Nat.mod_lt _ (by decide)
  omega

/-- The staged window's length, when `nb` is the block count of `n` bytes. -/
theorem utf8Window_length (doc : List UInt8) (n nb : Nat) (hn : n = doc.length)
    (hnb : nb = (n + 63) / 64) : (utf8Window doc n nb).length = 3 + 64 * nb := by
  have hle := le_mul_div_sixtyfour n
  subst hn
  subst hnb
  unfold utf8Window
  simp only [List.length_append, List.length_replicate]
  omega

/-- The run's fuel, as a function of the block count.  The worst case is
`3 * nb + 5`: `entry` and `for.body.lr.ph` before the loop, at most three control
steps per gated block (`for.body.us`, `if.then11.us`, `if.end14.us`; the ungated
loop takes one per block), then `for.cond.cleanup` and at most two more
(`if.then20`, `if.end24`).  The constant is `3 * nb + 8`, so it carries three
steps of slack rather than one — slack, not a derived count, which is why the
proof obligation is that this budget suffices and not that it is tight. -/
def fuelOf (nb : Nat) : Nat := 3 * nb + 8

end LeanLLVM.Vellum.JsonUtf8IR
