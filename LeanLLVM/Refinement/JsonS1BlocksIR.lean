/-
An emitted-IR bridge for the contracted stage-1 block unit.

`probes/install/ir/json-s1-blocks.candidate.ll` is the emission of
`kernel/json/s1_blocks.c` at the measured compiler line, normalised;
`probes/install/ir/capture-s1-blocks.sh` records the invocation and derives, by
diffing its own clang block against what it emits, every item the normalisation
took out (`json-s1-blocks.strip.tsv`, by class), every place it rewrote text
(`json-s1-blocks.rewrites.tsv`, with the reason), and the fixture's own
construct inventory (`json-s1-blocks.inventory`, opcodes and call targets).

This module parses the file and pins the parsed AST against the literal below.
The pin is a `#guard` rather than a `rfl` proposition because the parser runs on
`String` primitives, which the kernel does not reduce, so a proposition about a
`parseModule` result cannot be closed by reflexivity.  What the pin buys is that
the hand-written AST and the committed text are the same object: a change to
either that the other does not carry fails elaboration, and no theorem can be
stated about a body the text does not contain.

The registers the emission names are its own (`%0`, `%add.ptr`, `%cmp.i39.i`,
…).  The body's seven parameters keep the source's names (`%b`, `%n`, `%ent`,
`%xp`, `%nxp`, `%xcarry`, `%arm`), so the capture applies no rename.

## What the pin establishes

The unit's body is the classifier's text inlined into one loop, with the UTF-8
stage's Keiser-Lemire DFA fused into the same block: the mask words, both
carries, the entry word and the DFA's `u8k`/`prev_ascii` pair stay in registers,
the entry word is composed and stored at `ent[i]`, and the escape list is
appended when `arm & 2`.  The block's two vectors are tested once for ASCII (the
`ptestz` on their `or`), and the DFA runs in `if.then`/`if.then74` when the block
or its predecessor is not ASCII, or on every block when `arm & 4` selects the
ungated path.  The return word composes the ASCII probe (bit 0) and the UTF-8
stage's error word (bit 1) in `if.end100`.

Five facts the proof and the contract rest on are guarded here:

* the body allocates nothing (`allocaTypes = []`): its scratch is the caller's,
  so no callee-moved allocator appears in a frame the pipeline does not name;
* the call census is the classifier's two intrinsics, the ASCII probe's and the
  UTF-8 stage's lane test, the UTF-8 stage's saturating subtraction, and the
  escape list, with the multiplicity the loop, the peeled block and their two
  DFA arms emit;
* the ABI is `s1_blocks.h`'s, in its argument order, and it returns `i64`;
* the return's shape is valued (`.ret (.int 64) (some …)`), which is what a
  `Satisfies` record with a value-returning callee requires;
* the return value is `(ascii_probe) | (utf8_error << 1)`, whose two bits the
  contract reads separately.

The block loop's invariant, the mask identities and the DFA's refinement are the
steps modules' and `JsonUtf8Steps`'s, not this one's; here the body is only
pinned.
-/
import LeanLLVM.Parser
import LeanLLVM.Memory
import LeanLLVM.Refinement.Pclmul

namespace LeanLLVM.Refinement.JsonS1BlocksIR

open LeanLLVM

/-! ### The fixture -/

/-- The block unit as emitted and committed. -/
def s1BlocksSrc : String :=
  include_str "../../probes/install/ir/json-s1-blocks.candidate.ll"

/-- Parse a fixture and take its single function. -/
def firstFunction (src : String) : Option Function :=
  match parseModule src with
  | .ok m => m.functions.head?
  | .error _ => none

/-- Parse a fixture and take every function it defines, in order. -/
def parsedFunctions (src : String) : Option (List Function) :=
  match parseModule src with
  | .ok m => some m.functions
  | .error _ => none

/-! ### The pinned AST

The body, block by block, in the order the fixture holds it.  The helpers below
only spell an operand the way `parseConst`/`parseOperand` read one; they decide
nothing. -/

/-- A register operand. -/
def reg (n : String) : Operand := .reg n

/-- An integer literal of width `w`. -/
def lit (w : Nat) (v : Int) : Operand := .imm (.int w (BitVec.ofInt w v))

/-- A `splat` vector constant: `splat (i<w> <v>)` at `n` lanes. -/
def splatOf (n w : Nat) (v : Int) : Operand := .imm (.splat n w (BitVec.ofInt w v))

/-- A lane-list vector constant `<i<w> v₀, …, i<w> v₍ₖ₋₁₎>`. -/
def lanesOf (w : Nat) (vs : List Int) : Operand :=
  .imm (.vector w (vs.map (BitVec.ofInt w)))

/-! The unit's blocks, in the fixture's order. -/

def entryBlock : Block :=
  { name := "entry",
    instrs := [
      .binop "%shr" .lshr 64 (reg "%n") (lit 64 6),
      .binop "%and" .and 64 (reg "%n") (lit 64 63),
      .trunc "%0" 64 32 (reg "%arm"),
      .binop "%1" .lshr 32 (reg "%0") (lit 32 2),
      .binop "%conv" .and 32 (reg "%1") (lit 32 1),
      .icmp "%cmp4280.not" .ult 64 (reg "%n") (lit 64 64)
    ],
    term := .condbr (reg "%cmp4280.not") "for.cond.cleanup" "for.body.lr.ph" }

def for_body_lr_phBlock : Block :=
  { name := "for.body.lr.ph",
    instrs := [
      .icmp "%tobool" .eq 32 (reg "%conv") (lit 32 0),
      .binop "%and27" .and 64 (reg "%arm") (lit 64 2),
      .icmp "%tobool28.not" .eq 64 (reg "%and27") (lit 64 0)
    ],
    term := .br "for.body" }

def for_cond_cleanup_loopexitBlock : Block :=
  { name := "for.cond.cleanup.loopexit",
    instrs := [
      .icmp "%2" .ne 32 (reg "%5") (lit 32 0)
    ],
    term := .br "for.cond.cleanup" }

def for_cond_cleanupBlock : Block :=
  { name := "for.cond.cleanup",
    instrs := [
      .phi "%st.sroa.11.0.lcssa" (.int 64) [("entry", lit 64 0), ("for.cond.cleanup.loopexit", reg "%shr.i")],
      .phi "%st.sroa.7.0.lcssa" (.int 64) [("entry", lit 64 0), ("for.cond.cleanup.loopexit", reg "%conv13.i.i")],
      .phi "%st.sroa.0.0.lcssa" (.int 64) [("entry", lit 64 0), ("for.cond.cleanup.loopexit", reg "%shr.i.i")],
      .phi "%prev_ascii.0.lcssa" (.int 1) [("entry", lit 1 1), ("for.cond.cleanup.loopexit", reg "%2")],
      .phi "%u8k.0.lcssa" (.vec 4 (.int 64)) [("entry", splatOf 4 64 0), ("for.cond.cleanup.loopexit", reg "%u8k.1")],
      .phi "%ascii.0.lcssa" (.vec 4 (.int 64)) [("entry", splatOf 4 64 0), ("for.cond.cleanup.loopexit", reg "%or.i169")],
      .phi "%prevS.0.lcssa" (.int 64) [("entry", lit 64 0), ("for.cond.cleanup.loopexit", reg "%shr22")],
      .icmp "%tobool32.not" .eq 64 (reg "%and") (lit 64 0)
    ],
    term := .condbr (reg "%tobool32.not") "if.end83" "if.then33" }

def for_bodyBlock : Block :=
  { name := "for.body",
    instrs := [
      .phi "%prevS.0288" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end31", reg "%shr22")],
      .phi "%ascii.0287" (.vec 4 (.int 64)) [("for.body.lr.ph", splatOf 4 64 0), ("if.end31", reg "%or.i169")],
      .phi "%u8k.0286" (.vec 4 (.int 64)) [("for.body.lr.ph", splatOf 4 64 0), ("if.end31", reg "%u8k.1")],
      .phi "%prev_ascii.0285" (.int 32) [("for.body.lr.ph", lit 32 1), ("if.end31", reg "%5")],
      .phi "%i.0284" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end31", reg "%inc")],
      .phi "%st.sroa.0.0283" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end31", reg "%shr.i.i")],
      .phi "%st.sroa.7.0282" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end31", reg "%conv13.i.i")],
      .phi "%st.sroa.11.0281" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end31", reg "%shr.i")],
      .binop "%shl" .shl 64 (reg "%i.0284") (lit 64 6),
      .gep "%add.ptr" (.int 8) (reg "%b") (reg "%shl"),
      .load "%3" (.vec 4 (.int 64)) (reg "%add.ptr"),
      .gep "%add.ptr7" (.int 8) (reg "%add.ptr") (lit 64 32),
      .load "%4" (.vec 4 (.int 64)) (reg "%add.ptr7"),
      .binopVec "%or.i170" .or 4 64 (reg "%4") (reg "%3"),
      .call "%5" (.int 32) "llvm.x86.avx.ptestz.256" [(.vec 4 (.int 64), reg "%or.i170"), (.vec 4 (.int 64), splatOf 4 64 (-9187201950435737472))],
      .binopVec "%or.i169" .or 4 64 (reg "%or.i170") (reg "%ascii.0287"),
      .vecBitcast "%6" 4 64 32 8 (reg "%3"),
      .vecBitcast "%7" 4 64 32 8 (reg "%4"),
      .shuffleVec "%8" 4 64 (reg "%3") (reg "%4") [0, 1, 2, 3, 4, 5, 6, 7],
      .vecBitcast "%9" 8 64 64 8 (reg "%8"),
      .icmpVec "%10" .eq 64 8 (reg "%9") (splatOf 64 8 34),
      .bitcastMask "%or.i171" 64 (reg "%10"),
      .icmpVec "%cmp.i39.i" .eq 32 8 (reg "%6") (splatOf 32 8 92),
      .bitcastMask "%11" 32 (reg "%cmp.i39.i"),
      .zext "%conv9.i" 32 64 (reg "%11"),
      .icmpVec "%cmp.i.i" .eq 32 8 (reg "%7") (splatOf 32 8 92),
      .bitcastMask "%12" 32 (reg "%cmp.i.i"),
      .zext "%conv12.i" 32 64 (reg "%12"),
      .binop "%shl13.i" .shl 64 (reg "%conv12.i") (lit 64 32),
      .binop "%or14.i" .or 64 (reg "%shl13.i") (reg "%conv9.i"),
      .binop "%and.i.i" .and 64 (reg "%st.sroa.0.0283") (reg "%st.sroa.7.0282"),
      .binop "%shl.i.i" .shl 64 (reg "%or14.i") (lit 64 1),
      .binop "%not.i.i" .xor 64 (reg "%shl.i.i") (lit 64 (-1)),
      .binop "%and1.i.i" .and 64 (reg "%or14.i") (reg "%not.i.i"),
      .binop "%xor.i.i" .xor 64 (reg "%and.i.i") (lit 64 6148914691236517205),
      .binop "%and2.i.i" .and 64 (reg "%and1.i.i") (reg "%xor.i.i"),
      .binop "%xor3.i.i" .xor 64 (reg "%and2.i.i") (reg "%and1.i.i"),
      .binop "%not4.i.i" .xor 64 (reg "%or14.i") (lit 64 (-1)),
      .binop "%add.i.i" .add 64 (reg "%and2.i.i") (reg "%or14.i"),
      .binop "%add5.i.i" .add 64 (reg "%xor3.i.i") (reg "%or14.i"),
      .binop "%and6.i.i" .and 64 (reg "%not4.i.i") (lit 64 (-6148914691236517206)),
      .binop "%and7.i.i" .and 64 (reg "%and6.i.i") (reg "%add.i.i"),
      .binop "%and8.i.i" .and 64 (reg "%not4.i.i") (lit 64 6148914691236517205),
      .binop "%and9.i.i" .and 64 (reg "%and8.i.i") (reg "%add5.i.i"),
      .binop "%and11.i.i" .and 64 (reg "%and.i.i") (reg "%not4.i.i"),
      .binop "%or.i.i" .or 64 (reg "%and7.i.i") (reg "%and11.i.i"),
      .binop "%or12.i.i" .or 64 (reg "%or.i.i") (reg "%and9.i.i"),
      .icmp "%cmp.i45.i" .ult 64 (reg "%add5.i.i") (reg "%or14.i"),
      .zext "%conv13.i.i" 1 64 (reg "%cmp.i45.i"),
      .binop "%shr.i.i" .lshr 64 (reg "%conv12.i") (lit 64 31),
      .binop "%not.i" .xor 64 (reg "%or12.i.i") (lit 64 (-1)),
      .binop "%and.i" .and 64 (reg "%or.i171") (reg "%not.i"),
      .vecBitcast "%13" 4 64 16 16 (reg "%3"),
      .binopVec "%14" .lshr 16 16 (reg "%13") (splatOf 16 16 4),
      .binopVec "%15" .and 32 8 (reg "%6") (splatOf 32 8 15),
      .call "%16" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [64, 0, 0, 0, 0, 0, 0, 0, 0, -128, -126, 20, 1, -88, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, -128, -126, 20, 1, -88, 0, 0]), (.vec 32 (.int 8), reg "%15")],
      .vecBitcast "%17" 16 16 32 8 (reg "%14"),
      .binopVec "%18" .and 32 8 (reg "%17") (splatOf 32 8 15),
      .call "%19" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [-128, 0, 65, 2, 0, 48, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, -128, 0, 65, 2, 0, 48, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0]), (.vec 32 (.int 8), reg "%18")],
      .binopVec "%and.i2326.i.i" .and 32 8 (reg "%19") (reg "%16"),
      .binopVec "%20" .and 32 8 (reg "%and.i2326.i.i") (splatOf 32 8 63),
      .icmpVec "%cmp.i21.i.i" .eq 32 8 (reg "%20") (splatOf 32 8 0),
      .bitcastMask "%21" 32 (reg "%cmp.i21.i.i"),
      .binop "%not.i46.i" .xor 32 (reg "%21") (lit 32 (-1)),
      .vecBitcast "%22" 4 64 16 16 (reg "%4"),
      .binopVec "%23" .lshr 16 16 (reg "%22") (splatOf 16 16 4),
      .binopVec "%24" .and 32 8 (reg "%7") (splatOf 32 8 15),
      .call "%25" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [64, 0, 0, 0, 0, 0, 0, 0, 0, -128, -126, 20, 1, -88, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, -128, -126, 20, 1, -88, 0, 0]), (.vec 32 (.int 8), reg "%24")],
      .vecBitcast "%26" 16 16 32 8 (reg "%23"),
      .binopVec "%27" .and 32 8 (reg "%26") (splatOf 32 8 15),
      .call "%28" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [-128, 0, 65, 2, 0, 48, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, -128, 0, 65, 2, 0, 48, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0]), (.vec 32 (.int 8), reg "%27")],
      .binopVec "%and.i2326.i47.i" .and 32 8 (reg "%28") (reg "%25"),
      .binopVec "%29" .and 32 8 (reg "%and.i2326.i47.i") (splatOf 32 8 63),
      .icmpVec "%cmp.i21.i48.i" .eq 32 8 (reg "%29") (splatOf 32 8 0),
      .bitcastMask "%30" 32 (reg "%cmp.i21.i48.i"),
      .binop "%not.i49.i" .xor 32 (reg "%30") (lit 32 (-1)),
      .zext "%conv16.i" 32 64 (reg "%not.i46.i"),
      .zext "%conv17.i" 32 64 (reg "%not.i49.i"),
      .binop "%shl18.i" .shl 64 (reg "%conv17.i") (lit 64 32),
      .binop "%or19.i" .or 64 (reg "%shl18.i") (reg "%conv16.i"),
      .shuffleVec "%31" 32 8 (reg "%and.i2326.i.i") (reg "%and.i2326.i47.i") [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63],
      .icmpVec "%32" .eq 64 8 (reg "%31") (splatOf 64 8 0),
      .bitcastMask "%or23.i" 64 (reg "%32"),
      .insertelement "%vecinit1.i.i.i" 2 64 (splatOf 2 64 0) (reg "%and.i") (lit 64 0),
      .call "%33" (.vec 2 (.int 64)) "llvm.x86.pclmulqdq" [(.vec 2 (.int 64), reg "%vecinit1.i.i.i"), (.vec 2 (.int 64), lanesOf 64 [-1, 0]), (.int 8, lit 8 0)],
      .extractelement "%vecext.i.i.i" 2 64 (reg "%33") (lit 64 0),
      .binop "%xor.i" .xor 64 (reg "%vecext.i.i.i") (reg "%st.sroa.11.0281"),
      .binop "%shr.i" .ashr 64 (reg "%xor.i") (lit 64 63),
      .binop "%not13" .xor 64 (reg "%xor.i") (lit 64 (-1)),
      .binop "%34" .or 64 (reg "%and.i") (reg "%xor.i"),
      .binop "%35" .xor 64 (reg "%34") (lit 64 (-1)),
      .binop "%and14" .and 64 (reg "%or23.i") (reg "%35"),
      .binop "%and16" .and 64 (reg "%or19.i") (reg "%not13"),
      .binop "%shl17" .shl 64 (reg "%and14") (lit 64 1),
      .binop "%or18" .or 64 (reg "%shl17") (reg "%prevS.0288"),
      .binop "%not19" .xor 64 (reg "%or18") (lit 64 (-1)),
      .binop "%and20" .and 64 (reg "%and14") (reg "%not19"),
      .binop "%36" .or 64 (reg "%and16") (reg "%and20"),
      .binop "%or21" .or 64 (reg "%36") (reg "%and.i"),
      .binop "%shr22" .lshr 64 (reg "%and14") (lit 64 63),
      .gep "%arrayidx" (.int 64) (reg "%ent") (reg "%i.0284"),
      .store (.int 64) (reg "%or21") (reg "%arrayidx"),
      .icmp "%tobool23" .ne 32 (reg "%5") (lit 32 0),
      .icmp "%tobool24" .ne 32 (reg "%prev_ascii.0285") (lit 32 0),
      .binop "%37" .and 1 (reg "%tobool24") (reg "%tobool23"),
      .select "%or.cond107" (.int 1) (reg "%tobool") (reg "%37") (lit 1 0)
    ],
    term := .condbr (reg "%or.cond107") "if.end" "if.then" }

def if_thenBlock : Block :=
  { name := "if.then",
    instrs := [
      .gep "%add.ptr.i.i" (.int 8) (reg "%add.ptr") (lit 64 (-1)),
      .load "%38" (.vec 4 (.int 64)) (reg "%add.ptr.i.i"),
      .gep "%add.ptr3.i.i" (.int 8) (reg "%add.ptr") (lit 64 (-2)),
      .load "%39" (.vec 32 (.int 8)) (reg "%add.ptr3.i.i"),
      .gep "%add.ptr5.i.i" (.int 8) (reg "%add.ptr") (lit 64 (-3)),
      .load "%40" (.vec 32 (.int 8)) (reg "%add.ptr5.i.i"),
      .vecBitcast "%41" 4 64 32 8 (reg "%38"),
      .binopVec "%42" .and 32 8 (reg "%41") (splatOf 32 8 15),
      .call "%43" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [-25, -93, -125, -125, -117, -53, -53, -53, -53, -53, -53, -53, -53, -37, -53, -53, -25, -93, -125, -125, -117, -53, -53, -53, -53, -53, -53, -53, -53, -37, -53, -53]), (.vec 32 (.int 8), reg "%42")],
      .vecBitcast "%44" 4 64 16 16 (reg "%38"),
      .binopVec "%45" .lshr 16 16 (reg "%44") (splatOf 16 16 4),
      .vecBitcast "%46" 16 16 32 8 (reg "%45"),
      .binopVec "%47" .and 32 8 (reg "%46") (splatOf 32 8 15),
      .call "%48" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [2, 2, 2, 2, 2, 2, 2, 2, -128, -128, -128, -128, 33, 1, 21, 73, 2, 2, 2, 2, 2, 2, 2, 2, -128, -128, -128, -128, 33, 1, 21, 73]), (.vec 32 (.int 8), reg "%47")],
      .binopVec "%and.i3741.i.i" .and 32 8 (reg "%48") (reg "%43"),
      .call "%49" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [1, 1, 1, 1, 1, 1, 1, 1, -26, -82, -70, -70, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -26, -82, -70, -70, 1, 1, 1, 1]), (.vec 32 (.int 8), reg "%18")],
      .binopVec "%and.i3542.i.i" .and 32 8 (reg "%and.i3741.i.i") (reg "%49"),
      .vecBitcast "%and.i35.i.i" 32 8 4 64 (reg "%and.i3542.i.i"),
      .call "%elt.sat.i40.i.i" (.vec 32 (.int 8)) "llvm.usub.sat.v32i8" [(.vec 32 (.int 8), reg "%39"), (.vec 32 (.int 8), splatOf 32 8 96)],
      .call "%elt.sat.i.i.i" (.vec 32 (.int 8)) "llvm.usub.sat.v32i8" [(.vec 32 (.int 8), reg "%40"), (.vec 32 (.int 8), splatOf 32 8 112)],
      .binopVec "%or.i43.i.i" .or 32 8 (reg "%elt.sat.i.i.i") (reg "%elt.sat.i40.i.i"),
      .vecBitcast "%or.i.i.i" 32 8 4 64 (reg "%or.i43.i.i"),
      .binopVec "%and.i.i.i" .and 4 64 (reg "%or.i.i.i") (splatOf 4 64 (-9187201950435737472)),
      .binopVec "%xor.i.i.i" .xor 4 64 (reg "%and.i.i.i") (reg "%and.i35.i.i"),
      .gep "%add.ptr.i4.i" (.int 8) (reg "%add.ptr") (lit 64 31),
      .load "%50" (.vec 4 (.int 64)) (reg "%add.ptr.i4.i"),
      .gep "%add.ptr3.i5.i" (.int 8) (reg "%add.ptr") (lit 64 30),
      .load "%51" (.vec 32 (.int 8)) (reg "%add.ptr3.i5.i"),
      .gep "%add.ptr5.i6.i" (.int 8) (reg "%add.ptr") (lit 64 29),
      .load "%52" (.vec 32 (.int 8)) (reg "%add.ptr5.i6.i"),
      .vecBitcast "%53" 4 64 32 8 (reg "%50"),
      .binopVec "%54" .and 32 8 (reg "%53") (splatOf 32 8 15),
      .call "%55" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [-25, -93, -125, -125, -117, -53, -53, -53, -53, -53, -53, -53, -53, -37, -53, -53, -25, -93, -125, -125, -117, -53, -53, -53, -53, -53, -53, -53, -53, -37, -53, -53]), (.vec 32 (.int 8), reg "%54")],
      .vecBitcast "%56" 4 64 16 16 (reg "%50"),
      .binopVec "%57" .lshr 16 16 (reg "%56") (splatOf 16 16 4),
      .vecBitcast "%58" 16 16 32 8 (reg "%57"),
      .binopVec "%59" .and 32 8 (reg "%58") (splatOf 32 8 15),
      .call "%60" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [2, 2, 2, 2, 2, 2, 2, 2, -128, -128, -128, -128, 33, 1, 21, 73, 2, 2, 2, 2, 2, 2, 2, 2, -128, -128, -128, -128, 33, 1, 21, 73]), (.vec 32 (.int 8), reg "%59")],
      .binopVec "%and.i3741.i7.i" .and 32 8 (reg "%60") (reg "%55"),
      .call "%61" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [1, 1, 1, 1, 1, 1, 1, 1, -26, -82, -70, -70, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -26, -82, -70, -70, 1, 1, 1, 1]), (.vec 32 (.int 8), reg "%27")],
      .binopVec "%and.i3542.i8.i" .and 32 8 (reg "%and.i3741.i7.i") (reg "%61"),
      .vecBitcast "%and.i35.i9.i" 32 8 4 64 (reg "%and.i3542.i8.i"),
      .call "%elt.sat.i40.i10.i" (.vec 32 (.int 8)) "llvm.usub.sat.v32i8" [(.vec 32 (.int 8), reg "%51"), (.vec 32 (.int 8), splatOf 32 8 96)],
      .call "%elt.sat.i.i11.i" (.vec 32 (.int 8)) "llvm.usub.sat.v32i8" [(.vec 32 (.int 8), reg "%52"), (.vec 32 (.int 8), splatOf 32 8 112)],
      .binopVec "%or.i43.i12.i" .or 32 8 (reg "%elt.sat.i.i11.i") (reg "%elt.sat.i40.i10.i"),
      .vecBitcast "%or.i.i13.i" 32 8 4 64 (reg "%or.i43.i12.i"),
      .binopVec "%and.i.i14.i" .and 4 64 (reg "%or.i.i13.i") (splatOf 4 64 (-9187201950435737472)),
      .binopVec "%xor.i.i15.i" .xor 4 64 (reg "%and.i.i14.i") (reg "%and.i35.i9.i"),
      .binopVec "%62" .or 4 64 (reg "%xor.i.i.i") (reg "%xor.i.i15.i"),
      .binopVec "%or.i168" .or 4 64 (reg "%62") (reg "%u8k.0286")
    ],
    term := .br "if.end" }

def if_endBlock : Block :=
  { name := "if.end",
    instrs := [
      .phi "%u8k.1" (.vec 4 (.int 64)) [("for.body", reg "%u8k.0286"), ("if.then", reg "%or.i168")]
    ],
    term := .condbr (reg "%tobool28.not") "if.end31" "if.then29" }

def if_then29Block : Block :=
  { name := "if.then29",
    instrs := [
      .shuffleVec "%63" 4 64 (reg "%3") (reg "%4") [0, 1, 2, 3, 4, 5, 6, 7],
      .vecBitcast "%64" 8 64 64 8 (reg "%63"),
      .icmpVec "%65" .ult 64 8 (reg "%64") (splatOf 64 8 32),
      .bitcastMask "%or.i176" 64 (reg "%65"),
      .callVoid "leanllvm_json_escape_list" [(.int 64, reg "%or14.i"), (.int 64, reg "%or.i176"), (.int 64, reg "%xor.i"), (.int 64, reg "%i.0284"), (.ptr, reg "%xp"), (.ptr, reg "%nxp"), (.ptr, reg "%xcarry")]
    ],
    term := .br "if.end31" }

def if_end31Block : Block :=
  { name := "if.end31",
    instrs := [
      .binop "%inc" .add 64 (reg "%i.0284") (lit 64 1),
      .icmp "%exitcond.not" .eq 64 (reg "%inc") (reg "%shr")
    ],
    term := .condbr (reg "%exitcond.not") "for.cond.cleanup.loopexit" "for.body" }

def if_then33Block : Block :=
  { name := "if.then33",
    instrs := [
      .binop "%shl35" .and 64 (reg "%n") (lit 64 (-64)),
      .gep "%add.ptr36" (.int 8) (reg "%b") (reg "%shl35"),
      .load "%66" (.vec 4 (.int 64)) (reg "%add.ptr36"),
      .gep "%add.ptr40" (.int 8) (reg "%add.ptr36") (lit 64 32),
      .load "%67" (.vec 4 (.int 64)) (reg "%add.ptr40"),
      .binopVec "%or.i167" .or 4 64 (reg "%67") (reg "%66"),
      .call "%68" (.int 32) "llvm.x86.avx.ptestz.256" [(.vec 4 (.int 64), reg "%or.i167"), (.vec 4 (.int 64), splatOf 4 64 (-9187201950435737472))],
      .binopVec "%or.i166" .or 4 64 (reg "%or.i167") (reg "%ascii.0.lcssa"),
      .vecBitcast "%69" 4 64 32 8 (reg "%66"),
      .vecBitcast "%70" 4 64 32 8 (reg "%67"),
      .shuffleVec "%71" 4 64 (reg "%66") (reg "%67") [0, 1, 2, 3, 4, 5, 6, 7],
      .vecBitcast "%72" 8 64 64 8 (reg "%71"),
      .icmpVec "%73" .eq 64 8 (reg "%72") (splatOf 64 8 34),
      .bitcastMask "%or.i182" 64 (reg "%73"),
      .shuffleVec "%74" 4 64 (reg "%66") (reg "%67") [0, 1, 2, 3, 4, 5, 6, 7],
      .vecBitcast "%75" 8 64 64 8 (reg "%74"),
      .icmpVec "%76" .eq 64 8 (reg "%75") (splatOf 64 8 92),
      .bitcastMask "%or14.i188" 64 (reg "%76"),
      .binop "%and.i.i190" .and 64 (reg "%st.sroa.0.0.lcssa") (reg "%st.sroa.7.0.lcssa"),
      .binop "%shl.i.i191" .shl 64 (reg "%or14.i188") (lit 64 1),
      .binop "%not.i.i192" .xor 64 (reg "%shl.i.i191") (lit 64 (-1)),
      .binop "%and1.i.i193" .and 64 (reg "%or14.i188") (reg "%not.i.i192"),
      .binop "%xor.i.i194" .xor 64 (reg "%and.i.i190") (lit 64 6148914691236517205),
      .binop "%and2.i.i195" .and 64 (reg "%and1.i.i193") (reg "%xor.i.i194"),
      .binop "%xor3.i.i196" .xor 64 (reg "%and2.i.i195") (reg "%and1.i.i193"),
      .binop "%not4.i.i197" .xor 64 (reg "%or14.i188") (lit 64 (-1)),
      .binop "%add.i.i198" .add 64 (reg "%and2.i.i195") (reg "%or14.i188"),
      .binop "%add5.i.i199" .add 64 (reg "%xor3.i.i196") (reg "%or14.i188"),
      .binop "%and6.i.i200" .and 64 (reg "%not4.i.i197") (lit 64 (-6148914691236517206)),
      .binop "%and7.i.i201" .and 64 (reg "%and6.i.i200") (reg "%add.i.i198"),
      .binop "%and8.i.i202" .and 64 (reg "%not4.i.i197") (lit 64 6148914691236517205),
      .binop "%and9.i.i203" .and 64 (reg "%and8.i.i202") (reg "%add5.i.i199"),
      .binop "%and11.i.i205" .and 64 (reg "%and.i.i190") (reg "%not4.i.i197"),
      .binop "%or.i.i206" .or 64 (reg "%and7.i.i201") (reg "%and11.i.i205"),
      .binop "%or12.i.i207" .or 64 (reg "%or.i.i206") (reg "%and9.i.i203"),
      .binop "%not.i211" .xor 64 (reg "%or12.i.i207") (lit 64 (-1)),
      .binop "%and.i212" .and 64 (reg "%or.i182") (reg "%not.i211"),
      .vecBitcast "%77" 4 64 16 16 (reg "%66"),
      .binopVec "%78" .lshr 16 16 (reg "%77") (splatOf 16 16 4),
      .binopVec "%79" .and 32 8 (reg "%69") (splatOf 32 8 15),
      .call "%80" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [64, 0, 0, 0, 0, 0, 0, 0, 0, -128, -126, 20, 1, -88, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, -128, -126, 20, 1, -88, 0, 0]), (.vec 32 (.int 8), reg "%79")],
      .vecBitcast "%81" 16 16 32 8 (reg "%78"),
      .binopVec "%82" .and 32 8 (reg "%81") (splatOf 32 8 15),
      .call "%83" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [-128, 0, 65, 2, 0, 48, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, -128, 0, 65, 2, 0, 48, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0]), (.vec 32 (.int 8), reg "%82")],
      .binopVec "%and.i2326.i.i213" .and 32 8 (reg "%83") (reg "%80"),
      .binopVec "%84" .and 32 8 (reg "%and.i2326.i.i213") (splatOf 32 8 63),
      .icmpVec "%cmp.i21.i.i214" .eq 32 8 (reg "%84") (splatOf 32 8 0),
      .bitcastMask "%85" 32 (reg "%cmp.i21.i.i214"),
      .binop "%not.i46.i215" .xor 32 (reg "%85") (lit 32 (-1)),
      .vecBitcast "%86" 4 64 16 16 (reg "%67"),
      .binopVec "%87" .lshr 16 16 (reg "%86") (splatOf 16 16 4),
      .binopVec "%88" .and 32 8 (reg "%70") (splatOf 32 8 15),
      .call "%89" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [64, 0, 0, 0, 0, 0, 0, 0, 0, -128, -126, 20, 1, -88, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, -128, -126, 20, 1, -88, 0, 0]), (.vec 32 (.int 8), reg "%88")],
      .vecBitcast "%90" 16 16 32 8 (reg "%87"),
      .binopVec "%91" .and 32 8 (reg "%90") (splatOf 32 8 15),
      .call "%92" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [-128, 0, 65, 2, 0, 48, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, -128, 0, 65, 2, 0, 48, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0]), (.vec 32 (.int 8), reg "%91")],
      .binopVec "%and.i2326.i47.i217" .and 32 8 (reg "%92") (reg "%89"),
      .binopVec "%93" .and 32 8 (reg "%and.i2326.i47.i217") (splatOf 32 8 63),
      .icmpVec "%cmp.i21.i48.i218" .eq 32 8 (reg "%93") (splatOf 32 8 0),
      .bitcastMask "%94" 32 (reg "%cmp.i21.i48.i218"),
      .binop "%not.i49.i219" .xor 32 (reg "%94") (lit 32 (-1)),
      .zext "%conv16.i221" 32 64 (reg "%not.i46.i215"),
      .zext "%conv17.i222" 32 64 (reg "%not.i49.i219"),
      .binop "%shl18.i223" .shl 64 (reg "%conv17.i222") (lit 64 32),
      .binop "%or19.i224" .or 64 (reg "%shl18.i223") (reg "%conv16.i221"),
      .shuffleVec "%95" 32 8 (reg "%and.i2326.i.i213") (reg "%and.i2326.i47.i217") [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63],
      .icmpVec "%96" .eq 64 8 (reg "%95") (splatOf 64 8 0),
      .bitcastMask "%or23.i228" 64 (reg "%96"),
      .insertelement "%vecinit1.i.i.i229" 2 64 (splatOf 2 64 0) (reg "%and.i212") (lit 64 0),
      .call "%97" (.vec 2 (.int 64)) "llvm.x86.pclmulqdq" [(.vec 2 (.int 64), reg "%vecinit1.i.i.i229"), (.vec 2 (.int 64), lanesOf 64 [-1, 0]), (.int 8, lit 8 0)],
      .extractelement "%vecext.i.i.i230" 2 64 (reg "%97") (lit 64 0),
      .binop "%xor.i232" .xor 64 (reg "%vecext.i.i.i230") (reg "%st.sroa.11.0.lcssa"),
      .binop "%not55" .xor 64 (reg "%xor.i232") (lit 64 (-1)),
      .binop "%98" .or 64 (reg "%and.i212") (reg "%xor.i232"),
      .binop "%99" .xor 64 (reg "%98") (lit 64 (-1)),
      .binop "%and56" .and 64 (reg "%or23.i228") (reg "%99"),
      .binop "%and59" .and 64 (reg "%or19.i224") (reg "%not55"),
      .binop "%shl61" .shl 64 (reg "%and56") (lit 64 1),
      .binop "%or62" .or 64 (reg "%shl61") (reg "%prevS.0.lcssa"),
      .binop "%not63" .xor 64 (reg "%or62") (lit 64 (-1)),
      .binop "%and64" .and 64 (reg "%and56") (reg "%not63"),
      .binop "%100" .or 64 (reg "%and59") (reg "%and64"),
      .binop "%or65" .or 64 (reg "%100") (reg "%and.i212"),
      .binop "%notmask" .shl 64 (lit 64 (-1)) (reg "%and"),
      .binop "%sub" .xor 64 (reg "%notmask") (lit 64 (-1)),
      .binop "%and67" .and 64 (reg "%or65") (reg "%sub"),
      .gep "%arrayidx68" (.int 64) (reg "%ent") (reg "%shr"),
      .store (.int 64) (reg "%and67") (reg "%arrayidx68"),
      .icmp "%tobool69" .eq 32 (reg "%conv") (lit 32 0),
      .icmp "%tobool71" .ne 32 (reg "%68") (lit 32 0),
      .select "%or.cond108" (.int 1) (reg "%tobool69") (reg "%tobool71") (lit 1 0),
      .select "%or.cond109" (.int 1) (reg "%or.cond108") (reg "%prev_ascii.0.lcssa") (lit 1 0)
    ],
    term := .condbr (reg "%or.cond109") "if.end77" "if.then74" }

def if_then74Block : Block :=
  { name := "if.then74",
    instrs := [
      .gep "%add.ptr.i.i234" (.int 8) (reg "%add.ptr36") (lit 64 (-1)),
      .load "%101" (.vec 4 (.int 64)) (reg "%add.ptr.i.i234"),
      .gep "%add.ptr3.i.i235" (.int 8) (reg "%add.ptr36") (lit 64 (-2)),
      .load "%102" (.vec 32 (.int 8)) (reg "%add.ptr3.i.i235"),
      .gep "%add.ptr5.i.i236" (.int 8) (reg "%add.ptr36") (lit 64 (-3)),
      .load "%103" (.vec 32 (.int 8)) (reg "%add.ptr5.i.i236"),
      .vecBitcast "%104" 4 64 32 8 (reg "%101"),
      .binopVec "%105" .and 32 8 (reg "%104") (splatOf 32 8 15),
      .call "%106" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [-25, -93, -125, -125, -117, -53, -53, -53, -53, -53, -53, -53, -53, -37, -53, -53, -25, -93, -125, -125, -117, -53, -53, -53, -53, -53, -53, -53, -53, -37, -53, -53]), (.vec 32 (.int 8), reg "%105")],
      .vecBitcast "%107" 4 64 16 16 (reg "%101"),
      .binopVec "%108" .lshr 16 16 (reg "%107") (splatOf 16 16 4),
      .vecBitcast "%109" 16 16 32 8 (reg "%108"),
      .binopVec "%110" .and 32 8 (reg "%109") (splatOf 32 8 15),
      .call "%111" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [2, 2, 2, 2, 2, 2, 2, 2, -128, -128, -128, -128, 33, 1, 21, 73, 2, 2, 2, 2, 2, 2, 2, 2, -128, -128, -128, -128, 33, 1, 21, 73]), (.vec 32 (.int 8), reg "%110")],
      .binopVec "%and.i3741.i.i237" .and 32 8 (reg "%111") (reg "%106"),
      .call "%112" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [1, 1, 1, 1, 1, 1, 1, 1, -26, -82, -70, -70, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -26, -82, -70, -70, 1, 1, 1, 1]), (.vec 32 (.int 8), reg "%82")],
      .binopVec "%and.i3542.i.i238" .and 32 8 (reg "%and.i3741.i.i237") (reg "%112"),
      .vecBitcast "%and.i35.i.i239" 32 8 4 64 (reg "%and.i3542.i.i238"),
      .call "%elt.sat.i40.i.i240" (.vec 32 (.int 8)) "llvm.usub.sat.v32i8" [(.vec 32 (.int 8), reg "%102"), (.vec 32 (.int 8), splatOf 32 8 96)],
      .call "%elt.sat.i.i.i241" (.vec 32 (.int 8)) "llvm.usub.sat.v32i8" [(.vec 32 (.int 8), reg "%103"), (.vec 32 (.int 8), splatOf 32 8 112)],
      .binopVec "%or.i43.i.i242" .or 32 8 (reg "%elt.sat.i.i.i241") (reg "%elt.sat.i40.i.i240"),
      .vecBitcast "%or.i.i.i243" 32 8 4 64 (reg "%or.i43.i.i242"),
      .binopVec "%and.i.i.i244" .and 4 64 (reg "%or.i.i.i243") (splatOf 4 64 (-9187201950435737472)),
      .binopVec "%xor.i.i.i245" .xor 4 64 (reg "%and.i.i.i244") (reg "%and.i35.i.i239"),
      .gep "%add.ptr.i4.i246" (.int 8) (reg "%add.ptr36") (lit 64 31),
      .load "%113" (.vec 4 (.int 64)) (reg "%add.ptr.i4.i246"),
      .gep "%add.ptr3.i5.i247" (.int 8) (reg "%add.ptr36") (lit 64 30),
      .load "%114" (.vec 32 (.int 8)) (reg "%add.ptr3.i5.i247"),
      .gep "%add.ptr5.i6.i248" (.int 8) (reg "%add.ptr36") (lit 64 29),
      .load "%115" (.vec 32 (.int 8)) (reg "%add.ptr5.i6.i248"),
      .vecBitcast "%116" 4 64 32 8 (reg "%113"),
      .binopVec "%117" .and 32 8 (reg "%116") (splatOf 32 8 15),
      .call "%118" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [-25, -93, -125, -125, -117, -53, -53, -53, -53, -53, -53, -53, -53, -37, -53, -53, -25, -93, -125, -125, -117, -53, -53, -53, -53, -53, -53, -53, -53, -37, -53, -53]), (.vec 32 (.int 8), reg "%117")],
      .vecBitcast "%119" 4 64 16 16 (reg "%113"),
      .binopVec "%120" .lshr 16 16 (reg "%119") (splatOf 16 16 4),
      .vecBitcast "%121" 16 16 32 8 (reg "%120"),
      .binopVec "%122" .and 32 8 (reg "%121") (splatOf 32 8 15),
      .call "%123" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [2, 2, 2, 2, 2, 2, 2, 2, -128, -128, -128, -128, 33, 1, 21, 73, 2, 2, 2, 2, 2, 2, 2, 2, -128, -128, -128, -128, 33, 1, 21, 73]), (.vec 32 (.int 8), reg "%122")],
      .binopVec "%and.i3741.i7.i249" .and 32 8 (reg "%123") (reg "%118"),
      .call "%124" (.vec 32 (.int 8)) "llvm.x86.avx2.pshuf.b" [(.vec 32 (.int 8), lanesOf 8 [1, 1, 1, 1, 1, 1, 1, 1, -26, -82, -70, -70, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -26, -82, -70, -70, 1, 1, 1, 1]), (.vec 32 (.int 8), reg "%91")],
      .binopVec "%and.i3542.i8.i250" .and 32 8 (reg "%and.i3741.i7.i249") (reg "%124"),
      .vecBitcast "%and.i35.i9.i251" 32 8 4 64 (reg "%and.i3542.i8.i250"),
      .call "%elt.sat.i40.i10.i252" (.vec 32 (.int 8)) "llvm.usub.sat.v32i8" [(.vec 32 (.int 8), reg "%114"), (.vec 32 (.int 8), splatOf 32 8 96)],
      .call "%elt.sat.i.i11.i253" (.vec 32 (.int 8)) "llvm.usub.sat.v32i8" [(.vec 32 (.int 8), reg "%115"), (.vec 32 (.int 8), splatOf 32 8 112)],
      .binopVec "%or.i43.i12.i254" .or 32 8 (reg "%elt.sat.i.i11.i253") (reg "%elt.sat.i40.i10.i252"),
      .vecBitcast "%or.i.i13.i255" 32 8 4 64 (reg "%or.i43.i12.i254"),
      .binopVec "%and.i.i14.i256" .and 4 64 (reg "%or.i.i13.i255") (splatOf 4 64 (-9187201950435737472)),
      .binopVec "%xor.i.i15.i257" .xor 4 64 (reg "%and.i.i14.i256") (reg "%and.i35.i9.i251"),
      .binopVec "%125" .or 4 64 (reg "%xor.i.i.i245") (reg "%xor.i.i15.i257"),
      .binopVec "%or.i" .or 4 64 (reg "%125") (reg "%u8k.0.lcssa")
    ],
    term := .br "if.end77" }

def if_end77Block : Block :=
  { name := "if.end77",
    instrs := [
      .phi "%u8k.2" (.vec 4 (.int 64)) [("if.then33", reg "%u8k.0.lcssa"), ("if.then74", reg "%or.i")],
      .binop "%and78" .and 64 (reg "%arm") (lit 64 2),
      .icmp "%tobool79.not" .eq 64 (reg "%and78") (lit 64 0)
    ],
    term := .condbr (reg "%tobool79.not") "if.end83.thread" "if.then80" }

def if_then80Block : Block :=
  { name := "if.then80",
    instrs := [
      .shuffleVec "%126" 4 64 (reg "%66") (reg "%67") [0, 1, 2, 3, 4, 5, 6, 7],
      .vecBitcast "%127" 8 64 64 8 (reg "%126"),
      .icmpVec "%128" .ult 64 8 (reg "%127") (splatOf 64 8 32),
      .bitcastMask "%or.i264" 64 (reg "%128"),
      .callVoid "leanllvm_json_escape_list" [(.int 64, reg "%or14.i188"), (.int 64, reg "%or.i264"), (.int 64, reg "%xor.i232"), (.int 64, reg "%shr"), (.ptr, reg "%xp"), (.ptr, reg "%nxp"), (.ptr, reg "%xcarry")]
    ],
    term := .br "if.end83.thread" }

def if_end83_threadBlock : Block :=
  { name := "if.end83.thread",
    instrs := [
      .call "%129" (.int 32) "llvm.x86.avx.ptestz.256" [(.vec 4 (.int 64), reg "%u8k.2"), (.vec 4 (.int 64), reg "%u8k.2")],
      .icmp "%cmp85274" .eq 32 (reg "%129") (lit 32 0)
    ],
    term := .br "if.end100" }

def if_end83Block : Block :=
  { name := "if.end83",
    instrs := [
      .call "%130" (.int 32) "llvm.x86.avx.ptestz.256" [(.vec 4 (.int 64), reg "%u8k.0.lcssa"), (.vec 4 (.int 64), reg "%u8k.0.lcssa")],
      .icmp "%cmp85" .eq 32 (reg "%130") (lit 32 0),
      .icmp "%cmp88.not.not" .eq 64 (reg "%n") (lit 64 0)
    ],
    term := .condbr (reg "%cmp88.not.not") "if.end100" "if.then94" }

def if_then94Block : Block :=
  { name := "if.then94",
    instrs := [
      .gep "%131" (.int 8) (reg "%b") (reg "%n"),
      .gep "%arrayidx96" (.int 8) (reg "%131") (lit 64 (-1)),
      .load "%132" (.int 8) (reg "%arrayidx96"),
      .binop "%133" .and 8 (reg "%132") (lit 8 (-2)),
      .icmp "%cmp.i" .eq 8 (reg "%133") (lit 8 (-64)),
      .icmp "%cmp3.i" .ugt 8 (reg "%132") (lit 8 (-12)),
      .binop "%134" .or 1 (reg "%cmp3.i") (reg "%cmp.i"),
      .binop "%or99279" .or 1 (reg "%cmp85") (reg "%134")
    ],
    term := .br "if.end100" }

def if_end100Block : Block :=
  { name := "if.end100",
    instrs := [
      .phi "%ascii.1278" (.vec 4 (.int 64)) [("if.then94", reg "%ascii.0.lcssa"), ("if.end83", reg "%ascii.0.lcssa"), ("if.end83.thread", reg "%or.i166")],
      .phi "%err.0.in" (.int 1) [("if.then94", reg "%or99279"), ("if.end83", reg "%cmp85"), ("if.end83.thread", reg "%cmp85274")],
      .call "%135" (.int 32) "llvm.x86.avx.ptestz.256" [(.vec 4 (.int 64), reg "%ascii.1278"), (.vec 4 (.int 64), splatOf 4 64 (-9187201950435737472))],
      .icmp "%cmp102" .ne 32 (reg "%135") (lit 32 0),
      .zext "%conv104" 1 64 (reg "%cmp102"),
      .select "%shl105" (.int 64) (reg "%err.0.in") (lit 64 2) (lit 64 0),
      .binop "%or106" .or 64 (reg "%shl105") (reg "%conv104")
    ],
    term := .ret (.int 64) (some (reg "%or106")) }

def s1BlocksFunction : Function :=
  { name := "leanllvm_json_s1_blocks",
    retTy := .int 64,
    params := [("%b", .ptr), ("%n", .int 64), ("%ent", .ptr), ("%xp", .ptr),
               ("%nxp", .ptr), ("%xcarry", .ptr), ("%arm", .int 64)],
    blocks := [entryBlock, for_body_lr_phBlock, for_cond_cleanup_loopexitBlock,
               for_cond_cleanupBlock, for_bodyBlock, if_thenBlock, if_endBlock,
               if_then29Block, if_end31Block, if_then33Block, if_then74Block,
               if_end77Block, if_then80Block, if_end83_threadBlock,
               if_end83Block, if_then94Block, if_end100Block] }

/-! ### The pin -/

-- The committed text parses to the AST above: the pin is that the two are one
-- object, so a change to either that the other does not carry fails here.  The
-- second guard fixes that the module holds exactly this one function.
def namesOf (f : Function) : List (String × Nat) :=
  f.blocks.map fun (b : Block) => (b.name, b.instrs.length)

def firstDiff : List Instr → List Instr → Nat → Option Nat
  | [], [], _ => none
  | a :: as, b :: bs, n => if a = b then firstDiff as bs (n + 1) else some n
  | _, _, n => some n

def blockDiffs (p q : Function) : List (String × Option Nat) :=
  p.blocks.zip q.blocks |>.map fun (a, b) => (a.name, firstDiff a.instrs b.instrs 0)

#guard decide (firstFunction s1BlocksSrc = some s1BlocksFunction)
#guard decide (parsedFunctions s1BlocksSrc = some [s1BlocksFunction])

-- And the interface the AST pins: the symbol, the `i64` return, and the seven
-- parameters in `s1_blocks.h`'s order.
#guard
  match firstFunction s1BlocksSrc with
  | some f =>
      f.name = "leanllvm_json_s1_blocks" ∧
      f.retTy = Ty.int 64 ∧
      f.params = [("%b", .ptr), ("%n", .int 64), ("%ent", .ptr), ("%xp", .ptr),
                  ("%nxp", .ptr), ("%xcarry", .ptr), ("%arm", .int 64)]
  | none => false

/-! ### The census and the frame -/

/-- The call targets the pinned body names, in text order: a `call` that binds a
result and a `call void` are both calls, because the census is the callee and
not the shape the instruction has. -/
def callTargets (f : Function) : List String :=
  (f.blocks.flatMap (·.instrs)).filterMap fun i =>
    match i with
    | .call _ _ callee _ => some callee
    | .callVoid callee _ => some callee
    | _ => none

/-- Every allocation instruction's destination type, in text order. -/
def allocaTypes (f : Function) : List Ty :=
  (f.blocks.flatMap (·.instrs)).filterMap fun i =>
    match i with
    | .alloca _ ty _ => some ty
    | _ => none

/-- The five symbols the pinned body may call: the classifier's two intrinsics,
the ASCII probe's and the UTF-8 stage's lane test, the UTF-8 stage's saturating
subtraction, and the escape list. -/
def censusSymbols : List String :=
  ["leanllvm_json_escape_list", "llvm.usub.sat.v32i8",
   "llvm.x86.avx.ptestz.256", "llvm.x86.avx2.pshuf.b",
   "llvm.x86.pclmulqdq"]

-- The census, enumerated from the pinned AST: the symbol set is exactly those
-- five, and the emitted multiset is the eight `pshuf.b` sites per classifier
-- body plus the twelve the two DFA arms add, the eight `usub.sat` sites the
-- DFA arms use, the two `pclmulqdq` sites, five lane tests (two ASCII probes,
-- three UTF-8 words), and the two escape-list calls.  No other callee can
-- appear.
#guard
  decide (((callTargets s1BlocksFunction).mergeSort (fun a b => a ≤ b)).eraseDups =
    censusSymbols)
#guard
  decide ((callTargets s1BlocksFunction).mergeSort (fun a b => a ≤ b) =
    ["leanllvm_json_escape_list", "leanllvm_json_escape_list",
     "llvm.usub.sat.v32i8", "llvm.usub.sat.v32i8",
     "llvm.usub.sat.v32i8", "llvm.usub.sat.v32i8",
     "llvm.usub.sat.v32i8", "llvm.usub.sat.v32i8",
     "llvm.usub.sat.v32i8", "llvm.usub.sat.v32i8",
     "llvm.x86.avx.ptestz.256", "llvm.x86.avx.ptestz.256",
     "llvm.x86.avx.ptestz.256", "llvm.x86.avx.ptestz.256",
     "llvm.x86.avx.ptestz.256",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.pclmulqdq", "llvm.x86.pclmulqdq"])

-- The pinned body allocates nothing: the classifier carry, the previous block's
-- scalar lane, the UTF-8 accumulator and its gate cell are registers, so the
-- run's allocator base is the caller's and no callee-moved frame appears.
#guard decide (allocaTypes s1BlocksFunction = [])

-- The return is valued: a `Satisfies` record at a value-returning callee needs
-- the completion's shape, and the body's only return carries the two-bit word.
#guard decide (s1BlocksFunction.blocks.all fun b =>
  match b.term with
  | .ret ty vp => ty = Ty.int 64 ∧ vp.isSome
  | _ => true)

end LeanLLVM.Refinement.JsonS1BlocksIR
