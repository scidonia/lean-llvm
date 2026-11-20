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

The registers the emission names are its own.  The body's seven parameters keep
the source's names (`%b`, `%n`, `%ent`, `%xp`, `%nxp`, `%xcarry`, `%arm`), so the
capture applies no rename.

## What the pin establishes

The body is the fast mask pass: the classifier computes the unescaped quotes,
the delimiter word and the *neither* word (neither structural nor whitespace),
plus the in-string word; the composition's scalar word is
`neither & ~quote & ~in_string`; the full-block loop carries the run start and
the three classifier carries in `phi`s, and the final partial block is peeled
into its own body.  The control-byte word is measured only where the escape list
is called.  Three facts the proof and the contract rest on are guarded here:

* the body allocates nothing (`allocaTypes = []`): its scratch is the caller's,
  so no callee-moved allocator appears in a frame the pipeline does not name;
* the call census is the classifier's two intrinsics and the escape list, with
  the intrinsics' multiplicity the two unswitched bodies' (four `pshuf.b` per
  body) and the escape list called from both bodies;
* the ABI is `s1_blocks.h`'s, in its argument order.

The block loop's invariant and the mask identities are the steps module's, not
this one's; here the body is only pinned.
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

/-- `s1f_lo_tab` as the shuffle operand spells it: two copies of the sixteen
nibble entries, one per 128-bit lane. -/
def loTab : List Int :=
  [0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x80, 0x82, 0x14, 0x01, 0xA8, 0x00, 0x00,
   0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x80, 0x82, 0x14, 0x01, 0xA8, 0x00, 0x00]

/-- `s1f_hi_tab` as the shuffle operand spells it. -/
def hiTab : List Int :=
  [0x80, 0x00, 0x41, 0x02, 0x00, 0x30, 0x00, 0x0C,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x80, 0x00, 0x41, 0x02, 0x00, 0x30, 0x00, 0x0C,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- `<32 x i8>`, the lane type of the classification tables. -/
abbrev v32i8 : Ty := .vec 32 (.int 8)

/-- `<64 x i8>`, the lane type of the sixty-four-lane comparisons. -/
abbrev v64i8 : Ty := .vec 64 (.int 8)

/-- The shuffle pair `%0, %1` read as `<8 x i64>`: the low block then the high
block, which is the 64-byte lane order. -/
def shuffle64 (dst : String) : Instr :=
  .shuffleVec dst 4 64 (.reg "%0") (.reg "%1") [0, 1, 2, 3, 4, 5, 6, 7]

/-- One `pshuf.b` table lookup: the table's lane list against the nibble lanes. -/
def pshufb (dst : String) (tab : List Int) (v : Operand) : Instr :=
  .call dst v32i8 "llvm.x86.avx2.pshuf.b"
    [(v32i8, lanesOf 8 tab), (v32i8, v)]

/-- The 64-lane identity shuffle: two thirty-two-lane operands read in order. -/
def join64 (dst : String) (a b : String) : Instr :=
  .shuffleVec dst 32 8 (.reg a) (.reg b) (List.range 64)

/-- The tail body's `<8 x i64>` shuffle, over its own two loads. -/
def tailShuffle (dst : String) : Instr :=
  .shuffleVec dst 4 64 (.reg "%36") (.reg "%37") [0, 1, 2, 3, 4, 5, 6, 7]

/-- The classifier's escape arithmetic, shared by the two bodies: `%or14.i` (the
backslash word) and the three carry words in, the escaped-quote word and the
outgoing run-open and run-parity words out.  The register suffixes differ
between the bodies, so each instruction's destination is given. -/
def s1fEscapedInstrs (suf openReg pparReg bsReg : String) : List Instr :=
  [ .binop ("%and.i.i" ++ suf) .and 64 (reg openReg) (reg pparReg),
    .binop ("%shl.i.i" ++ suf) .shl 64 (reg bsReg) (lit 64 1),
    .binop ("%not.i.i" ++ suf) .xor 64 (reg ("%shl.i.i" ++ suf)) (lit 64 (-1)),
    .binop ("%and1.i.i" ++ suf) .and 64 (reg bsReg) (reg ("%not.i.i" ++ suf)),
    .binop ("%xor.i.i" ++ suf) .xor 64 (reg ("%and.i.i" ++ suf))
      (lit 64 0x5555555555555555),
    .binop ("%and2.i.i" ++ suf) .and 64 (reg ("%and1.i.i" ++ suf))
      (reg ("%xor.i.i" ++ suf)),
    .binop ("%xor3.i.i" ++ suf) .xor 64 (reg ("%and2.i.i" ++ suf))
      (reg ("%and1.i.i" ++ suf)),
    .binop ("%not4.i.i" ++ suf) .xor 64 (reg bsReg) (lit 64 (-1)),
    .binop ("%add.i.i" ++ suf) .add 64 (reg ("%and2.i.i" ++ suf)) (reg bsReg),
    .binop ("%add5.i.i" ++ suf) .add 64 (reg ("%xor3.i.i" ++ suf)) (reg bsReg),
    .binop ("%and6.i.i" ++ suf) .and 64 (reg ("%not4.i.i" ++ suf))
      (lit 64 (-6148914691236517206)),
    .binop ("%and7.i.i" ++ suf) .and 64 (reg ("%and6.i.i" ++ suf))
      (reg ("%add.i.i" ++ suf)),
    .binop ("%and8.i.i" ++ suf) .and 64 (reg ("%not4.i.i" ++ suf))
      (lit 64 0x5555555555555555),
    .binop ("%and9.i.i" ++ suf) .and 64 (reg ("%and8.i.i" ++ suf))
      (reg ("%add5.i.i" ++ suf)),
    .binop ("%and11.i.i" ++ suf) .and 64 (reg ("%and.i.i" ++ suf))
      (reg ("%not4.i.i" ++ suf)),
    .binop ("%or.i.i" ++ suf) .or 64 (reg ("%and7.i.i" ++ suf))
      (reg ("%and11.i.i" ++ suf)),
    .binop ("%or12.i.i" ++ suf) .or 64 (reg ("%or.i.i" ++ suf))
      (reg ("%and9.i.i" ++ suf)) ]

/-! The unit's blocks, in the fixture's order. -/

def entryBlock : Block :=
  { name := "entry",
    instrs := [
      .binop "%shr" .lshr 64 (reg "%n") (lit 64 6),
      .binop "%and" .and 64 (reg "%n") (lit 64 63),
      .icmp "%cmp155.not" .ult 64 (reg "%n") (lit 64 64)],
    term := .condbr (reg "%cmp155.not") "for.cond.cleanup" "for.body.lr.ph" }

def preheaderBlock : Block :=
  { name := "for.body.lr.ph",
    instrs := [
      .binop "%and14" .and 64 (reg "%arm") (lit 64 2),
      .icmp "%tobool.not" .eq 64 (reg "%and14") (lit 64 0)],
    term := .br "for.body" }

def cleanupBlock : Block :=
  { name := "for.cond.cleanup",
    instrs := [
      .phi "%st.sroa.11.0.lcssa" (.int 64)
        [("entry", lit 64 0), ("if.end", reg "%shr.i")],
      .phi "%st.sroa.7.0.lcssa" (.int 64)
        [("entry", lit 64 0), ("if.end", reg "%conv13.i.i")],
      .phi "%st.sroa.0.0.lcssa" (.int 64)
        [("entry", lit 64 0), ("if.end", reg "%shr.i.i")],
      .phi "%prevS.0.lcssa" (.int 64)
        [("entry", lit 64 0), ("if.end", reg "%shr13")],
      .icmp "%tobool16.not" .eq 64 (reg "%and") (lit 64 0)],
    term := .condbr (reg "%tobool16.not") "if.end53" "if.then17" }

/-- The full-block loop body: the classifier, the fast composition, the `ent`
store, and the gate. -/
def loopBodyBlock : Block :=
  { name := "for.body",
    instrs := [
      .phi "%prevS.0160" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end", reg "%shr13")],
      .phi "%i.0159" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end", reg "%inc")],
      .phi "%st.sroa.0.0158" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end", reg "%shr.i.i")],
      .phi "%st.sroa.7.0157" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end", reg "%conv13.i.i")],
      .phi "%st.sroa.11.0156" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end", reg "%shr.i")],
      .binop "%shl" .shl 64 (reg "%i.0159") (lit 64 6),
      .gep "%add.ptr" (.int 8) (reg "%b") (reg "%shl"),
      .load "%0" (.vec 4 (.int 64)) (reg "%add.ptr"),
      .gep "%add.ptr1" (.int 8) (reg "%add.ptr") (lit 64 32),
      .load "%1" (.vec 4 (.int 64)) (reg "%add.ptr1"),
      .vecBitcast "%2" 4 64 32 8 (reg "%0"),
      .vecBitcast "%3" 4 64 32 8 (reg "%1"),
      shuffle64 "%4",
      .vecBitcast "%5" 8 64 64 8 (reg "%4"),
      .icmpVec "%6" .eq 64 8 (reg "%5") (splatOf 64 8 34),
      .bitcastMask "%or.i" 64 (reg "%6"),
      .icmpVec "%cmp.i39.i" .eq 32 8 (reg "%2") (splatOf 32 8 92),
      .bitcastMask "%7" 32 (reg "%cmp.i39.i"),
      .zext "%conv9.i" 32 64 (reg "%7"),
      .icmpVec "%cmp.i.i" .eq 32 8 (reg "%3") (splatOf 32 8 92),
      .bitcastMask "%8" 32 (reg "%cmp.i.i"),
      .zext "%conv12.i" 32 64 (reg "%8"),
      .binop "%shl13.i" .shl 64 (reg "%conv12.i") (lit 64 32),
      .binop "%or14.i" .or 64 (reg "%shl13.i") (reg "%conv9.i")] ++
      s1fEscapedInstrs "" "%st.sroa.0.0158" "%st.sroa.7.0157" "%or14.i" ++ [
      .icmp "%cmp.i45.i" .ult 64 (reg "%add5.i.i") (reg "%or14.i"),
      .zext "%conv13.i.i" 1 64 (reg "%cmp.i45.i"),
      .binop "%shr.i.i" .lshr 64 (reg "%conv12.i") (lit 64 31),
      .binop "%not.i" .xor 64 (reg "%or12.i.i") (lit 64 (-1)),
      .binop "%and.i" .and 64 (reg "%or.i") (reg "%not.i"),
      -- the delimiter and neither words: the same table pair, read twice
      .vecBitcast "%9" 4 64 16 16 (reg "%0"),
      .binopVec "%10" .lshr 16 16 (reg "%9") (splatOf 16 16 4),
      .binopVec "%11" .and 32 8 (reg "%2") (splatOf 32 8 15),
      pshufb "%12" loTab (reg "%11"),
      .vecBitcast "%13" 16 16 32 8 (reg "%10"),
      .binopVec "%14" .and 32 8 (reg "%13") (splatOf 32 8 15),
      pshufb "%15" hiTab (reg "%14"),
      .binopVec "%and.i2326.i.i" .and 32 8 (reg "%15") (reg "%12"),
      .binopVec "%16" .and 32 8 (reg "%and.i2326.i.i") (splatOf 32 8 63),
      .icmpVec "%cmp.i21.i.i" .eq 32 8 (reg "%16") (splatOf 32 8 0),
      .bitcastMask "%17" 32 (reg "%cmp.i21.i.i"),
      .binop "%not.i46.i" .xor 32 (reg "%17") (lit 32 (-1)),
      .vecBitcast "%18" 4 64 16 16 (reg "%1"),
      .binopVec "%19" .lshr 16 16 (reg "%18") (splatOf 16 16 4),
      .binopVec "%20" .and 32 8 (reg "%3") (splatOf 32 8 15),
      pshufb "%21" loTab (reg "%20"),
      .vecBitcast "%22" 16 16 32 8 (reg "%19"),
      .binopVec "%23" .and 32 8 (reg "%22") (splatOf 32 8 15),
      pshufb "%24" hiTab (reg "%23"),
      .binopVec "%and.i2326.i47.i" .and 32 8 (reg "%24") (reg "%21"),
      .binopVec "%25" .and 32 8 (reg "%and.i2326.i47.i") (splatOf 32 8 63),
      .icmpVec "%cmp.i21.i48.i" .eq 32 8 (reg "%25") (splatOf 32 8 0),
      .bitcastMask "%26" 32 (reg "%cmp.i21.i48.i"),
      .binop "%not.i49.i" .xor 32 (reg "%26") (lit 32 (-1)),
      .zext "%conv16.i" 32 64 (reg "%not.i46.i"),
      .zext "%conv17.i" 32 64 (reg "%not.i49.i"),
      .binop "%shl18.i" .shl 64 (reg "%conv17.i") (lit 64 32),
      .binop "%or19.i" .or 64 (reg "%shl18.i") (reg "%conv16.i"),
      join64 "%27" "%and.i2326.i.i" "%and.i2326.i47.i",
      .icmpVec "%28" .eq 64 8 (reg "%27") (splatOf 64 8 0),
      .bitcastMask "%or23.i" 64 (reg "%28"),
      -- the in-string word
      .insertelement "%vecinit1.i.i.i" 2 64 (splatOf 2 64 0) (reg "%and.i") (lit 64 0),
      .call "%29" (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
        [(.vec 2 (.int 64), reg "%vecinit1.i.i.i"),
         (.vec 2 (.int 64), lanesOf 64 [-1, 0]), (.int 8, lit 8 0)],
      .extractelement "%vecext.i.i.i" 2 64 (reg "%29") (lit 64 0),
      .binop "%xor.i" .xor 64 (reg "%vecext.i.i.i") (reg "%st.sroa.11.0156"),
      .binop "%shr.i" .ashr 64 (reg "%xor.i") (lit 64 63),
      -- the composition: S = neither & ~quote & ~in_string, e = quote | (delim & ~im) | starts
      .binop "%not4" .xor 64 (reg "%xor.i") (lit 64 (-1)),
      .binop "%30" .or 64 (reg "%and.i") (reg "%xor.i"),
      .binop "%31" .xor 64 (reg "%30") (lit 64 (-1)),
      .binop "%and5" .and 64 (reg "%or23.i") (reg "%31"),
      .binop "%and7" .and 64 (reg "%or19.i") (reg "%not4"),
      .binop "%shl8" .shl 64 (reg "%and5") (lit 64 1),
      .binop "%or9" .or 64 (reg "%shl8") (reg "%prevS.0160"),
      .binop "%not10" .xor 64 (reg "%or9") (lit 64 (-1)),
      .binop "%and11" .and 64 (reg "%and5") (reg "%not10"),
      .binop "%32" .or 64 (reg "%and7") (reg "%and11"),
      .binop "%or12" .or 64 (reg "%32") (reg "%and.i"),
      .binop "%shr13" .lshr 64 (reg "%and5") (lit 64 63),
      .gep "%arrayidx" (.int 64) (reg "%ent") (reg "%i.0159"),
      .store (.int 64) (reg "%or12") (reg "%arrayidx")],
    term := .condbr (reg "%tobool.not") "if.end" "if.then" }

/-- The gate-on arm of the full-block body: the control word and the escape
list's call. -/
def escapeBlock : Block :=
  { name := "if.then",
    instrs := [
      shuffle64 "%33",
      .vecBitcast "%34" 8 64 64 8 (reg "%33"),
      .icmpVec "%35" .ult 64 8 (reg "%34") (splatOf 64 8 32),
      .bitcastMask "%or.i84" 64 (reg "%35"),
      .callVoid "leanllvm_json_escape_list"
        [(.int 64, reg "%or14.i"), (.int 64, reg "%or.i84"),
         (.int 64, reg "%xor.i"), (.int 64, reg "%i.0159"),
         (.ptr, reg "%xp"), (.ptr, reg "%nxp"), (.ptr, reg "%xcarry")]],
    term := .br "if.end" }

def latchBlock : Block :=
  { name := "if.end",
    instrs := [
      .binop "%inc" .add 64 (reg "%i.0159") (lit 64 1),
      .icmp "%exitcond.not" .eq 64 (reg "%inc") (reg "%shr")],
    term := .condbr (reg "%exitcond.not") "for.cond.cleanup" "for.body" }

/-- The peeled final partial block, with its own escape arm. -/
def tailBlock : Block :=
  { name := "if.then17",
    instrs := [
      .binop "%shl19" .and 64 (reg "%n") (lit 64 (-64)),
      .gep "%add.ptr20" (.int 8) (reg "%b") (reg "%shl19"),
      .load "%36" (.vec 4 (.int 64)) (reg "%add.ptr20"),
      .gep "%add.ptr24" (.int 8) (reg "%add.ptr20") (lit 64 32),
      .load "%37" (.vec 4 (.int 64)) (reg "%add.ptr24"),
      .vecBitcast "%38" 4 64 32 8 (reg "%36"),
      .vecBitcast "%39" 4 64 32 8 (reg "%37"),
      tailShuffle "%40",
      .vecBitcast "%41" 8 64 64 8 (reg "%40"),
      .icmpVec "%42" .eq 64 8 (reg "%41") (splatOf 64 8 34),
      .bitcastMask "%or.i90" 64 (reg "%42"),
      tailShuffle "%43",
      .vecBitcast "%44" 8 64 64 8 (reg "%43"),
      .icmpVec "%45" .eq 64 8 (reg "%44") (splatOf 64 8 92),
      .bitcastMask "%or14.i96" 64 (reg "%45"),
      .binop "%and.i.i98" .and 64 (reg "%st.sroa.0.0.lcssa") (reg "%st.sroa.7.0.lcssa"),
      .binop "%shl.i.i99" .shl 64 (reg "%or14.i96") (lit 64 1),
      .binop "%not.i.i100" .xor 64 (reg "%shl.i.i99") (lit 64 (-1)),
      .binop "%and1.i.i101" .and 64 (reg "%or14.i96") (reg "%not.i.i100"),
      .binop "%xor.i.i102" .xor 64 (reg "%and.i.i98") (lit 64 0x5555555555555555),
      .binop "%and2.i.i103" .and 64 (reg "%and1.i.i101") (reg "%xor.i.i102"),
      .binop "%xor3.i.i104" .xor 64 (reg "%and2.i.i103") (reg "%and1.i.i101"),
      .binop "%not4.i.i105" .xor 64 (reg "%or14.i96") (lit 64 (-1)),
      .binop "%add.i.i106" .add 64 (reg "%and2.i.i103") (reg "%or14.i96"),
      .binop "%add5.i.i107" .add 64 (reg "%xor3.i.i104") (reg "%or14.i96"),
      .binop "%and6.i.i108" .and 64 (reg "%not4.i.i105") (lit 64 (-6148914691236517206)),
      .binop "%and7.i.i109" .and 64 (reg "%and6.i.i108") (reg "%add.i.i106"),
      .binop "%and8.i.i110" .and 64 (reg "%not4.i.i105") (lit 64 0x5555555555555555),
      .binop "%and9.i.i111" .and 64 (reg "%and8.i.i110") (reg "%add5.i.i107"),
      .binop "%and11.i.i113" .and 64 (reg "%and.i.i98") (reg "%not4.i.i105"),
      .binop "%or.i.i114" .or 64 (reg "%and7.i.i109") (reg "%and11.i.i113"),
      .binop "%or12.i.i115" .or 64 (reg "%or.i.i114") (reg "%and9.i.i111"),
      .binop "%not.i119" .xor 64 (reg "%or12.i.i115") (lit 64 (-1)),
      .binop "%and.i120" .and 64 (reg "%or.i90") (reg "%not.i119"),
      .vecBitcast "%46" 4 64 16 16 (reg "%36"),
      .binopVec "%47" .lshr 16 16 (reg "%46") (splatOf 16 16 4),
      .binopVec "%48" .and 32 8 (reg "%38") (splatOf 32 8 15),
      pshufb "%49" loTab (reg "%48"),
      .vecBitcast "%50" 16 16 32 8 (reg "%47"),
      .binopVec "%51" .and 32 8 (reg "%50") (splatOf 32 8 15),
      pshufb "%52" hiTab (reg "%51"),
      .binopVec "%and.i2326.i.i121" .and 32 8 (reg "%52") (reg "%49"),
      .binopVec "%53" .and 32 8 (reg "%and.i2326.i.i121") (splatOf 32 8 63),
      .icmpVec "%cmp.i21.i.i122" .eq 32 8 (reg "%53") (splatOf 32 8 0),
      .bitcastMask "%54" 32 (reg "%cmp.i21.i.i122"),
      .binop "%not.i46.i123" .xor 32 (reg "%54") (lit 32 (-1)),
      .vecBitcast "%55" 4 64 16 16 (reg "%37"),
      .binopVec "%56" .lshr 16 16 (reg "%55") (splatOf 16 16 4),
      .binopVec "%57" .and 32 8 (reg "%39") (splatOf 32 8 15),
      pshufb "%58" loTab (reg "%57"),
      .vecBitcast "%59" 16 16 32 8 (reg "%56"),
      .binopVec "%60" .and 32 8 (reg "%59") (splatOf 32 8 15),
      pshufb "%61" hiTab (reg "%60"),
      .binopVec "%and.i2326.i47.i125" .and 32 8 (reg "%61") (reg "%58"),
      .binopVec "%62" .and 32 8 (reg "%and.i2326.i47.i125") (splatOf 32 8 63),
      .icmpVec "%cmp.i21.i48.i126" .eq 32 8 (reg "%62") (splatOf 32 8 0),
      .bitcastMask "%63" 32 (reg "%cmp.i21.i48.i126"),
      .binop "%not.i49.i127" .xor 32 (reg "%63") (lit 32 (-1)),
      .zext "%conv16.i129" 32 64 (reg "%not.i46.i123"),
      .zext "%conv17.i130" 32 64 (reg "%not.i49.i127"),
      .binop "%shl18.i131" .shl 64 (reg "%conv17.i130") (lit 64 32),
      .binop "%or19.i132" .or 64 (reg "%shl18.i131") (reg "%conv16.i129"),
      join64 "%64" "%and.i2326.i.i121" "%and.i2326.i47.i125",
      .icmpVec "%65" .eq 64 8 (reg "%64") (splatOf 64 8 0),
      .bitcastMask "%or23.i136" 64 (reg "%65"),
      .insertelement "%vecinit1.i.i.i137" 2 64 (splatOf 2 64 0)
        (reg "%and.i120") (lit 64 0),
      .call "%66" (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
        [(.vec 2 (.int 64), reg "%vecinit1.i.i.i137"),
         (.vec 2 (.int 64), lanesOf 64 [-1, 0]), (.int 8, lit 8 0)],
      .extractelement "%vecext.i.i.i138" 2 64 (reg "%66") (lit 64 0),
      .binop "%xor.i140" .xor 64 (reg "%vecext.i.i.i138")
        (reg "%st.sroa.11.0.lcssa"),
      .binop "%not34" .xor 64 (reg "%xor.i140") (lit 64 (-1)),
      .binop "%67" .or 64 (reg "%and.i120") (reg "%xor.i140"),
      .binop "%68" .xor 64 (reg "%67") (lit 64 (-1)),
      .binop "%and35" .and 64 (reg "%or23.i136") (reg "%68"),
      .binop "%and38" .and 64 (reg "%or19.i132") (reg "%not34"),
      .binop "%shl40" .shl 64 (reg "%and35") (lit 64 1),
      .binop "%or41" .or 64 (reg "%shl40") (reg "%prevS.0.lcssa"),
      .binop "%not42" .xor 64 (reg "%or41") (lit 64 (-1)),
      .binop "%and43" .and 64 (reg "%and35") (reg "%not42"),
      .binop "%69" .or 64 (reg "%and38") (reg "%and43"),
      .binop "%or44" .or 64 (reg "%69") (reg "%and.i120"),
      .binop "%notmask" .shl 64 (lit 64 (-1)) (reg "%and"),
      .binop "%sub" .xor 64 (reg "%notmask") (lit 64 (-1)),
      .binop "%and46" .and 64 (reg "%or44") (reg "%sub"),
      .gep "%arrayidx47" (.int 64) (reg "%ent") (reg "%shr"),
      .store (.int 64) (reg "%and46") (reg "%arrayidx47"),
      .binop "%and48" .and 64 (reg "%arm") (lit 64 2),
      .icmp "%tobool49.not" .eq 64 (reg "%and48") (lit 64 0)],
    term := .condbr (reg "%tobool49.not") "if.end53" "if.then50" }

def tailEscapeBlock : Block :=
  { name := "if.then50",
    instrs := [
      tailShuffle "%70",
      .vecBitcast "%71" 8 64 64 8 (reg "%70"),
      .icmpVec "%72" .ult 64 8 (reg "%71") (splatOf 64 8 32),
      .bitcastMask "%or.i147" 64 (reg "%72"),
      .callVoid "leanllvm_json_escape_list"
        [(.int 64, reg "%or14.i96"), (.int 64, reg "%or.i147"),
         (.int 64, reg "%xor.i140"), (.int 64, reg "%shr"),
         (.ptr, reg "%xp"), (.ptr, reg "%nxp"), (.ptr, reg "%xcarry")]],
    term := .br "if.end53" }

def doneBlock : Block :=
  { name := "if.end53", instrs := [], term := .ret .void none }

/-- `probes/install/ir/json-s1-blocks.candidate.ll`, as an AST. -/
def s1BlocksFunction : Function :=
  { name := "leanllvm_json_s1_blocks",
    retTy := .void,
    params := [("%b", .ptr), ("%n", .int 64), ("%ent", .ptr), ("%xp", .ptr),
               ("%nxp", .ptr), ("%xcarry", .ptr), ("%arm", .int 64)],
    blocks := [entryBlock, preheaderBlock, cleanupBlock, loopBodyBlock,
               escapeBlock, latchBlock, tailBlock, tailEscapeBlock, doneBlock] }

/-! ### The pin -/

-- The committed text parses to the AST above: the pin is that the two are one
-- object, so a change to either that the other does not carry fails here.  The
-- second guard fixes that the module holds exactly this one function.
#guard decide (firstFunction s1BlocksSrc = some s1BlocksFunction)
#guard decide (parsedFunctions s1BlocksSrc = some [s1BlocksFunction])

-- And the interface the AST pins: the symbol, the `void` return, and the seven
-- parameters in `s1_blocks.h`'s order.
#guard
  match firstFunction s1BlocksSrc with
  | some f =>
      f.name = "leanllvm_json_s1_blocks" ∧
      f.retTy = Ty.void ∧
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

/-- The three symbols the pinned body may call: the classifier's two intrinsics
and the escape list. -/
def censusSymbols : List String :=
  ["leanllvm_json_escape_list", "llvm.x86.avx2.pshuf.b", "llvm.x86.pclmulqdq"]

-- The census, enumerated from the pinned AST: the symbol set is exactly those
-- three, and the emitted multiset is the eight `pshuf.b` sites (four per body),
-- the two `pclmulqdq` sites and the two escape-list calls.  No other callee can
-- appear.
#guard
  decide (((callTargets s1BlocksFunction).mergeSort (fun a b => a ≤ b)).eraseDups =
    censusSymbols)
#guard
  decide ((callTargets s1BlocksFunction).mergeSort (fun a b => a ≤ b) =
    ["leanllvm_json_escape_list",
     "leanllvm_json_escape_list",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.pclmulqdq", "llvm.x86.pclmulqdq"])

-- The pinned body allocates nothing: the classifier carry and the previous
-- block's scalar lane are registers, so the run's allocator base is the
-- caller's and no callee-moved frame appears.
#guard decide (allocaTypes s1BlocksFunction = [])

end LeanLLVM.Refinement.JsonS1BlocksIR
