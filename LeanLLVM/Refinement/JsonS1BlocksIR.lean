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

The unit's body is the classifier's text inlined into one loop: the mask words
and both carries stay in registers, the entry word is composed and stored at
`ent[i]`, and the escape list is appended when `arm & 2`.  The return word is
the ASCII probe: each block's two loaded lanes are ORed into `<4 x i64>
%ascii`, and the done block tests that accumulator's high bits once with
`llvm.x86.avx.ptestz.256`.  Four facts the proof and the contract rest on are
guarded here:

* the body allocates nothing (`allocaTypes = []`): its scratch is the caller's,
  so no callee-moved allocator appears in a frame the pipeline does not name;
* the call census is the classifier's two intrinsics, the ASCII probe's lane
  test, and the escape list, with the intrinsics' multiplicity the loop and the
  peeled block emit;
* the ABI is `s1_blocks.h`'s, in its argument order, and it returns `i64`;
* the return's shape is valued (`.ret (.int 64) (some …)`), which is what a
  `Satisfies` record with a value-returning callee requires.

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

/-- `<4 x i64>`, the ASCII accumulator's type. -/
abbrev v4i64 : Ty := .vec 4 (.int 64)

/-- The shuffle pair `%0, %1` read as `<8 x i64>`: the low block then the high
block, which is the 64-byte lane order. -/
def shuffle64 (dst : String) : Instr :=
  .shuffleVec dst 4 64 (.reg "%0") (.reg "%1") [0, 1, 2, 3, 4, 5, 6, 7]

/-- One `pshuf.b` table lookup: the table's lane list against the nibble lanes. -/
def pshufb (dst : String) (tab : List Int) (v : Operand) : Instr :=
  .call dst v32i8 "llvm.x86.avx2.pshuf.b"
    [(v32i8, lanesOf 8 tab), (v32i8, v)]

/-! The unit's blocks, in the fixture's order. -/

def entryBlock : Block :=
  { name := "entry",
    instrs := [
      .binop "%shr" .lshr 64 (reg "%n") (lit 64 6),
      .binop "%and" .and 64 (reg "%n") (lit 64 63),
      .icmp "%cmp174.not" .ult 64 (reg "%n") (lit 64 64)],
    term := .condbr (reg "%cmp174.not") "for.cond.cleanup" "for.body.lr.ph" }

def preheaderBlock : Block :=
  { name := "for.body.lr.ph",
    instrs := [
      .binop "%and17" .and 64 (reg "%arm") (lit 64 2),
      .icmp "%tobool.not" .eq 64 (reg "%and17") (lit 64 0)],
    term := .br "for.body" }

/-- The loop exit's carried values, the document's ASCII accumulator, and the
peeled tail's test. -/
def cleanupBlock : Block :=
  { name := "for.cond.cleanup",
    instrs := [
      .phi "%st.sroa.11.0.lcssa" (.int 64)
        [("entry", lit 64 0), ("if.end", reg "%shr.i")],
      .phi "%st.sroa.7.0.lcssa" (.int 64)
        [("entry", lit 64 0), ("if.end", reg "%conv13.i.i")],
      .phi "%st.sroa.0.0.lcssa" (.int 64)
        [("entry", lit 64 0), ("if.end", reg "%shr.i.i")],
      .phi "%ascii.0.lcssa" v4i64
        [("entry", .imm (.splat 4 64 (BitVec.ofInt 64 0))), ("if.end", reg "%or.i97")],
      .phi "%prevS.0.lcssa" (.int 64)
        [("entry", lit 64 0), ("if.end", reg "%shr16")],
      .icmp "%tobool19.not" .eq 64 (reg "%and") (lit 64 0)],
    term := .condbr (reg "%tobool19.not") "if.end58" "if.then20" }

/-- The loop body: the block's two loads, the ASCII probe's two ORs, the mask
words, the entry word's composition with the carried run start and the tail
clamp, and the `ent` store.  The six `phi`s are the loop's carried values: the
previous block's top scalar lane, the ASCII accumulator, the block index, and the
classifier's three carry words. -/
def bodyBlock : Block :=
  { name := "for.body",
    instrs := [
      .phi "%prevS.0180" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end", reg "%shr16")],
      .phi "%ascii.0179" v4i64
        [("for.body.lr.ph", .imm (.splat 4 64 (BitVec.ofInt 64 0))),
         ("if.end", reg "%or.i97")],
      .phi "%i.0178" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end", reg "%inc")],
      .phi "%st.sroa.0.0177" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end", reg "%shr.i.i")],
      .phi "%st.sroa.7.0176" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end", reg "%conv13.i.i")],
      .phi "%st.sroa.11.0175" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end", reg "%shr.i")],
      -- The block base and the two unaligned 32-byte loads.
      .binop "%shl" .shl 64 (reg "%i.0178") (lit 64 6),
      .gep "%add.ptr" (.int 8) (reg "%b") (reg "%shl"),
      .load "%0" (.vec 4 (.int 64)) (reg "%add.ptr"),
      .gep "%add.ptr2" (.int 8) (reg "%add.ptr") (lit 64 32),
      .load "%1" (.vec 4 (.int 64)) (reg "%add.ptr2"),
      -- The ASCII probe: the two loaded lanes ORed into the accumulator.
      .binopVec "%or.i98" .or 4 64 (reg "%0") (reg "%ascii.0179"),
      .binopVec "%or.i97" .or 4 64 (reg "%or.i98") (reg "%1"),
      .vecBitcast "%2" 4 64 32 8 (reg "%0"),
      .vecBitcast "%3" 4 64 32 8 (reg "%1"),
      -- The quote word, the backslash words and the control word.
      shuffle64 "%4",
      .vecBitcast "%5" 8 64 64 8 (reg "%4"),
      .icmpVec "%6" .eq 64 8 (reg "%5") (splatOf 64 8 34),
      .bitcastMask "%or.i99" 64 (reg "%6"),
      .icmpVec "%cmp.i39.i" .eq 32 8 (reg "%2") (splatOf 32 8 92),
      .bitcastMask "%7" 32 (reg "%cmp.i39.i"),
      .zext "%conv9.i" 32 64 (reg "%7"),
      .icmpVec "%cmp.i.i" .eq 32 8 (reg "%3") (splatOf 32 8 92),
      .bitcastMask "%8" 32 (reg "%cmp.i.i"),
      .zext "%conv12.i" 32 64 (reg "%8"),
      .binop "%shl13.i" .shl 64 (reg "%conv12.i") (lit 64 32),
      .binop "%or14.i" .or 64 (reg "%shl13.i") (reg "%conv9.i"),
      -- `s1f_escaped`: the two carry-propagating sums, the boundary lane and
      -- the outgoing run parity, from the backslash word and the carry words.
      .binop "%and.i.i" .and 64 (reg "%st.sroa.0.0177") (reg "%st.sroa.7.0176"),
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
      -- The unescaped quote word.
      .binop "%not.i" .xor 64 (reg "%or12.i.i") (lit 64 (-1)),
      .binop "%and.i" .and 64 (reg "%or.i99") (reg "%not.i"),
      -- The structural and *neither* words of the low half.
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
      -- The same pair of words for the high half.
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
      -- The two halves joined into the delimiter and *neither* words.
      .zext "%conv16.i" 32 64 (reg "%not.i46.i"),
      .zext "%conv17.i" 32 64 (reg "%not.i49.i"),
      .binop "%shl18.i" .shl 64 (reg "%conv17.i") (lit 64 32),
      .binop "%or19.i" .or 64 (reg "%shl18.i") (reg "%conv16.i"),
      .shuffleVec "%27" 32 8 (reg "%and.i2326.i.i") (reg "%and.i2326.i47.i")
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
         16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
         32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
         48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63],
      .icmpVec "%28" .eq 64 8 (reg "%27") (splatOf 64 8 0),
      .bitcastMask "%or23.i" 64 (reg "%28"),
      -- `s1f_prefix_xor`: the clmul with an all-ones operand, lane 0 only.
      .insertelement "%vecinit1.i.i.i" 2 64 (.imm (.splat 2 64 (BitVec.ofNat 64 0)))
        (reg "%and.i") (lit 64 0),
      .call "%29" (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
        [(.vec 2 (.int 64), reg "%vecinit1.i.i.i"),
         (.vec 2 (.int 64), lanesOf 64 [-1, 0]), (.int 8, lit 8 0)],
      .extractelement "%vecext.i.i.i" 2 64 (reg "%29") (lit 64 0),
      .binop "%xor.i" .xor 64 (reg "%vecext.i.i.i") (reg "%st.sroa.11.0175"),
      .binop "%shr.i" .ashr 64 (reg "%xor.i") (lit 64 63),
      -- The entry word: the quote, the structural outside a string, the run
      -- start carried from the previous block, then the tail clamp.
      .binop "%not7" .xor 64 (reg "%xor.i") (lit 64 (-1)),
      .binop "%30" .or 64 (reg "%and.i") (reg "%xor.i"),
      .binop "%31" .xor 64 (reg "%30") (lit 64 (-1)),
      .binop "%and8" .and 64 (reg "%or23.i") (reg "%31"),
      .binop "%and10" .and 64 (reg "%or19.i") (reg "%not7"),
      .binop "%shl11" .shl 64 (reg "%and8") (lit 64 1),
      .binop "%or12" .or 64 (reg "%shl11") (reg "%prevS.0180"),
      .binop "%not13" .xor 64 (reg "%or12") (lit 64 (-1)),
      .binop "%and14" .and 64 (reg "%and8") (reg "%not13"),
      .binop "%32" .or 64 (reg "%and10") (reg "%and14"),
      .binop "%or15" .or 64 (reg "%32") (reg "%and.i"),
      .binop "%shr16" .lshr 64 (reg "%and8") (lit 64 63),
      .gep "%arrayidx" (.int 64) (reg "%ent") (reg "%i.0178"),
      .store (.int 64) (reg "%or15") (reg "%arrayidx")],
    term := .condbr (reg "%tobool.not") "if.end" "if.then" }

/-- The gate-on arm: the raw control word and the escape-list call, whose three
mask words go by value. -/
def escapeBlock : Block :=
  { name := "if.then",
    instrs := [
      shuffle64 "%33",
      .vecBitcast "%34" 8 64 64 8 (reg "%33"),
      .icmpVec "%35" .ult 64 8 (reg "%34") (splatOf 64 8 32),
      .bitcastMask "%or.i103" 64 (reg "%35"),
      .callVoid "leanllvm_json_escape_list"
        [(.int 64, reg "%or14.i"), (.int 64, reg "%or.i103"),
         (.int 64, reg "%xor.i"), (.int 64, reg "%i.0178"),
         (.ptr, reg "%xp"), (.ptr, reg "%nxp"), (.ptr, reg "%xcarry")]],
    term := .br "if.end" }

/-- The loop latch: the index increment and the block-count test. -/
def latchBlock : Block :=
  { name := "if.end",
    instrs := [
      .binop "%inc" .add 64 (reg "%i.0178") (lit 64 1),
      .icmp "%exitcond.not" .eq 64 (reg "%inc") (reg "%shr")],
    term := .condbr (reg "%exitcond.not") "for.cond.cleanup" "for.body" }

/-- The peeled partial block: the same classifier at the document's last bytes,
with the clamp applied to the word and the ASCII probe folded into the
accumulator the loop left. -/
def tailBlock : Block :=
  { name := "if.then20",
    instrs := [
      .binop "%shl22" .and 64 (reg "%n") (lit 64 (-64)),
      .gep "%add.ptr23" (.int 8) (reg "%b") (reg "%shl22"),
      .load "%36" (.vec 4 (.int 64)) (reg "%add.ptr23"),
      .gep "%add.ptr27" (.int 8) (reg "%add.ptr23") (lit 64 32),
      .load "%37" (.vec 4 (.int 64)) (reg "%add.ptr27"),
      .binopVec "%or.i96" .or 4 64 (reg "%36") (reg "%ascii.0.lcssa"),
      .binopVec "%or.i" .or 4 64 (reg "%or.i96") (reg "%37"),
      .vecBitcast "%38" 4 64 32 8 (reg "%36"),
      .vecBitcast "%39" 4 64 32 8 (reg "%37"),
      .shuffleVec "%40" 4 64 (.reg "%36") (.reg "%37") [0, 1, 2, 3, 4, 5, 6, 7],
      .vecBitcast "%41" 8 64 64 8 (reg "%40"),
      .icmpVec "%42" .eq 64 8 (reg "%41") (splatOf 64 8 34),
      .bitcastMask "%or.i109" 64 (reg "%42"),
      .shuffleVec "%43" 4 64 (.reg "%36") (.reg "%37") [0, 1, 2, 3, 4, 5, 6, 7],
      .vecBitcast "%44" 8 64 64 8 (reg "%43"),
      .icmpVec "%45" .eq 64 8 (reg "%44") (splatOf 64 8 92),
      .bitcastMask "%or14.i115" 64 (reg "%45"),
      .binop "%and.i.i117" .and 64 (reg "%st.sroa.0.0.lcssa") (reg "%st.sroa.7.0.lcssa"),
      .binop "%shl.i.i118" .shl 64 (reg "%or14.i115") (lit 64 1),
      .binop "%not.i.i119" .xor 64 (reg "%shl.i.i118") (lit 64 (-1)),
      .binop "%and1.i.i120" .and 64 (reg "%or14.i115") (reg "%not.i.i119"),
      .binop "%xor.i.i121" .xor 64 (reg "%and.i.i117") (lit 64 6148914691236517205),
      .binop "%and2.i.i122" .and 64 (reg "%and1.i.i120") (reg "%xor.i.i121"),
      .binop "%xor3.i.i123" .xor 64 (reg "%and2.i.i122") (reg "%and1.i.i120"),
      .binop "%not4.i.i124" .xor 64 (reg "%or14.i115") (lit 64 (-1)),
      .binop "%add.i.i125" .add 64 (reg "%and2.i.i122") (reg "%or14.i115"),
      .binop "%add5.i.i126" .add 64 (reg "%xor3.i.i123") (reg "%or14.i115"),
      .binop "%and6.i.i127" .and 64 (reg "%not4.i.i124") (lit 64 (-6148914691236517206)),
      .binop "%and7.i.i128" .and 64 (reg "%and6.i.i127") (reg "%add.i.i125"),
      .binop "%and8.i.i129" .and 64 (reg "%not4.i.i124") (lit 64 6148914691236517205),
      .binop "%and9.i.i130" .and 64 (reg "%and8.i.i129") (reg "%add5.i.i126"),
      .binop "%and11.i.i132" .and 64 (reg "%and.i.i117") (reg "%not4.i.i124"),
      .binop "%or.i.i133" .or 64 (reg "%and7.i.i128") (reg "%and11.i.i132"),
      .binop "%or12.i.i134" .or 64 (reg "%or.i.i133") (reg "%and9.i.i130"),
      .binop "%not.i138" .xor 64 (reg "%or12.i.i134") (lit 64 (-1)),
      .binop "%and.i139" .and 64 (reg "%or.i109") (reg "%not.i138"),
      .vecBitcast "%46" 4 64 16 16 (reg "%36"),
      .binopVec "%47" .lshr 16 16 (reg "%46") (splatOf 16 16 4),
      .binopVec "%48" .and 32 8 (reg "%38") (splatOf 32 8 15),
      pshufb "%49" loTab (reg "%48"),
      .vecBitcast "%50" 16 16 32 8 (reg "%47"),
      .binopVec "%51" .and 32 8 (reg "%50") (splatOf 32 8 15),
      pshufb "%52" hiTab (reg "%51"),
      .binopVec "%and.i2326.i.i140" .and 32 8 (reg "%52") (reg "%49"),
      .binopVec "%53" .and 32 8 (reg "%and.i2326.i.i140") (splatOf 32 8 63),
      .icmpVec "%cmp.i21.i.i141" .eq 32 8 (reg "%53") (splatOf 32 8 0),
      .bitcastMask "%54" 32 (reg "%cmp.i21.i.i141"),
      .binop "%not.i46.i142" .xor 32 (reg "%54") (lit 32 (-1)),
      .vecBitcast "%55" 4 64 16 16 (reg "%37"),
      .binopVec "%56" .lshr 16 16 (reg "%55") (splatOf 16 16 4),
      .binopVec "%57" .and 32 8 (reg "%39") (splatOf 32 8 15),
      pshufb "%58" loTab (reg "%57"),
      .vecBitcast "%59" 16 16 32 8 (reg "%56"),
      .binopVec "%60" .and 32 8 (reg "%59") (splatOf 32 8 15),
      pshufb "%61" hiTab (reg "%60"),
      .binopVec "%and.i2326.i47.i144" .and 32 8 (reg "%61") (reg "%58"),
      .binopVec "%62" .and 32 8 (reg "%and.i2326.i47.i144") (splatOf 32 8 63),
      .icmpVec "%cmp.i21.i48.i145" .eq 32 8 (reg "%62") (splatOf 32 8 0),
      .bitcastMask "%63" 32 (reg "%cmp.i21.i48.i145"),
      .binop "%not.i49.i146" .xor 32 (reg "%63") (lit 32 (-1)),
      .zext "%conv16.i148" 32 64 (reg "%not.i46.i142"),
      .zext "%conv17.i149" 32 64 (reg "%not.i49.i146"),
      .binop "%shl18.i150" .shl 64 (reg "%conv17.i149") (lit 64 32),
      .binop "%or19.i151" .or 64 (reg "%shl18.i150") (reg "%conv16.i148"),
      .shuffleVec "%64" 32 8 (reg "%and.i2326.i.i140") (reg "%and.i2326.i47.i144")
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
         16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
         32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
         48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63],
      .icmpVec "%65" .eq 64 8 (reg "%64") (splatOf 64 8 0),
      .bitcastMask "%or23.i155" 64 (reg "%65"),
      .insertelement "%vecinit1.i.i.i156" 2 64 (.imm (.splat 2 64 (BitVec.ofNat 64 0)))
        (reg "%and.i139") (lit 64 0),
      .call "%66" (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
        [(.vec 2 (.int 64), reg "%vecinit1.i.i.i156"),
         (.vec 2 (.int 64), lanesOf 64 [-1, 0]), (.int 8, lit 8 0)],
      .extractelement "%vecext.i.i.i157" 2 64 (reg "%66") (lit 64 0),
      .binop "%xor.i159" .xor 64 (reg "%vecext.i.i.i157") (reg "%st.sroa.11.0.lcssa"),
      .binop "%not39" .xor 64 (reg "%xor.i159") (lit 64 (-1)),
      .binop "%67" .or 64 (reg "%and.i139") (reg "%xor.i159"),
      .binop "%68" .xor 64 (reg "%67") (lit 64 (-1)),
      .binop "%and40" .and 64 (reg "%or23.i155") (reg "%68"),
      .binop "%and43" .and 64 (reg "%or19.i151") (reg "%not39"),
      .binop "%shl45" .shl 64 (reg "%and40") (lit 64 1),
      .binop "%or46" .or 64 (reg "%shl45") (reg "%prevS.0.lcssa"),
      .binop "%not47" .xor 64 (reg "%or46") (lit 64 (-1)),
      .binop "%and48" .and 64 (reg "%and40") (reg "%not47"),
      .binop "%69" .or 64 (reg "%and43") (reg "%and48"),
      .binop "%or49" .or 64 (reg "%69") (reg "%and.i139"),
      .binop "%notmask" .shl 64 (lit 64 (-1)) (reg "%and"),
      .binop "%sub" .xor 64 (reg "%notmask") (lit 64 (-1)),
      .binop "%and51" .and 64 (reg "%or49") (reg "%sub"),
      .gep "%arrayidx52" (.int 64) (reg "%ent") (reg "%shr"),
      .store (.int 64) (reg "%and51") (reg "%arrayidx52"),
      .binop "%and53" .and 64 (reg "%arm") (lit 64 2),
      .icmp "%tobool54.not" .eq 64 (reg "%and53") (lit 64 0)],
    term := .condbr (reg "%tobool54.not") "if.end58" "if.then55" }

/-- The peeled block's gate-on arm. -/
def tailEscapeBlock : Block :=
  { name := "if.then55",
    instrs := [
      .shuffleVec "%70" 4 64 (.reg "%36") (.reg "%37") [0, 1, 2, 3, 4, 5, 6, 7],
      .vecBitcast "%71" 8 64 64 8 (reg "%70"),
      .icmpVec "%72" .ult 64 8 (reg "%71") (splatOf 64 8 32),
      .bitcastMask "%or.i166" 64 (reg "%72"),
      .callVoid "leanllvm_json_escape_list"
        [(.int 64, reg "%or14.i115"), (.int 64, reg "%or.i166"),
         (.int 64, reg "%xor.i159"), (.int 64, reg "%shr"),
         (.ptr, reg "%xp"), (.ptr, reg "%nxp"), (.ptr, reg "%xcarry")]],
    term := .br "if.end58" }

/-- The done block: the ASCII accumulator's high bits, tested once, and the
return word. -/
def doneBlock : Block :=
  { name := "if.end58",
    instrs := [
      .phi "%ascii.1" v4i64
        [("for.cond.cleanup", reg "%ascii.0.lcssa"), ("if.then55", reg "%or.i"),
         ("if.then20", reg "%or.i")],
      .call "%73" (.int 32) "llvm.x86.avx.ptestz.256"
        [(v4i64, reg "%ascii.1"),
         (v4i64, .imm (.splat 4 64 (BitVec.ofInt 64 (-9187201950435737472))))],
      .icmp "%cmp61" .ne 32 (reg "%73") (lit 32 0),
      .zext "%conv62" 1 64 (reg "%cmp61")],
    term := .ret (.int 64) (some (reg "%conv62")) }

/-- `probes/install/ir/json-s1-blocks.candidate.ll`, as an AST. -/
def s1BlocksFunction : Function :=
  { name := "leanllvm_json_s1_blocks",
    retTy := .int 64,
    params := [("%b", .ptr), ("%n", .int 64), ("%ent", .ptr), ("%xp", .ptr),
               ("%nxp", .ptr), ("%xcarry", .ptr), ("%arm", .int 64)],
    blocks := [entryBlock, preheaderBlock, cleanupBlock, bodyBlock, escapeBlock,
               latchBlock, tailBlock, tailEscapeBlock, doneBlock] }

/-! ### The pin -/

-- The committed text parses to the AST above: the pin is that the two are one
-- object, so a change to either that the other does not carry fails here.  The
-- second guard fixes that the module holds exactly this one function.
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

/-- The four symbols the pinned body may call: the classifier's two intrinsics,
the ASCII probe's lane test, and the escape list. -/
def censusSymbols : List String :=
  ["leanllvm_json_escape_list", "llvm.x86.avx.ptestz.256",
   "llvm.x86.avx2.pshuf.b", "llvm.x86.pclmulqdq"]

-- The census, enumerated from the pinned AST: the symbol set is exactly those
-- four, and the emitted multiset is the eight `pshuf.b` sites (four per body),
-- the two `pclmulqdq` sites, the one lane test and the two escape-list calls.
-- No other callee can appear.
#guard
  decide (((callTargets s1BlocksFunction).mergeSort (fun a b => a ≤ b)).eraseDups =
    censusSymbols)
#guard
  decide ((callTargets s1BlocksFunction).mergeSort (fun a b => a ≤ b) =
    ["leanllvm_json_escape_list", "leanllvm_json_escape_list",
     "llvm.x86.avx.ptestz.256",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.pclmulqdq", "llvm.x86.pclmulqdq"])

-- The pinned body allocates nothing: the classifier carry and the previous
-- block's scalar lane are registers, so the run's allocator base is the
-- caller's and no callee-moved frame appears.
#guard decide (allocaTypes s1BlocksFunction = [])

-- The return is valued: a `Satisfies` record at a value-returning callee needs
-- the completion's shape, and the body's only return carries the probe word.
#guard decide (s1BlocksFunction.blocks.all fun b =>
  match b.term with
  | .ret ty vp => ty = Ty.int 64 ∧ vp.isSome
  | _ => true)

end LeanLLVM.Refinement.JsonS1BlocksIR
