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

The registers the emission names are its own (`%0`, `%add.ptr`, `%cmp.i54.i`,
…).  The body's seven parameters keep the source's names (`%b`, `%n`, `%ent`,
`%xp`, `%nxp`, `%xcarry`, `%arm`), so the capture applies no rename.

## What the pin establishes

The unit's body is the classifier's text inlined into one loop: the six mask
words and both carries stay in registers, the entry word is composed and stored
at `ent[i]`, and the escape list is appended when `arm & 2`.  Three facts the
proof and the contract rest on are guarded here:

* the body allocates nothing (`allocaTypes = []`): its scratch is the caller's,
  so no callee-moved allocator appears in a frame the pipeline does not name;
* the call census is the classifier's two intrinsics and the escape list, with
  the intrinsics' multiplicity the unswitched loop's;
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
      .binop "%add" .add 64 (reg "%n") (lit 64 63),
      .binop "%shr" .lshr 64 (reg "%add") (lit 64 6),
      .icmp "%cmp34.not" .ult 64 (reg "%add") (lit 64 64)],
    term := .condbr (reg "%cmp34.not") "for.cond.cleanup" "for.body.lr.ph" }

def preheaderBlock : Block :=
  { name := "for.body.lr.ph",
    instrs := [
      .binop "%and18" .and 64 (reg "%arm") (lit 64 2),
      .icmp "%tobool.not" .eq 64 (reg "%and18") (lit 64 0)],
    term := .br "for.body" }

def exitBlock : Block :=
  { name := "for.cond.cleanup",
    instrs := [],
    term := .ret .void none }

/-- The loop body: the block's two loads, the six mask words, the entry word's
composition with the carried run start and the tail clamp, and the `ent` store.
The five `phi`s are the loop's carried values: the previous block's top scalar
lane, the block index, and the classifier's three carry words. -/
def bodyBlock : Block :=
  { name := "for.body",
    instrs := [
      .phi "%prevS.039" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end20", reg "%shr12")],
      .phi "%i.038" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end20", reg "%inc")],
      .phi "%st.sroa.0.037" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end20", reg "%shr.i.i")],
      .phi "%st.sroa.5.036" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end20", reg "%conv13.i.i")],
      .phi "%st.sroa.7.035" (.int 64) [("for.body.lr.ph", lit 64 0), ("if.end20", reg "%shr.i")],
      -- The block base and the two unaligned 32-byte loads.
      .binop "%shl" .shl 64 (reg "%i.038") (lit 64 6),
      .gep "%add.ptr" (.int 8) (reg "%b") (reg "%shl"),
      .load "%0" (.vec 4 (.int 64)) (reg "%add.ptr"),
      .gep "%add.ptr1" (.int 8) (reg "%add.ptr") (lit 64 32),
      .load "%1" (.vec 4 (.int 64)) (reg "%add.ptr1"),
      .vecBitcast "%2" 4 64 32 8 (reg "%0"),
      .vecBitcast "%3" 4 64 32 8 (reg "%1"),
      -- The quote word, the backslash words and the control word.
      shuffle64 "%4",
      .vecBitcast "%5" 8 64 64 8 (reg "%4"),
      .icmpVec "%6" .eq 64 8 (reg "%5") (splatOf 64 8 34),
      .bitcastMask "%or.i" 64 (reg "%6"),
      .icmpVec "%cmp.i54.i" .eq 32 8 (reg "%2") (splatOf 32 8 92),
      .bitcastMask "%7" 32 (reg "%cmp.i54.i"),
      .zext "%conv9.i" 32 64 (reg "%7"),
      .icmpVec "%cmp.i52.i" .eq 32 8 (reg "%3") (splatOf 32 8 92),
      .bitcastMask "%8" 32 (reg "%cmp.i52.i"),
      .zext "%conv12.i" 32 64 (reg "%8"),
      .binop "%shl13.i" .shl 64 (reg "%conv12.i") (lit 64 32),
      .binop "%or14.i" .or 64 (reg "%shl13.i") (reg "%conv9.i"),
      -- The structural and whitespace words of the low half: two-nibble tables.
      .vecBitcast "%9" 4 64 16 16 (reg "%0"),
      .binopVec "%10" .lshr 16 16 (reg "%9") (splatOf 16 16 4),
      .binopVec "%11" .and 32 8 (reg "%2") (splatOf 32 8 15),
      pshufb "%12" loTab (reg "%11"),
      .vecBitcast "%13" 16 16 32 8 (reg "%10"),
      .binopVec "%14" .and 32 8 (reg "%13") (splatOf 32 8 15),
      pshufb "%15" hiTab (reg "%14"),
      .binopVec "%and.i2831.i.i.i" .and 32 8 (reg "%15") (reg "%12"),
      .binopVec "%16" .and 32 8 (reg "%and.i2831.i.i.i") (splatOf 32 8 63),
      .icmpVec "%cmp.i25.i.i.i" .eq 32 8 (reg "%16") (splatOf 32 8 0),
      .bitcastMask "%17" 32 (reg "%cmp.i25.i.i.i"),
      .binop "%not.i.i.i" .xor 32 (reg "%17") (lit 32 (-1)),
      .icmpVec "%cmp.i.i.i.i" .ult 32 8 (reg "%and.i2831.i.i.i") (splatOf 32 8 64),
      .bitcastMask "%18" 32 (reg "%cmp.i.i.i.i"),
      .binop "%not18.i.i.i" .xor 32 (reg "%18") (lit 32 (-1)),
      -- The same pair of words for the high half.
      .vecBitcast "%19" 4 64 16 16 (reg "%1"),
      .binopVec "%20" .lshr 16 16 (reg "%19") (splatOf 16 16 4),
      .binopVec "%21" .and 32 8 (reg "%3") (splatOf 32 8 15),
      pshufb "%22" loTab (reg "%21"),
      .vecBitcast "%23" 16 16 32 8 (reg "%20"),
      .binopVec "%24" .and 32 8 (reg "%23") (splatOf 32 8 15),
      pshufb "%25" hiTab (reg "%24"),
      .binopVec "%and.i2831.i6.i.i" .and 32 8 (reg "%25") (reg "%22"),
      .binopVec "%26" .and 32 8 (reg "%and.i2831.i6.i.i") (splatOf 32 8 63),
      .icmpVec "%cmp.i25.i7.i.i" .eq 32 8 (reg "%26") (splatOf 32 8 0),
      .bitcastMask "%27" 32 (reg "%cmp.i25.i7.i.i"),
      .binop "%not.i8.i.i" .xor 32 (reg "%27") (lit 32 (-1)),
      .icmpVec "%cmp.i.i9.i.i" .ult 32 8 (reg "%and.i2831.i6.i.i") (splatOf 32 8 64),
      .bitcastMask "%28" 32 (reg "%cmp.i.i9.i.i"),
      .binop "%not18.i10.i.i" .xor 32 (reg "%28") (lit 32 (-1)),
      -- The two halves joined into the 64-lane words.
      .zext "%conv.i.i" 32 64 (reg "%not18.i.i.i"),
      .zext "%conv1.i.i" 32 64 (reg "%not18.i10.i.i"),
      .binop "%shl.i.i" .shl 64 (reg "%conv1.i.i") (lit 64 32),
      .binop "%or.i.i" .or 64 (reg "%shl.i.i") (reg "%conv.i.i"),
      .zext "%conv2.i.i" 32 64 (reg "%not.i.i.i"),
      .zext "%conv3.i.i" 32 64 (reg "%not.i8.i.i"),
      .binop "%shl4.i.i" .shl 64 (reg "%conv3.i.i") (lit 64 32),
      .binop "%or5.i.i" .or 64 (reg "%shl4.i.i") (reg "%conv2.i.i"),
      -- `s1f_escaped`: the two carry-propagating sums, the boundary lane and
      -- the outgoing run parity, from the backslash word and the carry words.
      .binop "%and.i.i" .and 64 (reg "%st.sroa.0.037") (reg "%st.sroa.5.036"),
      .binop "%shl.i61.i" .shl 64 (reg "%or14.i") (lit 64 1),
      .binop "%not.i.i" .xor 64 (reg "%shl.i61.i") (lit 64 (-1)),
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
      .binop "%or.i62.i" .or 64 (reg "%and7.i.i") (reg "%and11.i.i"),
      .binop "%or12.i.i" .or 64 (reg "%or.i62.i") (reg "%and9.i.i"),
      .icmp "%cmp.i63.i" .ult 64 (reg "%add5.i.i") (reg "%or14.i"),
      .zext "%conv13.i.i" 1 64 (reg "%cmp.i63.i"),
      .binop "%shr.i.i" .lshr 64 (reg "%conv12.i") (lit 64 31),
      -- `s1f_prefix_xor`: the clmul with an all-ones operand, lane 0 only.
      .binop "%not.i" .xor 64 (reg "%or12.i.i") (lit 64 (-1)),
      .binop "%and.i" .and 64 (reg "%or.i") (reg "%not.i"),
      .insertelement "%vecinit1.i.i.i" 2 64 (splatOf 2 64 0) (reg "%and.i") (lit 64 0),
      .call "%29" (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
        [(.vec 2 (.int 64), reg "%vecinit1.i.i.i"),
         (.vec 2 (.int 64), lanesOf 64 [-1, 0]), (.int 8, lit 8 0)],
      .extractelement "%vecext.i.i.i" 2 64 (reg "%29") (lit 64 0),
      .binop "%xor.i" .xor 64 (reg "%vecext.i.i.i") (reg "%st.sroa.7.035"),
      .binop "%shr.i" .ashr 64 (reg "%xor.i") (lit 64 63),
      -- The entry word: the quote, the structural outside a string, the run
      -- start carried from the previous block, then the tail clamp.
      .binop "%30" .or 64 (reg "%or.i.i") (reg "%xor.i"),
      .binop "%31" .or 64 (reg "%30") (reg "%or5.i.i"),
      .binop "%or4" .or 64 (reg "%31") (reg "%and.i"),
      .binop "%not" .xor 64 (reg "%or4") (lit 64 (-1)),
      .binop "%not5" .xor 64 (reg "%xor.i") (lit 64 (-1)),
      .binop "%and" .and 64 (reg "%or5.i.i") (reg "%not5"),
      .binop "%shl7" .shl 64 (reg "%not") (lit 64 1),
      .binop "%or8" .or 64 (reg "%shl7") (reg "%prevS.039"),
      .binop "%not9" .xor 64 (reg "%or8") (lit 64 (-1)),
      .binop "%and10" .and 64 (reg "%not9") (reg "%not"),
      .binop "%32" .or 64 (reg "%and") (reg "%and10"),
      .binop "%or11" .or 64 (reg "%32") (reg "%and.i"),
      .binop "%shr12" .lshr 64 (reg "%not") (lit 64 63),
      .binop "%sub" .sub 64 (reg "%n") (reg "%shl"),
      .icmp "%cmp14" .ult 64 (reg "%sub") (lit 64 64),
      .binop "%notmask" .shl 64 (lit 64 (-1)) (reg "%sub"),
      .binop "%sub16" .xor 64 (reg "%notmask") (lit 64 (-1)),
      .select "%and17" (.int 64) (reg "%cmp14") (reg "%sub16") (lit 64 (-1)),
      .binop "%e.0" .and 64 (reg "%or11") (reg "%and17"),
      .gep "%arrayidx" (.int 64) (reg "%ent") (reg "%i.038"),
      .store (.int 64) (reg "%e.0") (reg "%arrayidx")],
    term := .condbr (reg "%tobool.not") "if.end20" "if.then19" }

/-- The gate-on arm: the raw control word and the escape-list call, whose three
mask words go by value. -/
def escapeBlock : Block :=
  { name := "if.then19",
    instrs := [
      shuffle64 "%33",
      .vecBitcast "%34" 8 64 64 8 (reg "%33"),
      .icmpVec "%35" .ult 64 8 (reg "%34") (splatOf 64 8 32),
      .bitcastMask "%or25.i" 64 (reg "%35"),
      .callVoid "leanllvm_json_escape_list"
        [(.int 64, reg "%or14.i"), (.int 64, reg "%or25.i"),
         (.int 64, reg "%xor.i"), (.int 64, reg "%i.038"),
         (.ptr, reg "%xp"), (.ptr, reg "%nxp"), (.ptr, reg "%xcarry")]],
    term := .br "if.end20" }

/-- The loop latch: the index increment and the block-count test. -/
def latchBlock : Block :=
  { name := "if.end20",
    instrs := [
      .binop "%inc" .add 64 (reg "%i.038") (lit 64 1),
      .icmp "%exitcond.not" .eq 64 (reg "%inc") (reg "%shr")],
    term := .condbr (reg "%exitcond.not") "for.cond.cleanup" "for.body" }

/-- `probes/install/ir/json-s1-blocks.candidate.ll`, as an AST. -/
def s1BlocksFunction : Function :=
  { name := "leanllvm_json_s1_blocks",
    retTy := .void,
    params := [("%b", .ptr), ("%n", .int 64), ("%ent", .ptr), ("%xp", .ptr),
               ("%nxp", .ptr), ("%xcarry", .ptr), ("%arm", .int 64)],
    blocks := [entryBlock, preheaderBlock, exitBlock, bodyBlock, escapeBlock,
               latchBlock] }

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
-- three, and the emitted multiset is the four `pshuf.b` sites, the one
-- `pclmulqdq`, and the one escape-list call.  No other callee can appear.
#guard
  decide (((callTargets s1BlocksFunction).mergeSort (fun a b => a ≤ b)).eraseDups =
    censusSymbols)
#guard
  decide ((callTargets s1BlocksFunction).mergeSort (fun a b => a ≤ b) =
    ["leanllvm_json_escape_list",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.pclmulqdq"])

-- The pinned body allocates nothing: the classifier carry and the previous
-- block's scalar lane are registers, so the run's allocator base is the
-- caller's and no callee-moved frame appears.
#guard decide (allocaTypes s1BlocksFunction = [])

end LeanLLVM.Refinement.JsonS1BlocksIR
