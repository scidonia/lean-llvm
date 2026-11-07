/-
An emitted-IR bridge for the stage-1 classification mask unit.

`probes/install/ir/json-s1-masks.candidate.ll` is the emission of
`kernel/json/s1_block.c` at the measured compiler line, normalised;
`probes/install/ir/capture-s1-masks.sh` records the invocation and derives, by
diffing its own clang block against what it emits, every item the normalisation
took out (`json-s1-masks.strip.tsv`, by class), every place it rewrote text
(`json-s1-masks.rewrites.tsv`, with the reason), and the fixture's own
construct inventory (`json-s1-masks.inventory`, opcodes and call targets).

This module parses the file and pins the parsed AST against the literal below.
The pin is a `#guard` rather than a `rfl` proposition because the parser runs on
`String` primitives, which the kernel does not reduce, so a proposition about a
`parseModule` result cannot be closed by reflexivity.  What the pin buys is that
the hand-written AST and the committed text are the same object: a change to
either that the other does not carry fails elaboration, and no theorem below can
be stated about a body the text does not contain.

The registers the emission names are its own (`%0`, `%add.ptr`, `%cmp.i54.i`,
…): the capture compiles with `-fno-discard-value-names`, which names values and
labels the entry block and changes no instruction, and renames the three
parameters to the ABI's `%p`, `%c`, `%o`.

## What is proved here, and what the steps module proves

`s1Calls` is the body's call environment — the five intrinsic targets resolved to
`pshufbLanes`, `clmul` at immediate 0, and `BitLanes`' `pext`/`pdep`/`ctlz` — so
a run of the body has a meaning: under `noCalls` the body's first call is `ub`
and every statement about it is vacuous.

This module is the **specification side**: the fixture and its pin, the call
environment, the block's lane vocabulary (`Ctx`, `loWord`/`hiWord`,
`loLanes`/`hiLanes`/`blockLanes`, `unpackLanes_lo/hi`, `packLanes_join`), the
generic `evalInstr_*` lemmas, `lookupName_bind_ne`/`lookupName_bind_self`, and the
lane-to-word bridge (`lanesToNat_lt`, `lanesToNat_ofFn_pack32`, `or_ofNat_shift`).
The two usability corollaries `s1_masks_decompose` and `s1_masks_candidate` are
here, pinned in `LeanLLVMTest/Vellum.lean`.

The body's **execution** lives in `LeanLLVM.Vellum.JsonS1MasksSteps`: each
instruction's step at an opaque environment, and the composition of all 115.
This module's older `State.bind`-chain steps were deleted once that composition
carried the body, so there is one shape in the tree and it is the measured one.

`JsonS1MasksSteps` holds the whole proof: the six per-mask identities, in the
order `s1_masks_refines` consumes them — `s1_quote_eq`, `s1_delimiter_eq`,
`s1_inString`, `s1_whitespace_eq`, `s1_backslash_eq`, `s1_control_eq` (`s1_quote`
without the suffix is the *step* lemma for the raw quote word, not the identity) —
the headline `s1_masks_refines` over the whole body, and its totality companion
`s1_masks_undefined_of_no_read`, which reaches `ub` from a block that is absent
across the whole 64 bytes the body reads.  The mask identities reuse
`kernelQuote64` and `ppn64` (`QuoteDerive`), `specInString64_eq_clmul` (`Pclmul`),
`delimiterMask_eq_maskOfListWith` and `backslashMask_eq_maskOfListWith`
(`JsonScanSpec`), and `pack32_eq_bitcast` with the `mask64_*` join lemmas.
-/
import LeanLLVM.Parser
import LeanLLVM.Memory
import LeanLLVM.Vellum.Pclmul


namespace LeanLLVM.Vellum.JsonS1MasksIR

open LeanLLVM
open LeanLLVM.JSON (Block32 IsQuoteB IsBackslashB IsSpaceB IsStructuralB IsStructOrSpaceB
  maskOfList maskOfListWith)
open LeanLLVM.Vellum.BitLanes (pext pdep ctlz)
open LeanLLVM.Vellum.Pclmul (clmul)
open LeanLLVM.Vellum.JsonScanSpec

/-! ### The fixture -/

/-- The mask unit as emitted and committed. -/
def s1MasksSrc : String :=
  include_str "../../probes/install/ir/json-s1-masks.candidate.ll"

/-- Parse a fixture and take its single function. -/
def firstFunction (src : String) : Option Function :=
  match parseModule src with
  | .ok m => m.functions.head?
  | .error _ => none

/-! ### The pinned AST

The body, instruction by instruction, in the order the fixture holds it.  The
helpers below only spell an operand the way `parseConst`/`parseOperand` read
one; they decide nothing. -/

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

/-- The unit's instructions, in the fixture's order. -/
def s1MasksInstrs : List Instr := [
  -- The block: two 32-byte unaligned loads, the widening, and the quote word.
  .load "%0" (.vec 4 (.int 64)) (.reg "%p"),
  .gep "%add.ptr" (.int 8) (.reg "%p") (lit 64 32),
  .load "%1" (.vec 4 (.int 64)) (.reg "%add.ptr"),
  .vecBitcast "%2" 4 64 32 8 (.reg "%0"),
  .vecBitcast "%3" 4 64 32 8 (.reg "%1"),
  shuffle64 "%4",
  .vecBitcast "%5" 8 64 64 8 (.reg "%4"),
  .icmpVec "%6" .eq 64 8 (.reg "%5") (splatOf 64 8 34),
  .bitcastMask "%or.i" 64 (.reg "%6"),
  -- The backslash word, both halves.
  .icmpVec "%cmp.i54.i" .eq 32 8 (.reg "%2") (splatOf 32 8 92),
  .bitcastMask "%7" 32 (.reg "%cmp.i54.i"),
  .zext "%conv9.i" 32 64 (.reg "%7"),
  .icmpVec "%cmp.i52.i" .eq 32 8 (.reg "%3") (splatOf 32 8 92),
  .bitcastMask "%8" 32 (.reg "%cmp.i52.i"),
  .zext "%conv12.i" 32 64 (.reg "%8"),
  .binop "%shl13.i" .shl 64 (.reg "%conv12.i") (lit 64 32),
  .binop "%or14.i" .or 64 (.reg "%shl13.i") (.reg "%conv9.i"),
  -- The control word: `icmp ult` against 0x20 over the whole block.
  shuffle64 "%9",
  .vecBitcast "%10" 8 64 64 8 (.reg "%9"),
  .icmpVec "%11" .ult 64 8 (.reg "%10") (splatOf 64 8 32),
  -- The structural and whitespace words of the low half: two-nibble tables.
  .vecBitcast "%12" 4 64 16 16 (.reg "%0"),
  .binopVec "%13" .lshr 16 16 (.reg "%12") (splatOf 16 16 4),
  .binopVec "%14" .and 32 8 (.reg "%2") (splatOf 32 8 15),
  pshufb "%15" loTab (.reg "%14"),
  .vecBitcast "%16" 16 16 32 8 (.reg "%13"),
  .binopVec "%17" .and 32 8 (.reg "%16") (splatOf 32 8 15),
  pshufb "%18" hiTab (.reg "%17"),
  .binopVec "%and.i2831.i.i.i" .and 32 8 (.reg "%18") (.reg "%15"),
  .binopVec "%19" .and 32 8 (.reg "%and.i2831.i.i.i") (splatOf 32 8 63),
  .icmpVec "%cmp.i25.i.i.i" .eq 32 8 (.reg "%19")
    (splatOf 32 8 0),
  .bitcastMask "%20" 32 (.reg "%cmp.i25.i.i.i"),
  .binop "%not.i.i.i" .xor 32 (.reg "%20") (lit 32 (-1)),
  .icmpVec "%cmp.i.i.i.i" .ult 32 8 (.reg "%and.i2831.i.i.i")
    (splatOf 32 8 64),
  .bitcastMask "%21" 32 (.reg "%cmp.i.i.i.i"),
  .binop "%not18.i.i.i" .xor 32 (.reg "%21") (lit 32 (-1)),
  -- The same pair of words for the high half.
  .vecBitcast "%22" 4 64 16 16 (.reg "%1"),
  .binopVec "%23" .lshr 16 16 (.reg "%22") (splatOf 16 16 4),
  .binopVec "%24" .and 32 8 (.reg "%3") (splatOf 32 8 15),
  pshufb "%25" loTab (.reg "%24"),
  .vecBitcast "%26" 16 16 32 8 (.reg "%23"),
  .binopVec "%27" .and 32 8 (.reg "%26") (splatOf 32 8 15),
  pshufb "%28" hiTab (.reg "%27"),
  .binopVec "%and.i2831.i6.i.i" .and 32 8 (.reg "%28") (.reg "%25"),
  .binopVec "%29" .and 32 8 (.reg "%and.i2831.i6.i.i") (splatOf 32 8 63),
  .icmpVec "%cmp.i25.i7.i.i" .eq 32 8 (.reg "%29")
    (splatOf 32 8 0),
  .bitcastMask "%30" 32 (.reg "%cmp.i25.i7.i.i"),
  .binop "%not.i8.i.i" .xor 32 (.reg "%30") (lit 32 (-1)),
  .icmpVec "%cmp.i.i9.i.i" .ult 32 8 (.reg "%and.i2831.i6.i.i")
    (splatOf 32 8 64),
  .bitcastMask "%31" 32 (.reg "%cmp.i.i9.i.i"),
  .binop "%not18.i10.i.i" .xor 32 (.reg "%31") (lit 32 (-1)),
  -- The two halves joined into the 64-lane words.
  .zext "%conv.i.i" 32 64 (.reg "%not18.i.i.i"),
  .zext "%conv1.i.i" 32 64 (.reg "%not18.i10.i.i"),
  .binop "%shl.i.i" .shl 64 (.reg "%conv1.i.i") (lit 64 32),
  .binop "%or.i.i" .or 64 (.reg "%shl.i.i") (.reg "%conv.i.i"),
  .zext "%conv2.i.i" 32 64 (.reg "%not.i.i.i"),
  .zext "%conv3.i.i" 32 64 (.reg "%not.i8.i.i"),
  .binop "%shl4.i.i" .shl 64 (.reg "%conv3.i.i") (lit 64 32),
  .binop "%or5.i.i" .or 64 (.reg "%shl4.i.i") (.reg "%conv2.i.i"),
  -- `s1f_escaped`: the run starts and lasts, the two `pext`s, the `pdep` and the
  -- outgoing run parity.
  .gep "%esc_ppar.i" (.int 8) (.reg "%c") (lit 64 8),
  .binop "%shl.i61.i" .shl 64 (.reg "%or14.i") (lit 64 1),
  .load "%32" (.int 64) (.reg "%c"),
  .binop "%or.i62.i" .or 64 (.reg "%shl.i61.i") (.reg "%32"),
  .binop "%not.i.i" .xor 64 (.reg "%or.i62.i") (lit 64 (-1)),
  .binop "%and.i.i" .and 64 (.reg "%or14.i") (.reg "%not.i.i"),
  .binop "%and1.i.i" .and 64 (.reg "%conv9.i") (lit 64 1),
  .binop "%and2.i.i" .and 64 (.reg "%32") (.reg "%and1.i.i"),
  .binop "%or3.i.i" .or 64 (.reg "%and.i.i") (.reg "%and2.i.i"),
  .binop "%shr.i.i" .lshr 64 (.reg "%or14.i") (lit 64 1),
  .binop "%not4.i.i" .xor 64 (.reg "%shr.i.i") (lit 64 (-1)),
  .binop "%and5.i.i" .and 64 (.reg "%or14.i") (.reg "%not4.i.i"),
  .binop "%shl6.i.i" .shl 64 (.reg "%and5.i.i") (lit 64 1),
  .load "%33" (.int 64) (.reg "%esc_ppar.i"),
  .binop "%and7.i.i" .and 64 (.reg "%33") (.reg "%32"),
  .binop "%xor.i.i" .xor 64 (.reg "%and7.i.i") (lit 64 0x5555555555555555),
  .call "%34" (.int 64) "llvm.x86.bmi.pext.64"
    [(.int 64, .reg "%xor.i.i"), (.int 64, .reg "%or3.i.i")],
  .call "%35" (.int 64) "llvm.x86.bmi.pext.64"
    [(.int 64, lit 64 0x5555555555555555), (.int 64, .reg "%and5.i.i")],
  .binop "%36" .xor 64 (.reg "%34") (.reg "%35"),
  .binop "%not10.i.i" .xor 64 (.reg "%36") (lit 64 (-1)),
  .call "%37" (.int 64) "llvm.x86.bmi.pdep.64"
    [(.int 64, .reg "%not10.i.i"), (.int 64, .reg "%shl6.i.i")],
  .icmp "%cmp.i63.i" .ne 64 (.reg "%or14.i") (lit 64 (-1)),
  .icmp "%tobool.not.i.i" .eq 64 (.reg "%32") (lit 64 0),
  .select "%or.cond.i.i" (.int 1) (.reg "%cmp.i63.i") (lit 1 1)
    (.reg "%tobool.not.i.i"),
  .select "%cond24.i.i" (.int 64) (.reg "%or.cond.i.i") (lit 64 0)
    (.reg "%33"),
  .binop "%not17.i.i" .xor 64 (.reg "%or14.i") (lit 64 (-1)),
  .call "%38" (.int 64) "llvm.ctlz.i64"
    [(.int 64, .reg "%not17.i.i"), (.int 1, lit 1 0)],
  .binop "%shr16.i.i" .lshr 64 (.reg "%conv12.i") (lit 64 31),
  .binop "%not12.i.i" .xor 64 (.reg "%and1.i.i") (lit 64 (-1)),
  .binop "%39" .and 64 (.reg "%32") (.reg "%not12.i.i"),
  .binop "%and14.i.i" .and 64 (.reg "%39") (.reg "%33"),
  .binop "%or15.i.i" .or 64 (.reg "%37") (.reg "%and14.i.i"),
  .binop "%xor25.i.i" .xor 64 (.reg "%cond24.i.i") (.reg "%38"),
  .binop "%and26.i.i" .and 64 (.reg "%xor25.i.i") (.reg "%shr16.i.i"),
  -- The carry, in place.
  .store (.int 64) (.reg "%and26.i.i") (.reg "%esc_ppar.i"),
  .store (.int 64) (.reg "%shr16.i.i") (.reg "%c"),
  -- `s1f_prefix_xor`: the clmul with an all-ones operand, lane 0 only.
  .binop "%not.i" .xor 64 (.reg "%or15.i.i") (lit 64 (-1)),
  .binop "%and.i" .and 64 (.reg "%or.i") (.reg "%not.i"),
  .insertelement "%vecinit1.i.i.i" 2 64 (.imm (.splat 2 64 (BitVec.ofNat 64 0)))
    (.reg "%and.i") (lit 64 0),
  .call "%40" (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
    [(.vec 2 (.int 64), .reg "%vecinit1.i.i.i"),
     (.vec 2 (.int 64), lanesOf 64 [-1, 0]), (.int 8, lit 8 0)],
  .extractelement "%vecext.i.i.i" 2 64 (.reg "%40") (lit 64 0),
  .gep "%im_carry.i" (.int 8) (.reg "%c") (lit 64 16),
  .load "%41" (.int 64) (.reg "%im_carry.i"),
  .binop "%xor.i" .xor 64 (.reg "%vecext.i.i.i") (.reg "%41"),
  .binop "%shr.i" .ashr 64 (.reg "%xor.i") (lit 64 63),
  .store (.int 64) (.reg "%shr.i") (.reg "%im_carry.i"),
  -- The six word stores at the output slot.
  .store (.int 64) (.reg "%and.i") (.reg "%o"),
  .gep "%delim" (.int 8) (.reg "%o") (lit 64 8),
  .store (.int 64) (.reg "%or5.i.i") (.reg "%delim"),
  .gep "%in_string" (.int 8) (.reg "%o") (lit 64 16),
  .store (.int 64) (.reg "%xor.i") (.reg "%in_string"),
  .gep "%ws2" (.int 8) (.reg "%o") (lit 64 24),
  .store (.int 64) (.reg "%or.i.i") (.reg "%ws2"),
  .gep "%backslash" (.int 8) (.reg "%o") (lit 64 32),
  .store (.int 64) (.reg "%or14.i") (.reg "%backslash"),
  .gep "%ctl3" (.int 8) (.reg "%o") (lit 64 40),
  .store (.vec 64 (.int 1)) (.reg "%11") (.reg "%ctl3")]

/-- The unit's single block: the body above, returning nothing. -/
def s1MasksBody : Block :=
  { name := "entry", instrs := s1MasksInstrs, term := .ret .void none }

/-- `probes/install/ir/json-s1-masks.candidate.ll`, as an AST. -/
def s1MasksFunction : Function :=
  { name := "leanllvm_json_s1_masks",
    retTy := .void,
    params := [("%p", .ptr), ("%c", .ptr), ("%o", .ptr)],
    blocks := [s1MasksBody] }

/-! ### The pin -/

-- The committed text parses to the AST above: the pin is that the two are one
-- object, so a change to either that the other does not carry fails here.
#guard decide (firstFunction s1MasksSrc = some s1MasksFunction)

-- And the interface the AST pins: the symbol, the `void` return, and the three
-- pointer parameters in the ABI's order.
#guard
  match firstFunction s1MasksSrc with
  | some f =>
      f.name = "leanllvm_json_s1_masks" ∧
      f.retTy = Ty.void ∧
      f.params = [("%p", Ty.ptr), ("%c", Ty.ptr), ("%o", Ty.ptr)]
  | none => false

/-! ### The call environment

The body calls five intrinsic targets, and `evalInstr`'s `.call` case consults
`Calls`; `noCalls` answers `none`, which `step` reads as `ub`, so a statement
over `noCalls` says nothing about this body.  The environment below resolves
exactly those five, each to the definition the fragment already has — the same
shape `envForScanWindow` uses for the scanner's body — and nothing else: an
unresolved call stays `ub`.

The operand shapes are the parser's (`checkIntrinsicShape`): `pshuf.b` at two
`<32 x i8>` operands, `pclmulqdq` at a `<2 x i64>` pair and immediate 0, `pext`
and `pdep` at two `i64`, and `ctlz.i64` with the flag `i1 false`.  A call whose
symbol or operands are any other shape is refused here rather than approximated.

`pclmulqdq` at immediate 0 multiplies lane 0 of each operand and writes the
product into lane 0 of the result, leaving lane 1 zero — the immediate selects
the lanes, so the second lane is not a second product.  `ctlz` at the zero word
is the width, which is the flag's `false` case. -/

/-- The unit's reference call environment. -/
def s1Calls : Calls :=
  fun callee args mem next =>
    match callee, args with
    | "llvm.x86.avx2.pshuf.b", [.vec 32 8 table, .vec 32 8 control] =>
        some { ret := .vec 32 8 (pshufbLanes table control), mem := mem, next := next }
    | "llvm.x86.pclmulqdq", [.vec 2 64 a, .vec 2 64 b, .int 8 imm] =>
        match a, b with
        | [a0, a1], [b0, b1] =>
            if imm.toNat = 0 then
              some { ret := .vec 2 64 [clmul a0 b0, (0 : BitVec 64)],
                     mem := mem, next := next }
            else none
        | _, _ => none
    | "llvm.x86.bmi.pext.64", [.int 64 a, .int 64 m] =>
        some { ret := .int 64 (pext a m), mem := mem, next := next }
    | "llvm.x86.bmi.pdep.64", [.int 64 a, .int 64 m] =>
        some { ret := .int 64 (pdep a m), mem := mem, next := next }
    | "llvm.ctlz.i64", [.int 64 x, .int 1 flag] =>
        if flag.toNat = 0 then
          some { ret := .int 64 (BitVec.ofNat 64 (ctlz x)), mem := mem, next := next }
        else none
    | _, _ => none

/-- The table lookup the body calls. -/
theorem s1Calls_pshufb (table control : List (BitVec 8)) (mem : Mem) (next : Nat) :
    s1Calls "llvm.x86.avx2.pshuf.b" [.vec 32 8 table, .vec 32 8 control] mem next =
      some { ret := .vec 32 8 (pshufbLanes table control), mem := mem, next := next } :=
  rfl

/-- The carry-less product at immediate 0: lane 0 is the product of the two lane 0s
and lane 1 is zero. -/
theorem s1Calls_pclmulqdq (a0 a1 b0 b1 : BitVec 64) (mem : Mem) (next : Nat) :
    s1Calls "llvm.x86.pclmulqdq"
        [.vec 2 64 [a0, a1], .vec 2 64 [b0, b1], .int 8 (0 : BitVec 8)] mem next =
      some { ret := .vec 2 64 [clmul a0 b0, (0 : BitVec 64)],
             mem := mem, next := next } :=
  rfl

/-- The gather. -/
theorem s1Calls_pext (a m : BitVec 64) (mem : Mem) (next : Nat) :
    s1Calls "llvm.x86.bmi.pext.64" [.int 64 a, .int 64 m] mem next =
      some { ret := .int 64 (pext a m), mem := mem, next := next } :=
  rfl

/-- The scatter. -/
theorem s1Calls_pdep (a m : BitVec 64) (mem : Mem) (next : Nat) :
    s1Calls "llvm.x86.bmi.pdep.64" [.int 64 a, .int 64 m] mem next =
      some { ret := .int 64 (pdep a m), mem := mem, next := next } :=
  rfl

/-- The leading-zero count with the flag `false`. -/
theorem s1Calls_ctlz (x : BitVec 64) (mem : Mem) (next : Nat) :
    s1Calls "llvm.ctlz.i64" [.int 64 x, .int 1 (0 : BitVec 1)] mem next =
      some { ret := .int 64 (BitVec.ofNat 64 (ctlz x)), mem := mem, next := next } :=
  rfl

/-! ### The specification's vocabulary

The theorem is stated over the block layer's two halves and the classifier's
carry, so the three objects the body's ABI names are spelled here in those terms:
the block's sixty-four bytes, the carry the fold leaves after them, and the
twenty-four bytes the carry slot holds. -/

/-- The block, as the model's byte list: the low half then the high half. -/
def block64 (lo hi : Block32) : List UInt8 := List.ofFn lo ++ List.ofFn hi

/-- The carry the specification leaves after a sixty-four-lane block: the high half
is entered with the carry the low half left.  This is `classMask64`'s own carry
composition, named. -/
def carry64 (lo hi : Block32) (st : ClassState) : ClassState :=
  (classWindow (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).carry

/-- The inbound carry slot, at the kernel's three words: the run-open bit, the
run parity, and the in-string word (zero or all-ones).  The scenario's
`carryBytes` writes the same three words. -/
def carrySlot (opened ppar inside : Bool) : List UInt8 :=
  natToBytes (if opened then 1 else 0) 8 ++
    natToBytes (if ppar then 1 else 0) 8 ++
    natToBytes (if inside then 0xFFFFFFFFFFFFFFFF else 0) 8

/-! ### The two corollaries

`s1_masks_decompose` states the milestone's result in the block layer's own
vocabulary, so the kernel and `ScanBlock` are one set of masks rather than two;
`s1_masks_candidate` restates the specification's candidate identity at the
kernel's units, so the entry milestone has its premise in hand.

The join is stated with `mask64` and two `maskOfList`s and **not** as
`maskOfList (block64 lo hi)`: `maskOfList` folds the first thirty-two lanes only,
so a sixty-four-lane `maskOf` does not exist and inventing one here would be a
second packing rather than the block layer's. -/

set_option linter.unusedVariables false in
/-- The five-way join of two halves, so a five-component mask can be folded back
into one `mask64`. -/
theorem mask64_or5 (a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 : BitVec 32) :
    mask64 a1 b1 ||| mask64 a2 b2 ||| mask64 a3 b3 ||| mask64 a4 b4 ||| mask64 a5 b5
      = mask64 (a1 ||| a2 ||| a3 ||| a4 ||| a5) (b1 ||| b2 ||| b3 ||| b4 ||| b5) := by
  rw [mask64_or, mask64_or, mask64_or, mask64_or]

set_option linter.unusedVariables false in
/-- **The block layer's mask is the kernel's five words.**  `maskOfList` over each
half, joined, is the union of the specification's delimiter, unescaped-quote,
escaped-quote, backslash and whitespace words.

The carry hypothesis is the state's own invariant, the one the kernel's arithmetic
keeps and `QuoteDerive` derives; the identity itself does not consume it, because
`maskOfList` asks only about bytes — the five words on the right read the carry
through `classMask64` and the fold, and it is `maskOfList_decompose` that says the
two agree lane by lane.

The components are in the specification's order — delimiter, then the two quote
splits, then backslash, then whitespace — and `maskOfList_decompose` writes them in
another; the disjunction is commutative, which is the whole of that difference. -/
theorem s1_masks_decompose (lo hi : Block32) (st : ClassState) (opened ppar : Bool)
    (hodd : st.oddRun = (opened && ppar)) :
    mask64 (maskOfList (List.ofFn lo)) (maskOfList (List.ofFn hi)) =
      specQuote64 lo hi st ||| specEscapedQuote64 lo hi st ||| specDelimiter64 lo hi st |||
      specBackslash64 lo hi st ||| specSpace64 lo hi st := by
  rw [maskOfList_decompose (List.ofFn lo) st (by simp),
    maskOfList_decompose (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry) (by simp)]
  unfold specQuote64 specEscapedQuote64 specDelimiter64 specBackslash64 specSpace64
    classMask64 spaceMask
  rw [mask64_or5]
  congr 1
  · ac_rfl
  · ac_rfl

/-- **The candidate identity at the kernel's units.**  `q | (s & ~im)` over the
sixty-four-lane block is the specification's candidate mask, which is the premise
the entry milestone consumes.  This is `candidateMask64_eq` said in the vocabulary
the kernel's slots are written in. -/
theorem s1_masks_candidate (lo hi : Block32) (st : ClassState) :
    specCandidate64 lo hi st =
      specQuote64 lo hi st |||
        (specDelimiter64 lo hi st &&& ~~~specInString64 lo hi st) :=
  candidateMask64_eq lo hi st

/-! ### The instructions the body uses, at the values it feeds them

Each of these is `evalInstr`'s branch for one constructor, stated at a value the
caller has already established.  They exist so a step of the body's execution is a
rewrite rather than an unfolding: the unfolding itself is where a hundred-step
simulation becomes unreadable. -/

/-- A binding for another name does not shadow this one. -/
theorem lookupName_bind_ne (s : State) (m : String) (v : Value) {n : String} (h : m ≠ n) :
    lookupName (s.bind m v).env n = lookupName s.env n := by
  simp [State.bind, lookupName, h]

/-- A binding is found at its own name. -/
theorem lookupName_bind_self (s : State) (n : String) (v : Value) :
    lookupName (s.bind n v).env n = some v := by
  simp [State.bind]

theorem evalInstr_load {calls : Calls} {s : State} {d : String} {ty : Ty} {p : Operand}
    {a : Nat} {v : Value} (hp : evalOperand s p = some (.ptr a))
    (hv : loadValue s.mem ty a = some v) :
    evalInstr calls s (.load d ty p) = some (s.bind d v) := by
  simp [evalInstr, hp, hv]

theorem evalInstr_binop {calls : Calls} {s : State} {d : String} {op : BinOp} {w : Nat}
    {a b : Operand} {x y : BitVec w} {r : Nat}
    (ha : evalOperand s a = some (.int w x)) (hb : evalOperand s b = some (.int w y))
    (hr : evalBinopNat op w x.toNat y.toNat = some r) :
    evalInstr calls s (.binop d op w a b) = some (s.bind d (.int w (BitVec.ofNat w r))) := by
  simp [evalInstr, Value.intToNat, ha, hb, hr]

/-- The lane-wise binary operation, at the two lane lists its operands yield.  The
two lengths are hypotheses because `vecLanes` returns `none` for a list whose length
is not the lane count, and the arms the body feeds a splat are only known to have
that length through their own construction. -/
theorem evalInstr_binopVec {calls : Calls} {s : State} {d : String} {op : BinOp}
    {n w : Nat} {a b : Operand} {l1 l2 ls : List (BitVec w)}
    (h1 : l1.length = n) (h2 : l2.length = n)
    (ha : evalOperand s a = some (.vec n w l1))
    (hb : evalOperand s b = some (.vec n w l2))
    (hm : (l1.zip l2).mapM (fun (x, y) => evalBinop op x y) = some ls) :
    evalInstr calls s (.binopVec d op n w a b) = some (s.bind d (.vec n w ls)) := by
  have ha' : (@Value.vecLanes n w) (.vec n w l1) = some l1 := by
    simp [Value.vecLanes, h1]
  have hb' : (@Value.vecLanes n w) (.vec n w l2) = some l2 := by
    simp [Value.vecLanes, h2]
  simp [evalInstr, ha, hb, ha', hb', hm]

theorem evalInstr_icmp {calls : Calls} {s : State} {d : String} {pred : IPred} {w : Nat}
    {a b : Operand} {x y : BitVec w}
    (ha : evalOperand s a = some (.int w x)) (hb : evalOperand s b = some (.int w y)) :
    evalInstr calls s (.icmp d pred w a b) =
      some (s.bind d (.int 1 (evalICmp pred x y))) := by
  simp [evalInstr, Value.intToNat, ha, hb, evalICmpNat, BitVec.ofNat_toNat]

theorem evalInstr_select_true {calls : Calls} {s : State} {d : String} {ty : Ty}
    {c a b : Operand} {va vb : Value}
    (hc : evalOperand s c = some (.int 1 (1 : BitVec 1)))
    (ha : evalOperand s a = some va) (hb : evalOperand s b = some vb) :
    evalInstr calls s (.select d ty c a b) = some (s.bind d va) := by
  simp [evalInstr, hc, ha, hb]

theorem evalInstr_select_false {calls : Calls} {s : State} {d : String} {ty : Ty}
    {c a b : Operand} {va vb : Value}
    (hc : evalOperand s c = some (.int 1 (0 : BitVec 1)))
    (ha : evalOperand s a = some va) (hb : evalOperand s b = some vb) :
    evalInstr calls s (.select d ty c a b) = some (s.bind d vb) := by
  simp [evalInstr, hc, ha, hb]

theorem evalInstr_zext {calls : Calls} {s : State} {d : String} {wIn wOut : Nat}
    {v : Operand} {x : BitVec wIn} (hv : evalOperand s v = some (.int wIn x)) :
    evalInstr calls s (.zext d wIn wOut v) =
      some (s.bind d (.int wOut (BitVec.ofNat wOut x.toNat))) := by
  simp [evalInstr, hv]

theorem evalInstr_icmpVec {calls : Calls} {s : State} {d : String} {pred : IPred}
    {n w : Nat} {a b : Operand} {va vb : Value} {l1 l2 : List (BitVec w)}
    (ha : evalOperand s a = some va) (hb : evalOperand s b = some vb)
    (h1 : va.vecLanes n w = some l1) (h2 : vb.vecLanes n w = some l2) :
    evalInstr calls s (.icmpVec d pred n w a b) =
      some (s.bind d (.vec n 1 ((l1.zip l2).map fun (x, y) => evalICmp pred x y))) := by
  simp [evalInstr, ha, hb, h1, h2]

theorem evalInstr_bitcastMask {calls : Calls} {s : State} {d : String} {n : Nat}
    {v : Operand} {l : List (BitVec 1)}
    (hv : evalOperand s v = some (.vec n 1 l)) (hlen : l.length = n) :
    evalInstr calls s (.bitcastMask d n v) =
      some (s.bind d (.int n (BitVec.ofNat n (lanesToNat l)))) := by
  simp [evalInstr, hv, hlen]

theorem evalInstr_vecBitcast {calls : Calls} {s : State} {d : String} {n w m jw : Nat}
    {v : Operand} {vv : Value} {lanes : List (BitVec w)}
    (hv : evalOperand s v = some vv) (hl : vv.vecLanes n w = some lanes)
    (hwidth : n * w = m * jw) :
    evalInstr calls s (.vecBitcast d n w m jw v) =
      some (s.bind d (.vec m jw (bitcastVecLanes jw m lanes))) := by
  simp [evalInstr, hv, hl, hwidth]

theorem evalInstr_store {calls : Calls} {s s' : State} {ty : Ty} {v p : Operand}
    {vv : Value} {a : Nat} (hv : evalOperand s v = some vv)
    (hp : evalOperand s p = some (.ptr a)) (hs : storeValue s ty vv a = some s') :
    evalInstr calls s (.store ty v p) = some s' := by
  simp [evalInstr, hv, hp, hs]

theorem evalInstr_call {calls : Calls} {s : State} {d : String} {ty : Ty} {callee : String}
    {args : List (Ty × Operand)} {vs : List Value} {r : CallOutcome}
    (ha : evalOperands s args = some vs) (hc : calls callee vs s.mem s.next = some r) :
    evalInstr calls s (.call d ty callee args) =
      some { s with env := (d, r.ret) :: s.env, mem := r.mem, next := r.next } := by
  simp [evalInstr, ha, hc]

/-- An argument list read one operand at a time: the head's value consed onto the
tail's.  The types are carried but not checked, as `evalOperands` itself does. -/
theorem evalOperands_cons {s : State} {t : Ty} {op : Operand} {rest : List (Ty × Operand)}
    {v : Value} {vs : List Value} (h : evalOperand s op = some v)
    (hr : evalOperands s rest = some vs) :
    evalOperands s ((t, op) :: rest) = some (v :: vs) := by
  simp [evalOperands, h, hr]

theorem evalInstr_extractelement {calls : Calls} {s : State} {d : String} {n w : Nat}
    {v idx : Operand} {vv : Value} {lanes : List (BitVec w)} {wi : Nat} {k : BitVec wi}
    {x : BitVec w} (hv : evalOperand s v = some vv) (hl : vv.vecLanes n w = some lanes)
    (hi : evalOperand s idx = some (.int wi k)) (hx : lanes[k.toNat]? = some x) :
    evalInstr calls s (.extractelement d n w v idx) = some (s.bind d (.int w x)) := by
  simp [evalInstr, hv, hl, hi, hx]

theorem vecLanes_self {n w : Nat} {l : List (BitVec w)} (hlen : l.length = n) :
    Value.vecLanes n w (.vec n w l) = some l := by
  simp [Value.vecLanes, hlen]

/-! ### The block's lanes

The body reads the block as two `<4 x i64>` loads, bitcasts each to `<32 x i8>`, and
joins them with `shufflevector` into `<8 x i64>` before bitcasting again to
`<64 x i8>`.  Everything downstream is a lane-wise function of those bytes, so the
names here say what the loads bind in the byte vocabulary the specification uses. -/

/-- The inputs the body's first eight instructions are a function of. -/
structure Ctx where
  /-- The block's address. -/
  p : Nat
  /-- The carry slot's address. -/
  c : Nat
  /-- The output slot's address. -/
  o : Nat
  /-- The low half. -/
  lo : Block32
  /-- The high half. -/
  hi : Block32
  /-- The run-open bit the carry slot holds. -/
  opened : Bool
  /-- The run parity the carry slot holds. -/
  ppar : Bool
  /-- The classifier's carry. -/
  st : ClassState

/-- The low half's bytes as a word. -/
def loWord (k : Ctx) : Nat := bytesToNat (List.ofFn k.lo)

/-- The high half's bytes as a word. -/
def hiWord (k : Ctx) : Nat := bytesToNat (List.ofFn k.hi)

/-- The low half's lanes, as a `<32 x i8>` value holds them. -/
def loLanes (k : Ctx) : List (BitVec 8) := List.ofFn fun i => BitVec.ofNat 8 (k.lo i).toNat

/-- The high half's lanes. -/
def hiLanes (k : Ctx) : List (BitVec 8) := List.ofFn fun i => BitVec.ofNat 8 (k.hi i).toNat

/-- The block's sixty-four lanes, low half then high half — the emission's
`shufflevector` order. -/
def blockLanes (k : Ctx) : List (BitVec 8) := loLanes k ++ hiLanes k


theorem loLanes_length (k : Ctx) : (loLanes k).length = 32 := by simp [loLanes]
theorem hiLanes_length (k : Ctx) : (hiLanes k).length = 32 := by simp [hiLanes]
theorem blockLanes_length (k : Ctx) : (blockLanes k).length = 64 := by
  simp [blockLanes, loLanes_length, hiLanes_length]
theorem joinedLanes_length (k : Ctx) :
    (unpackLanes 64 4 (loWord k) ++ unpackLanes 64 4 (hiWord k)).length = 8 := by
  simp [unpackLanes_length]

theorem loWord_lt (k : Ctx) : loWord k < 2 ^ 256 := by
  have h := bytesToNat_lt (List.ofFn k.lo)
  rw [List.length_ofFn] at h
  have h2 : (256 : Nat) ^ 32 = 2 ^ 256 := by
    rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_mul,
      show 8 * 32 = 256 from by decide]
  rw [h2] at h
  exact h

theorem hiWord_lt (k : Ctx) : hiWord k < 2 ^ 256 := by
  have h := bytesToNat_lt (List.ofFn k.hi)
  rw [List.length_ofFn] at h
  have h2 : (256 : Nat) ^ 32 = 2 ^ 256 := by
    rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_mul,
      show 8 * 32 = 256 from by decide]
  rw [h2] at h
  exact h

theorem byteLanes_ofFn {f : Fin 32 → UInt8} :
    byteLanes (List.ofFn f) = List.ofFn fun i => BitVec.ofNat 8 (f i).toNat := by
  simp [byteLanes, List.map_ofFn]

theorem unpackLanes_lo (k : Ctx) : unpackLanes 8 32 (loWord k) = loLanes k := by
  rw [loWord, byteLanes_eq_unpackLanes (by simp), byteLanes_ofFn]
  rfl

theorem unpackLanes_hi (k : Ctx) : unpackLanes 8 32 (hiWord k) = hiLanes k := by
  rw [hiWord, byteLanes_eq_unpackLanes (by simp), byteLanes_ofFn]
  rfl

/-- The two loads' lanes, as one `<64 x i8>`: the join's packing is the block's
`bytesToNat`, so the shuffle-then-bitcast pair binds the block's own lanes. -/
theorem packLanes_join (k : Ctx) :
    unpackLanes 8 64 (packLanes (unpackLanes 64 4 (loWord k) ++
        unpackLanes 64 4 (hiWord k))) = blockLanes k := by
  have h2 : (256 : Nat) ^ 32 = 2 ^ 256 := by
    rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_mul,
      show 8 * 32 = 256 from by decide]
  rw [packLanes_append, unpackLanes_length, packLanes_unpackLanes, packLanes_unpackLanes,
    show (4 * 64 : Nat) = 256 from rfl,
    Nat.mod_eq_of_lt (loWord_lt k), Nat.mod_eq_of_lt (hiWord_lt k)]
  have h3 : loWord k + 256 ^ 32 * hiWord k = bytesToNat (block64 k.lo k.hi) := by
    rw [block64, bytesToNat_append, List.length_ofFn]
    rfl
  rw [h3, byteLanes_eq_unpackLanes (by simp [block64] : (block64 k.lo k.hi).length = 64)]
  rw [block64, byteLanes_append, byteLanes_ofFn, byteLanes_ofFn]
  rfl

/-! ### The body, instruction by instruction

The values the first nine instructions bind, and the step that binds each.  The
registers are the emission's own names; `%or.i` is the raw quote word, which the
escape arithmetic below then filters. -/

theorem evalInstr_shuffleVec {calls : Calls} {s : State} {d : String} {n w : Nat}
    {a b : Operand} {mask : List Nat} {va vb : Value} {l1 l2 : List (BitVec w)}
    {ls : List (BitVec w)}
    (ha : evalOperand s a = some va) (hb : evalOperand s b = some vb)
    (h1 : va.vecLanes n w = some l1) (h2 : vb.vecLanes n w = some l2)
    (hm : mask.mapM (fun k => if k < n then l1[k]? else l2[k - n]?) = some ls) :
    evalInstr calls s (.shuffleVec d n w a b mask) =
      some (s.bind d (.vec mask.length w ls)) := by
  simp [evalInstr, ha, hb, h1, h2, hm]

/-- The shuffle's mask `[0 … 7]` at two four-lane operands reads the first, then
the second: the join is the concatenation. -/
theorem mapM_pick8 {w : Nat} {l1 l2 : List (BitVec w)} (h1 : l1.length = 4)
    (h2 : l2.length = 4) :
    ([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).mapM
        (fun k => if k < 4 then l1[k]? else l2[k - 4]?) = some (l1 ++ l2) := by
  have hcat : l1 ++ l2 =
      [l1[0]'(by omega), l1[1]'(by omega), l1[2]'(by omega), l1[3]'(by omega),
       l2[0]'(by omega), l2[1]'(by omega), l2[2]'(by omega), l2[3]'(by omega)] := by
    apply List.ext_getElem
    · simp [h1, h2]
    · intro k hk1 hk2
      have hk : k < 8 := by simpa [List.length_append, h1, h2] using hk1
      have h8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
      rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [List.getElem_append, h1]
  simp only [List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some]
  rw [List.getElem?_eq_getElem (by omega : (0 : Nat) < l1.length),
    List.getElem?_eq_getElem (by omega : (1 : Nat) < l1.length),
    List.getElem?_eq_getElem (by omega : (2 : Nat) < l1.length),
    List.getElem?_eq_getElem (by omega : (3 : Nat) < l1.length),
    List.getElem?_eq_getElem (by omega : (0 : Nat) < l2.length),
    List.getElem?_eq_getElem (by omega : (1 : Nat) < l2.length),
    List.getElem?_eq_getElem (by omega : (2 : Nat) < l2.length),
    List.getElem?_eq_getElem (by omega : (3 : Nat) < l2.length)]
  rw [ite_eq_left (by decide : (0 : Nat) < 4), ite_eq_left (by decide : (1 : Nat) < 4),
    ite_eq_left (by decide : (2 : Nat) < 4), ite_eq_left (by decide : (3 : Nat) < 4),
    ite_eq_right (by decide : ¬ (4 : Nat) < 4), ite_eq_right (by decide : ¬ (5 : Nat) < 4),
    ite_eq_right (by decide : ¬ (6 : Nat) < 4), ite_eq_right (by decide : ¬ (7 : Nat) < 4)]
  simp only [Option.bind_some]
  rw [← hcat]

/-- The lanes `%6` binds: the block's bytes compared with `"`. -/
def quoteLanes (k : Ctx) : List (BitVec 1) :=
  ((blockLanes k).zip (List.replicate 64 (BitVec.ofInt 8 34))).map
    fun (x, y) => evalICmp .eq x y

theorem quoteLanes_length (k : Ctx) : (quoteLanes k).length = 64 := by
  simp [quoteLanes, blockLanes_length]


/-! ### The lane-to-word bridge

One bridge per **predicate**, not per mask: a half's lanes, packed, are that half's
`pack32` word, and the two halves join into `mask64`.  Every mask below is an
instance, so the shared work is these three lemmas rather than six. -/

/-- A lane list's packing stays inside the bits its lanes occupy. -/
theorem lanesToNat_lt (l : List (BitVec 1)) : lanesToNat l < 2 ^ l.length := by
  rw [← packLanes_eq_lanesToNat]
  simpa using packLanes_lt l

/-- The lanes of a half, packed, are that half's `pack32` word. -/
theorem lanesToNat_ofFn_pack32 (f : UInt8 → Bool) (blk : Block32) :
    lanesToNat (List.ofFn fun i => BitVec.ofBool (f (blk i))) = (pack32 f blk).toNat := by
  have h := pack32_eq_bitcast f blk
  have hlt : lanesToNat (List.ofFn fun i => BitVec.ofBool (f (blk i))) < 2 ^ 32 := by
    have := lanesToNat_lt (List.ofFn fun i => BitVec.ofBool (f (blk i)))
    simpa using this
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- The kernel's join: the low half's word, or the high half's shifted up by
thirty-two, is `mask64`. -/
theorem or_ofNat_shift {X Y : Nat} (hX : X < 2 ^ 32) :
    (BitVec.ofNat 64 X : BitVec 64) ||| (BitVec.ofNat 64 Y <<< 32)
      = mask64 (BitVec.ofNat 32 X) (BitVec.ofNat 32 Y) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_or]
  by_cases hk32 : k < 32
  · have h1 : (BitVec.ofNat 64 X).getLsbD k = X.testBit k := by
      rw [BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and]
    have h2 : (BitVec.ofNat 64 Y <<< 32).getLsbD k = false := by
      rw [BitVec.getLsbD_shiftLeft, decide_eq_true hk, Bool.true_and,
        decide_eq_true hk32, Bool.not_true, Bool.false_and]
    have h3 : (mask64 (BitVec.ofNat 32 X) (BitVec.ofNat 32 Y)).getLsbD k = X.testBit k := by
      rw [mask64_getLsbD_lo _ _ hk32, BitVec.getLsbD_ofNat, decide_eq_true hk32,
        Bool.true_and]
    rw [h1, h2, h3]
    exact Bool.or_false _
  · have h32 : 32 ≤ k := by omega
    have h1 : (BitVec.ofNat 64 X).getLsbD k = false := by
      rw [BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and,
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by decide) h32))]
    have h2 : (BitVec.ofNat 64 Y <<< 32).getLsbD k = Y.testBit (k - 32) := by
      rw [BitVec.getLsbD_shiftLeft, decide_eq_true hk, Bool.true_and,
        decide_eq_false_iff_not.mpr (by omega), Bool.not_false, Bool.true_and,
        BitVec.getLsbD_ofNat, decide_eq_true (by omega : k - 32 < 64), Bool.true_and]
    have h3 : (mask64 (BitVec.ofNat 32 X) (BitVec.ofNat 32 Y)).getLsbD k
        = Y.testBit (k - 32) := by
      rw [show k = (k - 32) + 32 from by omega, mask64_getLsbD_hi _ _ (by omega),
        BitVec.getLsbD_ofNat, decide_eq_true (by omega : k - 32 < 32), Bool.true_and]
      have hidx : k - 32 + 32 - 32 = k - 32 := by omega
      rw [hidx]
    rw [h1, h2, h3]
    exact Bool.false_or _


/-- The specification's clean backslash word: the two halves' `IsBackslashB` masks,
joined.  This is the form `s1_masks_refines` can use; the body's own register value
reaches it at `toNat` level, because the step words are bound in the raw shape
`evalInstr` builds. -/
def backslashWord (k : Ctx) : BitVec 64 :=
  mask64 (pack32 IsBackslashB k.lo) (pack32 IsBackslashB k.hi)

/-- **Packing sixty-four lanes is joining the two packed halves.**  This is the
bridge the masks whose body word is a single sixty-four-lane comparison need: the
body leaves `ofNat 64 (lanesToNat …)` of the whole block, and the specification's
word is `mask64` of the halves.

It is stated over the lane **lists**, not over a `lanesToNat` sum, and that is
deliberate: the sum formulation needs a `Nat` lemma about `testBit` of `X + 2^32 * Y`
that this toolchain does not ship, while reading the bit on each side as
`(l[k]? = some 1)` needs nothing beyond `lanesToNat_testBit`, `mask64_getLsbD_lo/hi`
and `List.getElem?_append_left/right`. -/
theorem ofNat_lanesToNat_join {a b : List (BitVec 1)} (ha : a.length = 32)
    (hb : b.length = 32) :
    BitVec.ofNat 64 (lanesToNat (a ++ b)) =
      mask64 (BitVec.ofNat 32 (lanesToNat a)) (BitVec.ofNat 32 (lanesToNat b)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and]
  by_cases hk32 : k < 32
  · simp only [mask64_getLsbD_lo _ _ hk32, BitVec.getLsbD_ofNat, decide_eq_true hk32,
      Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    rw [lanesToNat_testBit (a ++ b) k, lanesToNat_testBit a k,
      List.getElem?_append_left (by omega : k < a.length)]
  · rw [show k = (k - 32) + 32 from by omega,
      mask64_getLsbD_hi _ _ (by omega), BitVec.getLsbD_ofNat,
      decide_eq_true (by omega : k - 32 < 32), Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    rw [lanesToNat_testBit (a ++ b) ((k - 32) + 32), lanesToNat_testBit b (k - 32),
      List.getElem?_append_right (by omega : a.length ≤ (k - 32) + 32), ha,
      show (k - 32) + 32 - 32 = k - 32 from by omega]

/-- **A lane lookup on a `zip` with a repeated constant, then a map.**  The quote
and control constructions are both `(lans.zip (replicate 64 c)).map g`, and both
identities need `(…)[j]?` as a single lane.

The lane is delivered with **`getD`**, not `getElem`: a dependent proof term in a
statement travels into every downstream motive, and `rw`/`simp` then fail with
"motive is not type correct" — which is what happened when this lemma carried
`l[j]'(by …)`.  `getD` is proof-free, so the caller's rewrites stay ordinary.

`List.getElem?_zip` is **not** in this toolchain; `List.getElem?_zip_eq_some` is
(`(l₁.zip l₂)[i]? = some z ↔ …`), which forces a case split per lane.  Going through
`getElem?_eq_getElem` and `List.getElem_zip` instead gives the functional form in
two rewrites. -/
theorem zipReplicate_getElem? {w : Nat} {α : Type} (l : List (BitVec w)) (c : BitVec w)
    (g : BitVec w → BitVec w → α) (hlen : l.length = 64) {j : Nat} (hj : j < 64) :
    ((l.zip (List.replicate 64 c)).map fun p => g p.1 p.2)[j]? =
      some (g (l.getD j 0) c) := by
  rw [List.getElem?_map,
    List.getElem?_eq_getElem (by simp [List.length_zip, hlen, hj] :
      j < (l.zip (List.replicate 64 c)).length)]
  simp only [List.getElem_zip, List.getElem_replicate, Option.map_some, Option.some.injEq]
  congr 1
  simp [List.getD, List.getElem?_eq_getElem (by rw [hlen]; exact hj)]

/-- The same lookup at a list whose length is the lane count itself.  The table
region's constructions all zip against a splat of their own length, so this is the
form those lane facts read. -/
theorem zipReplicate_getElem?_len {w : Nat} {α : Type} (l : List (BitVec w)) (c : BitVec w)
    (g : BitVec w → BitVec w → α) {j : Nat} (hj : j < l.length) :
    ((l.zip (List.replicate l.length c)).map fun p => g p.1 p.2)[j]? =
      some (g (l.getD j 0) c) := by
  rw [List.getElem?_map,
    List.getElem?_eq_getElem (by simp [List.length_zip, hj] :
      j < (l.zip (List.replicate l.length c)).length)]
  simp only [List.getElem_zip, List.getElem_replicate, Option.map_some, Option.some.injEq]
  congr 1
  simp [List.getD, List.getElem?_eq_getElem hj]

/-- A `zip` against a replicated constant, mapped by a two-argument function: the
lane at the constant.  The `bitcast`-less table region's value lists are all of this
shape, so the step's value and the identity's reading share one lemma. -/
theorem zipReplicate_map {α : Type} {w : Nat} (l : List (BitVec w)) (c : BitVec w)
    (f : BitVec w → BitVec w → α) :
    (l.zip (List.replicate l.length c)).map (fun p => f p.1 p.2) = l.map fun x => f x c := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.map_cons, ih]

/-- The monadic form of the same: a lane-wise operation that always answers, so the
`mapM` is the `map` the semantics' `.binopVec` arm builds. -/
theorem zipReplicate_mapM {w : Nat} (l : List (BitVec w)) (c : BitVec w)
    (g : BitVec w → BitVec w → Option (BitVec w)) (f : BitVec w → BitVec w)
    (hg : ∀ x, g x c = some (f x)) :
    (l.zip (List.replicate l.length c)).mapM (fun p => g p.1 p.2) = some (l.map f) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.mapM_cons,
        List.map_cons, hg x, ih]
      rfl

/-- A `mapM` that never fails is the `map` of what it answers. -/
theorem mapM_some_map {α β : Type} (l : List α) (f : α → β) :
    l.mapM (fun x => some (f x)) = some (l.map f) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mapM_cons, List.map_cons, ih]
      rfl

/-- The `= 1` reading of a one-bit lane: a lane is set exactly when its proposition
holds.  Core has none of `BitVec.ofBool_eq_one`, `BitVec.ofBool_eq_iff`,
`BitVec.ofBool_inj` or `BitVec.ofBool_eq_true`, so the mask identities state it
here.  It is necessary, not a convenience: a per-byte lemma's `BitVec 1 = BitVec 1`
conclusion rewrites inside the `some` and leaves `= some 1` untouched. -/
theorem ofBool_eq_one {p : Prop} [Decidable p] : (BitVec.ofBool p = (1 : BitVec 1)) ↔ p := by
  by_cases hp : p
  · simp [hp]
  · simp [hp]

/-- The control lanes: the block's sixty-four bytes compared `ult` with `0x20`.
The body writes this one as `icmp ult <64 x i8> …`, so — like `quoteLanes` and
unlike the two-half words — it is a single sixty-four-lane construction. -/
def controlLanes (k : Ctx) : List (BitVec 1) :=
  ((blockLanes k).zip (List.replicate 64 (BitVec.ofInt 8 32))).map
    fun (x, y) => evalICmp .ult x y

/-- The `= 1` reading at a **`Bool`**, which is the form an `ult`-shaped lane needs:
`evalICmp .ult` hands `ofBool` a `Bool` directly, while `evalICmp .eq` hands it a
`Prop` (coerced by `decide`), so the two comparisons need the two forms. -/
theorem ofBool_eq_one_bool (b : Bool) : (BitVec.ofBool b = (1 : BitVec 1)) ↔ b = true := by
  cases b <;> simp

/-! ### The two-nibble tables

`s1f_lo_tab` and `s1f_hi_tab` are sixteen entries each, written twice in the
emission so that one `pshufb` covers both 128-bit lanes.  The kernel consults the low
nibble in one and the high nibble in the other and `&&`s the results; the AND is
non-zero exactly for the six structural bytes in bits 0–5 and the four whitespace
bytes in bits 6–7.

The per-byte facts are `decide` over `BitVec 8` — 256 cases, and cheap: the
enumeration is a decision procedure on a literal table, not a rewrite, and it costs
about a second for the pair.  This is the one piece of the vocabulary that is an
enumeration rather than a rewrite, and it turned out not to need a restatement. -/

/-- `s1f_lo_tab`, sixteen entries (the emission's second copy repeats them). -/
def loTab16 : List (BitVec 8) :=
  [0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x80, 0x82, 0x14, 0x01, 0xA8, 0x00, 0x00]

/-- `s1f_hi_tab`, sixteen entries. -/
def hiTab16 : List (BitVec 8) :=
  [0x80, 0x00, 0x41, 0x02, 0x00, 0x30, 0x00, 0x0C,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- The two-nibble lookup at a byte: the low nibble indexes one table, the high
nibble the other, and the results are `&&`ed. -/
def tabAnd (x : BitVec 8) : BitVec 8 :=
  loTab16.getD (x &&& 0x0F).toNat 0 &&& hiTab16.getD ((x >>> 4).toNat) 0

/-- The table's structural bit: bits 0–5 are set exactly at the six delimiters. -/
theorem tabAnd_delim_bv (x : BitVec 8) :
    (tabAnd x &&& (0x3F : BitVec 8) ≠ 0) ↔ (IsDelimB (UInt8.ofNat x.toNat) = true) := by
  revert x
  decide

/-- The table's whitespace bit: bits 6–7 are set exactly at the four whitespace
bytes. -/
theorem tabAnd_space_bv (x : BitVec 8) :
    (tabAnd x &&& (0xC0 : BitVec 8) ≠ 0) ↔ (IsSpaceB (UInt8.ofNat x.toNat) = true) := by
  revert x
  decide

/-- The table's structural bit, at a byte. -/
theorem tabAnd_delim (b : UInt8) :
    (tabAnd b.toBitVec &&& (0x3F : BitVec 8) ≠ 0) ↔ (IsDelimB b = true) := by
  have h := tabAnd_delim_bv b.toBitVec
  rw [show b.toBitVec.toNat = b.toNat from rfl,
    show UInt8.ofNat b.toNat = b from UInt8.ofNat_toNat] at h
  exact h

/-- The table's whitespace bit, at a byte. -/
theorem tabAnd_space (b : UInt8) :
    (tabAnd b.toBitVec &&& (0xC0 : BitVec 8) ≠ 0) ↔ (IsSpaceB b = true) := by
  have h := tabAnd_space_bv b.toBitVec
  rw [show b.toBitVec.toNat = b.toNat from rfl,
    show UInt8.ofNat b.toNat = b from UInt8.ofNat_toNat] at h
  exact h

/-! ### The index arithmetic of a duplicated table

`pshufb`'s control lane selects an entry at `16 * (i / 16) + c % 16`, and for a
table written twice the base `16 * (i / 16)` is `0` or `16`.  Extracting that as a
`Nat` fact, **before any `getD` is in scope**, is what makes the proof go:

`omega` keeps no relation between `a / k` and `a`, nor between `x % k` and `x`,
across a product-and-sum.  `Nat.div_lt_iff_lt_mul` supplies the bound
(`i < 32` gives `i / 16 < 2`) and `Nat.mod_lt` the other (`c % 16 < 16`); with both
in hand the arithmetic is linear and `omega` closes it. -/

/-- In the first copy of a doubled table: the base is zero. -/
theorem split16 {i c : Nat} (hi : i < 32) (h : 16 * (i / 16) + c % 16 < 16) :
    16 * (i / 16) = 0 := by
  have hd : i / 16 < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 16)]
    omega
  have hc : c % 16 < 16 := Nat.mod_lt _ (by decide)
  rcases Nat.eq_zero_or_pos (16 * (i / 16)) with h0 | hpos
  · exact h0
  · exfalso
    omega

/-- In the second copy: the base is sixteen, so the index minus sixteen is the
control's own nibble. -/
theorem split16' {i c : Nat} (hi : i < 32) (h : ¬ (16 * (i / 16) + c % 16 < 16)) :
    16 * (i / 16) + c % 16 - 16 = c % 16 := by
  have hd : i / 16 < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 16)]
    omega
  have hc : c % 16 < 16 := Nat.mod_lt _ (by decide)
  have h16 : 16 * (i / 16) = 16 := by omega
  omega

/-- A doubled table reads the same entry from either copy. -/
theorem getD_two_copies {t : List (BitVec 8)} (hlen : t.length = 16) {i : Nat}
    (hi : i < 32) (c : BitVec 8) :
    (t ++ t).getD (16 * (i / 16) + c.toNat % 16) 0 = t.getD (c.toNat % 16) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append, hlen]
  by_cases h : 16 * (i / 16) + c.toNat % 16 < 16
  · rw [ite_eq_left h, show 16 * (i / 16) + c.toNat % 16 = c.toNat % 16 from by
      rw [split16 hi h]; omega]
  · rw [ite_eq_right h, show 16 * (i / 16) + c.toNat % 16 - 16 = c.toNat % 16 from
      split16' hi h]

/-! ### `pshufb` over a table written twice

`pshufbLanes` is lane-local: control lane `i` selects `16 * (i / 16) + c % 16`, so a
table written twice (`s1f_lo_tab` and `s1f_hi_tab` are sixteen entries each, repeated
once per 128-bit lane) reads the same entry from either copy.  That is this lemma.

**It is not an equality of the two `pshufbLanes` applications.**  Lane 16 is where
that form fails: with a sixteen-entry table and a zero control,
`#eval (pshufbLanes (t16 ++ t16) ctl).getD 16 0` is `0x01` against `0x00` for the
single table, because the doubled table's lane 16 re-reads the first copy while the
single one indexes past its end and takes `getD`'s default.  The equality holds lane
by lane against the *entry*, which is what this states; a reader tempted by the
corpus-level form should run those two `#eval`s first.

Two mechanical facts the proof needs, and they are the whole of what made it look
stuck:
* `List.getElem?_range` leaves its **bound as a side goal** after `rw` — that is the
  `⊢ i < 32` the earlier attempts saw attributed to the statement line.  It is
  discharged by a bullet and `omega`, not by `dif_pos`, `simp` or an ascription.
* the `rw` chain must run `unfold`, then the four rewrites, with the bullets in the
  order the goals appear: the bound first, then the main goal. -/

/-- A doubled table reads the control's entry at every lane. -/
theorem pshufbLanes_two_copies_lane (t : List (BitVec 8)) (hlen : t.length = 16)
    (control : List (BitVec 8)) {i : Nat} (hi : i < 32) (hc : control.length = 32) :
    (pshufbLanes (t ++ t) control).getD i (0 : BitVec 8)
      = (if (control.getD i (0 : BitVec 8)).getLsbD 7 = true then (0 : BitVec 8)
         else t.getD ((control.getD i (0 : BitVec 8)).toNat % 16) (0 : BitVec 8)) := by
  unfold pshufbLanes
  rw [List.getD_eq_getElem?_getD, hc, List.getElem?_map, List.getElem?_range]
  · simp only [Option.map_some, Option.getD_some]
    by_cases hb : (control.getD i (0 : BitVec 8)).getLsbD 7 = true
    · rw [ite_eq_left hb, ite_eq_left hb]
    · rw [ite_eq_right hb, ite_eq_right hb]
      exact getD_two_copies hlen hi (control.getD i (0 : BitVec 8))
  · omega

/-! ### `bitcastVecLanes` at differing widths

**The answer to whether `bitcastVecLanes` needs a companion lemma: it does not.**
`bitcastVecLanes jw m lanes = unpackLanes jw m (packLanes lanes)` by definition, and
`packLanes_unpackLanes` (`Memory.lean`) already says what `packLanes` does to
`unpackLanes` — so the general round-trip at *differing* element widths is those two
facts composed, one line, with nothing new to prove or pin on the semantics side.

That is the second semantics definition this milestone has found well-shaped for the
proofs that consume it (the first is `pshufbLanes`, whose lemma is index arithmetic);
it is worth recording because the alternative — a byte-specific instance of the
round-trip — would have hidden a general fact behind one mask's needs.

The third is `s1Calls`'s `pclmulqdq` arm at immediate 0.  It gives
`.vec 2 64 [clmul a₀ b₀, 0]` — lane 1 is **zero**, because the immediate selects which
lanes are multiplied and the imm-0 case multiplies lane 0 only, not because a second
product is dropped.  So the body's `%vecext.i.i.i = extractelement %40, 0` is one step
to `clmul a₀ b₀`, and `%xor.i = xor %vecext.i.i.i, %41` is already the right-hand side
of `specInString64_eq_clmul`: `clmul (specQuote64 lo hi st) (allOnes 64) ^^^ seedVec 64
st.inside`.  The in-string identity therefore needs **no packing bridge** — only
`%and.i = specQuote64 lo hi st` and `%41 = seedVec 64 st.inside`, both `toNat`-level
readings this vocabulary already covers.  The arm is well-shaped for the same reason as
the other two: the modelling choice (lane 1 zero) is the semantics' own statement of
the immediate's meaning, not a simplification the proof has to work around. -/

/-- The lane reinterpretation of a packed word, at any pair of element widths. -/
theorem bitcastVecLanes_unpackLanes (w n m jw v : Nat) :
    bitcastVecLanes jw m (unpackLanes w n v) = unpackLanes jw m (v % 2 ^ (n * w)) := by
  unfold bitcastVecLanes
  rw [packLanes_unpackLanes]

end LeanLLVM.Vellum.JsonS1MasksIR
