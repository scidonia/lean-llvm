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
the literal AST and the committed text are the same object: a change to either
that the other does not carry fails elaboration, and no theorem can be stated
about a body the text does not contain.

The registers the emission names are its own (`%0`, `%add.ptr`, `%cmp.i39.i`,
…).  The body's seven parameters keep the source's names (`%b`, `%n`, `%ent`,
`%xp`, `%nxp`, `%xcarry`, `%arm`), so the capture applies no rename.

## What the pin establishes

The unit's body is the classifier's text in two loop shapes plus a peeled tail.
The first loop (`for.body`) classifies block after block while they are all
ASCII and carries no DFA or ASCII-probe state; on the first block with a high
bit it runs that block's DFA step (`if.then38`), then hands the rest of the
document to the fused loop.  That loop (`for.body54`) keeps the mask words,
both carries, the entry word and the DFA's `u8k`/`prev_ascii` pair in registers,
composes the entry word and stores it at `ent[i]`, and appends the escape list
when `arm & 2`.  Its block's two vectors are tested once for ASCII (the `ptestz`
on their `or`), and the DFA runs in `if.then90` when the block or its
predecessor is not ASCII, or on every block the loop reaches when `arm & 4`
selects the ungated path; the all-ASCII prefix before the hand-off never reaches
this loop and contributes zero to the error vector.  The tail's DFA arm is
`if.then144`.  The return word composes the ASCII probe (bit 0) and the UTF-8
stage's error word (bit 1) in `if.end170`.

Five facts the proof and the contract rest on are guarded here:

* the body allocates nothing (`allocaTypes = []`): its scratch is the caller's,
  so no callee-moved allocator appears in a frame the pipeline does not name;
* the call census is the classifier's two intrinsics, the ASCII probe's and the
  UTF-8 stage's lane test, the UTF-8 stage's saturating subtraction, and the
  escape list, with the multiplicity the ASCII phase, the fused loop, the
  peeled block and their three DFA sites emit;
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

The body in the fixture's block order.  The literal is the fixture's parse tree,
field for field: the guards below compare it with the committed text again, so a
fixture edit that this definition does not carry fails elaboration. -/

def s1BlocksFunction : Function :=
{ name := "leanllvm_json_s1_blocks",
  retTy := LeanLLVM.Ty.int 64,
  params := [("%b", LeanLLVM.Ty.ptr),
             ("%n", LeanLLVM.Ty.int 64),
             ("%ent", LeanLLVM.Ty.ptr),
             ("%xp", LeanLLVM.Ty.ptr),
             ("%nxp", LeanLLVM.Ty.ptr),
             ("%xcarry", LeanLLVM.Ty.ptr),
             ("%arm", LeanLLVM.Ty.int 64)],
  blocks := [{ name := "entry",
               instrs := [LeanLLVM.Instr.binop
                            "%shr"
                            (LeanLLVM.BinOp.lshr)
                            64
                            (LeanLLVM.Operand.reg "%n")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000006#64)),
                          LeanLLVM.Instr.binop
                            "%and"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%n")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000003f#64)),
                          LeanLLVM.Instr.trunc "%0" 64 32 (LeanLLVM.Operand.reg "%arm"),
                          LeanLLVM.Instr.binop
                            "%1"
                            (LeanLLVM.BinOp.lshr)
                            32
                            (LeanLLVM.Operand.reg "%0")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0x00000002#32)),
                          LeanLLVM.Instr.binop
                            "%conv"
                            (LeanLLVM.BinOp.and)
                            32
                            (LeanLLVM.Operand.reg "%1")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0x00000001#32)),
                          LeanLLVM.Instr.icmp
                            "%cmp2506.not"
                            (LeanLLVM.IPred.ult)
                            64
                            (LeanLLVM.Operand.reg "%n")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000040#64))],
               term := LeanLLVM.Term.condbr (LeanLLVM.Operand.reg "%cmp2506.not") "if.end50" "for.body.lr.ph" },
             { name := "for.body.lr.ph",
               instrs := [LeanLLVM.Instr.binop
                            "%and18"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%arm")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000002#64)),
                          LeanLLVM.Instr.icmp
                            "%tobool.not"
                            (LeanLLVM.IPred.eq)
                            64
                            (LeanLLVM.Operand.reg "%and18")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64))],
               term := LeanLLVM.Term.br "for.body" },
             { name := "for.body",
               instrs := [LeanLLVM.Instr.phi
                            "%prevS.0511"
                            (LeanLLVM.Ty.int 64)
                            [("for.body.lr.ph", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                             ("for.inc", LeanLLVM.Operand.reg "%shr17")],
                          LeanLLVM.Instr.phi
                            "%i.0510"
                            (LeanLLVM.Ty.int 64)
                            [("for.body.lr.ph", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                             ("for.inc", LeanLLVM.Operand.reg "%inc")],
                          LeanLLVM.Instr.phi
                            "%st.sroa.0.0509"
                            (LeanLLVM.Ty.int 64)
                            [("for.body.lr.ph", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                             ("for.inc", LeanLLVM.Operand.reg "%shr.i.i")],
                          LeanLLVM.Instr.phi
                            "%st.sroa.9.0508"
                            (LeanLLVM.Ty.int 64)
                            [("for.body.lr.ph", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                             ("for.inc", LeanLLVM.Operand.reg "%conv13.i.i")],
                          LeanLLVM.Instr.phi
                            "%st.sroa.15.0507"
                            (LeanLLVM.Ty.int 64)
                            [("for.body.lr.ph", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                             ("for.inc", LeanLLVM.Operand.reg "%shr.i")],
                          LeanLLVM.Instr.binop
                            "%shl"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%i.0510")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000006#64)),
                          LeanLLVM.Instr.gep
                            "%add.ptr"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%b")
                            (LeanLLVM.Operand.reg "%shl"),
                          LeanLLVM.Instr.load
                            "%2"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr"),
                          LeanLLVM.Instr.gep
                            "%add.ptr5"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000020#64)),
                          LeanLLVM.Instr.load
                            "%3"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr5"),
                          LeanLLVM.Instr.vecBitcast "%4" 4 64 32 8 (LeanLLVM.Operand.reg "%2"),
                          LeanLLVM.Instr.vecBitcast "%5" 4 64 32 8 (LeanLLVM.Operand.reg "%3"),
                          LeanLLVM.Instr.shuffleVec
                            "%6"
                            4
                            64
                            (LeanLLVM.Operand.reg "%2")
                            (LeanLLVM.Operand.reg "%3")
                            [0, 1, 2, 3, 4, 5, 6, 7],
                          LeanLLVM.Instr.vecBitcast "%7" 8 64 64 8 (LeanLLVM.Operand.reg "%6"),
                          LeanLLVM.Instr.icmpVec
                            "%8"
                            (LeanLLVM.IPred.eq)
                            64
                            8
                            (LeanLLVM.Operand.reg "%7")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 64 8 0x22#8)),
                          LeanLLVM.Instr.bitcastMask "%or.i286" 64 (LeanLLVM.Operand.reg "%8"),
                          LeanLLVM.Instr.icmpVec
                            "%cmp.i39.i"
                            (LeanLLVM.IPred.eq)
                            32
                            8
                            (LeanLLVM.Operand.reg "%4")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x5c#8)),
                          LeanLLVM.Instr.bitcastMask "%9" 32 (LeanLLVM.Operand.reg "%cmp.i39.i"),
                          LeanLLVM.Instr.zext "%conv9.i" 32 64 (LeanLLVM.Operand.reg "%9"),
                          LeanLLVM.Instr.icmpVec
                            "%cmp.i.i"
                            (LeanLLVM.IPred.eq)
                            32
                            8
                            (LeanLLVM.Operand.reg "%5")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x5c#8)),
                          LeanLLVM.Instr.bitcastMask "%10" 32 (LeanLLVM.Operand.reg "%cmp.i.i"),
                          LeanLLVM.Instr.zext "%conv12.i" 32 64 (LeanLLVM.Operand.reg "%10"),
                          LeanLLVM.Instr.binop
                            "%shl13.i"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%conv12.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000020#64)),
                          LeanLLVM.Instr.binop
                            "%or14.i"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%shl13.i")
                            (LeanLLVM.Operand.reg "%conv9.i"),
                          LeanLLVM.Instr.binop
                            "%and.i.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%st.sroa.0.0509")
                            (LeanLLVM.Operand.reg "%st.sroa.9.0508"),
                          LeanLLVM.Instr.binop
                            "%shl.i.i"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%or14.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000001#64)),
                          LeanLLVM.Instr.binop
                            "%not.i.i"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%shl.i.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and1.i.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or14.i")
                            (LeanLLVM.Operand.reg "%not.i.i"),
                          LeanLLVM.Instr.binop
                            "%xor.i.i"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%and.i.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x5555555555555555#64)),
                          LeanLLVM.Instr.binop
                            "%and2.i.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and1.i.i")
                            (LeanLLVM.Operand.reg "%xor.i.i"),
                          LeanLLVM.Instr.binop
                            "%xor3.i.i"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%and2.i.i")
                            (LeanLLVM.Operand.reg "%and1.i.i"),
                          LeanLLVM.Instr.binop
                            "%not4.i.i"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%or14.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%add.i.i"
                            (LeanLLVM.BinOp.add)
                            64
                            (LeanLLVM.Operand.reg "%and2.i.i")
                            (LeanLLVM.Operand.reg "%or14.i"),
                          LeanLLVM.Instr.binop
                            "%add5.i.i"
                            (LeanLLVM.BinOp.add)
                            64
                            (LeanLLVM.Operand.reg "%xor3.i.i")
                            (LeanLLVM.Operand.reg "%or14.i"),
                          LeanLLVM.Instr.binop
                            "%and6.i.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%not4.i.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xaaaaaaaaaaaaaaaa#64)),
                          LeanLLVM.Instr.binop
                            "%and7.i.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and6.i.i")
                            (LeanLLVM.Operand.reg "%add.i.i"),
                          LeanLLVM.Instr.binop
                            "%and8.i.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%not4.i.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x5555555555555555#64)),
                          LeanLLVM.Instr.binop
                            "%and9.i.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and8.i.i")
                            (LeanLLVM.Operand.reg "%add5.i.i"),
                          LeanLLVM.Instr.binop
                            "%and11.i.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and.i.i")
                            (LeanLLVM.Operand.reg "%not4.i.i"),
                          LeanLLVM.Instr.binop
                            "%or.i.i"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%and7.i.i")
                            (LeanLLVM.Operand.reg "%and11.i.i"),
                          LeanLLVM.Instr.binop
                            "%or12.i.i"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%or.i.i")
                            (LeanLLVM.Operand.reg "%and9.i.i"),
                          LeanLLVM.Instr.icmp
                            "%cmp.i45.i"
                            (LeanLLVM.IPred.ult)
                            64
                            (LeanLLVM.Operand.reg "%add5.i.i")
                            (LeanLLVM.Operand.reg "%or14.i"),
                          LeanLLVM.Instr.zext "%conv13.i.i" 1 64 (LeanLLVM.Operand.reg "%cmp.i45.i"),
                          LeanLLVM.Instr.binop
                            "%shr.i.i"
                            (LeanLLVM.BinOp.lshr)
                            64
                            (LeanLLVM.Operand.reg "%conv12.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000001f#64)),
                          LeanLLVM.Instr.binop
                            "%not.i"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%or12.i.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and.i"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or.i286")
                            (LeanLLVM.Operand.reg "%not.i"),
                          LeanLLVM.Instr.vecBitcast "%11" 4 64 16 16 (LeanLLVM.Operand.reg "%2"),
                          LeanLLVM.Instr.binopVec
                            "%12"
                            (LeanLLVM.BinOp.lshr)
                            16
                            16
                            (LeanLLVM.Operand.reg "%11")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 16 16 0x0004#16)),
                          LeanLLVM.Instr.binopVec
                            "%13"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%4")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%14"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x40#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x82#8,
                                   0x14#8,
                                   0x01#8,
                                   0xa8#8,
                                   0x00#8,
                                   0x00#8,
                                   0x40#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x82#8,
                                   0x14#8,
                                   0x01#8,
                                   0xa8#8,
                                   0x00#8,
                                   0x00#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%13")],
                          LeanLLVM.Instr.vecBitcast "%15" 16 16 32 8 (LeanLLVM.Operand.reg "%12"),
                          LeanLLVM.Instr.binopVec
                            "%16"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%15")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%17"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x80#8,
                                   0x00#8,
                                   0x41#8,
                                   0x02#8,
                                   0x00#8,
                                   0x30#8,
                                   0x00#8,
                                   0x0c#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x00#8,
                                   0x41#8,
                                   0x02#8,
                                   0x00#8,
                                   0x30#8,
                                   0x00#8,
                                   0x0c#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%16")],
                          LeanLLVM.Instr.binopVec
                            "%and.i2326.i.i"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%17")
                            (LeanLLVM.Operand.reg "%14"),
                          LeanLLVM.Instr.binopVec
                            "%18"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i2326.i.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x3f#8)),
                          LeanLLVM.Instr.icmpVec
                            "%cmp.i21.i.i"
                            (LeanLLVM.IPred.eq)
                            32
                            8
                            (LeanLLVM.Operand.reg "%18")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x00#8)),
                          LeanLLVM.Instr.bitcastMask "%19" 32 (LeanLLVM.Operand.reg "%cmp.i21.i.i"),
                          LeanLLVM.Instr.binop
                            "%not.i46.i"
                            (LeanLLVM.BinOp.xor)
                            32
                            (LeanLLVM.Operand.reg "%19")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0xffffffff#32)),
                          LeanLLVM.Instr.vecBitcast "%20" 4 64 16 16 (LeanLLVM.Operand.reg "%3"),
                          LeanLLVM.Instr.binopVec
                            "%21"
                            (LeanLLVM.BinOp.lshr)
                            16
                            16
                            (LeanLLVM.Operand.reg "%20")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 16 16 0x0004#16)),
                          LeanLLVM.Instr.binopVec
                            "%22"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%5")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%23"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x40#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x82#8,
                                   0x14#8,
                                   0x01#8,
                                   0xa8#8,
                                   0x00#8,
                                   0x00#8,
                                   0x40#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x82#8,
                                   0x14#8,
                                   0x01#8,
                                   0xa8#8,
                                   0x00#8,
                                   0x00#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%22")],
                          LeanLLVM.Instr.vecBitcast "%24" 16 16 32 8 (LeanLLVM.Operand.reg "%21"),
                          LeanLLVM.Instr.binopVec
                            "%25"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%24")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%26"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x80#8,
                                   0x00#8,
                                   0x41#8,
                                   0x02#8,
                                   0x00#8,
                                   0x30#8,
                                   0x00#8,
                                   0x0c#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x00#8,
                                   0x41#8,
                                   0x02#8,
                                   0x00#8,
                                   0x30#8,
                                   0x00#8,
                                   0x0c#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%25")],
                          LeanLLVM.Instr.binopVec
                            "%and.i2326.i47.i"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%26")
                            (LeanLLVM.Operand.reg "%23"),
                          LeanLLVM.Instr.binopVec
                            "%27"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i2326.i47.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x3f#8)),
                          LeanLLVM.Instr.icmpVec
                            "%cmp.i21.i48.i"
                            (LeanLLVM.IPred.eq)
                            32
                            8
                            (LeanLLVM.Operand.reg "%27")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x00#8)),
                          LeanLLVM.Instr.bitcastMask "%28" 32 (LeanLLVM.Operand.reg "%cmp.i21.i48.i"),
                          LeanLLVM.Instr.binop
                            "%not.i49.i"
                            (LeanLLVM.BinOp.xor)
                            32
                            (LeanLLVM.Operand.reg "%28")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0xffffffff#32)),
                          LeanLLVM.Instr.zext "%conv16.i" 32 64 (LeanLLVM.Operand.reg "%not.i46.i"),
                          LeanLLVM.Instr.zext "%conv17.i" 32 64 (LeanLLVM.Operand.reg "%not.i49.i"),
                          LeanLLVM.Instr.binop
                            "%shl18.i"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%conv17.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000020#64)),
                          LeanLLVM.Instr.binop
                            "%or19.i"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%shl18.i")
                            (LeanLLVM.Operand.reg "%conv16.i"),
                          LeanLLVM.Instr.shuffleVec
                            "%29"
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i2326.i.i")
                            (LeanLLVM.Operand.reg "%and.i2326.i47.i")
                            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
                             25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
                             48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63],
                          LeanLLVM.Instr.icmpVec
                            "%30"
                            (LeanLLVM.IPred.eq)
                            64
                            8
                            (LeanLLVM.Operand.reg "%29")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 64 8 0x00#8)),
                          LeanLLVM.Instr.bitcastMask "%or23.i" 64 (LeanLLVM.Operand.reg "%30"),
                          LeanLLVM.Instr.insertelement
                            "%vecinit1.i.i.i"
                            2
                            64
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 2 64 0x0000000000000000#64))
                            (LeanLLVM.Operand.reg "%and.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                          LeanLLVM.Instr.call
                            "%31"
                            (LeanLLVM.Ty.vec 2 (LeanLLVM.Ty.int 64))
                            "llvm.x86.pclmulqdq"
                            [(LeanLLVM.Ty.vec 2 (LeanLLVM.Ty.int 64), LeanLLVM.Operand.reg "%vecinit1.i.i.i"),
                             (LeanLLVM.Ty.vec 2 (LeanLLVM.Ty.int 64),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector 64 [0xffffffffffffffff#64, 0x0000000000000000#64])),
                             (LeanLLVM.Ty.int 8, LeanLLVM.Operand.imm (LeanLLVM.Const.int 8 0x00#8))],
                          LeanLLVM.Instr.extractelement
                            "%vecext.i.i.i"
                            2
                            64
                            (LeanLLVM.Operand.reg "%31")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                          LeanLLVM.Instr.binop
                            "%xor.i"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%vecext.i.i.i")
                            (LeanLLVM.Operand.reg "%st.sroa.15.0507"),
                          LeanLLVM.Instr.binop
                            "%shr.i"
                            (LeanLLVM.BinOp.ashr)
                            64
                            (LeanLLVM.Operand.reg "%xor.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000003f#64)),
                          LeanLLVM.Instr.binop
                            "%not8"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%xor.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%32"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%and.i")
                            (LeanLLVM.Operand.reg "%xor.i"),
                          LeanLLVM.Instr.binop
                            "%33"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%32")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and9"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or23.i")
                            (LeanLLVM.Operand.reg "%33"),
                          LeanLLVM.Instr.binop
                            "%and11"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or19.i")
                            (LeanLLVM.Operand.reg "%not8"),
                          LeanLLVM.Instr.binop
                            "%shl12"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%and9")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000001#64)),
                          LeanLLVM.Instr.binop
                            "%or13"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%shl12")
                            (LeanLLVM.Operand.reg "%prevS.0511"),
                          LeanLLVM.Instr.binop
                            "%not14"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%or13")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and15"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and9")
                            (LeanLLVM.Operand.reg "%not14"),
                          LeanLLVM.Instr.binop
                            "%34"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%and11")
                            (LeanLLVM.Operand.reg "%and15"),
                          LeanLLVM.Instr.binop
                            "%or16"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%34")
                            (LeanLLVM.Operand.reg "%and.i"),
                          LeanLLVM.Instr.binop
                            "%shr17"
                            (LeanLLVM.BinOp.lshr)
                            64
                            (LeanLLVM.Operand.reg "%and9")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000003f#64)),
                          LeanLLVM.Instr.gep
                            "%arrayidx"
                            (LeanLLVM.Ty.int 64)
                            (LeanLLVM.Operand.reg "%ent")
                            (LeanLLVM.Operand.reg "%i.0510"),
                          LeanLLVM.Instr.store
                            (LeanLLVM.Ty.int 64)
                            (LeanLLVM.Operand.reg "%or16")
                            (LeanLLVM.Operand.reg "%arrayidx")],
               term := LeanLLVM.Term.condbr (LeanLLVM.Operand.reg "%tobool.not") "if.end" "if.then" },
             { name := "if.then",
               instrs := [LeanLLVM.Instr.shuffleVec
                            "%35"
                            4
                            64
                            (LeanLLVM.Operand.reg "%2")
                            (LeanLLVM.Operand.reg "%3")
                            [0, 1, 2, 3, 4, 5, 6, 7],
                          LeanLLVM.Instr.vecBitcast "%36" 8 64 64 8 (LeanLLVM.Operand.reg "%35"),
                          LeanLLVM.Instr.icmpVec
                            "%37"
                            (LeanLLVM.IPred.ult)
                            64
                            8
                            (LeanLLVM.Operand.reg "%36")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 64 8 0x20#8)),
                          LeanLLVM.Instr.bitcastMask "%or.i290" 64 (LeanLLVM.Operand.reg "%37"),
                          LeanLLVM.Instr.callVoid
                            "leanllvm_json_escape_list"
                            [(LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%or14.i"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%or.i290"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%xor.i"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%i.0510"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%xp"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%nxp"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%xcarry")]],
               term := LeanLLVM.Term.br "if.end" },
             { name := "if.end",
               instrs := [LeanLLVM.Instr.binopVec
                            "%or.i285"
                            (LeanLLVM.BinOp.or)
                            4
                            64
                            (LeanLLVM.Operand.reg "%3")
                            (LeanLLVM.Operand.reg "%2"),
                          LeanLLVM.Instr.call
                            "%38"
                            (LeanLLVM.Ty.int 32)
                            "llvm.x86.avx.ptestz.256"
                            [(LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64), LeanLLVM.Operand.reg "%or.i285"),
                             (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64),
                              LeanLLVM.Operand.imm (LeanLLVM.Const.splat 4 64 0x8080808080808080#64))],
                          LeanLLVM.Instr.icmp
                            "%tobool22.not"
                            (LeanLLVM.IPred.eq)
                            32
                            (LeanLLVM.Operand.reg "%38")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0x00000000#32))],
               term := LeanLLVM.Term.condbr (LeanLLVM.Operand.reg "%tobool22.not") "if.then38" "for.inc" },
             { name := "for.inc",
               instrs := [LeanLLVM.Instr.binop
                            "%inc"
                            (LeanLLVM.BinOp.add)
                            64
                            (LeanLLVM.Operand.reg "%i.0510")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000001#64)),
                          LeanLLVM.Instr.icmp
                            "%exitcond.not"
                            (LeanLLVM.IPred.eq)
                            64
                            (LeanLLVM.Operand.reg "%inc")
                            (LeanLLVM.Operand.reg "%shr")],
               term := LeanLLVM.Term.condbr (LeanLLVM.Operand.reg "%exitcond.not") "for.end101" "for.body" },
             { name := "if.then38",
               instrs := [LeanLLVM.Instr.gep
                            "%add.ptr5.le"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000020#64)),
                          LeanLLVM.Instr.load
                            "%39"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr"),
                          LeanLLVM.Instr.load
                            "%40"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr5.le"),
                          LeanLLVM.Instr.binopVec
                            "%or.i284"
                            (LeanLLVM.BinOp.or)
                            4
                            64
                            (LeanLLVM.Operand.reg "%40")
                            (LeanLLVM.Operand.reg "%39"),
                          LeanLLVM.Instr.gep
                            "%add.ptr.i.i"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.load
                            "%41"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr.i.i"),
                          LeanLLVM.Instr.gep
                            "%add.ptr3.i.i"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xfffffffffffffffe#64)),
                          LeanLLVM.Instr.load
                            "%42"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            (LeanLLVM.Operand.reg "%add.ptr3.i.i"),
                          LeanLLVM.Instr.gep
                            "%add.ptr5.i.i"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xfffffffffffffffd#64)),
                          LeanLLVM.Instr.load
                            "%43"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            (LeanLLVM.Operand.reg "%add.ptr5.i.i"),
                          LeanLLVM.Instr.vecBitcast "%44" 4 64 32 8 (LeanLLVM.Operand.reg "%41"),
                          LeanLLVM.Instr.binopVec
                            "%45"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%44")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%46"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0xe7#8,
                                   0xa3#8,
                                   0x83#8,
                                   0x83#8,
                                   0x8b#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xdb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xe7#8,
                                   0xa3#8,
                                   0x83#8,
                                   0x83#8,
                                   0x8b#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xdb#8,
                                   0xcb#8,
                                   0xcb#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%45")],
                          LeanLLVM.Instr.vecBitcast "%47" 4 64 16 16 (LeanLLVM.Operand.reg "%41"),
                          LeanLLVM.Instr.binopVec
                            "%48"
                            (LeanLLVM.BinOp.lshr)
                            16
                            16
                            (LeanLLVM.Operand.reg "%47")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 16 16 0x0004#16)),
                          LeanLLVM.Instr.vecBitcast "%49" 16 16 32 8 (LeanLLVM.Operand.reg "%48"),
                          LeanLLVM.Instr.binopVec
                            "%50"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%49")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%51"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x21#8,
                                   0x01#8,
                                   0x15#8,
                                   0x49#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x21#8,
                                   0x01#8,
                                   0x15#8,
                                   0x49#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%50")],
                          LeanLLVM.Instr.binopVec
                            "%and.i3741.i.i"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%51")
                            (LeanLLVM.Operand.reg "%46"),
                          LeanLLVM.Instr.vecBitcast "%52" 4 64 16 16 (LeanLLVM.Operand.reg "%39"),
                          LeanLLVM.Instr.binopVec
                            "%53"
                            (LeanLLVM.BinOp.lshr)
                            16
                            16
                            (LeanLLVM.Operand.reg "%52")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 16 16 0x0004#16)),
                          LeanLLVM.Instr.vecBitcast "%54" 16 16 32 8 (LeanLLVM.Operand.reg "%53"),
                          LeanLLVM.Instr.binopVec
                            "%55"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%54")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%56"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0xe6#8,
                                   0xae#8,
                                   0xba#8,
                                   0xba#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0xe6#8,
                                   0xae#8,
                                   0xba#8,
                                   0xba#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%55")],
                          LeanLLVM.Instr.binopVec
                            "%and.i3542.i.i"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i3741.i.i")
                            (LeanLLVM.Operand.reg "%56"),
                          LeanLLVM.Instr.vecBitcast "%and.i35.i.i" 32 8 4 64 (LeanLLVM.Operand.reg "%and.i3542.i.i"),
                          LeanLLVM.Instr.call
                            "%elt.sat.i40.i.i"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.usub.sat.v32i8"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%42"),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x60#8))],
                          LeanLLVM.Instr.call
                            "%elt.sat.i.i.i"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.usub.sat.v32i8"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%43"),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x70#8))],
                          LeanLLVM.Instr.binopVec
                            "%or.i43.i.i"
                            (LeanLLVM.BinOp.or)
                            32
                            8
                            (LeanLLVM.Operand.reg "%elt.sat.i.i.i")
                            (LeanLLVM.Operand.reg "%elt.sat.i40.i.i"),
                          LeanLLVM.Instr.vecBitcast "%or.i.i.i" 32 8 4 64 (LeanLLVM.Operand.reg "%or.i43.i.i"),
                          LeanLLVM.Instr.binopVec
                            "%and.i.i.i"
                            (LeanLLVM.BinOp.and)
                            4
                            64
                            (LeanLLVM.Operand.reg "%or.i.i.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 4 64 0x8080808080808080#64)),
                          LeanLLVM.Instr.binopVec
                            "%xor.i.i.i"
                            (LeanLLVM.BinOp.xor)
                            4
                            64
                            (LeanLLVM.Operand.reg "%and.i.i.i")
                            (LeanLLVM.Operand.reg "%and.i35.i.i"),
                          LeanLLVM.Instr.gep
                            "%add.ptr.i4.i"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000001f#64)),
                          LeanLLVM.Instr.load
                            "%57"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr.i4.i"),
                          LeanLLVM.Instr.gep
                            "%add.ptr3.i5.i"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000001e#64)),
                          LeanLLVM.Instr.load
                            "%58"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            (LeanLLVM.Operand.reg "%add.ptr3.i5.i"),
                          LeanLLVM.Instr.gep
                            "%add.ptr5.i6.i"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000001d#64)),
                          LeanLLVM.Instr.load
                            "%59"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            (LeanLLVM.Operand.reg "%add.ptr5.i6.i"),
                          LeanLLVM.Instr.vecBitcast "%60" 4 64 32 8 (LeanLLVM.Operand.reg "%57"),
                          LeanLLVM.Instr.binopVec
                            "%61"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%60")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%62"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0xe7#8,
                                   0xa3#8,
                                   0x83#8,
                                   0x83#8,
                                   0x8b#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xdb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xe7#8,
                                   0xa3#8,
                                   0x83#8,
                                   0x83#8,
                                   0x8b#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xdb#8,
                                   0xcb#8,
                                   0xcb#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%61")],
                          LeanLLVM.Instr.vecBitcast "%63" 4 64 16 16 (LeanLLVM.Operand.reg "%57"),
                          LeanLLVM.Instr.binopVec
                            "%64"
                            (LeanLLVM.BinOp.lshr)
                            16
                            16
                            (LeanLLVM.Operand.reg "%63")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 16 16 0x0004#16)),
                          LeanLLVM.Instr.vecBitcast "%65" 16 16 32 8 (LeanLLVM.Operand.reg "%64"),
                          LeanLLVM.Instr.binopVec
                            "%66"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%65")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%67"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x21#8,
                                   0x01#8,
                                   0x15#8,
                                   0x49#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x21#8,
                                   0x01#8,
                                   0x15#8,
                                   0x49#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%66")],
                          LeanLLVM.Instr.binopVec
                            "%and.i3741.i7.i"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%67")
                            (LeanLLVM.Operand.reg "%62"),
                          LeanLLVM.Instr.vecBitcast "%68" 4 64 16 16 (LeanLLVM.Operand.reg "%40"),
                          LeanLLVM.Instr.binopVec
                            "%69"
                            (LeanLLVM.BinOp.lshr)
                            16
                            16
                            (LeanLLVM.Operand.reg "%68")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 16 16 0x0004#16)),
                          LeanLLVM.Instr.vecBitcast "%70" 16 16 32 8 (LeanLLVM.Operand.reg "%69"),
                          LeanLLVM.Instr.binopVec
                            "%71"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%70")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%72"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0xe6#8,
                                   0xae#8,
                                   0xba#8,
                                   0xba#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0xe6#8,
                                   0xae#8,
                                   0xba#8,
                                   0xba#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%71")],
                          LeanLLVM.Instr.binopVec
                            "%and.i3542.i8.i"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i3741.i7.i")
                            (LeanLLVM.Operand.reg "%72"),
                          LeanLLVM.Instr.vecBitcast "%and.i35.i9.i" 32 8 4 64 (LeanLLVM.Operand.reg "%and.i3542.i8.i"),
                          LeanLLVM.Instr.call
                            "%elt.sat.i40.i10.i"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.usub.sat.v32i8"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%58"),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x60#8))],
                          LeanLLVM.Instr.call
                            "%elt.sat.i.i11.i"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.usub.sat.v32i8"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%59"),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x70#8))],
                          LeanLLVM.Instr.binopVec
                            "%or.i43.i12.i"
                            (LeanLLVM.BinOp.or)
                            32
                            8
                            (LeanLLVM.Operand.reg "%elt.sat.i.i11.i")
                            (LeanLLVM.Operand.reg "%elt.sat.i40.i10.i"),
                          LeanLLVM.Instr.vecBitcast "%or.i.i13.i" 32 8 4 64 (LeanLLVM.Operand.reg "%or.i43.i12.i"),
                          LeanLLVM.Instr.binopVec
                            "%and.i.i14.i"
                            (LeanLLVM.BinOp.and)
                            4
                            64
                            (LeanLLVM.Operand.reg "%or.i.i13.i")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 4 64 0x8080808080808080#64)),
                          LeanLLVM.Instr.binopVec
                            "%xor.i.i15.i"
                            (LeanLLVM.BinOp.xor)
                            4
                            64
                            (LeanLLVM.Operand.reg "%and.i.i14.i")
                            (LeanLLVM.Operand.reg "%and.i35.i9.i"),
                          LeanLLVM.Instr.binopVec
                            "%or.i.i291"
                            (LeanLLVM.BinOp.or)
                            4
                            64
                            (LeanLLVM.Operand.reg "%xor.i.i15.i")
                            (LeanLLVM.Operand.reg "%xor.i.i.i"),
                          LeanLLVM.Instr.binop
                            "%inc49"
                            (LeanLLVM.BinOp.add)
                            64
                            (LeanLLVM.Operand.reg "%i.0510")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000001#64))],
               term := LeanLLVM.Term.br "if.end50" },
             { name := "if.end50",
               instrs := [LeanLLVM.Instr.phi
                            "%prevS.1491"
                            (LeanLLVM.Ty.int 64)
                            [("if.then38", LeanLLVM.Operand.reg "%shr17"),
                             ("entry", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64))],
                          LeanLLVM.Instr.phi
                            "%st.sroa.0.1489"
                            (LeanLLVM.Ty.int 64)
                            [("if.then38", LeanLLVM.Operand.reg "%shr.i.i"),
                             ("entry", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64))],
                          LeanLLVM.Instr.phi
                            "%st.sroa.9.1487"
                            (LeanLLVM.Ty.int 64)
                            [("if.then38", LeanLLVM.Operand.reg "%conv13.i.i"),
                             ("entry", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64))],
                          LeanLLVM.Instr.phi
                            "%st.sroa.15.1485"
                            (LeanLLVM.Ty.int 64)
                            [("if.then38", LeanLLVM.Operand.reg "%shr.i"),
                             ("entry", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64))],
                          LeanLLVM.Instr.phi
                            "%prev_ascii.0"
                            (LeanLLVM.Ty.int 32)
                            [("if.then38", LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0x00000000#32)),
                             ("entry", LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0x00000001#32))],
                          LeanLLVM.Instr.phi
                            "%u8k.0"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            [("if.then38", LeanLLVM.Operand.reg "%or.i.i291"),
                             ("entry", LeanLLVM.Operand.imm (LeanLLVM.Const.splat 4 64 0x0000000000000000#64))],
                          LeanLLVM.Instr.phi
                            "%ascii.0"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            [("if.then38", LeanLLVM.Operand.reg "%or.i284"),
                             ("entry", LeanLLVM.Operand.imm (LeanLLVM.Const.splat 4 64 0x0000000000000000#64))],
                          LeanLLVM.Instr.phi
                            "%i.1"
                            (LeanLLVM.Ty.int 64)
                            [("if.then38", LeanLLVM.Operand.reg "%inc49"),
                             ("entry", LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64))],
                          LeanLLVM.Instr.icmp
                            "%cmp52516"
                            (LeanLLVM.IPred.ult)
                            64
                            (LeanLLVM.Operand.reg "%i.1")
                            (LeanLLVM.Operand.reg "%shr")],
               term := LeanLLVM.Term.condbr (LeanLLVM.Operand.reg "%cmp52516") "for.body54.lr.ph" "for.end101" },
             { name := "for.body54.lr.ph",
               instrs := [LeanLLVM.Instr.icmp
                            "%tobool87"
                            (LeanLLVM.IPred.eq)
                            32
                            (LeanLLVM.Operand.reg "%conv")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0x00000000#32)),
                          LeanLLVM.Instr.binop
                            "%and94"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%arm")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000002#64)),
                          LeanLLVM.Instr.icmp
                            "%tobool95.not"
                            (LeanLLVM.IPred.eq)
                            64
                            (LeanLLVM.Operand.reg "%and94")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64))],
               term := LeanLLVM.Term.br "for.body54" },
             { name := "for.body54",
               instrs := [LeanLLVM.Instr.phi
                            "%prevS.2524"
                            (LeanLLVM.Ty.int 64)
                            [("for.body54.lr.ph", LeanLLVM.Operand.reg "%prevS.1491"),
                             ("if.end98", LeanLLVM.Operand.reg "%shr85")],
                          LeanLLVM.Instr.phi
                            "%i.2523"
                            (LeanLLVM.Ty.int 64)
                            [("for.body54.lr.ph", LeanLLVM.Operand.reg "%i.1"),
                             ("if.end98", LeanLLVM.Operand.reg "%inc100")],
                          LeanLLVM.Instr.phi
                            "%ascii.1522"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            [("for.body54.lr.ph", LeanLLVM.Operand.reg "%ascii.0"),
                             ("if.end98", LeanLLVM.Operand.reg "%or.i282")],
                          LeanLLVM.Instr.phi
                            "%u8k.1521"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            [("for.body54.lr.ph", LeanLLVM.Operand.reg "%u8k.0"),
                             ("if.end98", LeanLLVM.Operand.reg "%u8k.2")],
                          LeanLLVM.Instr.phi
                            "%prev_ascii.1520"
                            (LeanLLVM.Ty.int 32)
                            [("for.body54.lr.ph", LeanLLVM.Operand.reg "%prev_ascii.0"),
                             ("if.end98", LeanLLVM.Operand.reg "%75")],
                          LeanLLVM.Instr.phi
                            "%st.sroa.0.2519"
                            (LeanLLVM.Ty.int 64)
                            [("for.body54.lr.ph", LeanLLVM.Operand.reg "%st.sroa.0.1489"),
                             ("if.end98", LeanLLVM.Operand.reg "%shr.i.i325")],
                          LeanLLVM.Instr.phi
                            "%st.sroa.9.2518"
                            (LeanLLVM.Ty.int 64)
                            [("for.body54.lr.ph", LeanLLVM.Operand.reg "%st.sroa.9.1487"),
                             ("if.end98", LeanLLVM.Operand.reg "%conv13.i.i324")],
                          LeanLLVM.Instr.phi
                            "%st.sroa.15.2517"
                            (LeanLLVM.Ty.int 64)
                            [("for.body54.lr.ph", LeanLLVM.Operand.reg "%st.sroa.15.1485"),
                             ("if.end98", LeanLLVM.Operand.reg "%shr.i348")],
                          LeanLLVM.Instr.binop
                            "%shl56"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%i.2523")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000006#64)),
                          LeanLLVM.Instr.gep
                            "%add.ptr57"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%b")
                            (LeanLLVM.Operand.reg "%shl56"),
                          LeanLLVM.Instr.load
                            "%73"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr57"),
                          LeanLLVM.Instr.gep
                            "%add.ptr61"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr57")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000020#64)),
                          LeanLLVM.Instr.load
                            "%74"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr61"),
                          LeanLLVM.Instr.binopVec
                            "%or.i283"
                            (LeanLLVM.BinOp.or)
                            4
                            64
                            (LeanLLVM.Operand.reg "%74")
                            (LeanLLVM.Operand.reg "%73"),
                          LeanLLVM.Instr.call
                            "%75"
                            (LeanLLVM.Ty.int 32)
                            "llvm.x86.avx.ptestz.256"
                            [(LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64), LeanLLVM.Operand.reg "%or.i283"),
                             (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64),
                              LeanLLVM.Operand.imm (LeanLLVM.Const.splat 4 64 0x8080808080808080#64))],
                          LeanLLVM.Instr.binopVec
                            "%or.i282"
                            (LeanLLVM.BinOp.or)
                            4
                            64
                            (LeanLLVM.Operand.reg "%or.i283")
                            (LeanLLVM.Operand.reg "%ascii.1522"),
                          LeanLLVM.Instr.vecBitcast "%76" 4 64 32 8 (LeanLLVM.Operand.reg "%73"),
                          LeanLLVM.Instr.vecBitcast "%77" 4 64 32 8 (LeanLLVM.Operand.reg "%74"),
                          LeanLLVM.Instr.shuffleVec
                            "%78"
                            4
                            64
                            (LeanLLVM.Operand.reg "%73")
                            (LeanLLVM.Operand.reg "%74")
                            [0, 1, 2, 3, 4, 5, 6, 7],
                          LeanLLVM.Instr.vecBitcast "%79" 8 64 64 8 (LeanLLVM.Operand.reg "%78"),
                          LeanLLVM.Instr.icmpVec
                            "%80"
                            (LeanLLVM.IPred.eq)
                            64
                            8
                            (LeanLLVM.Operand.reg "%79")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 64 8 0x22#8)),
                          LeanLLVM.Instr.bitcastMask "%or.i297" 64 (LeanLLVM.Operand.reg "%80"),
                          LeanLLVM.Instr.icmpVec
                            "%cmp.i39.i298"
                            (LeanLLVM.IPred.eq)
                            32
                            8
                            (LeanLLVM.Operand.reg "%76")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x5c#8)),
                          LeanLLVM.Instr.bitcastMask "%81" 32 (LeanLLVM.Operand.reg "%cmp.i39.i298"),
                          LeanLLVM.Instr.zext "%conv9.i299" 32 64 (LeanLLVM.Operand.reg "%81"),
                          LeanLLVM.Instr.icmpVec
                            "%cmp.i.i300"
                            (LeanLLVM.IPred.eq)
                            32
                            8
                            (LeanLLVM.Operand.reg "%77")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x5c#8)),
                          LeanLLVM.Instr.bitcastMask "%82" 32 (LeanLLVM.Operand.reg "%cmp.i.i300"),
                          LeanLLVM.Instr.zext "%conv12.i301" 32 64 (LeanLLVM.Operand.reg "%82"),
                          LeanLLVM.Instr.binop
                            "%shl13.i302"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%conv12.i301")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000020#64)),
                          LeanLLVM.Instr.binop
                            "%or14.i303"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%shl13.i302")
                            (LeanLLVM.Operand.reg "%conv9.i299"),
                          LeanLLVM.Instr.binop
                            "%and.i.i305"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%st.sroa.0.2519")
                            (LeanLLVM.Operand.reg "%st.sroa.9.2518"),
                          LeanLLVM.Instr.binop
                            "%shl.i.i306"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%or14.i303")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000001#64)),
                          LeanLLVM.Instr.binop
                            "%not.i.i307"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%shl.i.i306")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and1.i.i308"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or14.i303")
                            (LeanLLVM.Operand.reg "%not.i.i307"),
                          LeanLLVM.Instr.binop
                            "%xor.i.i309"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%and.i.i305")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x5555555555555555#64)),
                          LeanLLVM.Instr.binop
                            "%and2.i.i310"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and1.i.i308")
                            (LeanLLVM.Operand.reg "%xor.i.i309"),
                          LeanLLVM.Instr.binop
                            "%xor3.i.i311"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%and2.i.i310")
                            (LeanLLVM.Operand.reg "%and1.i.i308"),
                          LeanLLVM.Instr.binop
                            "%not4.i.i312"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%or14.i303")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%add.i.i313"
                            (LeanLLVM.BinOp.add)
                            64
                            (LeanLLVM.Operand.reg "%and2.i.i310")
                            (LeanLLVM.Operand.reg "%or14.i303"),
                          LeanLLVM.Instr.binop
                            "%add5.i.i314"
                            (LeanLLVM.BinOp.add)
                            64
                            (LeanLLVM.Operand.reg "%xor3.i.i311")
                            (LeanLLVM.Operand.reg "%or14.i303"),
                          LeanLLVM.Instr.binop
                            "%and6.i.i315"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%not4.i.i312")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xaaaaaaaaaaaaaaaa#64)),
                          LeanLLVM.Instr.binop
                            "%and7.i.i316"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and6.i.i315")
                            (LeanLLVM.Operand.reg "%add.i.i313"),
                          LeanLLVM.Instr.binop
                            "%and8.i.i317"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%not4.i.i312")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x5555555555555555#64)),
                          LeanLLVM.Instr.binop
                            "%and9.i.i318"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and8.i.i317")
                            (LeanLLVM.Operand.reg "%add5.i.i314"),
                          LeanLLVM.Instr.binop
                            "%and11.i.i320"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and.i.i305")
                            (LeanLLVM.Operand.reg "%not4.i.i312"),
                          LeanLLVM.Instr.binop
                            "%or.i.i321"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%and7.i.i316")
                            (LeanLLVM.Operand.reg "%and11.i.i320"),
                          LeanLLVM.Instr.binop
                            "%or12.i.i322"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%or.i.i321")
                            (LeanLLVM.Operand.reg "%and9.i.i318"),
                          LeanLLVM.Instr.icmp
                            "%cmp.i45.i323"
                            (LeanLLVM.IPred.ult)
                            64
                            (LeanLLVM.Operand.reg "%add5.i.i314")
                            (LeanLLVM.Operand.reg "%or14.i303"),
                          LeanLLVM.Instr.zext "%conv13.i.i324" 1 64 (LeanLLVM.Operand.reg "%cmp.i45.i323"),
                          LeanLLVM.Instr.binop
                            "%shr.i.i325"
                            (LeanLLVM.BinOp.lshr)
                            64
                            (LeanLLVM.Operand.reg "%conv12.i301")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000001f#64)),
                          LeanLLVM.Instr.binop
                            "%not.i326"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%or12.i.i322")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and.i327"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or.i297")
                            (LeanLLVM.Operand.reg "%not.i326"),
                          LeanLLVM.Instr.vecBitcast "%83" 4 64 16 16 (LeanLLVM.Operand.reg "%73"),
                          LeanLLVM.Instr.binopVec
                            "%84"
                            (LeanLLVM.BinOp.lshr)
                            16
                            16
                            (LeanLLVM.Operand.reg "%83")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 16 16 0x0004#16)),
                          LeanLLVM.Instr.binopVec
                            "%85"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%76")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%86"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x40#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x82#8,
                                   0x14#8,
                                   0x01#8,
                                   0xa8#8,
                                   0x00#8,
                                   0x00#8,
                                   0x40#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x82#8,
                                   0x14#8,
                                   0x01#8,
                                   0xa8#8,
                                   0x00#8,
                                   0x00#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%85")],
                          LeanLLVM.Instr.vecBitcast "%87" 16 16 32 8 (LeanLLVM.Operand.reg "%84"),
                          LeanLLVM.Instr.binopVec
                            "%88"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%87")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%89"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x80#8,
                                   0x00#8,
                                   0x41#8,
                                   0x02#8,
                                   0x00#8,
                                   0x30#8,
                                   0x00#8,
                                   0x0c#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x00#8,
                                   0x41#8,
                                   0x02#8,
                                   0x00#8,
                                   0x30#8,
                                   0x00#8,
                                   0x0c#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%88")],
                          LeanLLVM.Instr.binopVec
                            "%and.i2326.i.i328"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%89")
                            (LeanLLVM.Operand.reg "%86"),
                          LeanLLVM.Instr.binopVec
                            "%90"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i2326.i.i328")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x3f#8)),
                          LeanLLVM.Instr.icmpVec
                            "%cmp.i21.i.i329"
                            (LeanLLVM.IPred.eq)
                            32
                            8
                            (LeanLLVM.Operand.reg "%90")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x00#8)),
                          LeanLLVM.Instr.bitcastMask "%91" 32 (LeanLLVM.Operand.reg "%cmp.i21.i.i329"),
                          LeanLLVM.Instr.binop
                            "%not.i46.i330"
                            (LeanLLVM.BinOp.xor)
                            32
                            (LeanLLVM.Operand.reg "%91")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0xffffffff#32)),
                          LeanLLVM.Instr.vecBitcast "%92" 4 64 16 16 (LeanLLVM.Operand.reg "%74"),
                          LeanLLVM.Instr.binopVec
                            "%93"
                            (LeanLLVM.BinOp.lshr)
                            16
                            16
                            (LeanLLVM.Operand.reg "%92")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 16 16 0x0004#16)),
                          LeanLLVM.Instr.binopVec
                            "%94"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%77")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%95"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x40#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x82#8,
                                   0x14#8,
                                   0x01#8,
                                   0xa8#8,
                                   0x00#8,
                                   0x00#8,
                                   0x40#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x82#8,
                                   0x14#8,
                                   0x01#8,
                                   0xa8#8,
                                   0x00#8,
                                   0x00#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%94")],
                          LeanLLVM.Instr.vecBitcast "%96" 16 16 32 8 (LeanLLVM.Operand.reg "%93"),
                          LeanLLVM.Instr.binopVec
                            "%97"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%96")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%98"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x80#8,
                                   0x00#8,
                                   0x41#8,
                                   0x02#8,
                                   0x00#8,
                                   0x30#8,
                                   0x00#8,
                                   0x0c#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x00#8,
                                   0x41#8,
                                   0x02#8,
                                   0x00#8,
                                   0x30#8,
                                   0x00#8,
                                   0x0c#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%97")],
                          LeanLLVM.Instr.binopVec
                            "%and.i2326.i47.i332"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%98")
                            (LeanLLVM.Operand.reg "%95"),
                          LeanLLVM.Instr.binopVec
                            "%99"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i2326.i47.i332")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x3f#8)),
                          LeanLLVM.Instr.icmpVec
                            "%cmp.i21.i48.i333"
                            (LeanLLVM.IPred.eq)
                            32
                            8
                            (LeanLLVM.Operand.reg "%99")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x00#8)),
                          LeanLLVM.Instr.bitcastMask "%100" 32 (LeanLLVM.Operand.reg "%cmp.i21.i48.i333"),
                          LeanLLVM.Instr.binop
                            "%not.i49.i334"
                            (LeanLLVM.BinOp.xor)
                            32
                            (LeanLLVM.Operand.reg "%100")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0xffffffff#32)),
                          LeanLLVM.Instr.zext "%conv16.i336" 32 64 (LeanLLVM.Operand.reg "%not.i46.i330"),
                          LeanLLVM.Instr.zext "%conv17.i337" 32 64 (LeanLLVM.Operand.reg "%not.i49.i334"),
                          LeanLLVM.Instr.binop
                            "%shl18.i338"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%conv17.i337")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000020#64)),
                          LeanLLVM.Instr.binop
                            "%or19.i339"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%shl18.i338")
                            (LeanLLVM.Operand.reg "%conv16.i336"),
                          LeanLLVM.Instr.shuffleVec
                            "%101"
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i2326.i.i328")
                            (LeanLLVM.Operand.reg "%and.i2326.i47.i332")
                            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
                             25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
                             48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63],
                          LeanLLVM.Instr.icmpVec
                            "%102"
                            (LeanLLVM.IPred.eq)
                            64
                            8
                            (LeanLLVM.Operand.reg "%101")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 64 8 0x00#8)),
                          LeanLLVM.Instr.bitcastMask "%or23.i343" 64 (LeanLLVM.Operand.reg "%102"),
                          LeanLLVM.Instr.insertelement
                            "%vecinit1.i.i.i344"
                            2
                            64
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 2 64 0x0000000000000000#64))
                            (LeanLLVM.Operand.reg "%and.i327")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                          LeanLLVM.Instr.call
                            "%103"
                            (LeanLLVM.Ty.vec 2 (LeanLLVM.Ty.int 64))
                            "llvm.x86.pclmulqdq"
                            [(LeanLLVM.Ty.vec 2 (LeanLLVM.Ty.int 64), LeanLLVM.Operand.reg "%vecinit1.i.i.i344"),
                             (LeanLLVM.Ty.vec 2 (LeanLLVM.Ty.int 64),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector 64 [0xffffffffffffffff#64, 0x0000000000000000#64])),
                             (LeanLLVM.Ty.int 8, LeanLLVM.Operand.imm (LeanLLVM.Const.int 8 0x00#8))],
                          LeanLLVM.Instr.extractelement
                            "%vecext.i.i.i345"
                            2
                            64
                            (LeanLLVM.Operand.reg "%103")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                          LeanLLVM.Instr.binop
                            "%xor.i347"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%vecext.i.i.i345")
                            (LeanLLVM.Operand.reg "%st.sroa.15.2517"),
                          LeanLLVM.Instr.binop
                            "%shr.i348"
                            (LeanLLVM.BinOp.ashr)
                            64
                            (LeanLLVM.Operand.reg "%xor.i347")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000003f#64)),
                          LeanLLVM.Instr.binop
                            "%not74"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%xor.i347")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%104"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%and.i327")
                            (LeanLLVM.Operand.reg "%xor.i347"),
                          LeanLLVM.Instr.binop
                            "%105"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%104")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and75"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or23.i343")
                            (LeanLLVM.Operand.reg "%105"),
                          LeanLLVM.Instr.binop
                            "%and78"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or19.i339")
                            (LeanLLVM.Operand.reg "%not74"),
                          LeanLLVM.Instr.binop
                            "%shl80"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%and75")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000001#64)),
                          LeanLLVM.Instr.binop
                            "%or81"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%shl80")
                            (LeanLLVM.Operand.reg "%prevS.2524"),
                          LeanLLVM.Instr.binop
                            "%not82"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%or81")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and83"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and75")
                            (LeanLLVM.Operand.reg "%not82"),
                          LeanLLVM.Instr.binop
                            "%106"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%and78")
                            (LeanLLVM.Operand.reg "%and83"),
                          LeanLLVM.Instr.binop
                            "%or84"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%106")
                            (LeanLLVM.Operand.reg "%and.i327"),
                          LeanLLVM.Instr.binop
                            "%shr85"
                            (LeanLLVM.BinOp.lshr)
                            64
                            (LeanLLVM.Operand.reg "%and75")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000003f#64)),
                          LeanLLVM.Instr.gep
                            "%arrayidx86"
                            (LeanLLVM.Ty.int 64)
                            (LeanLLVM.Operand.reg "%ent")
                            (LeanLLVM.Operand.reg "%i.2523"),
                          LeanLLVM.Instr.store
                            (LeanLLVM.Ty.int 64)
                            (LeanLLVM.Operand.reg "%or84")
                            (LeanLLVM.Operand.reg "%arrayidx86"),
                          LeanLLVM.Instr.icmp
                            "%tobool88"
                            (LeanLLVM.IPred.ne)
                            32
                            (LeanLLVM.Operand.reg "%75")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0x00000000#32)),
                          LeanLLVM.Instr.icmp
                            "%tobool89"
                            (LeanLLVM.IPred.ne)
                            32
                            (LeanLLVM.Operand.reg "%prev_ascii.1520")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0x00000000#32)),
                          LeanLLVM.Instr.binop
                            "%107"
                            (LeanLLVM.BinOp.and)
                            1
                            (LeanLLVM.Operand.reg "%tobool89")
                            (LeanLLVM.Operand.reg "%tobool88"),
                          LeanLLVM.Instr.select
                            "%or.cond189"
                            (LeanLLVM.Ty.int 1)
                            (LeanLLVM.Operand.reg "%tobool87")
                            (LeanLLVM.Operand.reg "%107")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 1 0x0#1))],
               term := LeanLLVM.Term.condbr (LeanLLVM.Operand.reg "%or.cond189") "if.end93" "if.then90" },
             { name := "if.then90",
               instrs := [LeanLLVM.Instr.gep
                            "%add.ptr.i.i349"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr57")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.load
                            "%108"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr.i.i349"),
                          LeanLLVM.Instr.gep
                            "%add.ptr3.i.i350"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr57")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xfffffffffffffffe#64)),
                          LeanLLVM.Instr.load
                            "%109"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            (LeanLLVM.Operand.reg "%add.ptr3.i.i350"),
                          LeanLLVM.Instr.gep
                            "%add.ptr5.i.i351"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr57")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xfffffffffffffffd#64)),
                          LeanLLVM.Instr.load
                            "%110"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            (LeanLLVM.Operand.reg "%add.ptr5.i.i351"),
                          LeanLLVM.Instr.vecBitcast "%111" 4 64 32 8 (LeanLLVM.Operand.reg "%108"),
                          LeanLLVM.Instr.binopVec
                            "%112"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%111")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%113"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0xe7#8,
                                   0xa3#8,
                                   0x83#8,
                                   0x83#8,
                                   0x8b#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xdb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xe7#8,
                                   0xa3#8,
                                   0x83#8,
                                   0x83#8,
                                   0x8b#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xdb#8,
                                   0xcb#8,
                                   0xcb#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%112")],
                          LeanLLVM.Instr.vecBitcast "%114" 4 64 16 16 (LeanLLVM.Operand.reg "%108"),
                          LeanLLVM.Instr.binopVec
                            "%115"
                            (LeanLLVM.BinOp.lshr)
                            16
                            16
                            (LeanLLVM.Operand.reg "%114")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 16 16 0x0004#16)),
                          LeanLLVM.Instr.vecBitcast "%116" 16 16 32 8 (LeanLLVM.Operand.reg "%115"),
                          LeanLLVM.Instr.binopVec
                            "%117"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%116")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%118"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x21#8,
                                   0x01#8,
                                   0x15#8,
                                   0x49#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x21#8,
                                   0x01#8,
                                   0x15#8,
                                   0x49#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%117")],
                          LeanLLVM.Instr.binopVec
                            "%and.i3741.i.i352"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%118")
                            (LeanLLVM.Operand.reg "%113"),
                          LeanLLVM.Instr.call
                            "%119"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0xe6#8,
                                   0xae#8,
                                   0xba#8,
                                   0xba#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0xe6#8,
                                   0xae#8,
                                   0xba#8,
                                   0xba#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%88")],
                          LeanLLVM.Instr.binopVec
                            "%and.i3542.i.i353"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i3741.i.i352")
                            (LeanLLVM.Operand.reg "%119"),
                          LeanLLVM.Instr.vecBitcast
                            "%and.i35.i.i354"
                            32
                            8
                            4
                            64
                            (LeanLLVM.Operand.reg "%and.i3542.i.i353"),
                          LeanLLVM.Instr.call
                            "%elt.sat.i40.i.i355"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.usub.sat.v32i8"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%109"),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x60#8))],
                          LeanLLVM.Instr.call
                            "%elt.sat.i.i.i356"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.usub.sat.v32i8"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%110"),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x70#8))],
                          LeanLLVM.Instr.binopVec
                            "%or.i43.i.i357"
                            (LeanLLVM.BinOp.or)
                            32
                            8
                            (LeanLLVM.Operand.reg "%elt.sat.i.i.i356")
                            (LeanLLVM.Operand.reg "%elt.sat.i40.i.i355"),
                          LeanLLVM.Instr.vecBitcast "%or.i.i.i358" 32 8 4 64 (LeanLLVM.Operand.reg "%or.i43.i.i357"),
                          LeanLLVM.Instr.binopVec
                            "%and.i.i.i359"
                            (LeanLLVM.BinOp.and)
                            4
                            64
                            (LeanLLVM.Operand.reg "%or.i.i.i358")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 4 64 0x8080808080808080#64)),
                          LeanLLVM.Instr.binopVec
                            "%xor.i.i.i360"
                            (LeanLLVM.BinOp.xor)
                            4
                            64
                            (LeanLLVM.Operand.reg "%and.i.i.i359")
                            (LeanLLVM.Operand.reg "%and.i35.i.i354"),
                          LeanLLVM.Instr.gep
                            "%add.ptr.i4.i361"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr57")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000001f#64)),
                          LeanLLVM.Instr.load
                            "%120"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr.i4.i361"),
                          LeanLLVM.Instr.gep
                            "%add.ptr3.i5.i362"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr57")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000001e#64)),
                          LeanLLVM.Instr.load
                            "%121"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            (LeanLLVM.Operand.reg "%add.ptr3.i5.i362"),
                          LeanLLVM.Instr.gep
                            "%add.ptr5.i6.i363"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr57")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000001d#64)),
                          LeanLLVM.Instr.load
                            "%122"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            (LeanLLVM.Operand.reg "%add.ptr5.i6.i363"),
                          LeanLLVM.Instr.vecBitcast "%123" 4 64 32 8 (LeanLLVM.Operand.reg "%120"),
                          LeanLLVM.Instr.binopVec
                            "%124"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%123")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%125"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0xe7#8,
                                   0xa3#8,
                                   0x83#8,
                                   0x83#8,
                                   0x8b#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xdb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xe7#8,
                                   0xa3#8,
                                   0x83#8,
                                   0x83#8,
                                   0x8b#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xdb#8,
                                   0xcb#8,
                                   0xcb#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%124")],
                          LeanLLVM.Instr.vecBitcast "%126" 4 64 16 16 (LeanLLVM.Operand.reg "%120"),
                          LeanLLVM.Instr.binopVec
                            "%127"
                            (LeanLLVM.BinOp.lshr)
                            16
                            16
                            (LeanLLVM.Operand.reg "%126")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 16 16 0x0004#16)),
                          LeanLLVM.Instr.vecBitcast "%128" 16 16 32 8 (LeanLLVM.Operand.reg "%127"),
                          LeanLLVM.Instr.binopVec
                            "%129"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%128")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%130"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x21#8,
                                   0x01#8,
                                   0x15#8,
                                   0x49#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x21#8,
                                   0x01#8,
                                   0x15#8,
                                   0x49#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%129")],
                          LeanLLVM.Instr.binopVec
                            "%and.i3741.i7.i364"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%130")
                            (LeanLLVM.Operand.reg "%125"),
                          LeanLLVM.Instr.call
                            "%131"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0xe6#8,
                                   0xae#8,
                                   0xba#8,
                                   0xba#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0xe6#8,
                                   0xae#8,
                                   0xba#8,
                                   0xba#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%97")],
                          LeanLLVM.Instr.binopVec
                            "%and.i3542.i8.i365"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i3741.i7.i364")
                            (LeanLLVM.Operand.reg "%131"),
                          LeanLLVM.Instr.vecBitcast
                            "%and.i35.i9.i366"
                            32
                            8
                            4
                            64
                            (LeanLLVM.Operand.reg "%and.i3542.i8.i365"),
                          LeanLLVM.Instr.call
                            "%elt.sat.i40.i10.i367"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.usub.sat.v32i8"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%121"),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x60#8))],
                          LeanLLVM.Instr.call
                            "%elt.sat.i.i11.i368"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.usub.sat.v32i8"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%122"),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x70#8))],
                          LeanLLVM.Instr.binopVec
                            "%or.i43.i12.i369"
                            (LeanLLVM.BinOp.or)
                            32
                            8
                            (LeanLLVM.Operand.reg "%elt.sat.i.i11.i368")
                            (LeanLLVM.Operand.reg "%elt.sat.i40.i10.i367"),
                          LeanLLVM.Instr.vecBitcast
                            "%or.i.i13.i370"
                            32
                            8
                            4
                            64
                            (LeanLLVM.Operand.reg "%or.i43.i12.i369"),
                          LeanLLVM.Instr.binopVec
                            "%and.i.i14.i371"
                            (LeanLLVM.BinOp.and)
                            4
                            64
                            (LeanLLVM.Operand.reg "%or.i.i13.i370")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 4 64 0x8080808080808080#64)),
                          LeanLLVM.Instr.binopVec
                            "%xor.i.i15.i372"
                            (LeanLLVM.BinOp.xor)
                            4
                            64
                            (LeanLLVM.Operand.reg "%and.i.i14.i371")
                            (LeanLLVM.Operand.reg "%and.i35.i9.i366"),
                          LeanLLVM.Instr.binopVec
                            "%132"
                            (LeanLLVM.BinOp.or)
                            4
                            64
                            (LeanLLVM.Operand.reg "%xor.i.i.i360")
                            (LeanLLVM.Operand.reg "%xor.i.i15.i372"),
                          LeanLLVM.Instr.binopVec
                            "%or.i281"
                            (LeanLLVM.BinOp.or)
                            4
                            64
                            (LeanLLVM.Operand.reg "%132")
                            (LeanLLVM.Operand.reg "%u8k.1521")],
               term := LeanLLVM.Term.br "if.end93" },
             { name := "if.end93",
               instrs := [LeanLLVM.Instr.phi
                            "%u8k.2"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            [("for.body54", LeanLLVM.Operand.reg "%u8k.1521"),
                             ("if.then90", LeanLLVM.Operand.reg "%or.i281")]],
               term := LeanLLVM.Term.condbr (LeanLLVM.Operand.reg "%tobool95.not") "if.end98" "if.then96" },
             { name := "if.then96",
               instrs := [LeanLLVM.Instr.shuffleVec
                            "%133"
                            4
                            64
                            (LeanLLVM.Operand.reg "%73")
                            (LeanLLVM.Operand.reg "%74")
                            [0, 1, 2, 3, 4, 5, 6, 7],
                          LeanLLVM.Instr.vecBitcast "%134" 8 64 64 8 (LeanLLVM.Operand.reg "%133"),
                          LeanLLVM.Instr.icmpVec
                            "%135"
                            (LeanLLVM.IPred.ult)
                            64
                            8
                            (LeanLLVM.Operand.reg "%134")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 64 8 0x20#8)),
                          LeanLLVM.Instr.bitcastMask "%or.i379" 64 (LeanLLVM.Operand.reg "%135"),
                          LeanLLVM.Instr.callVoid
                            "leanllvm_json_escape_list"
                            [(LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%or14.i303"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%or.i379"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%xor.i347"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%i.2523"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%xp"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%nxp"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%xcarry")]],
               term := LeanLLVM.Term.br "if.end98" },
             { name := "if.end98",
               instrs := [LeanLLVM.Instr.binop
                            "%inc100"
                            (LeanLLVM.BinOp.add)
                            64
                            (LeanLLVM.Operand.reg "%i.2523")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000001#64)),
                          LeanLLVM.Instr.icmp
                            "%exitcond537.not"
                            (LeanLLVM.IPred.eq)
                            64
                            (LeanLLVM.Operand.reg "%inc100")
                            (LeanLLVM.Operand.reg "%shr")],
               term := LeanLLVM.Term.condbr (LeanLLVM.Operand.reg "%exitcond537.not") "for.end101" "for.body54" },
             { name := "for.end101",
               instrs := [LeanLLVM.Instr.phi
                            "%st.sroa.15.2.lcssa"
                            (LeanLLVM.Ty.int 64)
                            [("if.end50", LeanLLVM.Operand.reg "%st.sroa.15.1485"),
                             ("if.end98", LeanLLVM.Operand.reg "%shr.i348"),
                             ("for.inc", LeanLLVM.Operand.reg "%shr.i")],
                          LeanLLVM.Instr.phi
                            "%st.sroa.9.2.lcssa"
                            (LeanLLVM.Ty.int 64)
                            [("if.end50", LeanLLVM.Operand.reg "%st.sroa.9.1487"),
                             ("if.end98", LeanLLVM.Operand.reg "%conv13.i.i324"),
                             ("for.inc", LeanLLVM.Operand.reg "%conv13.i.i")],
                          LeanLLVM.Instr.phi
                            "%st.sroa.0.2.lcssa"
                            (LeanLLVM.Ty.int 64)
                            [("if.end50", LeanLLVM.Operand.reg "%st.sroa.0.1489"),
                             ("if.end98", LeanLLVM.Operand.reg "%shr.i.i325"),
                             ("for.inc", LeanLLVM.Operand.reg "%shr.i.i")],
                          LeanLLVM.Instr.phi
                            "%prev_ascii.1.lcssa"
                            (LeanLLVM.Ty.int 32)
                            [("if.end50", LeanLLVM.Operand.reg "%prev_ascii.0"),
                             ("if.end98", LeanLLVM.Operand.reg "%75"),
                             ("for.inc", LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0x00000001#32))],
                          LeanLLVM.Instr.phi
                            "%u8k.1.lcssa"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            [("if.end50", LeanLLVM.Operand.reg "%u8k.0"),
                             ("if.end98", LeanLLVM.Operand.reg "%u8k.2"),
                             ("for.inc", LeanLLVM.Operand.imm (LeanLLVM.Const.splat 4 64 0x0000000000000000#64))],
                          LeanLLVM.Instr.phi
                            "%ascii.1.lcssa"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            [("if.end50", LeanLLVM.Operand.reg "%ascii.0"),
                             ("if.end98", LeanLLVM.Operand.reg "%or.i282"),
                             ("for.inc", LeanLLVM.Operand.imm (LeanLLVM.Const.splat 4 64 0x0000000000000000#64))],
                          LeanLLVM.Instr.phi
                            "%prevS.2.lcssa"
                            (LeanLLVM.Ty.int 64)
                            [("if.end50", LeanLLVM.Operand.reg "%prevS.1491"),
                             ("if.end98", LeanLLVM.Operand.reg "%shr85"),
                             ("for.inc", LeanLLVM.Operand.reg "%shr17")],
                          LeanLLVM.Instr.icmp
                            "%tobool102.not"
                            (LeanLLVM.IPred.eq)
                            64
                            (LeanLLVM.Operand.reg "%and")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64))],
               term := LeanLLVM.Term.condbr (LeanLLVM.Operand.reg "%tobool102.not") "if.end153" "if.then103" },
             { name := "if.then103",
               instrs := [LeanLLVM.Instr.binop
                            "%shl105"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%n")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffc0#64)),
                          LeanLLVM.Instr.gep
                            "%add.ptr106"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%b")
                            (LeanLLVM.Operand.reg "%shl105"),
                          LeanLLVM.Instr.load
                            "%136"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr106"),
                          LeanLLVM.Instr.gep
                            "%add.ptr110"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr106")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000020#64)),
                          LeanLLVM.Instr.load
                            "%137"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr110"),
                          LeanLLVM.Instr.binopVec
                            "%or.i280"
                            (LeanLLVM.BinOp.or)
                            4
                            64
                            (LeanLLVM.Operand.reg "%137")
                            (LeanLLVM.Operand.reg "%136"),
                          LeanLLVM.Instr.call
                            "%138"
                            (LeanLLVM.Ty.int 32)
                            "llvm.x86.avx.ptestz.256"
                            [(LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64), LeanLLVM.Operand.reg "%or.i280"),
                             (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64),
                              LeanLLVM.Operand.imm (LeanLLVM.Const.splat 4 64 0x8080808080808080#64))],
                          LeanLLVM.Instr.binopVec
                            "%or.i279"
                            (LeanLLVM.BinOp.or)
                            4
                            64
                            (LeanLLVM.Operand.reg "%or.i280")
                            (LeanLLVM.Operand.reg "%ascii.1.lcssa"),
                          LeanLLVM.Instr.vecBitcast "%139" 4 64 32 8 (LeanLLVM.Operand.reg "%136"),
                          LeanLLVM.Instr.vecBitcast "%140" 4 64 32 8 (LeanLLVM.Operand.reg "%137"),
                          LeanLLVM.Instr.shuffleVec
                            "%141"
                            4
                            64
                            (LeanLLVM.Operand.reg "%136")
                            (LeanLLVM.Operand.reg "%137")
                            [0, 1, 2, 3, 4, 5, 6, 7],
                          LeanLLVM.Instr.vecBitcast "%142" 8 64 64 8 (LeanLLVM.Operand.reg "%141"),
                          LeanLLVM.Instr.icmpVec
                            "%143"
                            (LeanLLVM.IPred.eq)
                            64
                            8
                            (LeanLLVM.Operand.reg "%142")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 64 8 0x22#8)),
                          LeanLLVM.Instr.bitcastMask "%or.i385" 64 (LeanLLVM.Operand.reg "%143"),
                          LeanLLVM.Instr.shuffleVec
                            "%144"
                            4
                            64
                            (LeanLLVM.Operand.reg "%136")
                            (LeanLLVM.Operand.reg "%137")
                            [0, 1, 2, 3, 4, 5, 6, 7],
                          LeanLLVM.Instr.vecBitcast "%145" 8 64 64 8 (LeanLLVM.Operand.reg "%144"),
                          LeanLLVM.Instr.icmpVec
                            "%146"
                            (LeanLLVM.IPred.eq)
                            64
                            8
                            (LeanLLVM.Operand.reg "%145")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 64 8 0x5c#8)),
                          LeanLLVM.Instr.bitcastMask "%or14.i391" 64 (LeanLLVM.Operand.reg "%146"),
                          LeanLLVM.Instr.binop
                            "%and.i.i393"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%st.sroa.0.2.lcssa")
                            (LeanLLVM.Operand.reg "%st.sroa.9.2.lcssa"),
                          LeanLLVM.Instr.binop
                            "%shl.i.i394"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%or14.i391")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000001#64)),
                          LeanLLVM.Instr.binop
                            "%not.i.i395"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%shl.i.i394")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and1.i.i396"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or14.i391")
                            (LeanLLVM.Operand.reg "%not.i.i395"),
                          LeanLLVM.Instr.binop
                            "%xor.i.i397"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%and.i.i393")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x5555555555555555#64)),
                          LeanLLVM.Instr.binop
                            "%and2.i.i398"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and1.i.i396")
                            (LeanLLVM.Operand.reg "%xor.i.i397"),
                          LeanLLVM.Instr.binop
                            "%xor3.i.i399"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%and2.i.i398")
                            (LeanLLVM.Operand.reg "%and1.i.i396"),
                          LeanLLVM.Instr.binop
                            "%not4.i.i400"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%or14.i391")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%add.i.i401"
                            (LeanLLVM.BinOp.add)
                            64
                            (LeanLLVM.Operand.reg "%and2.i.i398")
                            (LeanLLVM.Operand.reg "%or14.i391"),
                          LeanLLVM.Instr.binop
                            "%add5.i.i402"
                            (LeanLLVM.BinOp.add)
                            64
                            (LeanLLVM.Operand.reg "%xor3.i.i399")
                            (LeanLLVM.Operand.reg "%or14.i391"),
                          LeanLLVM.Instr.binop
                            "%and6.i.i403"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%not4.i.i400")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xaaaaaaaaaaaaaaaa#64)),
                          LeanLLVM.Instr.binop
                            "%and7.i.i404"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and6.i.i403")
                            (LeanLLVM.Operand.reg "%add.i.i401"),
                          LeanLLVM.Instr.binop
                            "%and8.i.i405"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%not4.i.i400")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x5555555555555555#64)),
                          LeanLLVM.Instr.binop
                            "%and9.i.i406"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and8.i.i405")
                            (LeanLLVM.Operand.reg "%add5.i.i402"),
                          LeanLLVM.Instr.binop
                            "%and11.i.i408"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and.i.i393")
                            (LeanLLVM.Operand.reg "%not4.i.i400"),
                          LeanLLVM.Instr.binop
                            "%or.i.i409"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%and7.i.i404")
                            (LeanLLVM.Operand.reg "%and11.i.i408"),
                          LeanLLVM.Instr.binop
                            "%or12.i.i410"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%or.i.i409")
                            (LeanLLVM.Operand.reg "%and9.i.i406"),
                          LeanLLVM.Instr.binop
                            "%not.i414"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%or12.i.i410")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and.i415"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or.i385")
                            (LeanLLVM.Operand.reg "%not.i414"),
                          LeanLLVM.Instr.vecBitcast "%147" 4 64 16 16 (LeanLLVM.Operand.reg "%136"),
                          LeanLLVM.Instr.binopVec
                            "%148"
                            (LeanLLVM.BinOp.lshr)
                            16
                            16
                            (LeanLLVM.Operand.reg "%147")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 16 16 0x0004#16)),
                          LeanLLVM.Instr.binopVec
                            "%149"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%139")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%150"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x40#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x82#8,
                                   0x14#8,
                                   0x01#8,
                                   0xa8#8,
                                   0x00#8,
                                   0x00#8,
                                   0x40#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x82#8,
                                   0x14#8,
                                   0x01#8,
                                   0xa8#8,
                                   0x00#8,
                                   0x00#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%149")],
                          LeanLLVM.Instr.vecBitcast "%151" 16 16 32 8 (LeanLLVM.Operand.reg "%148"),
                          LeanLLVM.Instr.binopVec
                            "%152"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%151")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%153"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x80#8,
                                   0x00#8,
                                   0x41#8,
                                   0x02#8,
                                   0x00#8,
                                   0x30#8,
                                   0x00#8,
                                   0x0c#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x00#8,
                                   0x41#8,
                                   0x02#8,
                                   0x00#8,
                                   0x30#8,
                                   0x00#8,
                                   0x0c#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%152")],
                          LeanLLVM.Instr.binopVec
                            "%and.i2326.i.i416"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%153")
                            (LeanLLVM.Operand.reg "%150"),
                          LeanLLVM.Instr.binopVec
                            "%154"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i2326.i.i416")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x3f#8)),
                          LeanLLVM.Instr.icmpVec
                            "%cmp.i21.i.i417"
                            (LeanLLVM.IPred.eq)
                            32
                            8
                            (LeanLLVM.Operand.reg "%154")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x00#8)),
                          LeanLLVM.Instr.bitcastMask "%155" 32 (LeanLLVM.Operand.reg "%cmp.i21.i.i417"),
                          LeanLLVM.Instr.binop
                            "%not.i46.i418"
                            (LeanLLVM.BinOp.xor)
                            32
                            (LeanLLVM.Operand.reg "%155")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0xffffffff#32)),
                          LeanLLVM.Instr.vecBitcast "%156" 4 64 16 16 (LeanLLVM.Operand.reg "%137"),
                          LeanLLVM.Instr.binopVec
                            "%157"
                            (LeanLLVM.BinOp.lshr)
                            16
                            16
                            (LeanLLVM.Operand.reg "%156")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 16 16 0x0004#16)),
                          LeanLLVM.Instr.binopVec
                            "%158"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%140")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%159"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x40#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x82#8,
                                   0x14#8,
                                   0x01#8,
                                   0xa8#8,
                                   0x00#8,
                                   0x00#8,
                                   0x40#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x82#8,
                                   0x14#8,
                                   0x01#8,
                                   0xa8#8,
                                   0x00#8,
                                   0x00#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%158")],
                          LeanLLVM.Instr.vecBitcast "%160" 16 16 32 8 (LeanLLVM.Operand.reg "%157"),
                          LeanLLVM.Instr.binopVec
                            "%161"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%160")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%162"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x80#8,
                                   0x00#8,
                                   0x41#8,
                                   0x02#8,
                                   0x00#8,
                                   0x30#8,
                                   0x00#8,
                                   0x0c#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x80#8,
                                   0x00#8,
                                   0x41#8,
                                   0x02#8,
                                   0x00#8,
                                   0x30#8,
                                   0x00#8,
                                   0x0c#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8,
                                   0x00#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%161")],
                          LeanLLVM.Instr.binopVec
                            "%and.i2326.i47.i420"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%162")
                            (LeanLLVM.Operand.reg "%159"),
                          LeanLLVM.Instr.binopVec
                            "%163"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i2326.i47.i420")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x3f#8)),
                          LeanLLVM.Instr.icmpVec
                            "%cmp.i21.i48.i421"
                            (LeanLLVM.IPred.eq)
                            32
                            8
                            (LeanLLVM.Operand.reg "%163")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x00#8)),
                          LeanLLVM.Instr.bitcastMask "%164" 32 (LeanLLVM.Operand.reg "%cmp.i21.i48.i421"),
                          LeanLLVM.Instr.binop
                            "%not.i49.i422"
                            (LeanLLVM.BinOp.xor)
                            32
                            (LeanLLVM.Operand.reg "%164")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0xffffffff#32)),
                          LeanLLVM.Instr.zext "%conv16.i424" 32 64 (LeanLLVM.Operand.reg "%not.i46.i418"),
                          LeanLLVM.Instr.zext "%conv17.i425" 32 64 (LeanLLVM.Operand.reg "%not.i49.i422"),
                          LeanLLVM.Instr.binop
                            "%shl18.i426"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%conv17.i425")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000020#64)),
                          LeanLLVM.Instr.binop
                            "%or19.i427"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%shl18.i426")
                            (LeanLLVM.Operand.reg "%conv16.i424"),
                          LeanLLVM.Instr.shuffleVec
                            "%165"
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i2326.i.i416")
                            (LeanLLVM.Operand.reg "%and.i2326.i47.i420")
                            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
                             25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
                             48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63],
                          LeanLLVM.Instr.icmpVec
                            "%166"
                            (LeanLLVM.IPred.eq)
                            64
                            8
                            (LeanLLVM.Operand.reg "%165")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 64 8 0x00#8)),
                          LeanLLVM.Instr.bitcastMask "%or23.i431" 64 (LeanLLVM.Operand.reg "%166"),
                          LeanLLVM.Instr.insertelement
                            "%vecinit1.i.i.i432"
                            2
                            64
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 2 64 0x0000000000000000#64))
                            (LeanLLVM.Operand.reg "%and.i415")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                          LeanLLVM.Instr.call
                            "%167"
                            (LeanLLVM.Ty.vec 2 (LeanLLVM.Ty.int 64))
                            "llvm.x86.pclmulqdq"
                            [(LeanLLVM.Ty.vec 2 (LeanLLVM.Ty.int 64), LeanLLVM.Operand.reg "%vecinit1.i.i.i432"),
                             (LeanLLVM.Ty.vec 2 (LeanLLVM.Ty.int 64),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector 64 [0xffffffffffffffff#64, 0x0000000000000000#64])),
                             (LeanLLVM.Ty.int 8, LeanLLVM.Operand.imm (LeanLLVM.Const.int 8 0x00#8))],
                          LeanLLVM.Instr.extractelement
                            "%vecext.i.i.i433"
                            2
                            64
                            (LeanLLVM.Operand.reg "%167")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                          LeanLLVM.Instr.binop
                            "%xor.i435"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%vecext.i.i.i433")
                            (LeanLLVM.Operand.reg "%st.sroa.15.2.lcssa"),
                          LeanLLVM.Instr.binop
                            "%not125"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%xor.i435")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%168"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%and.i415")
                            (LeanLLVM.Operand.reg "%xor.i435"),
                          LeanLLVM.Instr.binop
                            "%169"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%168")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and126"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or23.i431")
                            (LeanLLVM.Operand.reg "%169"),
                          LeanLLVM.Instr.binop
                            "%and129"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or19.i427")
                            (LeanLLVM.Operand.reg "%not125"),
                          LeanLLVM.Instr.binop
                            "%shl131"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.reg "%and126")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000001#64)),
                          LeanLLVM.Instr.binop
                            "%or132"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%shl131")
                            (LeanLLVM.Operand.reg "%prevS.2.lcssa"),
                          LeanLLVM.Instr.binop
                            "%not133"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%or132")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and134"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%and126")
                            (LeanLLVM.Operand.reg "%not133"),
                          LeanLLVM.Instr.binop
                            "%170"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%and129")
                            (LeanLLVM.Operand.reg "%and134"),
                          LeanLLVM.Instr.binop
                            "%or135"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%170")
                            (LeanLLVM.Operand.reg "%and.i415"),
                          LeanLLVM.Instr.binop
                            "%notmask"
                            (LeanLLVM.BinOp.shl)
                            64
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64))
                            (LeanLLVM.Operand.reg "%and"),
                          LeanLLVM.Instr.binop
                            "%sub"
                            (LeanLLVM.BinOp.xor)
                            64
                            (LeanLLVM.Operand.reg "%notmask")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.binop
                            "%and137"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%or135")
                            (LeanLLVM.Operand.reg "%sub"),
                          LeanLLVM.Instr.gep
                            "%arrayidx138"
                            (LeanLLVM.Ty.int 64)
                            (LeanLLVM.Operand.reg "%ent")
                            (LeanLLVM.Operand.reg "%shr"),
                          LeanLLVM.Instr.store
                            (LeanLLVM.Ty.int 64)
                            (LeanLLVM.Operand.reg "%and137")
                            (LeanLLVM.Operand.reg "%arrayidx138"),
                          LeanLLVM.Instr.icmp
                            "%tobool139"
                            (LeanLLVM.IPred.eq)
                            32
                            (LeanLLVM.Operand.reg "%conv")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0x00000000#32)),
                          LeanLLVM.Instr.icmp
                            "%tobool141"
                            (LeanLLVM.IPred.ne)
                            32
                            (LeanLLVM.Operand.reg "%138")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0x00000000#32)),
                          LeanLLVM.Instr.select
                            "%or.cond190"
                            (LeanLLVM.Ty.int 1)
                            (LeanLLVM.Operand.reg "%tobool139")
                            (LeanLLVM.Operand.reg "%tobool141")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 1 0x0#1)),
                          LeanLLVM.Instr.icmp
                            "%tobool143"
                            (LeanLLVM.IPred.ne)
                            32
                            (LeanLLVM.Operand.reg "%prev_ascii.1.lcssa")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0x00000000#32)),
                          LeanLLVM.Instr.select
                            "%or.cond191"
                            (LeanLLVM.Ty.int 1)
                            (LeanLLVM.Operand.reg "%or.cond190")
                            (LeanLLVM.Operand.reg "%tobool143")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 1 0x0#1))],
               term := LeanLLVM.Term.condbr (LeanLLVM.Operand.reg "%or.cond191") "if.end147" "if.then144" },
             { name := "if.then144",
               instrs := [LeanLLVM.Instr.gep
                            "%add.ptr.i.i437"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr106")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.load
                            "%171"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr.i.i437"),
                          LeanLLVM.Instr.gep
                            "%add.ptr3.i.i438"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr106")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xfffffffffffffffe#64)),
                          LeanLLVM.Instr.load
                            "%172"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            (LeanLLVM.Operand.reg "%add.ptr3.i.i438"),
                          LeanLLVM.Instr.gep
                            "%add.ptr5.i.i439"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr106")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xfffffffffffffffd#64)),
                          LeanLLVM.Instr.load
                            "%173"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            (LeanLLVM.Operand.reg "%add.ptr5.i.i439"),
                          LeanLLVM.Instr.vecBitcast "%174" 4 64 32 8 (LeanLLVM.Operand.reg "%171"),
                          LeanLLVM.Instr.binopVec
                            "%175"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%174")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%176"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0xe7#8,
                                   0xa3#8,
                                   0x83#8,
                                   0x83#8,
                                   0x8b#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xdb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xe7#8,
                                   0xa3#8,
                                   0x83#8,
                                   0x83#8,
                                   0x8b#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xdb#8,
                                   0xcb#8,
                                   0xcb#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%175")],
                          LeanLLVM.Instr.vecBitcast "%177" 4 64 16 16 (LeanLLVM.Operand.reg "%171"),
                          LeanLLVM.Instr.binopVec
                            "%178"
                            (LeanLLVM.BinOp.lshr)
                            16
                            16
                            (LeanLLVM.Operand.reg "%177")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 16 16 0x0004#16)),
                          LeanLLVM.Instr.vecBitcast "%179" 16 16 32 8 (LeanLLVM.Operand.reg "%178"),
                          LeanLLVM.Instr.binopVec
                            "%180"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%179")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%181"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x21#8,
                                   0x01#8,
                                   0x15#8,
                                   0x49#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x21#8,
                                   0x01#8,
                                   0x15#8,
                                   0x49#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%180")],
                          LeanLLVM.Instr.binopVec
                            "%and.i3741.i.i440"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%181")
                            (LeanLLVM.Operand.reg "%176"),
                          LeanLLVM.Instr.call
                            "%182"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0xe6#8,
                                   0xae#8,
                                   0xba#8,
                                   0xba#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0xe6#8,
                                   0xae#8,
                                   0xba#8,
                                   0xba#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%152")],
                          LeanLLVM.Instr.binopVec
                            "%and.i3542.i.i441"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i3741.i.i440")
                            (LeanLLVM.Operand.reg "%182"),
                          LeanLLVM.Instr.vecBitcast
                            "%and.i35.i.i442"
                            32
                            8
                            4
                            64
                            (LeanLLVM.Operand.reg "%and.i3542.i.i441"),
                          LeanLLVM.Instr.call
                            "%elt.sat.i40.i.i443"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.usub.sat.v32i8"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%172"),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x60#8))],
                          LeanLLVM.Instr.call
                            "%elt.sat.i.i.i444"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.usub.sat.v32i8"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%173"),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x70#8))],
                          LeanLLVM.Instr.binopVec
                            "%or.i43.i.i445"
                            (LeanLLVM.BinOp.or)
                            32
                            8
                            (LeanLLVM.Operand.reg "%elt.sat.i.i.i444")
                            (LeanLLVM.Operand.reg "%elt.sat.i40.i.i443"),
                          LeanLLVM.Instr.vecBitcast "%or.i.i.i446" 32 8 4 64 (LeanLLVM.Operand.reg "%or.i43.i.i445"),
                          LeanLLVM.Instr.binopVec
                            "%and.i.i.i447"
                            (LeanLLVM.BinOp.and)
                            4
                            64
                            (LeanLLVM.Operand.reg "%or.i.i.i446")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 4 64 0x8080808080808080#64)),
                          LeanLLVM.Instr.binopVec
                            "%xor.i.i.i448"
                            (LeanLLVM.BinOp.xor)
                            4
                            64
                            (LeanLLVM.Operand.reg "%and.i.i.i447")
                            (LeanLLVM.Operand.reg "%and.i35.i.i442"),
                          LeanLLVM.Instr.gep
                            "%add.ptr.i4.i449"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr106")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000001f#64)),
                          LeanLLVM.Instr.load
                            "%183"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            (LeanLLVM.Operand.reg "%add.ptr.i4.i449"),
                          LeanLLVM.Instr.gep
                            "%add.ptr3.i5.i450"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr106")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000001e#64)),
                          LeanLLVM.Instr.load
                            "%184"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            (LeanLLVM.Operand.reg "%add.ptr3.i5.i450"),
                          LeanLLVM.Instr.gep
                            "%add.ptr5.i6.i451"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%add.ptr106")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x000000000000001d#64)),
                          LeanLLVM.Instr.load
                            "%185"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            (LeanLLVM.Operand.reg "%add.ptr5.i6.i451"),
                          LeanLLVM.Instr.vecBitcast "%186" 4 64 32 8 (LeanLLVM.Operand.reg "%183"),
                          LeanLLVM.Instr.binopVec
                            "%187"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%186")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%188"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0xe7#8,
                                   0xa3#8,
                                   0x83#8,
                                   0x83#8,
                                   0x8b#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xdb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xe7#8,
                                   0xa3#8,
                                   0x83#8,
                                   0x83#8,
                                   0x8b#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xcb#8,
                                   0xdb#8,
                                   0xcb#8,
                                   0xcb#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%187")],
                          LeanLLVM.Instr.vecBitcast "%189" 4 64 16 16 (LeanLLVM.Operand.reg "%183"),
                          LeanLLVM.Instr.binopVec
                            "%190"
                            (LeanLLVM.BinOp.lshr)
                            16
                            16
                            (LeanLLVM.Operand.reg "%189")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 16 16 0x0004#16)),
                          LeanLLVM.Instr.vecBitcast "%191" 16 16 32 8 (LeanLLVM.Operand.reg "%190"),
                          LeanLLVM.Instr.binopVec
                            "%192"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%191")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x0f#8)),
                          LeanLLVM.Instr.call
                            "%193"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x21#8,
                                   0x01#8,
                                   0x15#8,
                                   0x49#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x02#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x80#8,
                                   0x21#8,
                                   0x01#8,
                                   0x15#8,
                                   0x49#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%192")],
                          LeanLLVM.Instr.binopVec
                            "%and.i3741.i7.i452"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%193")
                            (LeanLLVM.Operand.reg "%188"),
                          LeanLLVM.Instr.call
                            "%194"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.x86.avx2.pshuf.b"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm
                                (LeanLLVM.Const.vector
                                  8
                                  [0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0xe6#8,
                                   0xae#8,
                                   0xba#8,
                                   0xba#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0xe6#8,
                                   0xae#8,
                                   0xba#8,
                                   0xba#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8,
                                   0x01#8])),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%161")],
                          LeanLLVM.Instr.binopVec
                            "%and.i3542.i8.i453"
                            (LeanLLVM.BinOp.and)
                            32
                            8
                            (LeanLLVM.Operand.reg "%and.i3741.i7.i452")
                            (LeanLLVM.Operand.reg "%194"),
                          LeanLLVM.Instr.vecBitcast
                            "%and.i35.i9.i454"
                            32
                            8
                            4
                            64
                            (LeanLLVM.Operand.reg "%and.i3542.i8.i453"),
                          LeanLLVM.Instr.call
                            "%elt.sat.i40.i10.i455"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.usub.sat.v32i8"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%184"),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x60#8))],
                          LeanLLVM.Instr.call
                            "%elt.sat.i.i11.i456"
                            (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8))
                            "llvm.usub.sat.v32i8"
                            [(LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8), LeanLLVM.Operand.reg "%185"),
                             (LeanLLVM.Ty.vec 32 (LeanLLVM.Ty.int 8),
                              LeanLLVM.Operand.imm (LeanLLVM.Const.splat 32 8 0x70#8))],
                          LeanLLVM.Instr.binopVec
                            "%or.i43.i12.i457"
                            (LeanLLVM.BinOp.or)
                            32
                            8
                            (LeanLLVM.Operand.reg "%elt.sat.i.i11.i456")
                            (LeanLLVM.Operand.reg "%elt.sat.i40.i10.i455"),
                          LeanLLVM.Instr.vecBitcast
                            "%or.i.i13.i458"
                            32
                            8
                            4
                            64
                            (LeanLLVM.Operand.reg "%or.i43.i12.i457"),
                          LeanLLVM.Instr.binopVec
                            "%and.i.i14.i459"
                            (LeanLLVM.BinOp.and)
                            4
                            64
                            (LeanLLVM.Operand.reg "%or.i.i13.i458")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 4 64 0x8080808080808080#64)),
                          LeanLLVM.Instr.binopVec
                            "%xor.i.i15.i460"
                            (LeanLLVM.BinOp.xor)
                            4
                            64
                            (LeanLLVM.Operand.reg "%and.i.i14.i459")
                            (LeanLLVM.Operand.reg "%and.i35.i9.i454"),
                          LeanLLVM.Instr.binopVec
                            "%195"
                            (LeanLLVM.BinOp.or)
                            4
                            64
                            (LeanLLVM.Operand.reg "%xor.i.i.i448")
                            (LeanLLVM.Operand.reg "%xor.i.i15.i460"),
                          LeanLLVM.Instr.binopVec
                            "%or.i"
                            (LeanLLVM.BinOp.or)
                            4
                            64
                            (LeanLLVM.Operand.reg "%195")
                            (LeanLLVM.Operand.reg "%u8k.1.lcssa")],
               term := LeanLLVM.Term.br "if.end147" },
             { name := "if.end147",
               instrs := [LeanLLVM.Instr.phi
                            "%u8k.3"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            [("if.then103", LeanLLVM.Operand.reg "%u8k.1.lcssa"),
                             ("if.then144", LeanLLVM.Operand.reg "%or.i")],
                          LeanLLVM.Instr.binop
                            "%and148"
                            (LeanLLVM.BinOp.and)
                            64
                            (LeanLLVM.Operand.reg "%arm")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000002#64)),
                          LeanLLVM.Instr.icmp
                            "%tobool149.not"
                            (LeanLLVM.IPred.eq)
                            64
                            (LeanLLVM.Operand.reg "%and148")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64))],
               term := LeanLLVM.Term.condbr (LeanLLVM.Operand.reg "%tobool149.not") "if.end153.thread" "if.then150" },
             { name := "if.then150",
               instrs := [LeanLLVM.Instr.shuffleVec
                            "%196"
                            4
                            64
                            (LeanLLVM.Operand.reg "%136")
                            (LeanLLVM.Operand.reg "%137")
                            [0, 1, 2, 3, 4, 5, 6, 7],
                          LeanLLVM.Instr.vecBitcast "%197" 8 64 64 8 (LeanLLVM.Operand.reg "%196"),
                          LeanLLVM.Instr.icmpVec
                            "%198"
                            (LeanLLVM.IPred.ult)
                            64
                            8
                            (LeanLLVM.Operand.reg "%197")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.splat 64 8 0x20#8)),
                          LeanLLVM.Instr.bitcastMask "%or.i467" 64 (LeanLLVM.Operand.reg "%198"),
                          LeanLLVM.Instr.callVoid
                            "leanllvm_json_escape_list"
                            [(LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%or14.i391"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%or.i467"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%xor.i435"),
                             (LeanLLVM.Ty.int 64, LeanLLVM.Operand.reg "%shr"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%xp"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%nxp"),
                             (LeanLLVM.Ty.ptr, LeanLLVM.Operand.reg "%xcarry")]],
               term := LeanLLVM.Term.br "if.end153.thread" },
             { name := "if.end153.thread",
               instrs := [LeanLLVM.Instr.call
                            "%199"
                            (LeanLLVM.Ty.int 32)
                            "llvm.x86.avx.ptestz.256"
                            [(LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64), LeanLLVM.Operand.reg "%u8k.3"),
                             (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64), LeanLLVM.Operand.reg "%u8k.3")],
                          LeanLLVM.Instr.icmp
                            "%cmp155495"
                            (LeanLLVM.IPred.eq)
                            32
                            (LeanLLVM.Operand.reg "%199")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0x00000000#32))],
               term := LeanLLVM.Term.br "if.end170" },
             { name := "if.end153",
               instrs := [LeanLLVM.Instr.call
                            "%200"
                            (LeanLLVM.Ty.int 32)
                            "llvm.x86.avx.ptestz.256"
                            [(LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64), LeanLLVM.Operand.reg "%u8k.1.lcssa"),
                             (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64), LeanLLVM.Operand.reg "%u8k.1.lcssa")],
                          LeanLLVM.Instr.icmp
                            "%cmp155"
                            (LeanLLVM.IPred.eq)
                            32
                            (LeanLLVM.Operand.reg "%200")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0x00000000#32)),
                          LeanLLVM.Instr.icmp
                            "%cmp158.not.not"
                            (LeanLLVM.IPred.eq)
                            64
                            (LeanLLVM.Operand.reg "%n")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64))],
               term := LeanLLVM.Term.condbr (LeanLLVM.Operand.reg "%cmp158.not.not") "if.end170" "if.then164" },
             { name := "if.then164",
               instrs := [LeanLLVM.Instr.gep
                            "%201"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%b")
                            (LeanLLVM.Operand.reg "%n"),
                          LeanLLVM.Instr.gep
                            "%arrayidx166"
                            (LeanLLVM.Ty.int 8)
                            (LeanLLVM.Operand.reg "%201")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0xffffffffffffffff#64)),
                          LeanLLVM.Instr.load "%202" (LeanLLVM.Ty.int 8) (LeanLLVM.Operand.reg "%arrayidx166"),
                          LeanLLVM.Instr.binop
                            "%203"
                            (LeanLLVM.BinOp.and)
                            8
                            (LeanLLVM.Operand.reg "%202")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 8 0xfe#8)),
                          LeanLLVM.Instr.icmp
                            "%cmp.i"
                            (LeanLLVM.IPred.eq)
                            8
                            (LeanLLVM.Operand.reg "%203")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 8 0xc0#8)),
                          LeanLLVM.Instr.icmp
                            "%cmp3.i"
                            (LeanLLVM.IPred.ugt)
                            8
                            (LeanLLVM.Operand.reg "%202")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 8 0xf4#8)),
                          LeanLLVM.Instr.binop
                            "%204"
                            (LeanLLVM.BinOp.or)
                            1
                            (LeanLLVM.Operand.reg "%cmp3.i")
                            (LeanLLVM.Operand.reg "%cmp.i"),
                          LeanLLVM.Instr.binop
                            "%or169500"
                            (LeanLLVM.BinOp.or)
                            1
                            (LeanLLVM.Operand.reg "%cmp155")
                            (LeanLLVM.Operand.reg "%204")],
               term := LeanLLVM.Term.br "if.end170" },
             { name := "if.end170",
               instrs := [LeanLLVM.Instr.phi
                            "%ascii.2499"
                            (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64))
                            [("if.then164", LeanLLVM.Operand.reg "%ascii.1.lcssa"),
                             ("if.end153", LeanLLVM.Operand.reg "%ascii.1.lcssa"),
                             ("if.end153.thread", LeanLLVM.Operand.reg "%or.i279")],
                          LeanLLVM.Instr.phi
                            "%err.0.in"
                            (LeanLLVM.Ty.int 1)
                            [("if.then164", LeanLLVM.Operand.reg "%or169500"),
                             ("if.end153", LeanLLVM.Operand.reg "%cmp155"),
                             ("if.end153.thread", LeanLLVM.Operand.reg "%cmp155495")],
                          LeanLLVM.Instr.call
                            "%205"
                            (LeanLLVM.Ty.int 32)
                            "llvm.x86.avx.ptestz.256"
                            [(LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64), LeanLLVM.Operand.reg "%ascii.2499"),
                             (LeanLLVM.Ty.vec 4 (LeanLLVM.Ty.int 64),
                              LeanLLVM.Operand.imm (LeanLLVM.Const.splat 4 64 0x8080808080808080#64))],
                          LeanLLVM.Instr.icmp
                            "%cmp172"
                            (LeanLLVM.IPred.ne)
                            32
                            (LeanLLVM.Operand.reg "%205")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 32 0x00000000#32)),
                          LeanLLVM.Instr.zext "%conv174" 1 64 (LeanLLVM.Operand.reg "%cmp172"),
                          LeanLLVM.Instr.select
                            "%shl175"
                            (LeanLLVM.Ty.int 64)
                            (LeanLLVM.Operand.reg "%err.0.in")
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000002#64))
                            (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64)),
                          LeanLLVM.Instr.binop
                            "%or176"
                            (LeanLLVM.BinOp.or)
                            64
                            (LeanLLVM.Operand.reg "%shl175")
                            (LeanLLVM.Operand.reg "%conv174")],
               term := LeanLLVM.Term.ret (LeanLLVM.Ty.int 64) (some (LeanLLVM.Operand.reg "%or176")) }] }

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
-- five, and the emitted multiset is the four `pshuf.b` sites per classifier
-- body (three bodies: the ASCII phase, the fused loop and the peeled tail) plus
-- the six each of the three DFA sites adds, the four `usub.sat` sites per DFA
-- site, the one `pclmulqdq` site per classifier body, six lane tests (the three
-- per-block ASCII tests and the three return-word tests), and the three
-- escape-list calls.  No other callee can appear.
#guard
  decide (((callTargets s1BlocksFunction).mergeSort (fun a b => a ≤ b)).eraseDups =
    censusSymbols)
#guard
  decide ((callTargets s1BlocksFunction).mergeSort (fun a b => a ≤ b) =
    ["leanllvm_json_escape_list", "leanllvm_json_escape_list",
     "leanllvm_json_escape_list",
     "llvm.usub.sat.v32i8", "llvm.usub.sat.v32i8",
     "llvm.usub.sat.v32i8", "llvm.usub.sat.v32i8",
     "llvm.usub.sat.v32i8", "llvm.usub.sat.v32i8",
     "llvm.usub.sat.v32i8", "llvm.usub.sat.v32i8",
     "llvm.usub.sat.v32i8", "llvm.usub.sat.v32i8",
     "llvm.usub.sat.v32i8", "llvm.usub.sat.v32i8",
     "llvm.x86.avx.ptestz.256", "llvm.x86.avx.ptestz.256",
     "llvm.x86.avx.ptestz.256", "llvm.x86.avx.ptestz.256",
     "llvm.x86.avx.ptestz.256", "llvm.x86.avx.ptestz.256",
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
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.avx2.pshuf.b", "llvm.x86.avx2.pshuf.b",
     "llvm.x86.pclmulqdq", "llvm.x86.pclmulqdq",
     "llvm.x86.pclmulqdq"])

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
